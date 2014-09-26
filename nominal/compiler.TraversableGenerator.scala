// TODO: delete this file after obsolescence

package nominal
package compiler

/** Generate traversable instances for functors */

import scala.reflect.macros.blackbox.Context

import DatatypeRepresentation._

/** generate 'new Traversable { blah blah blah }'
  *
  * @param functor the functor whose traversable instance is to be generated
  * @param subcats @see generateSubcategories
  */
trait TraversableGenerator extends SynonymGenerator with util.Traverse {

  // only generate 'new TraversableN { ... }'
  // leave the wrapping of generics to someone else
  def generateTraversable(c: Context)(functor: DataConstructor): c.Tree =
    generateBoundedTraversable(c)(functor, extractSubcatBounds(functor.body))

  def generateBoundedTraversable(c: Context)(functor: DataConstructor, subcats: Map[Name, Datatype]): c.Tree =
    newTraversable(c)(functor.arity, generateTraversableBody(c)(functor, subcats))

  def generateTraversableBody(c: Context)(functor: DataConstructor, subcats: Map[Name, Datatype]): Many[c.Tree] = {
    // type Cat1 = Any; type Cat2 = Abs[_, _]
    val subcategories = generateSubcategories(c)(functor, subcats)
    val mapSynonym = generateBoundedSynonym(c)(mappingOnObjects, functor, subcats)
    val imports = scalaLanguageFeatureImports(c)
    val defTraverse = generateDefTraverse(c)(functor, subcats)
    imports ++ subcategories :+ mapSynonym :+ defTraverse
  }

  def extractSubcatBounds(data: Datatype): Map[Name, Datatype] =
    data.everywhereQ[Map[Name, Datatype]]({
      case Variant(_, nominals) =>
        nominals.view.map({
          case RecordAssignment(Record(name, fields), TypeVar(param)) =>
            Map(param -> Record(name, fields map {
              case Field(fieldName, _) => Field(fieldName, TypeVar(anyType))
            }))

          case _ =>
            Map.empty
        }).foldLeft(Map.empty[Name, Datatype])(_ ++ _)
    }).foldLeft(Map.empty[Name, Datatype])(_ ++ _)

  def newTraversable(c: Context)(arity: Int, body: Many[c.Tree]): c.Tree = {
    import c.universe._
    require(arity >= 1 /* && arity <= max N such that TraversableN exists */)
    val q"new $traversableN" = c.parse(s"new $fullyQualifiedTraversableTrait${if (arity == 1) "" else arity.toString }")
    q"new $traversableN { ..$body }"
  }

  /** type Cat1 = Any; type Cat2 = Abs[_, _]
    *
    * @param subcats mapping each param name to the subcategory whose objects the param can be bound to
    *                if a mapping doesn't exist, then that param can bind to any scala type
    */
  def generateSubcategories(c: Context)(functor: DataConstructor, subcats: Map[Name, Datatype]): Many[c.Tree] = {
    import c.universe._
    functor.params.zipWithIndex.map {
      case (Param(name, _), i) =>
        val catName = if (functor.params.size == 1) "Cat" else s"Cat${i + 1}"
        if (subcats contains name)
          generateConcreteSynonym(c)(catName, subcats(name))
        else
          c parse s"type $catName = Any"
    }
  }

  /** def traverse[A <: Cat, B <: Cat](G: Applicative)(f: A => G.Map[B], mA: this.Map[A]): G.Map[this.Map[B]]
    */
  def generateDefTraverse(c: Context)(functor: DataConstructor, subcats: Map[Name, Datatype]): c.Tree = {
        import c.universe._
    // type parameters of .traverse
    val tA: Many[TypeName] = functor.params.map(_ => TypeName(c freshName "A"))
    val tB: Many[TypeName] = functor.params.map(_ => TypeName(c freshName "B"))
    val unmangleA = Map((tA, functor.params).zipped.map({ case (a, p) => (a.toString, p.name) }): _*)
    val unmangleB = Map((tB, functor.params).zipped.map({ case (b, p) => (b.toString, p.name) }): _*)
    val unmangledTypeNames = unmangleA ++ unmangleB
    val typeDefs: Many[TypeDef] =
      mkBoundedTypeDefs(c)(
        (tA ++ tB) map (Param invariant _.toString),
        unmangledTypeNames flatMap {
          case (mangled, param) if subcats contains param => Some((mangled, subcats(param)))
          case _ => None
        })

    // applicative: Applicative.Endofunctor[F]
    val applicative: TermName = TermName(c freshName "applicative")
    val applicativeType = getApplicative(c)

    // type constructor of the applicative functor
    val tF = getFunctorMapOnObjects(c)(applicative)

    // functions A => F[B], C => F[D], etc.
    val functions: Many[TermName] = functor.params.map(param => TermName(c freshName "f"))
    val functionTypes: Many[Tree] = (tA, tB).zipped.map {
      case (a, b) =>
        val q"??? : $functionType" = q"??? : ($a => $tF[$b])"
        functionType
    }

    // mA: Map[A, C, ...]
    val mA: TermName = TermName(c freshName "mA")
    val mapping: TypeName = TypeName(mappingOnObjects)
    val q"??? : $mAType" = q"??? : $mapping[..$tA]"

    // F[Map[B, D, ...]]
    val q"??? : $resultType" = q"??? : $tF[$mapping[..$tB]]"

    // (f: A => F[B], g: C => F[D], ..., mA: Map[A, C, ...])
    val explicitParams = mkValDefs(c)(functions :+ mA, functionTypes :+ mAType)

    // mapping functor.params corresponding function calls
    val env: Map[DatatypeRepresentation.Name, Tree => Tree] =
      Map(
        (functor.params, functions).zipped.map {
          case (param, function) =>
            (param.name, (x: c.Tree) => q"$function($x)")
        } : _*)

    val body: Tree = generateDefTraverseBody(c)(
      q"$mA",
      functor.body,
      unmangleA.map(_.swap),
      unmangleB.map(_.swap),
      env, applicative)

    q"def traverse[..$typeDefs]($applicative : $applicativeType)(..$explicitParams): $resultType = $body"
  }

  /** body of def traverse[...](...)(...)
    *
    * @param mA          name of Map[A..]
    * @param datatype    structure of Map[A..]
    * @param env         mapping names to functions: beware name capturing!
    * @param applicative the name of the Applicative.Endofunctor instance
    */
  def generateDefTraverseBody(c: Context)(
    mA: c.Tree,
    datatype: Datatype,
    mangleA: Map[DatatypeRepresentation.Name, DatatypeRepresentation.Name],
    mangleB: Map[DatatypeRepresentation.Name, DatatypeRepresentation.Name],
    env: Map[DatatypeRepresentation.Name, c.Tree => c.Tree],
    applicative: c.TermName
  ):
      c.Tree =
  {
    import c.universe._

    def argType    = meaning(c)(datatype rename mangleA)
    def resultType = meaning(c)(datatype rename mangleB)
    def mkPure(x: Tree): Tree = q"$applicative.pure[$resultType]($x)"

    datatype match {
      case TypeVar(x) =>
        if (env contains x)
          q"${env(x)(mA)}"
        else
          mkPure(mA)

      case fixedpoint @ FixedPoint(x, body) =>
        // type synonyms, reduces clutter & code explosion
        //
        // takes synonym generation into own hand
        // s. t. type variables denoting recursive positions auto-expand,
        // making `body` the 1-step unrolling of the recursive datatype
        val argData = (fixedpoint rename mangleA).asInstanceOf[FixedPoint]
        val mBData = (fixedpoint rename mangleB).asInstanceOf[FixedPoint]
        val mAType = TypeName(c freshName x + "A")
        val argSynonym = generateConcreteSynonym(c)(mAType.toString, argData)
        val mBType = TypeName(x)
        val fixSynonym = generateConcreteSynonym(c)(x, mBData)
        val unrolledFix = TypeName(c freshName x + "U")
        val unrolledSynonym = generateConcreteSynonym(c)(unrolledFix.toString, mBData.body)
        val resultType = TypeName(c freshName "F_" + x)
        val resultSynonym = q"type $resultType = ${getFunctorMapOnObjects(c)(applicative)}[$mBType]"

        // `recurse`: fresh label for jumping to this point
        val recurse = TermName(c freshName "recurse")
        val recursiveCall: Tree => Tree = x => q"$recurse($x)"
        // on subsequent fixed-point variables, jump back to this point
        val newEnv = env.updated(x, recursiveCall)
        // body of things to jump into
        val unrolled = q"$mA.unroll"
        // update mangeleA and mangleB with new info
        val newMangleA = mangleA + (x -> mAType.toString) // toString is okay because mAType: TypeName
        val newMangleB = mangleB - x // B doesn't have to be mangled, because mBType = TypeName(x)
        val unrolledBody = generateDefTraverseBody(c)(unrolled, body, newMangleA, newMangleB, newEnv, applicative)

        // get unfolded part of the synonym
        val tq"$fix[$patternFunctor]" = meaning(c)(mBData)
        val roll = q"${getRoll(c)}.apply[$patternFunctor] _"
        val pureRoll = q"$applicative.pure[$unrolledFix => $mBType]($roll)"
        val autoRolled = q"$applicative.call($pureRoll, $unrolledBody)"

        val recursiveDef = q"def $recurse($mA : $mAType): $resultType = $autoRolled"
        q"{$argSynonym ; $fixSynonym ; $unrolledSynonym ; $resultSynonym ; $recursiveDef ; $recurse($mA)}"

      case variant @ Variant(header, cases) =>
        if (cases.isEmpty)
          c parse s"""_root_.scala.sys error "instance of empty variant $header""""
        else
          Match(mA,
            cases.map(_ match {
              case record @ Record(_, _) =>
                generateRecordBody(c)(mA, record, mangleA, mangleB, env, applicative)

              case RecordAssignment(recordDecl, typeVar) =>
                generateSummandPosition(c)(variant, recordDecl, typeVar, mangleA, mangleB, env, applicative)

              case otherwise =>
                abortWithError(c)(
                  mA.pos,
                  s"generating traversable instance for ${header.name}, got unexpected case:\n\n  $otherwise\n.")

            }).toList)

      case record @ Record(_, _) =>
        // put naked record in identity
        // should generate warning or not?
        //   c.warning(q"".pos, s"naked record $datatype")
        Match(mA, List(generateRecordBody(c)(mA, record, mangleA, mangleB, env, applicative)))

      case Reader(domain, range) =>
        // by function composition, can build `domain => F[ σ(range) ]`.
        // want F[ σ(domain => range) ] = F[ domain => σ(range) ].
        // this looks as if it requries F to be more than applicative.
        ???

      case Intersect(lhs, rhs) =>
        // not sure what to do in this case
        ???
    }
  }

  // parameter in a sum position
  def generateSummandPosition(c: Context)(
    _super: Variant,
    record: Record,
    typeVar: TypeVar,
    mangleA: Map[Name, Name],
    mangleB: Map[Name, Name],
    env: Map[Name, c.Tree => c.Tree],
    applicative: c.TermName
  ): c.universe.CaseDef =
    recordCaseDef(c)(record) {
      case (arg, fieldNames) =>
        import c.universe._
        val argType = meaning(c)(typeVar rename mangleA)
        val argCast = q"$arg.asInstanceOf[$argType]"
        val body = generateDefTraverseBody(c)(argCast, typeVar, mangleA, mangleB, env, applicative)
        val resultType = meaning(c)(_super rename mangleB)
        q"$body.asInstanceOf[${getFunctorMapOnObjects(c)(applicative)}[$resultType]]"
    }

  def generateRecordBody(c: Context)(
    mA: c.Tree,
    record: Record,
    mangleA: Map[Name, Name],
    mangleB: Map[Name, Name],
    env: Map[Name, c.Tree => c.Tree],
    applicative: c.TermName
  ): c.universe.CaseDef = {
    import c.universe._
    recordCaseDef(c)(record) {
      case (recordName, fieldNames) if fieldNames.size > 0 =>
        mkCallTree(c)(
          applicative,
          mkPureConstructor(c)((record rename mangleB).asInstanceOf[Record], applicative) +:
            fieldNames.zip(record.fields).map({
              case (name, Field(_, body)) =>
                generateDefTraverseBody(c)(q"$name", body, mangleA, mangleB, env, applicative)
            }))

      case (recordName, fieldNames) if fieldNames.size == 0 =>
        val resultType = meaning(c)(record rename mangleB)
        q"$applicative.pure[$resultType]($recordName)"
    }
  }

  def mkPureConstructor(c: Context)(
    record: Record, // mangled already
    applicative: c.TermName):
        c.Tree =
  {
    import c.universe._
    val resultType = meaning(c)(uncurryFunctionType(record.fields.map(_.get), record))

    val params = record.fields.map(field => TermName(c freshName field.name))
    val reconstructedRecord = q"${TermName(record.name)}(..$params)"
    val fun = params.foldRight(reconstructedRecord) {
      case (param, body) =>
        Function(List(mkValDef(c)(param, TypeTree())), body)
    }

    q"$applicative.pure[$resultType]($fun)"
  }

  // turn multi-argument function types into nested readers
  def uncurryFunctionType(args: Many[Datatype], result: Datatype): Datatype =
    args.foldRight(result) { case (arg, res) => Reader(arg, res) }

  def scalaLanguageFeatureImports(c: Context): Many[c.Tree] = {
    import c.universe._
    Many(
      q"import _root_.scala.language.higherKinds",
      q"import _root_.scala.language.implicitConversions")
  }
}

object TraversableGenerator {
  object Tests extends TraversableGenerator with util.AssertEqual with util.ExpectCompilerError {
    import scala.language.experimental.macros
    import scala.annotation.StaticAnnotation

    val ConstInt =
      DataConstructor(Many(Param covariant "X"), TypeVar("Int"))

    val Identity =
      DataConstructor(Many(Param covariant "X"), TypeVar("X"))

    val Product =
      DataConstructor(Many(Param covariant "X", Param covariant "Y"),
        Record("Tuple2", Many(Field("_1", TypeVar("X")), Field("_2", TypeVar("Y")))))

    val List2 =
      DataConstructor(Many(Param covariant "A"),
        FixedPoint("List",
          Variant("ListT", Many(
            Record("Nil", Many.empty),
            Record("Cons", Many(
              Field("head",
                FixedPoint("List",
                  Variant("ListT", Many(
                    Record("Nil", Many.empty),
                    Record("Cons", Many(
                      Field("head", TypeVar("A")),
                      Field("tail", TypeVar("List")))))))),
              Field("tail", TypeVar("List"))))))))

    val NilF =
      DataConstructor(Many(Param covariant "X"),
        FixedPoint("List",
          Variant("ListT", Many(
            RecordAssignment(Record("Nil", Many.empty), TypeVar("X")),
            Record("Cons", Many(
              Field("head", TypeVar("Int")),
              Field("tail", TypeVar("List"))))))))

    val NilT =
      DataConstructor(Many(Param covariant "X"),
        Variant("ListT", Many(
          RecordAssignment(Record("Nil", Many.empty), TypeVar("X")),
          Record("Cons", Many(
            Field("head", TypeVar("Int")),
            Field("tail", TypeVar("List[Int]")))))))

    val ConsF =
      DataConstructor(Many(Param covariant "X"),
        FixedPoint("List",
          Variant("ListT", Many(
            Record("Nil", Many.empty),
            RecordAssignment(
              Record("Cons", Many(
                Field("head", TypeVar("Int")),
                Field("tail", TypeVar("List")))),
              TypeVar("X"))))))

    val LF =
      DataConstructor(Many(Param covariant "X"),
        Variant("PlusT", Many(
          RecordAssignment(
            Record("LHS", Many(Field("get", TypeVar("Nothing")))),
            TypeVar("X")),
          Record("RHS", Many(Field("get", TypeVar("Int")))))))

    // test generation of `type Cat = ...`
    class c123 extends StaticAnnotation { def macroTransform(annottees: Any*): Any = macro Impl.c123 }

    // failed attempt to assert that C2.Map[Boolean] does not conform to declared bounds
    // because c.typecheck does not detect this error
    def c2MapError: String = macro Impl.c2MapError

    object Impl {
      def c123(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
        import c.universe._

        c.Expr(q"""
          // constant functor on everything
          val C1 = ${generateTraversable(c)(ConstInt)}

          // identity functor on integers
          val C2 = ${generateBoundedTraversable(c)(Identity, Map("X" -> TypeVar("Int")))}

          // product functor with 2nd component limited to Either[Int, Boolean]
          val C3 = ${generateBoundedTraversable(c)(Product, Map("Y" -> TypeVar("Either[Int, Boolean]")))}

          val List2 = ${generateTraversable(c)(List2)}

          val LF = ${generateTraversable(c)(LF)}

          val NilT = ${generateTraversable(c)(NilT)}

          val NilF = ${generateTraversable(c)(NilF)}

          val ConsF = ${generateTraversable(c)(ConsF)}
        """)
      }

      // must be called with a context where c123 is already expanded
      def c2MapError(c: Context): c.Expr[String] = {
        import c.universe._
        expectCompilerError(c)(q"??? : C2.Map[Boolean]")
      }
    }

  }
}
