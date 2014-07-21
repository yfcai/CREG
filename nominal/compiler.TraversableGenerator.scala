package nominal
package compiler

/** Generate code for the pattern functor only
  * To test the waters before generating for arbitrary functors
  */

import scala.reflect.macros.blackbox.Context

import DatatypeRepresentation._

/** generate 'new Traversable { blah blah blah }'
  *
  * @param functor the functor whose traversable instance is to be generated
  * @param subcats @see generateSubcategories
  */
trait TraversableGenerator extends SynonymGenerator {

  // only generate 'new TraversableN { ... }'
  // leave the wrapping of generics to someone else
  def generateTraversable(c: Context)(functor: DataConstructor, subcats: Map[Name, Datatype]): c.Tree =
    newTraversable(c)(functor.arity, generateTraversableBody(c)(functor, subcats))

  def generateTraversableBody(c: Context)(functor: DataConstructor, subcats: Map[Name, Datatype]): Many[c.Tree] = {
    // type Cat1 = Any; type Cat2 = Abs[_, _]
    val subcategories = generateSubcategories(c)(functor, subcats)
    val mapSynonym = generateBoundedSynonym(c)(mappingOnObjects, functor, subcats)
    val defTraverse = generateDefTraverse(c)(functor, subcats)
    val imports = scalaLanguageFeatureImports(c)
    imports ++ subcategories :+ mapSynonym :+ defTraverse
  }

  def mappingOnObjects: String = "Map"

  def identityFunctorLocationString: String = "_root_.nominal.lib.Applicative.Identity"

  def getRoll(c: Context): c.Tree = c parse "_root_.nominal.lib.Roll"

  def applicativeEndofunctor(c: Context)(f: c.TypeName): c.Tree = {
    import c.universe._
    val q"??? : $tpe" = q"??? : _root_.nominal.lib.Applicative.Endofunctor[$f]"
    tpe
  }

  def fullyQualifiedTraversableTrait: String = "_root_.nominal.lib.Traversable"

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

  /** def traverse[F[_]: IsApplicative, A <: Cat, B <: Cat](f: A => F[B], t0: Map[A]): F[Map[B]]
    */
  def generateDefTraverse(c: Context)(functor: DataConstructor, subcats: Map[Name, Datatype]): c.Tree = {
    import c.universe._
    // type parameters of .traverse
    val tF: TypeName = TypeName(c freshName "F")
    val tA: Many[TypeName] = functor.params.map(_ => TypeName(c freshName "A"))
    val tB: Many[TypeName] = functor.params.map(_ => TypeName(c freshName "B"))
    val q"trait Trait[$typeDefF]" = q"trait Trait[$tF[_]]"
    val unmangleA = Map((tA, functor.params).zipped.map({ case (a, p) => (a.toString, p.name) }): _*)
    val unmangleB = Map((tB, functor.params).zipped.map({ case (b, p) => (b.toString, p.name) }): _*)
    val unmangledTypeNames = unmangleA ++ unmangleB
    val typeDefs: Many[TypeDef] =
      typeDefF +: mkBoundedTypeDefs(c)(
        (tA ++ tB) map (Param invariant _.toString),
        unmangledTypeNames flatMap {
          case (mangled, param) if subcats contains param => Some((mangled, subcats(param)))
          case _ => None
        })

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

    // applicative: Applicative.Endofunctor[F]
    val applicative: TermName = TermName(c freshName "applicative")
    val q"??? : $applicativeType" = q"??? : ${applicativeEndofunctor(c)(tF)}"

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

    val result = q"def traverse[..$typeDefs](..$explicitParams)(implicit $applicative : $applicativeType): $resultType = $body"

    println(s"\nTRAVERSE: $result\n")
    println(s"TRAVERSE BODY: $body\n")

    result
  }

  def mkValDef(c: Context)(termName: c.TermName, tpe: c.Tree): c.universe.ValDef = {
    import c.universe._
    val methodIn = TermName(c freshName "method")
    val q"def $methodOut($valDef)" = q"def $methodIn($termName : $tpe)"
    valDef
  }

  def mkValDefs(c: Context)(names: Many[c.TermName], types: Many[c.Tree]): Many[c.universe.ValDef] =
    (names, types).zipped.map { case (name, tpe) => mkValDef(c)(name, tpe) }

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
        // `recurse`: fresh label for jumping to this point
        val recurse = TermName(c freshName "recurse")
        val recursiveCall: Tree => Tree = x => q"$recurse($x)"
        // on subsequent fixed-point variables, jump back to this point
        val newEnv = env.updated(x, recursiveCall)
        // body of things to jump into
        val unrolled = q"$mA.unroll"
        val newMangleA = mangleA - x
        val newMangleB = mangleB - x
        val recurseBody = generateDefTraverseBody(c)(unrolled, body, newMangleA, newMangleB, newEnv, applicative)
        // tie label and code together
        val mAType     = meaning(c)(fixedpoint rename mangleA)
        val resultType = meaning(c)(fixedpoint rename mangleB)
        val recursiveDef = q"def $recurse($mA : $mAType): $resultType = $recurseBody"
        q"{$recursiveDef ; $recurse($mA)}"

      case Variant(header, cases) =>
        if (cases.isEmpty)
          c parse s"""_root_.scala.sys error "instance of empty variant $header""""
        else {
          // for now, require subfields of variants be records
          // if they are not, then they should be reconstructed as records
          // with type reification.
          require(cases.map(_.isInstanceOf[Record]).min,
            s"expect cases of traversable variant be records; got:\n\n  $datatype")
          Match(mA,
            cases.map(record =>
              generateRecordBody(c)(
                mA, record.asInstanceOf[Record], mangleA, mangleB, env, applicative)).toList)
        }

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

  def generateRecordBody(c: Context)(
    mA: c.Tree,
    datatype: Record,
    mangleA: Map[DatatypeRepresentation.Name, DatatypeRepresentation.Name],
    mangleB: Map[DatatypeRepresentation.Name, DatatypeRepresentation.Name],
    env: Map[DatatypeRepresentation.Name, c.Tree => c.Tree],
    applicative: c.TermName
  ): c.universe.CaseDef = {
    import c.universe._
    // dupe code...
    def argType    = meaning(c)(datatype rename mangleA)
    def resultType = meaning(c)(datatype rename mangleB)
    def mkPure(x: Tree): Tree = q"$applicative.pure[$resultType]($x)"
    datatype match {
      case Record(name, fields) =>
        if (fields.size == 0) {
          val ident = Ident(TermName(name))
          cq"$ident => ${mkPure(ident)}"
        }
        else {
          val caseName = TermName(name)
          val fieldNames = fields.map(field => TermName(c freshName field.name))
          val fieldBindings = fieldNames.map(name => Bind(name, q"${termNames.WILDCARD}"))
          val body = mkCallTree(c)(
            applicative,
            mkPureConstructor(c)((datatype rename mangleB).asInstanceOf[Record], applicative) +:
              fieldNames.zip(fields).map({
                case (name, Field(_, body)) =>
                  generateDefTraverseBody(c)(q"$name", body, mangleA, mangleB, env, applicative)
              }))
          cq"$caseName(..$fieldBindings) => $body"
        }
    }
  }

  def mkCallTree(c: Context)(applicative: c.TermName, leaves: Many[c.Tree]): c.Tree = {
    import c.universe._
    leaves.reduceLeft[c.Tree]({
      case (callTree, nextArg) =>
        q"$applicative.call($callTree, $nextArg)"
    })
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
          Variant("ListF", Many(
            Record("Nil", Many.empty),
            Record("Cons", Many(
              Field("head",
                FixedPoint("List",
                  Variant("ListF", Many(
                    Record("Nil", Many.empty),
                    Record("Cons", Many(
                      Field("head", TypeVar("A")),
                      Field("tail", TypeVar("List")))))))),
              Field("tail", TypeVar("List"))))))))
              

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
          val C1 = ${generateTraversable(c)(ConstInt, Map.empty)}

          // identity functor on integers
          val C2 = ${generateTraversable(c)(Identity, Map("X" -> TypeVar("Int")))}

          // product functor with 2nd component limited to Either[Int, Boolean]
          val C3 = ${generateTraversable(c)(Product, Map("Y" -> TypeVar("Either[Int, Boolean]")))}

          val List2 = ${generateTraversable(c)(List2, Map.empty)}
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
