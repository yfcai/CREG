package nominal
package compiler

import scala.reflect.macros.blackbox.Context
import scala.reflect.macros.TypecheckException

import DatatypeRepresentation._

trait UniverseConstruction extends util.AbortWithError with util.TupleIndex with util.Paths {

  // ====================== //
  // FROM DATATYPE TO SCALA //
  // ====================== //

  /** @param rep    our representation of a datatype
    * @return       scala's representation of a type
    */
  def meaning(c: Context)(rep: Datatype): c.Tree = {
    import c.universe._
    rep match {
      case TypeConst(tpe) =>
        val q"??? : $result" = c parse(s"??? : ($tpe)")
        result

      case TypeVar(tpe) =>
        val q"??? : $result" = c.parse(s"??? : ($tpe)")
        result

      case Record(name, fields) =>
        tq"${TypeName(name)}[..${fields.map(field => meaning(c)(field.get))}]"

      case Variant(typeVar, records) =>
        tq"${meaning(c)(TypeVar(typeVar))}[..${records.map(record => meaning(c)(record))}]"

      case FixedPoint(paramName, body) =>
        // to take the fixed point, the data constructor must be unary
        val fix = getFix(c)
        val innerType = mkInnerType(c)
        val typeDef = covariantTypeDef(c)(paramName)

        tq"""
          $fix[({
            type $innerType[$typeDef] = ${meaning(c)(body)}
          })#$innerType]
        """

      case RecordAssignment(rcd, tvar) =>
        meaning(c)(tvar)

      case LetBinding(lhs, rhs) =>
        meaning(c)(rhs)

      case FunctorApplication(functor, args) =>
        val xs = args map (x => meaning(c)(x))
        tq"${getTreeMapOnObjects(c)(c parse functor.code)}[..$xs]"
    }
  }

  def noRecognition(data: Datatype): Nothing =
    sys error s"unrecognized datatype:\n\n    $data"

  /** @param rep datatype representation
    *
    * @return corresponding scala type with all type synonyms resolved
    */
  def scalaType(c: Context)(rep: Datatype): c.Type =
    treeToType(c)(meaning(c)(rep))

  def treeToType(c: Context)(typeTree: c.Tree): c.Type = {
    import c.universe._
    c.typecheck(q"??? : $typeTree").tpe.dealias
  }

  def mkInnerType(c: Context): c.TypeName = c.universe.TypeName(c freshName "innerType")

  /** @param name name of type parameter
    * @return covariant type parameter of that name
    */
  def covariantTypeParam(c: Context)(name: Name): c.Tree = {
    import c.universe._
    val q"type Dummy[$result]" = q"type Dummy[+${TypeName(name)}]"
    result
  }

  def covariantTypeParams(c: Context)(names: Many[Name]): Many[c.Tree] =
    names.map(name => covariantTypeParam(c)(name))

  // covariantTypeDef* are just like covariantTypeParam*, except outputting typedefs

  def covariantTypeDef(c: Context)(name: Name): c.universe.TypeDef = {
    import c.universe._
    val param = covariantTypeParam(c)(name)

    // strangely, macros can adapt TypeName arguments of a trait to TypeDefs,
    // but cannot adapt those of a type synonym.
    // hence the quote+unquote here.
    val traitIn = TypeName(c freshName "Trait")
    val q"trait $traitOut[$typeDef]" = q"trait $traitIn[$param]"
    typeDef
  }

  def covariantTypeDefs(c: Context)(names: Many[Name]): Many[c.universe.TypeDef] =
    names.map(name => covariantTypeDef(c)(name))

  def mkTypeDef(c: Context)(param: Param): c.universe.TypeDef = mkBoundedTypeDef(c)(param, Map.empty)

  // make a TypeDef according to variance
  def mkBoundedTypeDef(c: Context)(param: Param, bounds: Map[Name, Datatype]): c.universe.TypeDef = {
    import c.universe._
    val variance = param.variance.scalaSymbol
    val traitIn = TypeName(c freshName "Trait")
    if (bounds contains param.name) {
      val bound = meaning(c)(bounds(param.name))
      val q"class $traitOut[$typeDef] { ..$bodyOut }" = c.parse(s"class $traitIn[ $variance ${param.name} <: $bound ]")
      typeDef
    }
    else {
      val q"class $traitOut[$typeDef] { ..$bodyOut }" = c.parse(s"class $traitIn[ $variance ${param.name} ]")
      typeDef
    }
  }

  def mkTypeDefs(c: Context)(params: Many[Param]): Many[c.universe.TypeDef] = mkBoundedTypeDefs(c)(params, Map.empty)

  def mkBoundedTypeDefs(c: Context)(params: Many[Param], bounds: Map[Name, Datatype]): Many[c.universe.TypeDef] =
    params.map(param => mkBoundedTypeDef(c)(param, bounds))

  /* get implicit value of a reified type */
  def inferImplicitValue(c: Context)(typeTree: c.Tree): Option[c.Tree] = {
    import c.universe._
    c.inferImplicitValue(treeToType(c)(typeTree), true /*silent*/) match {
      case q"" =>
        None

      case tree =>
        Some(tree)
    }
  }



  // ====================== //
  // FROM SCALA TO DATATYPE //
  // ====================== //

  def reifyRegular(c: Context)(tpe: c.Type): Regular[c.Type] =
    reifyWithEnv(c)(tpe, tpe, Map.empty)

  //  precondition: `tpeOut` is valid type in c
  //                `env` contains only types valid in c
  //
  // postcondition: all types in return value are valid in c
  def reifyWithEnv(c: Context)
    (tpe0: c.Type, tpeOut: c.Type, env: Map[c.universe.Symbol, (String, c.Type)]):
      Regular[c.Type] =
  {
    val tpe = tpe0.dealias

    // bound type variable
    if (tpe.typeArgs.isEmpty && env.contains(tpe.typeSymbol)) {
      val (myId, myTpe) = env(tpe.typeSymbol)
      RegularVar(myId, myTpe)
    }

    // fixed point
    else if (isFixedPointOfSomeFunctor(c)(tpe)) {
      val List(fun0)  = tpe.typeArgs
      val functor     = fun0.etaExpand
      val List(param) = functor.typeParams
      val myId        = freshID(c)
      val newEnv      = env.updated(param, (myId, tpeOut))

      val myBody      = functor.resultType
      val myBodyOut   = applyEnv(c)(myBody, newEnv)

      RegularFix(myId, tpeOut, reifyWithEnv(c)(myBody, myBodyOut, newEnv))
    }

    // possibly a functor application
    // do not try to look up the functor here
    else if (tpe.typeArgs.nonEmpty) {
      assert(tpe.typeArgs.size == tpeOut.typeArgs.size)

      RegularFun(freshID(c), tpeOut,
        tpe.typeArgs.zip(tpeOut.typeArgs).map {
          case (child, childOut) =>
            reifyWithEnv(c)(child, childOut, env)
        }
      )
    }

    // unrecognized base type
    else
      RegularVar(freshID(c), tpeOut)
  }

  // resolve pending substitutions
  def applyEnv(c: Context)(
    tpe: c.Type,
    env: Map[c.universe.Symbol, (String, c.Type)]): c.Type =
  {
    val (lhs, rhs) = env.view.map(p => (p._1, p._2._2)).toList.unzip
    tpe.substituteTypes(lhs, rhs)
  }

  def freshID(c: Context): String = c.freshName()

  // requires `tpe` be dealiased
  def isFixedPointOfSomeFunctor(c: Context)(tpe: c.Type): Boolean =
    getFixWithoutRoot == tpe.typeConstructor.typeSymbol.fullName

  // BEGIN TODO REWRITE EVERYTHING

  object UC extends Enumeration {
    type Flag = Value
    type Flags = Set[Flag]
    val AllowFixedPointsOfConstantFunctors = Value

    implicit val defaultFlags: Flags = Set.empty
  }

  /** flesh out parsed datatype with some cases/fields omitted */
  def fleshOut(c: Context)(raw: DataConstructor)(implicit flags: UC.Flags): DataConstructor = {
    val care = raw.params.view.map(_.name).toSet

    // have to consider that the whole body is a typevar
    val tpe  = raw.body match {
      case typeVar @ TypeVar(_) =>
        fullyApplyToNothing(c)(typeVar, care)

      case Variant(header, _) =>
        fullyApplyToNothing(c)(TypeVar(header), care)

      case _ =>
        treeToType(c)(c.universe.TypeTree())
    }

    val body = representation(c)(tpe, care, Some(raw.body))(flags)
    raw copy (body = body)
  }

  def representation(c: Context)(tpe: c.Type, care: Set[Name], overrider: Option[Datatype])
      (implicit flags: UC.Flags): Datatype =
    carePackage(c)(tpe, care, overrider)(flags).get

  /** starting type hidden in an overrider; in other words, the entry point */
  def startingType(c: Context)(body: Datatype, care: Set[Name]): Option[c.Type] = 
    body match {
      case Variant(header, fields) =>
        Some(fullyApplyToNothing(c)(TypeVar(header), care))

      case Record(_, _) | TypeVar(_) =>
        None

      case _ =>
        abortWithError(c)(
          c.universe.EmptyTree.pos,
          s"expect parse tree produced by DatatypeP, got:\n  $body")
    }

  // if it's a type, then return it's meaning.
  // if it's a type constructor, then fully apply to `defaultArg` & return it.
  //
  // cai 23.07.2014
  // I don't know how to parse a type constructor,
  // so I give the constructor 0, 1, 2, ..., 22 type arguments until the whole thing typechecks,
  // and give up if it does not.
  def fullyApplyTo(default: String, c: Context)(firstTry: TypeVar, care: Set[Name]): c.Type = {
    val maxTypeParams = 22
    var nextTry = firstTry
    (1 to (maxTypeParams + 1)) foreach { i =>
      try {
        return dodgeFreeTypeVariables(c)(meaning(c)(nextTry), care)
      }
      catch {
        case e: scala.reflect.macros.TypecheckException
            if (e.getMessage matches "type .* takes type parameters")
            || (e.getMessage matches """wrong number of type arguments for .*, should be \d+""")
            =>
          // let's add more parameters and try again
          nextTry = TypeVar(firstTry.name + s"[${(1 to i) map (_ => default) mkString ", "}]")
      }
    }
    abortWithError(c)(
      c.universe.EmptyTree.pos,
      s"panic! ${firstTry.name} has more than $maxTypeParams type parameters?!")
  }

  def fullyApplyToNothing(c: Context)(firstTry: TypeVar, care: Set[Name]): c.Type =
    fullyApplyTo(nothingType, c)(firstTry, care)

  def fullyApplyToAny(c: Context)(firstTry: TypeVar, care: Set[Name]): c.Type =
    fullyApplyTo(anyType, c)(firstTry, care)

  /** I care about a Type if
    * 1. it is a leaf, not a class, and matches the name of a variable under my care
    * 2. it is a branch and I care about a child of its
    * 3. it matches one of the overriders
    *
    * If I care about a type, then I treat it as a part of a datatype
    * declaration, where all variants are abstract and all records are concrete.
    *
    * If I don't care about a type, then I treat it as a type constant.
    */
  sealed trait DoICare { def shouldCare: Boolean ; def get: Datatype }
  case class IDontCare(get: TypeVar) extends DoICare { def shouldCare = false }
  case class IDoCare(get: Datatype) extends DoICare { def shouldCare = true }

  def typeToCode(c: Context)(tpe: c.Type): String = {
    import c.universe._
    tq"$tpe".toString
  }

  /** convert scala type to datatype representation, without expanding
    * more than one level. Duplicate some code of `carePackage`.
    * Consider refactor.
    */
  def representOnce(c: Context)(tpe0: c.Type): Datatype = {
    val tpe = tpe0.dealias
    val symbol = tpe.typeSymbol
    if (isFixedPointOfSomeFunctor(c)(tpe)) {
      // CASE fixed point
      // relies on `carePackage` to consider the type parameter of
      // the functor to be worth caring
      carePackage(c)(tpe, Set.empty, None).get
    }
    else if (symbol.isAbstract && tpe.typeArgs.nonEmpty) {
      // CASE variant
      val cases: Many[Record] = tpe.typeArgs.map(child => {
        representOnce(c)(child) match {
          case record @ Record(_, _) =>
            record

          case other =>
            abortWithError(c)(
              c.enclosingPosition,
              s"representOnce on $tpe:\n expect record, got $other")
        }
      })(collection.breakOut)

      Variant(typeToCode(c)(tpe.typeConstructor), cases)
    }
    else { // ! symbol.isAbstract
      // CASE record
      // expand children without caring about them
      val childCare = tpe.typeArgs.map(child => carePackage(c)(child, Set.empty, None))
      representGeneratedRecord(c)(tpe, childCare)
    }
  }

  /** convert scala type to datatype representation while dealing with
    * many concerns.
    *
    * @param tpe0 scala type to represent
    * @param care set of names we care about, namely parameters of functors and names of fixed points
    * @param overrider the part overriding the default with parts inside braces: List { Cons(Int, R) }
    *
    * @return representation of tpe0 with flag whether I care about it or not
    */
  def carePackage(c: Context)(
    tpe0: c.Type,
    care: Set[Name],
    overrider: Option[Datatype])
    (implicit flags: UC.Flags): DoICare =
  {
    // dealiasing is not recursive. do it here.
    val tpe = (overrider flatMap (x => startingType(c)(x, care)) getOrElse tpe0).dealias

    // the case for type parameters of functors and sums without summand
    // and 0-argument records
    if (tpe.typeArgs.isEmpty) {
      val symbol = tpe.typeSymbol
      val name = symbol.name.toString
      val shouldCare = overrider.nonEmpty || ! symbol.isClass  &&  care(name)
      if (shouldCare)
        IDoCare(overrider getOrElse TypeVar(name))
      else
        IDontCare(TypeVar(typeToCode(c)(tpe)))
    }
    else {
      // deal with fixed point
      if (isFixedPointOfSomeFunctor(c)(tpe)) {
        import c.universe._

        // handle overridden fixed points
        if (overriddenByTypeParam(overrider, care))
          IDoCare(overrider.get)
        else {

          // name the fixed point
          val fixedPointName = c.freshName("Fixed").toString
          assert(
            ! care(fixedPointName),
            s"500 internal error: Context.freshName produces the clashing name $fixedPointName")
          val newCare = care + fixedPointName

          // get the functor
          val List(functor) = tpe.typeArgs
          val unrolledTpe = functor.etaExpand.resultType.substituteTypes(
            functor.typeParams,
            List(dodgeFreeTypeVariables(c)(tq"${TypeName(fixedPointName)}", newCare)))

          // adjust overrider
          // it has to be a variant whose typeVar reflects the overriders
          def adjustOverrider(overrider: Option[Datatype]): Option[Datatype] = overrider match {
            case Some(Variant(fixedPointDataTag, nominals)) =>

              Some(Variant(
                // e. g., replace "List" by "ListT[..., ...]"
                typeToCode(c)(unrolledTpe),

                // e. g., rename "List" to `fixedPointName`
                nominals.map(_ rename Map(fixedPointDataTag -> fixedPointName))
              ))

            // convert `Term` to `Term {}`, coz the first case is tough to handle downstream
            case Some(TypeVar(header)) =>
              adjustOverrider(Some(Variant(header, Many.empty)))

            case otherwise =>
              otherwise
          }

          val newOverrider = adjustOverrider(overrider)

          // since I care about tpe, I should also care about it when it's unrolled
          carePackage(c)(unrolledTpe, newCare, newOverrider)(flags) match {
            case IDoCare(result) =>
              if ( flags(UC.AllowFixedPointsOfConstantFunctors)
                || (result hasFreeOccurrencesOf fixedPointName) )
                IDoCare(FixedPoint(fixedPointName, result))
              else
                IDoCare(result)

            case IDontCare(TypeVar(body)) =>
              sys error "FIXME: this should not happen, right?"
          }
        }
      }
      else {
        val symbol = tpe.typeSymbol

        // match overrider with children
        val suboverriders: Many[Option[Datatype]] = matchSuboverriders(c)(tpe, care, overrider)

        // recursive calls
        val childCare = tpe.typeArgs.zip(suboverriders).map {
          case (child, overrider) =>
            carePackage(c)(child, care, overrider)(flags)
        }

        // I should care about `tpe` if I care about at least one of its children
        val shouldCare = overrider.nonEmpty || childCare.map(_.shouldCare).max

        if (shouldCare) {
          require(symbol.isClass,
            """|violation of expectation: type on a cared path is not a class.
               |Every type on a cared path should be a generated datatype.
               |We assume that every abstract type is a variant and every
               |concrete type is a record.
               |""".stripMargin)
          // having dealt with fixed point types,
          // assume all variants are abstract & all records are concrete,
          // given that `tpe` is not a leaf.
          //
          // empty records are leaves and their types are abstract.
          if (symbol.isAbstract && overriddenByTypeParam(overrider, care))
            IDoCare(overrider.get)
          else if (symbol.isAbstract) {

            // if there's an overrider, it should not be anything that cannot expand to a variant
            require(
              overrider.isEmpty ||
                overrider.get.isInstanceOf[Variant] ||
                overrider.get.isInstanceOf[TypeVar],
              s"got abstract class $tpe, expect:\n  ${overrider.get}")

            // if I do care about this type & it's a variant,
            // then children's IDontCare packages are useless.
            // they have to be records.
            val cases: Many[VariantCase] = (childCare, tpe.typeArgs, suboverriders).zipped.map({
              // normal record
              case (IDoCare(record @ Record(_, _)), _, suboverrider) =>
                record

              case (IDoCare(nonRecord), _, _) =>
                abortWithError(c)(
                  c.universe.EmptyTree.pos,
                  s"tentative variant $tpe expects record/type var, got $nonRecord")

              case (IDontCare(_), typeArg, suboverrider) =>
                val subsuboverriders = matchSuboverriders(c)(tpe, care, suboverrider)

                representGeneratedRecord(c)(
                  typeArg,
                  typeArg.typeArgs.zip(subsuboverriders).map {
                    case (tpe, overrider) =>
                      carePackage(c)(tpe, care, overrider)(flags)
                  })
            })(collection.breakOut)
            IDoCare(Variant(typeToCode(c)(tpe.typeConstructor), cases))
          }
          else { // ! symbol.isAbstract
            // this is the record case
            // if there is an overrider, it should not be anything that cannot expand to a record
            require(
              overrider.isEmpty ||
                overrider.get.isInstanceOf[Record] ||
                overrider.get.isInstanceOf[TypeVar],
              s"got concrete class $tpe, expect:\n  ${overrider.get}")

            // this thing is a record. That's easier to deal with.
            // children that are variants can simply be treated as
            // type constants.
            IDoCare(representGeneratedRecord(c)(tpe, childCare))
          }
        }
        else {
          // cast is safe: `shouldCare` is false only if all children are `IDontCare`
          val children = childCare.map(_.asInstanceOf[IDontCare].get.name)
          // if I don't care about `tpe`, then it will become a type constant
          // with all children fully qualified
          IDontCare(TypeVar(s"${typeToCode(c)(tpe.typeConstructor)}[${children mkString ", "}]"))
        }
      }
    }

  }

  def overriddenByTypeParam(overrider: Option[Datatype], care: Set[Name]): Boolean =
    overrider match {
      case Some(TypeVar(x)) => care(x)
      case _ => false
    }

  // requires `tpe` be dealiased
  def matchSuboverriders(c: Context)(tpe: c.Type, care: Set[Name], overrider: Option[Datatype]):
      Many[Option[Datatype]] = {
    def nones = tpe.typeArgs.map(_ => None)
    overrider match {
      case None =>
        nones

      case Some(typeVar @ TypeVar(_)) =>
        // for the first time, try to expand overrider
        val expandedOverrider = try {
          representation(c)(scalaType(c)(typeVar), care, None)
        }
        catch {
          case e: reflect.macros.TypecheckException =>
            typeVar
        }

        if (expandedOverrider.isInstanceOf[TypeVar])
          // `typeVar` cannot be expanded
          nones
        else
          matchSuboverriders(c)(tpe, care, Some(expandedOverrider))

      case Some(variant @ Variant(header, cases)) =>
        matchChildrenOverriders(c)(tpe, variant, cases)

      case Some(record @ Record(name, fields)) =>
        matchChildrenOverriders(c)(tpe, record, fields)

      case Some(FixedPoint(name, body)) =>
        // this case is possible if we do not convert
        //
        //   @functor val badF = XX => Term
        //
        // to the easier-to-handle case
        //
        //   @functor val badF = XX => Term {}
        //
        ???

      case Some(other) =>
        noRecognition(other)
    }
  }

  // requires `tpe` be dealiased
  def matchChildrenOverriders(c: Context)(tpe: c.Type, parent: Datatype, overriders: Many[Nominal]):
      Many[Option[Datatype]] =
  {
    val children = tpe.typeArgs
    val params = tpe.typeConstructor.typeParams.map(symbol => symbol.name.toString)
    val indexedOverriders: Map[Int, Option[Datatype]] =
      overriders.map({
        case overrider =>
          var i = params.indexOf(overrider.name)
          // if overrider did not provide a name,
          // attempt to map the index back.
          // therefore we must forbid names of the form "_i"
          // where i is not the index.
          if (i == -1)
            tupleIndex(overrider.name) map (i = _)

          if (i != -1)
            (i, Some(overrider.get))
          else
            abortWithError(c)(
              c.universe.EmptyTree.pos,
              s"`${tpe.typeConstructor}[${params.mkString(", ")}]` has no member called `${overrider.name}`")
      })(collection.breakOut)

    children.zipWithIndex.map {
      case (child, i) =>
        indexedOverriders.getOrElse(i, None)
    }
  }

  def representGeneratedRecord(c: Context)(tpe0: c.Type, fields: List[DoICare]): Record = {
    val tpe = tpe0.dealias
    val symbol = tpe.typeSymbol
    val typeParams = tpe.typeConstructor.typeParams

    // only require records to be concrete if they are nonleaves
    // (traits for case objects are abstract, but they are records without fields)
    if (! fields.isEmpty)
      require(
        symbol.isClass && ! symbol.isAbstract,
        s"generated records must be concrete classes; got $tpe")

    Record(
      symbol.name.toString,
      fields.zip(typeParams).map {
        case (carePkg, param) =>
          Field(param.name.toString, carePkg.get)
      })
  }

  def dodgeFreeTypeVariables(c: Context)(tpe: c.Tree, care: Set[Name]): c.Type = {
    import c.universe._
    val dummy = TypeName(c freshName "Dummy")
    val method = TermName(c freshName "method")
    val typeDefs = mkTypeDefs(c)(care.toSeq map (Param invariant _))
    val wrapper = q"{ class $dummy { def $method[..$typeDefs]: ${tpe} = ??? } ; new $dummy }"
    c.typecheck(wrapper).tpe.member(method).typeSignature.finalResultType
  }

  // END TODO REWRITE EVERYTHING
}

object UniverseConstruction {
  object Tests extends UniverseConstruction with Parsers with util.AssertEqual with util.Persist {
    import language.experimental.macros
    import scala.annotation.StaticAnnotation

    // OLD TESTS BEGIN

    private[this] def eval[T](c: Context)(x: c.Expr[T]): T =
      c.eval(c.Expr[T](c.untypecheck(x.tree.duplicate)))

    class interpretIntList extends StaticAnnotation {
      def macroTransform(annottees: Any*): Any = macro interpretIntList.impl
    }
    object interpretIntList {
      def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
        import c.universe._

        val q"trait IntList { $body }" = annottees.head.tree

        // duplicate test.UniverseConstructionSpec
        val datatype: Datatype =
          FixedPoint("L",
            Variant("ListT", Many(
              Record("Nil", Many.empty),
              Record("Cons", Many(
                Field("head", TypeVar("Int")),
                Field("tail", TypeVar("L")))))))

        // scala type corresponding to datatype
        val tpe = meaning(c)(datatype)

        c.Expr(q"""type IntList = $tpe""")
      }
    }


    class interpretGenList extends StaticAnnotation {
      def macroTransform(annottees: Any*): Any = macro interpretGenList.impl
    }
    object interpretGenList {
      def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
        import c.universe._

        val q"trait GenList { $body }" = annottees.head.tree

        // duplicate test.UniverseConstructionSpec
        val datatype: Datatype =
          FixedPoint("L",
            Variant("ListT", Many(
              Record("Nil", Many.empty),
              Record("Cons", Many(
                Field("head", TypeVar("A")), // should be bound by my[A]
                Field("tail", TypeVar("L")))))))

        c.Expr(q"type GenList = ${meaning(c)(datatype)}")
      }
    }

    class rep extends StaticAnnotation { def macroTransform(annottees: Any*): Any = macro repImpl }
    def repImpl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
      import c.universe._
      annottees.head.tree match {
        case ValDef(mods, name, tt @ TypeTree(), q"rep[$tpe]($careExpr)") =>
          val care = c.eval(c.Expr(careExpr)).asInstanceOf[Set[DatatypeRepresentation.Name]]
          val data = representation(c)(dodgeFreeTypeVariables(c)(tpe, care), care, None)
          c.Expr(ValDef(mods, name, tt, persist(c)(data)))
      }
    }

    // OLD TESTS END

    def isFix[T]: Boolean = macro isFixImpl[T]
    def isFixImpl[T](c: Context)(implicit tag: c.WeakTypeTag[T]): c.Tree = {
      import c.universe._

      val truth = isFixedPointOfSomeFunctor(c)(tag.tpe)

      if (truth)
        q"true"
      else
        q"false"
    }

    def reify[T]: DatatypeRepresentation.Datatype = macro reifyImpl[T]
    def reifyImpl[T](c: Context)(implicit tag: c.WeakTypeTag[T]): c.Tree = {
      val regular = reifyRegular(c)(tag.tpe).toDatatype.canonize
      persist(c)(regular)
    }

    def unrollFix[T]: String = macro unrollFixImpl[T]
    def unrollFixImpl[T](c: Context)(implicit tag: c.WeakTypeTag[T]): c.Tree = {
      val RegularFix(id, tpe, body) = reifyRegular(c)(tag.tpe)
      persist(c)(body.tpe.toString)
    }
  }
}
