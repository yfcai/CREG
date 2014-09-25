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
      case TypeVar(tpe) =>
        val q"??? : $result" = c.parse(s"??? : ($tpe)")
        result

      case Record(name, fields) =>
        val q"??? : $result" =
          q"??? : ${TypeName(name)}[..${fields.map(field => meaning(c)(field.get))}]"
        result

      case Variant(typeVar, records) =>
        val q"??? : $result" =
          q"??? : ${meaning(c)(typeVar)}[..${records.map(record => meaningOfNominal(c)(record))}]"
        result

      case FixedPoint(paramName, body) =>
        // to take the fixed point, the data constructor must be unary
        val fix = getFix(c)
        val innerType = mkInnerType(c)
        val typeDef = covariantTypeDef(c)(paramName)

        val q"??? : $result" =
          q"""
            ??? : $fix[({
              type $innerType[$typeDef] = ${meaning(c)(body)}
            })#$innerType]
          """
        result

      case Reader(domain, range) =>
        val domainType = meaning(c)(domain)
        val rangeType = meaning(c)(range)
        val q"??? : $result" = q"??? : ($domainType => $rangeType)"
        result

      case Intersect(lhs, rhs) =>
        val lhsType = meaning(c)(lhs)
        val rhsType = meaning(c)(rhs)
        val q"??? : $result" = q"??? : ($lhsType with $rhsType)"
        result
    }
  }

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

  def meaningOfNominal(c: Context)(rep: Nominal): c.Tree = rep match {
    case Field(name, body)            => meaning(c)(body)
    case RecordAssignment(_, typeVar) => meaning(c)(typeVar)
    case data: Datatype               => meaning(c)(data)
  }


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

  def nameOfAny: String = "_root_.scala.Any"

  def mkTypeDefs(c: Context)(params: Many[Param]): Many[c.universe.TypeDef] = mkBoundedTypeDefs(c)(params, Map.empty)

  def mkBoundedTypeDefs(c: Context)(params: Many[Param], bounds: Map[Name, Datatype]): Many[c.universe.TypeDef] =
    params.map(param => mkBoundedTypeDef(c)(param, bounds))

  // ====================== //
  // FROM SCALA TO DATATYPE //
  // ====================== //

  object UC extends Enumeration {
    type Flag = Value
    type Flags = Set[Flag]
    val AllowFixedPointsOfConstantFunctors = Value

    implicit val defaultFlags: Flags = Set.empty
  }

  def nothingType: String = "_root_.scala.Nothing"
  def anyType: String = "_root_.scala.Any"

  /** flesh out parsed datatype with some cases/fields omitted */
  def fleshOut(c: Context)(raw: DataConstructor)(implicit flags: UC.Flags): DataConstructor = {
    val care = raw.params.view.map(_.name).toSet

    // have to consider that the whole body is a typevar
    val tpe  = raw.body match {
      case typeVar @ TypeVar(_) =>
        fullyApplyToNothing(c)(typeVar, care)

      case Variant(header, _) =>
        fullyApplyToNothing(c)(header, care)

      case _ =>
        treeToType(c)(c.universe.TypeTree())
    }

    val body = representation(c)(tpe, care, Some(raw.body))(flags)
    DataConstructor(raw.params, body)
  }

  def representation(c: Context)(tpe: c.Type, care: Set[Name], overrider: Option[Datatype])
      (implicit flags: UC.Flags): Datatype =
    carePackage(c)(tpe, care, overrider)(flags).get

  /** starting type hidden in an overrider; in other words, the entry point */
  def startingType(c: Context)(body: Datatype, care: Set[Name]): Option[c.Type] = 
    body match {
      case Variant(header, fields) =>
        Some(fullyApplyToNothing(c)(header, care))

      case Record(_, _) | TypeVar(_) =>
        None

      case Intersect(_, _) | Reader(_, _) =>
        // not supported yet
        ???

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

      Variant(TypeVar(typeToCode(c)(tpe.typeConstructor)), cases)
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
            case Some(Variant(TypeVar(fixedPointDataTag), nominals)) =>

              Some(Variant(
                // e. g., replace "List" by "ListT[..., ...]"
                TypeVar(typeToCode(c)(unrolledTpe)),

                // e. g., rename "List" to `fixedPointName`
                nominals.map { nominal =>
                  nominal.replaceBody(
                    nominal.get everywhere {
                      case TypeVar(name) if name == fixedPointDataTag =>
                        TypeVar(fixedPointName)
                    }
                  )
                }
              ))

            // convert `Term` to `Term {}`, coz the first case is tough to handle downstream
            case Some(header @ TypeVar(_)) =>
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
            val cases: Many[Nominal] = (childCare, tpe.typeArgs, suboverriders).zipped.map({
              // summand record is overridden by a functor parameter in type argument part
              case (IDoCare(typeVar @ TypeVar(param)), actual, suboverrider)
                  if care(param) =>
                val record =
                  representGeneratedRecord(c)(
                    actual.etaExpand.resultType,
                    actual.typeParams.map(_ => IDoCare(TypeVar(anyType))))

                RecordAssignment(record, typeVar)

              // summand record is overridden by a functor parameter in overrider part
              case (IDoCare(record @ Record(_, _)), _, Some(typeVar @ TypeVar(param)))
                  if care(param) =>
                RecordAssignment(record, typeVar)

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
            IDoCare(Variant(TypeVar(typeToCode(c)(tpe.typeConstructor)), cases))
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
  def isFixedPointOfSomeFunctor(c: Context)(tpe: c.Type): Boolean = {
    import c.universe._
    val fix = treeToType(c)(tq"${getFix(c)}[({ type ID[+X] = X })#ID]")

    // Type.typeSymbol.fullName is unreliable for code generation.
    // hope it's good enough to distinguish types from each other.
    fix.typeConstructor.typeSymbol.fullName == tpe.typeConstructor.typeSymbol.fullName
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

      case Some(Reader(domain, range)) =>
        // what answer makes sense?
        ???

      case Some(Intersect(_, _)) =>
        // not sure what to do here
        ???
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
        case FixedPoint(_, _) =>
          sys error s"500 internal error: found fixed point as a case of a variant!?"

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
}

object UniverseConstruction {
  object Tests extends UniverseConstruction with ParserOfDatatypeRep with util.AssertEqual with util.Persist {
    import language.experimental.macros
    import scala.annotation.StaticAnnotation

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
            Variant(TypeVar("ListT"), Many(
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
            Variant(TypeVar("ListT"), Many(
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

    class functor extends StaticAnnotation { def macroTransform(annottees: Any*): Any = macro functorImpl }
    def functorImpl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
      import c.universe._
      annottees.head.tree match {
        case ValDef(mods, name, emptyType @ TypeTree(), tree) =>
          val input   = parseOrAbort(c)(FunctorP, tree)
          val functor = fleshOut(c)(input)
          c.Expr(ValDef(mods, name, emptyType, persist(c)(functor)))
      }
    }
  }
}
