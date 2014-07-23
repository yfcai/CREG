package nominal
package compiler

import scala.reflect.macros.blackbox.Context

import DatatypeRepresentation._

trait UniverseConstruction extends util.AbortWithError {

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
  def scalaType(c: Context)(rep: Datatype): c.Type = {
    import c.universe._
    c.typecheck(q"??? : ${meaning(c)(rep)}").tpe.dealias
  }

  def mkInnerType(c: Context): c.TypeName = c.universe.TypeName(c freshName "innerType")

  def meaningOfNominal(c: Context)(rep: Nominal): c.Tree = rep match {
    case Field(name, body) => meaning(c)(body)
    case data: Datatype    => meaning(c)(data)
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
    val traitIn = TypeName(c freshName "Trait") // TODO: use bounds
    if (bounds contains param.name) {
      val bound = meaning(c)(bounds(param.name))
      val q"trait $traitOut[$typeDef]" = c.parse(s"trait $traitIn[ $variance ${param.name} <: $bound ]")
      typeDef
    }
    else {
      val q"trait $traitOut[$typeDef]" = c.parse(s"trait $traitIn[ $variance ${param.name} ]")
      typeDef
    }
  }

  def nameOfAny: String = "_root_.scala.Any"

  def mkTypeDefs(c: Context)(params: Many[Param]): Many[c.universe.TypeDef] = mkBoundedTypeDefs(c)(params, Map.empty)

  def mkBoundedTypeDefs(c: Context)(params: Many[Param], bounds: Map[Name, Datatype]): Many[c.universe.TypeDef] =
    params.map(param => mkBoundedTypeDef(c)(param, bounds))

  // location of the Fix[_[_]] trait
  def getFix(c: Context) = {
    import c.universe._
    val q"??? : $fix [ ID ]" = q"??? : _root_.nominal.lib.Fix [ ID ]"
    fix
  }


  // ====================== //
  // FROM SCALA TO DATATYPE //
  // ====================== //

  def representation(c: Context)(tpe: c.Type, care: Set[Name]): Datatype =
    carePackage(c)(tpe, care).get

  /** I care about a Type if
    * 1. it is a leaf, not a class, and matches the name of a variable under my care
    * 2. it is a branch and I care about a child of its.
    *
    * If I care about a type, then I treat it as a part of a datatype
    * declaration, where all variants are abstract and all records are concrete.
    *
    * If I don't care about a type, then I treat it as a type constant.
    */
  sealed trait DoICare { def shouldCare: Boolean ; def get: Datatype }
  case class IDontCare(get: TypeVar) extends DoICare { def shouldCare = false }
  case class IDoCare(get: Datatype) extends DoICare { def shouldCare = true }
  def carePackage(c: Context)(tpe0: c.Type, care: Set[Name]): DoICare = {
    // dealiasing is not recursive. do it here.
    val tpe = tpe0.dealias

    if (tpe.typeArgs.isEmpty) {
      val symbol = tpe.typeSymbol
      val name = symbol.name.toString
      val shouldCare = ! symbol.isClass  &&  care(name)
      if (shouldCare)
        IDoCare(TypeVar(name))
      else
        IDontCare(TypeVar(symbol.fullName))
    }
    else {
      val symbol = tpe.typeSymbol
      val childCare = tpe.typeArgs.map(child => carePackage(c)(child, care))
      // I should care about `tpe` if I care about at least one of its children
      val shouldCare = childCare.map(_.shouldCare).max
      if (shouldCare) {
        require(symbol.isClass,
          """|violation of expectation: type on a cared path is not a class.
             |Every type on a cared path should be a generated datatype.
             |We assume that every abstract type is a variant and every
             |concrete type is a record.
             |""".stripMargin)

        // assume all variants are abstract & all records are concrete,
        // given that `tpe` is not a leaf.
        //
        // empty records are leaves and their types are abstract.
        if (symbol.isAbstract) {
          // if I do care about this type & it's a variant,
          // then children's IDontCare packages are useless.
          // they have to be records.
          val cases: Many[Nominal] = childCare.zip(tpe.typeArgs) map {
            case (IDoCare(record @ Record(_, _)), _) =>
              record

            case (IDoCare(nonRecord), _) =>
              abortWithError(c)(
                c.universe.EmptyTree.pos,
                s"tentative variant $tpe expects record/case class, got $nonRecord")

            case (IDontCare(_), typeArg) =>
              representGeneratedRecord(c)(
                typeArg,
                typeArg.typeArgs.map(tpe => carePackage(c)(tpe, care)))
          }
          IDoCare(Variant(TypeVar(symbol.fullName), cases))
        }
        else {
          // this thing is a record. That's easier to deal with.
          // children that are variants can simply be treated as
          // type constants.
          IDoCare(representGeneratedRecord(c)(tpe, childCare))
        }
      }
      else {
        // cast is safe: `shouldCare` is false only if all children are `IDontCare`
        val children = childCare.map(_.asInstanceOf[TypeVar].name)
        // if I don't care about `tpe`, then it will become a type constant
        // with all children fully qualified
        IDontCare(TypeVar(s"${symbol.fullName}[${children mkString ", "}]"))
      }
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
    val wrapper = q"class $dummy { def $method[..$typeDefs]: ${tpe} = ??? } ; new $dummy"
    c.typecheck(wrapper).tpe.member(method).typeSignature.finalResultType
  }
}

object UniverseConstruction {
  object Tests extends UniverseConstruction with util.AssertEqual with util.Persist {
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
          val data = representation(c)(dodgeFreeTypeVariables(c)(tpe, care), care)
          c.Expr(ValDef(mods, name, tt, persist(c)(data)))
      }
    }

  }
}
