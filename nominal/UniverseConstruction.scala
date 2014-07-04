package nominal

import scala.reflect.macros.blackbox.Context

import DatatypeRepresentation._

trait UniverseConstruction {
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

        val typeDef = covariantTypeDef(c)(paramName)

        val q"??? : $result" =
          q"""
            ??? : $fix[({
              type __innerType__[$typeDef] = ${meaning(c)(body)}
            })#__innerType__]
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

    val q"trait __Trait__ [$typeDef]" = q"trait __Trait__ [$param]"
    typeDef
  }

  def covariantTypeDefs(c: Context)(names: Many[Name]): Many[c.universe.TypeDef] =
    names.map(name => covariantTypeDef(c)(name))

  // make a TypeDef according to variance
  def mkTypeDef(c: Context)(param: Param): c.universe.TypeDef = {
    import c.universe._
    val variance = param.variance.scalaSymbol
    val q"trait __Trait__ [$typeDef]" = c.parse(s"trait __Trait__ [ $variance ${param.name} ]")
    typeDef
  }

def mkTypeDefs(c: Context)(params: Many[Param]): Many[c.universe.TypeDef] =
  params.map(param => mkTypeDef(c)(param))

  // location of the Fix[_[_]] trait
  def getFix(c: Context) = {
    import c.universe._
    val q"??? : $fix [ ID ]" = q"??? : _root_.nominal.functor.Fix [ ID ]"
    fix
  }
}

object UniverseConstruction {
  object Tests extends UniverseConstruction with AssertEqual {
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

  }
}