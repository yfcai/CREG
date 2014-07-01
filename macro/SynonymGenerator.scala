import scala.reflect.macros.blackbox.Context

import DatatypeRepresentation._

trait SynonymGenerator extends UniverseConstruction {
  def generateSynonym(c: Context)(name: Name, genericDatatype: DataConstructor): c.Tree = {
    import c.universe._
    val DataConstructor(paramNames, datatypeBody) = genericDatatype
    val typeName = TypeName(name)
    val typeDefs = covariantTypeDefs(c)(paramNames)
    val rhs = generateRHS(c)(datatypeBody)
    q"type $typeName [ ..$typeDefs ] = $rhs"
  }

  def generateRHS(c: Context)(datatype: Datatype): c.Tree =
    meaning(c)(datatype)
}

object SynonymGenerator {
  /** test macros */
  object Tests extends SynonymGenerator with DeclarationGenerator with AssertEqual {
    import scala.language.experimental.macros
    import scala.annotation.StaticAnnotation

    class flat extends StaticAnnotation { def macroTransform(annottees: Any*): Any = macro flat.impl }
    object flat {
      def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
        import c.universe._

        val q"trait Person { Boss ; Manager(dept: Int) ; Employee(name: String, dept: Int) }" =
          annottees.head.tree

        val person  = "Person"
        val personT = "PersonT"

        val datatype =
          Variant(personT, Many(
            Record("Boss", Many.empty),
            Record("Manager", Many(Field("dept", Scala("Int")))),
            Record("Employee", Many(Field("name", Scala("String")), Field("dept", Scala("Int"))))))

        val declaration = generateDeclaration(c)(datatype)
        val synonym = generateSynonym(c)(person, DataConstructor(Many.empty, datatype))
        val expected = q"type Person = PersonT[Boss, Manager[Int], Employee[String, Int]]"
        assertEqual(c)(expected, synonym)

        c.Expr(q"..${declaration :+ synonym}")
      }
    }

    class recursive extends StaticAnnotation { def macroTransform(annottees: Any*): Any = macro recursive.impl }
    object recursive {
      def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
        import c.universe._

        val q"trait IntList { Nil ; Cons(Int, IntList) }" = annottees.head.tree

        val intList  = "IntList"
        val intListT = "IntListT"
        val intListF = "IntListF"

        val datatypeBody =
          Variant(intListT, Many(
            Record("Nil", Many.empty),
            Record("Cons", Many(
              Field("_1", Scala("Int")),
              Field("_2", Hole(intList /* no T */))))))

        val genericDatatype =
          DataConstructor(Many.empty,
            FixedPoint(DataConstructor(Many(intList), datatypeBody)))

        val declaration = generateDeclaration(c)(datatypeBody)
        val synonym = generateSynonym(c)(intList, genericDatatype)
        val expected = q"""
          type IntList = _root_.fixedpoint.Fix[({
            type __innerType__[+IntList] = IntListT[Nil, Cons[Int, IntList]]
          })#__innerType__]"""
        assertEqual(c)(expected, synonym)

        // TODO: generate synonym IntListF

        c.Expr(q"..${declaration :+ synonym}")
      }
    }

    class generic extends StaticAnnotation { def macroTransform(annottees: Any*): Any = macro generic.impl }
    object generic {
      def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
        import c.universe._

        val q"trait GList[A] { Nil ; Cons(A, GList[A]) }" = annottees.head.tree

        // TODO: write datatypeBody etc. for GLists

        c.Expr(q"")
      }
    }

  } // end of SynonymGenerator.Test
} // end of SynonymGenerator
