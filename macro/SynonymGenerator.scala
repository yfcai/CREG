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

  def generateRHS(c: Context)(datatype: Datatype): c.Tree = meaning(c)(datatype)

  def generatePatternFunctor(c: Context)(patternFunctorName: Name, genericFixedPoint: DataConstructor): c.Tree = {
    import c.universe._
    val DataConstructor(genericParams, FixedPoint(DataConstructor(Many(recursiveParam), datatypeBody))) = genericFixedPoint
    val patternFunctorTypeName = TypeName(patternFunctorName)
    val typeParams = covariantTypeDefs(c)(genericParams :+ recursiveParam) // defer to scalac to report name clashes
    val rhs = generateRHS(c)(datatypeBody)
    q"type $patternFunctorTypeName [ ..$typeParams ] = $rhs"
  }
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

        val fixedPoint = FixedPoint(DataConstructor(Many(intList), datatypeBody))

        val genericDatatype = DataConstructor(Many.empty, fixedPoint)

        val declaration = generateDeclaration(c)(datatypeBody)

        val synonym = generateSynonym(c)(intList, genericDatatype)
        val expectedSynonym = q"""
          type IntList = _root_.fixedpoint.Fix[({
            type __innerType__[+IntList] = IntListT[Nil, Cons[Int, IntList]]
          })#__innerType__]"""
        assertEqual(c)(expectedSynonym, synonym)

        val patternF = generatePatternFunctor(c)(intListF, genericDatatype)
        val expectedPatternF = q"""
          type IntListF[+IntList] = IntListT[Nil, Cons[Int, IntList]]
        """
        assertEqual(c)(expectedPatternF, patternF)

        c.Expr(q"..${declaration ++ Many(synonym, patternF)}")
      }
    }

    class generic extends StaticAnnotation { def macroTransform(annottees: Any*): Any = macro generic.impl }
    object generic {
      def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
        import c.universe._

        val q"trait GList[A] { Nil ; Cons(A, GList[A]) }" = annottees.head.tree

        val gList  = "GList"
        val gListT = "GListT"
        val gListF = "GListF"

        val datatypeBody =
          Variant(gListT, Many(
            Record("Nil", Many.empty),
            Record("Cons", Many(
              Field("_1", Hole("A")),
              Field("_2", Hole(gList /* no T */))))))

        val fixedPoint = FixedPoint(DataConstructor(Many(gList), datatypeBody))

        val genericDatatype = DataConstructor(Many("A"), fixedPoint)

        val declaration = generateDeclaration(c)(datatypeBody)

        val synonym = generateSynonym(c)(gList, genericDatatype)
        val expectedSynonym = q"""
          type GList[+A] = _root_.fixedpoint.Fix[({
            type __innerType__[+GList] = GListT[Nil, Cons[A, GList]]
          })#__innerType__]"""
        assertEqual(c)(expectedSynonym, synonym)

        val patternF = generatePatternFunctor(c)(gListF, genericDatatype)
        val expectedPatternF = q"""
          type GListF[+A, +GList] = GListT[Nil, Cons[A, GList]]
        """
        assertEqual(c)(expectedPatternF, patternF)

        c.Expr(q"..${declaration ++ Many(synonym, patternF)}")
      }
    }

  } // end of SynonymGenerator.Test
} // end of SynonymGenerator
