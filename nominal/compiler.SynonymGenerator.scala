package nominal
package compiler

import scala.reflect.macros.blackbox.Context

import DatatypeRepresentation._

trait SynonymGenerator extends UniverseConstruction {
  def generateSynonym(c: Context)(name: Name, genericDatatype: DataConstructor): c.Tree =
    generateBoundedSynonym(c)(name, genericDatatype, Map.empty)

  def generateBoundedSynonym(c: Context)(name: Name, genericDatatype: DataConstructor, bounds: Map[Name, Datatype]): c.Tree = {
    val (newDatatype, newBounds) = disambiguate(c)(genericDatatype, bounds)
    boundedSynonymWithoutDisambiguation(c)(name, newDatatype, newBounds)
  }

  /** remove identical names from bounds (currently by failing otherwise) */
  private[this]
  def disambiguate(c: Context)(
    data: DataConstructor, bounds: Map[Name, Datatype]
  ): (DataConstructor, Map[Name, Datatype]) = {
    val identicals = bounds filter {
      case (x1, TypeVar(x2)) => x1 == x2
      case (x1, Record(x2, _)) => x1 == x2
      case _ => false
    }
    if (! identicals.isEmpty) sys error s"duplicate names in bounds: $identicals"
    (data, bounds) //stub
  }

  /** precondition: `bounds` contains no identity mapping */
  private[this]
  def boundedSynonymWithoutDisambiguation(c: Context)(
    name: Name, genericDatatype: DataConstructor, bounds: Map[Name, Datatype]
  ): c.Tree = {
    import c.universe._
    val DataConstructor(params, datatypeBody) = genericDatatype
    val typeName = TypeName(name)
    val typeDefs = mkBoundedTypeDefs(c)(params, bounds)
    val rhs = generateRHS(c)(datatypeBody)
    q"type $typeName [ ..$typeDefs ] = $rhs"
  }

  def generateConcreteSynonym(c: Context)(name: Name, concreteDatatype: Datatype): c.Tree =
    generateSynonym(c)(name, DataConstructor(Many.empty, concreteDatatype))

  def generateRHS(c: Context)(datatype: Datatype): c.Tree = meaning(c)(datatype)

  def generatePatternFunctorSynonym(c: Context)(patternFunctorName: Name, genericFixedPoint: DataConstructor): c.Tree = {
    import c.universe._
    val DataConstructor(genericParams, FixedPoint(recursiveParam, datatypeBody)) = genericFixedPoint
    val patternFunctorTypeName = TypeName(patternFunctorName)
    val typeParams = mkTypeDefs(c)(genericParams :+ Param.covariant(recursiveParam))
    val rhs = generateRHS(c)(datatypeBody)
    q"type $patternFunctorTypeName [ ..$typeParams ] = $rhs"
  }

  def generateConcretePatternFunctor(c: Context)(patternFunctorName: Name, fixedPoint: FixedPoint): c.Tree =
    generatePatternFunctorSynonym(c)(patternFunctorName, DataConstructor(Many.empty, fixedPoint))
}

object SynonymGenerator {
  /** test macros */
  object Tests extends SynonymGenerator with DeclarationGenerator with util.AssertEqual {
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
          Variant(TypeVar(person), Many(
            Record("Boss", Many.empty),
            Record("Manager", Many(Field("dept", TypeVar("Int")))),
            Record("Employee", Many(Field("name", TypeVar("String")), Field("dept", TypeVar("Int"))))))

        val declaration = generateDeclaration(c)(datatype, annottees.head.tree)
        val synonym = generateConcreteSynonym(c)(person, templatify(datatype))
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
          Variant(TypeVar(intList), Many(
            Record("Nil", Many.empty),
            Record("Cons", Many(
              Field("_1", TypeVar("Int")),
              Field("_2", TypeVar(intList /* no T */))))))

        val fixedPoint = FixedPoint(intList, datatypeBody)

        val declaration = generateDeclaration(c)(datatypeBody, annottees.head.tree)

        val synonym = generateConcreteSynonym(c)(intList, templatify(fixedPoint))
        val q"""
          type IntList = _root_.nominal.lib.Fix[({
            type $innerTypeL[+IntList] = IntListT[Nil, Cons[Int, IntList]]
          })#$innerTypeR]""" = synonym
        assert(innerTypeL == innerTypeR)

        val patternF = generateConcretePatternFunctor(c)(intListF, templatify(fixedPoint).asInstanceOf[FixedPoint])
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
          Variant(TypeVar(gList), Many(
            Record("Nil", Many.empty),
            Record("Cons", Many(
              Field("_1", TypeVar("A")),
              Field("_2", TypeVar(gList /* no T */))))))

        val fixedPoint = FixedPoint(gList, datatypeBody)

        val genericDatatype = DataConstructor(Many(Param.covariant("A")), fixedPoint)

        val declaration = generateDeclaration(c)(datatypeBody, annottees.head.tree)

        val synonym = generateSynonym(c)(gList, templatify(genericDatatype))
        val q"""
          type GList[+A] = _root_.nominal.lib.Fix[({
            type $innerTypeL[+GList] = GListT[Nil, Cons[A, GList]]
          })#$innerTypeR]""" = synonym
        assert(innerTypeL == innerTypeR)

        val patternF = generatePatternFunctorSynonym(c)(gListF, templatify(genericDatatype))
        val expectedPatternF = q"""
          type GListF[+A, +GList] = GListT[Nil, Cons[A, GList]]
        """
        assertEqual(c)(expectedPatternF, patternF)

        c.Expr(q"..${declaration ++ Many(synonym, patternF)}")
      }
    }

  } // end of SynonymGenerator.Test
} // end of SynonymGenerator
