import scala.reflect.macros.blackbox.Context

import DatatypeRepresentation._

trait DeclarationGenerator extends UniverseConstruction {
  /** @param datatype Representation of data type
    * @return AST of generated traits and case classes
    *
    * Caution: Classes involved in datatypes must *all* be uninheritable.
    * If this is the case, then we can make the fixed point type covariant
    * without sacrificing the functor instance inside Fix[+F[+_]], which
    * is necessary to obtain covariance in something like List[+A].
    */
  def generateDeclaration(c: Context)(datatype: Variant): Many[c.Tree] = {
    import c.universe._

    val template = mkTemplate(c)(datatype.name)

    if (datatype.cases.isEmpty)
      Many(q"sealed trait $template")
    else
      q"sealed trait $template [..${generateCaseNames(c)(datatype.cases)}]" +:
        generateCases(c)(template, datatype.cases)
  }

  /** create the name of the template trait by appending T */
  def mkTemplate(c: Context)(name: String): c.TypeName = c.universe.TypeName(name)

  /** @param cases a bunch of named variants
    * @return their names as TypeName
    */
  def generateCaseNames(c: Context)(cases: Many[Nominal]): Many[c.Tree] =
    covariantTypeParams(c)(cases.map(_.name))

  /** @param template TypeName of the template trait of the variant
    * @param cases cases of the variant
    * @return generated code for cases of the variant
    */
  def generateCases(c: Context)(template: c.TypeName, cases: Many[Nominal]): Many[c.Tree] = {
    import c.universe._
    cases.zipWithIndex flatMap {
      case (Record(name, Many()), i) =>
        val typeName = TypeName(name)
        val termName = TermName(name)
        val params = namedParamsWithNothing(c)(typeName, i, cases.size)
        Many(
          q"sealed trait $typeName extends $template[..$params]",
          q"case object $termName extends $typeName")

      case (Record(name, fields), i) =>
        // records are wholely free
        val typeName = TypeName(name)
        val fieldNames = fields.map(_.name)
        val caseParams = covariantTypeParams(c)(fieldNames)
        val q"??? : $myType" = q"??? : $typeName[..${fieldNames.map(name => TypeName(name))}]"
        val templateParams = appliedParamsWithNothing(c)(myType, i, cases.size)
        val decls = generateFreeDecls(c)(fieldNames)
        Many(q"sealed case class $typeName[..$caseParams](..$decls) extends $template[..$templateParams]")
    }
  }

  /** @param fieldNames names of fields _i to put in the form of _i: _i
    */
  def generateFreeDecls(c: Context)(fieldNames: Many[Name]): Many[c.Tree] =
    fieldNames.map {
      case name =>
        import c.universe._
        val q"case class __case_class__($decl)" =
          q"case class __case_class__(${TermName(name)}: ${TypeName(name)})"
        decl
    }

  /** @param param type name at position `index`
    * @param index index of `tpe`
    * @param size  size of whole param list
    */
  def namedParamsWithNothing(c: Context)(param: c.TypeName, index: Int, size: Int): Many[c.TypeName] = {
    import c.universe._
    val nothing = TypeName("Nothing")
    Many.tabulate(size)(i => if (i == index) param else nothing)
  }

  /** @param param applied type at position `index`
    * @param index index of `tpe`
    * @param size  size of whole param list
    */
  def appliedParamsWithNothing(c: Context)(param: c.Tree, index: Int, size: Int): Many[c.Tree] = {
    import c.universe._
    val nothing = Ident(TypeName("Nothing"))
    Many.tabulate(size)(i => if (i == index) param else nothing)
  }
}

object DeclarationGenerator {
  /** test macros */
  object Tests extends DeclarationGenerator with AssertEqual {
    import scala.language.experimental.macros
    import scala.annotation.StaticAnnotation

    class empty extends StaticAnnotation { def macroTransform(annottees: Any*): Any = macro empty.impl }
    object empty {
      def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
        import c.universe._
        val q"trait $name" = annottees.head.tree
        val actual = generateDeclaration(c)(
          Variant(name.toString, Many.empty)
        )
        val expected = q"sealed trait ${TypeName(name.toString)}"
        assertEqualBlock(c)(expected, actual)
      }
    }

    class caseObject extends StaticAnnotation { def macroTransform(annottees: Any*): Any = macro caseObject.impl }
    object caseObject {
      def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
        import c.universe._
        val q"trait $variant { $singletonBody }" = annottees.head.tree
        val actual = generateDeclaration(c)(
          Variant(variant.toString, Many(
            Record(singletonBody.toString, Many.empty)
          ))
        )
        val template = TypeName(variant.toString)
        val singleton = TermName(singletonBody.toString)
        val singletonType = TypeName(singleton.toString)
        val expected = q"""
          sealed trait $template[+$singletonType]
          sealed trait $singletonType extends $template[$singletonType]
          case object $singleton extends $singletonType
        """
        assertEqualBlock(c)(expected, actual)
      }
    }

    class fourCaseObjects extends StaticAnnotation { def macroTransform(annottees: Any*): Any = macro fourCaseObjects.impl }
    object fourCaseObjects {
      def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
        import c.universe._
        val q"trait $variant { $case1 ; $case2 ; $case3 ; $case4 }" = annottees.head.tree
        val actual = generateDeclaration(c)(
          Variant(variant.toString, Many(
            Record(case1.toString, Many.empty),
            Record(case2.toString, Many.empty),
            Record(case3.toString, Many.empty),
            Record(case4.toString, Many.empty)
          ))
        )
        val template = TypeName(variant.toString)
        val c1 = TypeName(case1.toString)
        val c2 = TypeName(case2.toString)
        val c3 = TypeName(case3.toString)
        val c4 = TypeName(case4.toString)
        val expected = q"""
          sealed trait $template[+$c1, +$c2, +$c3, +$c4]
          sealed trait $c1 extends $template[$c1, Nothing, Nothing, Nothing]
          case object ${TermName(c1.toString)} extends $c1
          sealed trait $c2 extends $template[Nothing, $c2, Nothing, Nothing]
          case object ${TermName(c2.toString)} extends $c2
          sealed trait $c3 extends $template[Nothing, Nothing, $c3, Nothing]
          case object ${TermName(c3.toString)} extends $c3
          sealed trait $c4 extends $template[Nothing, Nothing, Nothing, $c4]
          case object ${TermName(c4.toString)} extends $c4
        """
        assertEqualBlock(c)(expected, actual)
      }
    }

    class flatCaseClasses extends StaticAnnotation { def macroTransform(annottees: Any*): Any = macro flatCaseClasses.impl }
    object flatCaseClasses {
      def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
        import c.universe._

        val q"""
          trait HorsemanT {
             Conquest(A, A, A)
             War(A, A, B)
             Famine(B)
             Death
          }""" = annottees.head.tree

        val actual = generateDeclaration(c)(
          Variant("HorsemanT", Many(
            Record("Conquest", Many(
              Field("_1", TypeVar("A")),
              Field("_2", TypeVar("A")),
              Field("_3", TypeVar("A")))),
            Record("War", Many(
              Field("_1", TypeVar("A")),
              Field("_2", TypeVar("A")),
              Field("_3", TypeVar("B")))),
            Record("Famine", Many(
              Field("_1", TypeVar("B")))),
            Record("Death", Many.empty)
          ))
        )

        val expected = q"""
          sealed trait HorsemanT[+Conquest, +War, +Famine, +Death]
          sealed case class Conquest[+_1, +_2, +_3](_1: _1, _2: _2, _3: _3) extends
            HorsemanT[Conquest[_1, _2, _3], Nothing, Nothing, Nothing]
          sealed case class War[+_1, +_2, +_3](_1: _1, _2: _2, _3: _3) extends
            HorsemanT[Nothing, War[_1, _2, _3], Nothing, Nothing]
          sealed case class Famine[+_1](_1: _1) extends
            HorsemanT[Nothing, Nothing, Famine[_1], Nothing]
          sealed trait Death extends HorsemanT[Nothing, Nothing, Nothing, Death]
          case object Death extends Death
        """
        assertEqualBlock(c)(expected, actual)
      }
    }

  } // end of DeclarationGenerator.Tests
} // end of DeclarationGenerator
