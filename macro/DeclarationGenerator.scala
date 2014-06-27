import scala.reflect.macros.blackbox.Context

import DatatypeRepresentation._

trait DeclarationGenerator {
  /** @param datatype Representation of data type
    * @return AST of generated traits and case classes
    *
    * Caution: Classes involved in datatypes must *all* be uninheritable.
    * If this is the case, then we can make the fixed point type covariant
    * without sacrificing the functor instance inside Fix[+F[+_]], which
    * is necessary to obtain covariance in something like List[+A].
    */
  def generateDeclaration(c: Context)(datatype: Variant): c.Tree = {
    import c.universe._

    val template = mkTemplate(c)(datatype.name)

    if (datatype.cases.isEmpty)
      q"sealed trait $template"
    else {
      q"""
        sealed trait $template [..${generateCaseNames(c)(datatype.cases)}]
        ..${generateCases(c)(template, datatype.cases)}
      """
    }
  }

  /** create the name of the template trait by appending T */
  def mkTemplate(c: Context)(name: String): c.TypeName = c.universe.TypeName(name + "T")

  /** @param cases a bunch of named variants
    * @return their names as TypeName
    */
  def generateCaseNames(c: Context)(cases: Many[RecordOrHole]): Many[c.Tree] = {
    import c.universe._
    cases.map(record => covariantTypeParam(c)(record.name))
  }

  /** @param name name of type parameter
    * @return covariant type parameter of that name
    */
  def covariantTypeParam(c: Context)(name: String): c.Tree = {
    import c.universe._
    val q"type Dummy[$result]" = q"type Dummy[+${TypeName(name)}]"
    result
  }

  /** @param template TypeName of the template trait of the variant
    * @param cases cases of the variant
    * @return generated code for cases of the variant
    */
  def generateCases(c: Context)(template: c.TypeName, cases: Many[RecordOrHole]): Many[c.Tree] = {
    import c.universe._
    cases.zipWithIndex flatMap {
      case (Record(name, Many()), i) =>
        val typeName = TypeName(name)
        val termName = TermName(name)
        val params = namedParamsWithNothing(c)(typeName, i, cases.size)
        Many(
          q"sealed trait $typeName extends $template[..$params]",
          q"case object $termName extends $typeName")
    }
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
}

object DeclarationGenerator {
  /** test macros */
  object Tests extends DeclarationGenerator {
    import scala.language.experimental.macros
    import scala.annotation.StaticAnnotation

    private[this] def err(msg: String): Nothing = { System.err println msg ; sys error "got error" }

    def assertEqual(c: Context)(expected: c.Tree, actual: c.Tree): c.Expr[Any] = {
      import c.universe._
      // assert(actual.duplicate != actual) // this is actually true!
      // resorting to string comparison.
      // doesn't seem to have anything better.
      val eRaw = showRaw(expected)
      val aRaw = showRaw(actual)
      if (eRaw != aRaw)
        err(s"\nExpected:\n$eRaw\n\nActual:\n$aRaw\n")
      else
        c.Expr(actual)
    }

    class empty extends StaticAnnotation { def macroTransform(annottees: Any*): Any = macro empty.impl }
    object empty {
      def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
        import c.universe._
        val q"trait $name" = annottees.head.tree
        val actual = generateDeclaration(c)(
          Variant(name.toString, Many.empty)
        )
        val expected = q"sealed trait ${TypeName(name.toString + "T")}"
        assertEqual(c)(expected, actual)
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
        val template = TypeName(variant.toString + "T")
        val singleton = TermName(singletonBody.toString)
        val singletonType = TypeName(singleton.toString)
        val expected = q"""
          sealed trait $template[+$singletonType]
          sealed trait $singletonType extends $template[$singletonType]
          case object $singleton extends $singletonType
        """
        assertEqual(c)(expected, actual)
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
        val template = TypeName(variant.toString + "T")
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
        assertEqual(c)(expected, actual)
      }
    }
  }
}
