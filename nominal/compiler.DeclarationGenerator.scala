package nominal
package compiler

import scala.reflect.macros.blackbox.Context

import DatatypeRepresentation._

trait DeclarationGenerator extends UniverseConstruction with util.Traverse {
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

    val template = mkTemplate(c)(datatype.header.name)

    if (datatype.cases.isEmpty)
      Many(q"sealed trait $template extends ${getVariant(c)}")
    else
      q"sealed trait $template [..${generateCaseNames(c)(datatype.cases)}] extends ${getVariant(c)}" +: (
        generateCases(c)(template, datatype.cases) ++
          generateKIRV(c)(datatype)
      )
  }

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
          q"sealed trait $typeName extends $template[..$params] with ${getRecord(c)}",
          q"case object $termName extends $typeName")

      case (Record(name, fields), i) =>
        // records are wholely free
        val typeName = TypeName(name)
        val fieldNames = fields.map(_.name)
        val caseParams = covariantTypeParams(c)(fieldNames)
        val myType = tq"$typeName[..${fieldNames.map(name => TypeName(name))}]"
        val templateParams = appliedParamsWithNothing(c)(myType, i, cases.size)
        val decls = generateFreeDecls(c)(fieldNames)
        Many(q"""sealed case class $typeName[..$caseParams](..$decls) extends
          $template[..$templateParams] with ${getRecord(c)}""")
    }
  }

  /** @param fieldNames names of fields _i to put in the form of _i: _i
    */
  def generateFreeDecls(c: Context)(fieldNames: Many[Name]): Many[c.Tree] =
    fieldNames.map {
      case name =>
        import c.universe._
        val caseClassIn = TypeName(c freshName "CaseClass")
        val q"case class $caseClassOut($decl)" =
          q"case class $caseClassIn(${TermName(name)}: ${TypeName(name)})"
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

  def generateKIRV(c: Context)(datatype: Variant): Many[c.Tree] = {
    generateVariantPrototype(c)(datatype) +:
      datatype.cases.map(x => generateRecordPrototype(c)(x.asInstanceOf[Record]))
  }

  def generateVariantPrototype(c: Context)(datatype: Variant): c.Tree = {
    import c.universe._
    val n = datatype.cases.length
    val objName = TermName(datatype.header.name)
    val variantName = mkTemplate(c)(datatype.header.name)
    val traversableN = getTraversableN(c, n)
    val typeMap = mkTypeMap(c, n) { params => tq"$variantName[..$params]" }
    val defTraverse = mkDefTraverse(c, n) {
      case (g, fs, as, bs) =>
        val caseDefs: Many[CaseDef] =
          (fs, as, datatype.cases).zipped.map({
            case (f, a, record) =>
              recordCaseDef(c)(record.asInstanceOf[Record]) {
                case (rcd, _) =>
                  q"""
                    $f($rcd.asInstanceOf[$a]).
                      asInstanceOf[${getFunctorMapOnObjects(c)(g)}[${getThisMapOnObjects(c)}[..$bs]]]
                  """
              }
          })(collection.breakOut)
        val x = TermName(c freshName "x")
        q"{ ${mkValDef(c)(x, TypeTree())} => ${ Match(q"$x", caseDefs.toList) } }"
    }
    q"object $objName extends $traversableN { $typeMap ; $defTraverse }"
  }

  def generateRecordPrototype(c: Context)(record: Record): c.Tree = {
    import c.universe._
    if (record.fields.isEmpty)
      q"();" // EmptyTree does not work
    else {
      val n = record.fields.length
      val termName = TermName(record.name)
      val typeName = TypeName(record.name)
      val traversableN = getTraversableN(c, n)
      val typeMap = mkTypeMap(c, n) { params => tq"$typeName[..$params]" }
      val defTraverse = mkDefTraverse(c, n) {
        case (g, fs, as, bs) =>
          val caseDef = recordCaseDef(c)(record) {
            case (_, fieldNames) =>
              mkCallTree(c)(g,
                mkPureCurriedFunction(c)(g, termName, typeName, bs) +:
                  fs.zip(fieldNames).map({ case (f, x) => q"$f($x)" }))
          }
          val x = TermName(c freshName "x")
          q"{ ${mkValDef(c)(x, TypeTree())} => ${ Match(q"$x", List(caseDef)) } }"
      }
      q"object $termName extends $traversableN { $typeMap ; $defTraverse }"
    }
  }
}

object DeclarationGenerator {
  /** test macros */
  object Tests extends DeclarationGenerator with util.AssertEqual {
    import scala.language.experimental.macros
    import scala.annotation.StaticAnnotation

    class empty extends StaticAnnotation { def macroTransform(annottees: Any*): Any = macro empty.impl }
    object empty {
      def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
        import c.universe._
        val q"trait $name" = annottees.head.tree
        val actual = generateDeclaration(c)(
          Variant(TypeVar(name.toString), Many.empty)
        )
        val expected = q"sealed trait ${TypeName(name.toString + "T")} extends ${getVariant(c)}"
        assertHasPrefixBlock(c)(expected, actual)
      }
    }

    class caseObject extends StaticAnnotation { def macroTransform(annottees: Any*): Any = macro caseObject.impl }
    object caseObject {
      def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
        import c.universe._
        val q"trait $variant { $singletonBody }" = annottees.head.tree
        val actual = generateDeclaration(c)(
          Variant(TypeVar(variant.toString), Many(
            Record(singletonBody.toString, Many.empty)
          ))
        )
        val template = TypeName(variant.toString + "T")
        val singleton = TermName(singletonBody.toString)
        val singletonType = TypeName(singleton.toString)
        val expected = q"""
          sealed trait $template[+$singletonType] extends ${getVariant(c)}
          sealed trait $singletonType extends $template[$singletonType] with ${getRecord(c)}
          case object $singleton extends $singletonType
        """
        assertHasPrefixBlock(c)(expected, actual)
      }
    }

    class fourCaseObjects extends StaticAnnotation { def macroTransform(annottees: Any*): Any = macro fourCaseObjects.impl }
    object fourCaseObjects {
      def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
        import c.universe._
        val q"trait $variant { $case1 ; $case2 ; $case3 ; $case4 }" = annottees.head.tree
        val actual = generateDeclaration(c)(
          Variant(TypeVar(variant.toString), Many(
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
          sealed trait $template[+$c1, +$c2, +$c3, +$c4] extends ${getVariant(c)}
          sealed trait $c1 extends $template[$c1, Nothing, Nothing, Nothing] with ${getRecord(c)}
          case object ${TermName(c1.toString)} extends $c1
          sealed trait $c2 extends $template[Nothing, $c2, Nothing, Nothing] with ${getRecord(c)}
          case object ${TermName(c2.toString)} extends $c2
          sealed trait $c3 extends $template[Nothing, Nothing, $c3, Nothing] with ${getRecord(c)}
          case object ${TermName(c3.toString)} extends $c3
          sealed trait $c4 extends $template[Nothing, Nothing, Nothing, $c4] with ${getRecord(c)}
          case object ${TermName(c4.toString)} extends $c4
        """
        assertHasPrefixBlock(c)(expected, actual)
      }
    }

    class flatCaseClasses extends StaticAnnotation { def macroTransform(annottees: Any*): Any = macro flatCaseClasses.impl }
    object flatCaseClasses {
      def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
        import c.universe._

        val actual = generateDeclaration(c)(
          Variant(TypeVar("Horseman"), Many(
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
          sealed trait HorsemanT[+Conquest, +War, +Famine, +Death] extends ${getVariant(c)}
          sealed case class Conquest[+_1, +_2, +_3](_1: _1, _2: _2, _3: _3) extends
            HorsemanT[Conquest[_1, _2, _3], Nothing, Nothing, Nothing] with ${getRecord(c)}
          sealed case class War[+_1, +_2, +_3](_1: _1, _2: _2, _3: _3) extends
            HorsemanT[Nothing, War[_1, _2, _3], Nothing, Nothing] with ${getRecord(c)}
          sealed case class Famine[+_1](_1: _1) extends
            HorsemanT[Nothing, Nothing, Famine[_1], Nothing] with ${getRecord(c)}
          sealed trait Death extends HorsemanT[Nothing, Nothing, Nothing, Death] with ${getRecord(c)}
          case object Death extends Death
        """
        assertHasPrefixBlock(c)(expected, actual)
      }
    }

  } // end of DeclarationGenerator.Tests
} // end of DeclarationGenerator
