package nominal
package compiler

import scala.reflect.macros.blackbox.Context

import DatatypeRepresentation._

trait DeclarationGenerator extends UniverseConstruction with util.Traverse with util.Traits {
  /** @param datatype Representation of data type
    * @return AST of generated traits and case classes
    *
    * Caution: Classes involved in datatypes must *all* be uninheritable.
    * If this is the case, then we can make the fixed point type covariant
    * without sacrificing the functor instance inside Fix[+F[+_]], which
    * is necessary to obtain covariance in something like List[+A].
    */
  def generateDeclaration(c: Context)(datatype: Variant, input: c.Tree): Many[c.Tree] = {
    import c.universe._

    val template = mkTemplate(c)(datatype.header.name)
    val supers   = getSupersOfTrait(c)(input) :+ getVariant(c)

    if (datatype.cases.isEmpty)
      Many(q"sealed trait $template extends ..$supers")
    else
      q"sealed trait $template [..${generateCaseNames(c)(datatype.cases)}] extends ..$supers" +: (
        generateCases(c)(template, datatype.cases) ++
          generateKIRVPrimitives(c)(datatype)
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

  def generateKIRVPrimitives(c: Context)(datatype: Variant): Many[c.Tree] = {
    generateVariantPrototype(c)(datatype) +:
      datatype.cases.map(x => generateRecordPrototype(c)(x.asInstanceOf[Record]))
  }

  def generateVariantPrototype(c: Context)(datatype: Variant): c.Tree = {
    import c.universe._
    val n = datatype.cases.length
    val objName = TermName(datatype.header.name)
    val variantName = mkTemplate(c)(datatype.header.name)
    val records = datatype.cases.asInstanceOf[Many[Record]]

    // compute bounds
    val bounds = records map {
      case Record(recordName, fields) =>
        val typeName = TypeName(recordName)
        val theAny = getAnyType(c)
        val typeArgs = fields map (_ => theAny)
        tq"$typeName[..$typeArgs]"
    }

    // trait to extend
    val traversableN = getBoundedTraversable(c, n)

    // subcategory bounds
    val cats = bounds.zipWithIndex map {
      case (bound, i) =>
        val cat = typeNameCat(c, i)
        q"type $cat = $bound"
    }

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
    q"object $objName extends $traversableN { ..$cats ; $typeMap ; $defTraverse }"
  }

  def generateRecordPrototype(c: Context)(record: Record): c.Tree = {
    import c.universe._
    if (record.fields.isEmpty)
      q"();" // EmptyTree does not work
    else {
      val n = record.fields.length
      val termName = TermName(record.name)
      val typeName = TypeName(record.name)
      val traversableN = getTraversableEndofunctor(c, n)
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
