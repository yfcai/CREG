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
  def generateDeclaration(c: Context)(datatype: Variant, declaredSupers: Many[c.Tree]):
      Many[c.Tree] =
    generateVariants(c)(datatype, declaredSupers) ++ generateKIRVPrimitives(c)(datatype)

  def generateVariants(c: Context)(datatype: Variant, declaredSupers: Many[c.Tree]):
      Many[c.Tree] =
  {
    import c.universe._

    val template = mkTemplate(c)(datatype.name)
    val supers   = declaredSupers :+ getVariant(c)

    if (datatype.cases.isEmpty)
      Many(q"sealed trait $template extends ..$supers")
    else
      q"sealed trait $template [..${generateCaseNames(c)(datatype.cases)}] extends ..$supers" +: (
        generateCases(c)(template, datatype.cases)
      )
  }

  /** @param cases a bunch of named variants
    * @return their names as TypeName
    */
  def generateCaseNames(c: Context)(cases: Many[VariantCase]): Many[c.Tree] =
    covariantTypeParams(c)(cases.map(_.name))

  /** @param template TypeName of the template trait of the variant
    * @param cases cases of the variant
    * @return generated code for cases of the variant
    */
  def generateCases(c: Context)(template: c.TypeName, cases: Many[VariantCase]): Many[c.Tree] = {
    import c.universe._
    cases.zipWithIndex flatMap {
      case (record @ Record(name, Many()), i) => // empty record
        val typeName = TypeName(name)
        val params = namedParamsWithNothing(c)(typeName, i, cases.size)
        val (termName, traversableN, typeMap, emptyDefTraverse) = recordPrototypeFragments(c)(record)
        Many(
          q"sealed trait $typeName extends $template[..$params] with ${getRecord(c)}",
          q"case object $termName extends $typeName with $traversableN { $typeMap }")

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

      // copy-paste for variants
      case (variant @ Variant(name, Many()), i) =>
        val typeName = mkTemplate(c)(name)
        val termName = TermName(name)
        val params = namedParamsWithNothing(c)(typeName, i, cases.size)
        val newSuper = tq"$template[..$params]"
        generateVariants(c)(variant, Many(newSuper))

      case (variant @ Variant(name, fields), i) =>
        // records are wholely free
        val typeName = mkTemplate(c)(name)
        val fieldNames = fields.map(_.name)
        val caseParams = covariantTypeParams(c)(fieldNames)
        val myType = tq"$typeName[..${fieldNames.map(name => TypeName(name))}]"
        val templateParams = appliedParamsWithNothing(c)(myType, i, cases.size)
        val newSuper = tq"$template[..$templateParams]"
        generateVariants(c)(variant, Many(newSuper))
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
      datatype.cases.flatMap({
        case x: Record  => Many(generateRecordPrototype(c)(x))
        case x: Variant => generateKIRVPrimitives(c)(x)
      }) :+ generateVariantPrototype(c)(datatype)
  }

  def generateVariantPrototype(c: Context)(datatype: Variant): c.Tree = {
    import c.universe._
    val n = datatype.cases.length
    val objName = TermName(datatype.name)
    val variantName = mkTemplate(c)(datatype.name)

    // compute bounds
    val bounds = datatype.cases map {
      child => tq"${TermName(child.name)}.${typeNameRange(c)}"
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
          (fs, as, datatype.cases).zipped flatMap {
            case (f, a, record: Record) =>
              Many(generateRecordTraversal(c)(record, g, f, a, bs))

            case (f, a, variant: Variant) =>
              def loop(v: Variant): Many[CaseDef] = v.cases.flatMap {
                case record : Record  => Many(generateRecordTraversal(c)(record, g, f, a, bs))
                case variant: Variant => loop(variant)
              }
              loop(variant)
          }
        val x = TermName(c freshName "x")
        q"{ ${mkValDef(c)(x, TypeTree())} => ${ Match(q"$x", caseDefs.toList) } }"
    }
    q"object $objName extends $traversableN { ..$cats ; $typeMap ; $defTraverse }"
  }

  /** @param record the record to generate a CaseDef for
    * @param g the applicative functor
    * @param f the current function
    * @param a the argument type of f
    * @param bs the output params
    */
  def generateRecordTraversal(c: Context)(
    record: Record, g: c.TermName, f: c.TermName, a: c.TypeName, bs: Many[c.TypeName]): c.universe.CaseDef =
  {
    import c.universe._
    recordCaseDef(c)(record) {
      case (rcd, _) =>
        q"""
          $f($rcd.asInstanceOf[$a]).
            asInstanceOf[${getFunctorMapOnObjects(c)(g)}[${getThisMapOnObjects(c)}[..$bs]]]
        """
    }
  }

  def generateRecordPrototype(c: Context)(record: Record): c.Tree =
    if (record.fields.isEmpty)
      c parse "" // already generated as a case object
    else {
      import c.universe._
      val (termName, traversableN, typeMap, defTraverse) = recordPrototypeFragments(c)(record)
      q"object $termName extends $traversableN { $typeMap ; $defTraverse }"
    }

 /** @return (name, supertrait, typeMap, traverse)
   */
  def recordPrototypeFragments(c: Context)(record: Record): (c.TermName, c.Tree, c.Tree, c.Tree) = {
    import c.universe._
    val n = record.fields.length
    val termName = TermName(record.name)
    val typeName = TypeName(record.name)
    val traversableN = getTraversableEndofunctor(c, n)
    val typeMap = mkTypeMap(c, n) { params =>
      if (params.nonEmpty) tq"$typeName[..$params]" else tq"$typeName"
    }
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
    (termName, traversableN, typeMap, defTraverse)
  }
}
