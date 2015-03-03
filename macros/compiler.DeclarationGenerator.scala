package creg
package compiler

import scala.reflect.macros.blackbox.Context

import DatatypeRepresentation._

trait DeclarationGenerator extends UniverseConstruction with util.Traverse with util.Traits {
  def generateDeclarations(c: Context)(data: Datatype, declaredSupers: Many[c.Tree]):
      Many[c.Tree] =
    generateClasses(c)(data, declaredSupers) ++ generatePrimitives(c)(data)

  def generateClasses(c: Context)(data: Datatype, supers: Many[c.Tree]): Many[c.Tree] =
    data match {
      case r: Record =>
        generateStandaloneRecord(c)(r, supers)

      case v: Variant =>
        generateVariants(c)(v, supers)

      case FixedPoint(name, body) =>
        generateClasses(c)(body, supers)

      case TypeVar(_) | TypeConst(_) =>
        Many.empty

      case LetBinding(lhs, rhs) =>
        generateClasses(c)(rhs, supers)

      case other =>
        noRecognition(other)
    }

  def generateVariants(c: Context)(datatype: Variant, declaredSupers: Many[c.Tree]):
      Many[c.Tree] =
  {
    import c.universe._

    val template = TypeName(datatype.name)
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

  /** generate a record that's not a case of some variant */
  def generateStandaloneRecord(c: Context)(record: Record, declaredSupers: Many[c.Tree]): Many[c.Tree] = {
    import c.universe._
    val supers = declaredSupers :+ getRecord(c)
    val typeName = TypeName(record.name)
    if (record.fields.isEmpty) {
      val (termName, traversable0, typeMap, emptyDefTraverse) = recordPrototypeFragments(c)(record)
      Many(
        q"sealed trait $typeName extends ..$supers",
        q"case object $termName extends $typeName with $traversable0 { $typeMap }")
    }
    else {
      val fieldNames = record.fields map (_.name)
      val caseParams = covariantTypeParams(c)(fieldNames)
      val decls = generateFreeDecls(c)(fieldNames)
      Many(q"sealed case class $typeName[..$caseParams](..$decls) extends ..$supers")
    }
  }

  /** @param template TypeName of the template trait of the variant
    * @param cases cases of the variant
    * @return generated code for cases of the variant
    */
  def generateCases(c: Context)(template: c.TypeName, cases: Many[VariantCase]): Many[c.Tree] = {
    val n = cases.size
    cases.zipWithIndex flatMap { case (vcase, i) => generateVariantCase(c)(template, vcase, i, n) }
  }

  def generateVariantCase(c: Context)(template: c.TypeName, variantCase: VariantCase, i: Int, n: Int):
      Many[c.Tree] =
  {
    import c.universe._
    variantCase match {
      case record @ Record(name, Many()) => // empty record
        val typeName = TypeName(name)
        val params = namedParamsWithNothing(c)(typeName, i, n)
        val (termName, traversable0, typeMap, emptyDefTraverse) = recordPrototypeFragments(c)(record)
        Many(
          q"sealed trait $typeName extends $template[..$params] with ${getRecord(c)}",
          q"case object $termName extends $typeName with $traversable0 { $typeMap }")

      case Record(name, fields) =>
        // records are wholely free
        val typeName = TypeName(name)
        val fieldNames = fields.map(_.name)
        val caseParams = covariantTypeParams(c)(fieldNames)
        val myType = tq"$typeName[..${fieldNames.map(name => TypeName(name))}]"
        val templateParams = appliedParamsWithNothing(c)(myType, i, n)
        val decls = generateFreeDecls(c)(fieldNames)
        Many(q"""sealed case class $typeName[..$caseParams](..$decls) extends
          $template[..$templateParams] with ${getRecord(c)}""")

      // copy-paste for variants
      case variant @ Variant(name, Many()) =>
        val typeName = TypeName(name)
        val termName = TermName(name)
        val params = namedParamsWithNothing(c)(typeName, i, n)
        val newSuper = tq"$template[..$params]"
        generateVariants(c)(variant, Many(newSuper))

      case variant @ Variant(name, fields) =>
        // records are wholely free
        val typeName = TypeName(name)
        val fieldNames = fields.map(_.name)
        val caseParams = covariantTypeParams(c)(fieldNames)
        val myType = tq"$typeName[..${fieldNames.map(name => TypeName(name))}]"
        val templateParams = appliedParamsWithNothing(c)(myType, i, n)
        val newSuper = tq"$template[..$templateParams]"
        generateVariants(c)(variant, Many(newSuper))

      case LetBinding(lhs, rhs) =>
        generateVariantCase(c)(template, rhs, i, n)
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

  def generatePrimitives(c: Context)(datatype: Datatype): Many[c.Tree] =
    datatype match {
      // variant is special in that it appends the top-level variant prototype
      case v: Variant =>
        generateVariantPrimitives(c)(v)

      // other variant cases: records, record assignments, let bindings
      case vcase: VariantCase =>
        generateVariantCasePrimitives(c)(vcase)

      case FixedPoint(name, body) =>
        generatePrimitives(c)(body)

      case TypeVar(_) | TypeConst(_) =>
        Many.empty

      case other =>
        noRecognition(other)
    }

  def generateVariantCasePrimitives(c: Context)(variantCase: VariantCase): Many[c.Tree] =
    variantCase match {
      case x: Record => Many(generateRecordPrototype(c)(x))
      case x: Variant => generateVariantPrimitives(c)(x)
      case LetBinding(lhs, rhs) => generateVariantCasePrimitives(c)(rhs)
    }

  def generateVariantPrimitives(c: Context)(datatype: Variant): Many[c.Tree] = {
    datatype.cases.flatMap(x => generateVariantCasePrimitives(c)(x)) :+
    generateVariantPrototype(c)(datatype)
  }

  def generateVariantPrototype(c: Context)(datatype: Variant): c.Tree = {
    import c.universe._
    val n = datatype.cases.length
    val objName = TermName(datatype.name)
    val variantName = TypeName(datatype.name)

    // compute bounds
    val bounds = datatype.cases map {
      child => tq"${TermName(child.name)}.${typeNameRange(c)}"
    }

    // trait to extend
    val traversableN = getTraversableBounded(c, n)

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
            case (f, a, vcase) =>
              mkDefTraverseVariantCase(c)(g, f, a, bs, vcase)
          }
        val x = TermName(c freshName "x")
        q"{ ${mkValDef(c)(x, TypeTree())} => ${ Match(q"$x", caseDefs.toList) } }"
    }
    q"object $objName extends $traversableN { ..$cats ; $typeMap ; $defTraverse }"
  }

  def mkDefTraverseVariantCase(c: Context)(
    g: c.TermName, // the applicative functor
    f: c.TermName, // the appropriate mapping `A => Map[B]`
    a: c.TypeName, // the argument type `A`
    bs: Many[c.TypeName], // the result type params `B`
    v: VariantCase
  ): Many[c.universe.CaseDef] = {
    import c.universe._
    v match {
      case record: Record =>
        Many(generateRecordTraversal(c)(record, g, f, a, bs))

      case variant: Variant =>
        variant.cases.flatMap { vcase => mkDefTraverseVariantCase(c)(g, f, a, bs, vcase) }

      case LetBinding(lhs, rhs) => mkDefTraverseVariantCase(c)(g, f, a, bs, rhs)
    }
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
