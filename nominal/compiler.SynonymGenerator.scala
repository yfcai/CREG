package nominal
package compiler

import scala.reflect.macros.blackbox.Context

import DatatypeRepresentation._

trait SynonymGenerator extends UniverseConstruction {
  def generateSynonyms(c: Context)(data: DataConstructor): Many[c.Tree] = {
    Many(generateTopLevelSynonym(c)(data)) ++
    generatePatternFunctorSynonym(c)(data) ++
    generateNestedSynonyms(c)(data)
  }

  // generate synonyms for inner let-bindings
  def generateNestedSynonyms(c: Context)(genericDatatype: DataConstructor): Many[c.Tree] =
    generateContextualNestedSynonyms(c)(genericDatatype.params, genericDatatype.body, Map.empty)

  def generateContextualNestedSynonyms(c: Context)(
    genericParams: Many[Param],
    datatype: Datatype,
    fixedPointEnv: Map[Name, Datatype]
  ): Many[c.Tree] = {
    import c.universe._
    datatype match {
      case fixed @ FixedPoint(name, body) =>
        val newEnv = fixedPointEnv updated (name, fixed subst fixedPointEnv)
        generateContextualNestedSynonyms(c)(genericParams, body, newEnv)

      case LetBinding(lhs, rhs) =>
        generateTopLevelSynonym(c)(DataConstructor(lhs, genericParams, rhs subst fixedPointEnv)) +:
        generateContextualNestedSynonyms(c)(genericParams, rhs, fixedPointEnv)

      case other =>
        val subsynonyms = other.gmapQ {
          case child =>
            generateContextualNestedSynonyms(c)(genericParams, child, fixedPointEnv)
        }
        subsynonyms.toList flatMap identity
    }
  }

  def generateTopLevelSynonym(c: Context)(genericDatatype: DataConstructor): c.Tree =
    generateBoundedSynonym(c)(genericDatatype, Map.empty)

  def generateBoundedSynonym(c: Context)(genericDatatype: DataConstructor, bounds: Map[Name, Datatype]): c.Tree = {
    val (newDatatype, newBounds) = disambiguate(c)(genericDatatype, bounds)
    boundedSynonymWithoutDisambiguation(c)(newDatatype, newBounds)
  }

  /** remove identical names from bounds (currently by failing otherwise) */
  private[this]
  def disambiguate(c: Context)(
    data: DataConstructor, bounds: Map[Name, Datatype]
  ): (DataConstructor, Map[Name, Datatype]) = {
    val identicals = bounds filter {
      case (x1, TypeVar(x2)) => x1 == x2
      case (x1, c2: VariantCase) => x1 == c2.name
      case _ => false
    }
    if (! identicals.isEmpty) sys error s"duplicate names in bounds: $identicals"
    (data, bounds) //stub
  }

  /** precondition: `bounds` contains no identity mapping */
  private[this]
  def boundedSynonymWithoutDisambiguation(c: Context)(
    genericDatatype: DataConstructor, bounds: Map[Name, Datatype]
  ): c.Tree = {
    import c.universe._
    val DataConstructor(name, params, datatypeBody) = genericDatatype
    val typeName = TypeName(name)
    val typeDefs = mkBoundedTypeDefs(c)(params, bounds)
    val rhs = generateRHS(c)(datatypeBody)
    q"type $typeName [ ..$typeDefs ] = $rhs"
  }

  def generateRHS(c: Context)(datatype: Datatype): c.Tree = meaning(c)(datatype)

  def generatePatternFunctorSynonym(c: Context)(genericFixedPoint: DataConstructor): Option[c.Tree] =
    genericFixedPoint match {
      case DataConstructor(_, genericParams, fixed @ FixedPoint(_, _)) =>
        import c.universe._
        val DataConstructor(lowerCaseName, recursiveParams, datatypeBody) = fixed.patternFunctor
        val patternFunctorTypeName = TypeName(lowerCaseName.capitalize)
        val typeParams = mkTypeDefs(c)(genericParams ++ recursiveParams)
        val rhs = generateRHS(c)(datatypeBody)
        Some(q"type $patternFunctorTypeName [ ..$typeParams ] = $rhs")

      case _ =>
        None
    }
}
