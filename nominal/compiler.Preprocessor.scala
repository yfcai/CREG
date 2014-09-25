package nominal
package compiler

import scala.reflect.macros.blackbox.Context
import DatatypeRepresentation._

trait Preprocessor extends util.AbortWithError {

  sealed case class PreprocessorException(message: String) extends Exception(message)

  /** @return a series of declarations to generate
    */
  def digestForDeclarationGenerator(c: Context)(input: c.Tree, parseTree: DataConstructor): Iterator[Variant] = {
    // check that parseTree starts with a variant
    val variant = topLevelVariant(c)(input, parseTree)
    extractVariants(variant)
  }

  /** @param input the trait
    *
    * @return packaged food for synonym generator
    */
  def digestForSynonymGenerator(c: Context)(input: c.Tree, parseTree: DataConstructor): SynonymGeneratorFood = {
    val variant = topLevelVariant(c)(input, parseTree)
    val name = variant.header.name

    renameRecursiveVariant(c)(input, variant) match {
      // not recursive
      case None =>
        SynonymGeneratorFood(
        (name, DataConstructor(parseTree.params, variant)),
        None)

      // recursive
      case Some(variant) =>
        val pointless = DataConstructor(parseTree.params, pointlessify(variant, parseTree.params))
        SynonymGeneratorFood(
          (name, pointless),
          Some((appendF(name), pointless)))
    }
  }

  sealed case class SynonymGeneratorFood(
    dataSynonym: (Name, DataConstructor),
    patternFunctor: Option[(Name, DataConstructor)])

  /** turn a recursive variant into a fixed point
    *
    * WARNING: if `variant` is not recursive, will produce fixed point of
    *          constant functor.
    */
  def pointlessify(variant: Variant, genericParams: Many[Param]): FixedPoint = variant match {
    case Variant(TypeVar(name), body) => FixedPoint(name, variant)
  }


  /** extract variant from parse tree, abort on failure
    *
    * @param c          context for error reporting
    * @param input      tree for error reporting
    * @param parseTree  parse tree to digest for declaration generator
    */
  def topLevelVariant(c: Context)(input: c.Tree, parseTree: DataConstructor): Variant =
    parseTree match {
      case DataConstructor(_, variant @ Variant(_, _)) =>
        variant

      case _ =>
        abortWithError(c)(input.pos, "500 internal error: parse tree isn't a top-level variant")
    }

  /** @param input the trait annotated by @datatype macro
    * @param variant parsed variant
    *
    * @return renaming recursive positions to variant.header.name if variant is recursive
    *         nothing otherwise
    */
  def renameRecursiveVariant(c: Context)(input: c.Tree, variant: Variant): Option[Variant] = {
    val dangerMarker = variant.header.name + "["
    val expectedName = getFullNameOfTrait(c)(input).get
    val isRecursive = exists(variant) {
      case TypeVar(name) if name == expectedName => ()

      case TypeVar(name) if name != expectedName & name == variant.header.name =>
        throw new PreprocessorException(
          s"recursive position of $expectedName should not be marked by just $name")

      case TypeVar(name) if name != expectedName & name.startsWith(dangerMarker) =>
        throw new PreprocessorException(
          s"$name should not occur in the definition of $expectedName, because we don't support GADTs")
    }
    if (isRecursive)
      Some(variant.rename(Map(expectedName -> variant.header.name)).asInstanceOf[Variant])
    else
      None
  }

  private[this] def exists(data: Datatype)(predicate: PartialFunction[Datatype, Unit]): Boolean =
    ! data.everywhereQ(predicate).isEmpty

  // append 'F' to a TypeVar
  private[this] def appendF(name: Name): Name = name + "F"

  /** @return all variants nested in this datatype declaration
    */
  def extractVariants(datatype: Datatype): Iterator[Variant] = datatype everywhereQ {
    case variant @ Variant(_, _) => variant
  }

  def getNameOfTrait(c: Context)(tree: c.Tree): Option[String] = {
    import c.universe._
    tree match {
      case q"trait $name [..$params]" => Some(name.toString)
      case q"trait $name [..$params] {}" => Some(name.toString)
      case q"trait $name [..$params] { ..$body }" => Some(name.toString)
      case _ => None
    }
  }

  def getFullNameOfTrait(c: Context)(tree: c.Tree): Option[String] = {
    import c.universe._

    def mkName(name: c.TypeName, params: List[c.universe.TypeDef]): String = {
      //
      val paramNames = params map {
        case TypeDef(modifiers, typeName, typeParams, rhs) =>
          typeName.toString
      }

      if (paramNames.isEmpty)
        name.toString
      else
        s"$name[${paramNames mkString ", "}]"
    }

    tree match {
      case q"trait $name [..$params]" => Some(mkName(name, params))
      case q"trait $name [..$params] {}" => Some(mkName(name, params))
      case q"trait $name [..$params] { ..$body }" => Some(mkName(name, params))
      case _ => None
    }
  }
}
