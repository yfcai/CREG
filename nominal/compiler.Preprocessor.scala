package nominal
package compiler

import scala.reflect.macros.blackbox.Context
import DatatypeRepresentation._

trait Preprocessor extends util.AbortWithError with util.Traverse with util.Traits {

  sealed case class PreprocessorException(message: String) extends Exception(message)

  /** @return a series of declarations to generate
    */
  def digestForDeclarationGenerator(c: Context)(input: c.Tree, parseTree: DataConstructor): Iterator[Variant] = {
    // check that parseTree starts with a variant
    Iterator(topLevelVariant(c)(input, parseTree))
  }

  /** @param input the trait
    *
    * @return packaged food for synonym generator
    */
  def digestForSynonymGenerator(c: Context)(input: c.Tree, parseTree: DataConstructor): SynonymGeneratorFood = {
    val variant = topLevelVariant(c)(input, parseTree)
    val name = variant.name

    renameRecursiveVariant(c)(input, variant) match {
      // not recursive
      case None =>
        SynonymGeneratorFood(
        (name, DataConstructor(parseTree.params, templatify(variant))),
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
    case Variant(name, body) => FixedPoint(name, templatify(variant))
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
    * @return renaming recursive positions to variant.name if variant is recursive
    *         nothing otherwise
    */
  def renameRecursiveVariant(c: Context)(input: c.Tree, variant: Variant): Option[Variant] = {
    val dangerMarker = variant.name + "["
    val expectedName = getFullNameOfTrait(c)(input).get
    val isRecursive = variant.exist {
      case TypeVar(name) if name == expectedName => ()

      case TypeVar(name) if name != expectedName & name == variant.name =>
        throw new PreprocessorException(
          s"recursive position of $expectedName should not be marked by just $name")

      case TypeVar(name) if name != expectedName & name.startsWith(dangerMarker) =>
        throw new PreprocessorException(
          s"$name should not occur in the definition of $expectedName, because we don't support GADTs")
    }
    if (isRecursive)
      Some(variant.rename(Map(expectedName -> variant.name)).asInstanceOf[Variant])
    else
      None
  }

  // append 'F' to a TypeVar
  private[this] def appendF(name: Name): Name = name + "F"
}
