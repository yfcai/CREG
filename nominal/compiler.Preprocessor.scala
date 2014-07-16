package nominal

import scala.reflect.macros.blackbox.Context
import DatatypeRepresentation._

trait Preprocessor extends AbortWithError {

  sealed case class PreprocessorException(message: String) extends Exception(message)

  /** @return a series of declarations to generate
    */
  def digestForDeclarationGenerator(c: Context)(input: c.Tree, parseTree: DataConstructor): Iterator[Variant] = {
    // check that parseTree starts with a variant
    val variant = topLevelVariant(c)(input, parseTree)
    extractVariants(appendLetterT(variant))
  }

  /** @return packaged food for synonym generator
    */
  def digestForSynonymGenerator(c: Context)(input: c.Tree, parseTree: DataConstructor): SynonymGeneratorFood = {
    val variant = topLevelVariant(c)(input, parseTree)
    val name = variant.header.name
    if (isRecursiveVariant(variant)) {
      // recursive
      val pointless = DataConstructor(parseTree.params, pointlessify(variant, parseTree.params))
      SynonymGeneratorFood(
        (name, pointless),
        Some((appendF(name), pointless)))
    }
    else
      // not recursive
      SynonymGeneratorFood(
        (name, DataConstructor(parseTree.params, appendLetterT(variant))),
        None)
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
    case Variant(TypeVar(name), body) => FixedPoint(name, appendLetterT(variant))
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

  /** @return whether a top-level variant is recursive */
  def isRecursiveVariant(variant: Variant): Boolean = {
    val dangerMarker = variant.header.name + "["
    exists(variant) {
      case TypeVar(name) if name == variant.header.name => ()
      case TypeVar(name) if name startsWith dangerMarker =>
        throw new PreprocessorException(
          s"Never mark recursive positions by $name. " +
            s"Marked them by `${variant.header.name}` without arguments. " +
            "The @datatype macro does not support GADTs.")
    }
  }

  private[this] def exists(data: Datatype)(predicate: PartialFunction[Datatype, Unit]): Boolean =
    ! data.everywhereQ(predicate).isEmpty

  /** @return datatype with 'T' appended to every variant header
    *         TypeVars are otherwise left alone
    */
  def appendLetterT(datatype: Datatype): Datatype = datatype everywhere {
    case Variant(header, body) =>
      Variant(appendT(header), body)
  }

  // append 'T' to a TypeVar
  private[this] def appendT(header: TypeVar): TypeVar = TypeVar(header.name + "T")
  private[this] def appendF(name: Name): Name = name + "F"

  /** @return all variants nested in this datatype declaration
    */
  def extractVariants(datatype: Datatype): Iterator[Variant] = datatype everywhereQ {
    case variant @ Variant(_, _) => variant
  }
}
