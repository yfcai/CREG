import scala.reflect.macros.blackbox.Context
import DatatypeRepresentation._

trait Preprocessor extends AbortWithError {

  /** digest parse tree for declaration generator
    *
    * @param c          context for error reporting
    * @param input      tree for error reporting
    * @param parseTree  parse tree to digest for declaration generator
    *
    * @return           a series of declarations to generate
    */
  def digestForDeclarationGenerator(c: Context)(input: c.Tree, parseTree: DataConstructor): Iterator[Variant] = {
    // check that parseTree starts with a variant
    val variant = parseTree match {
      case DataConstructor(_, variant @ Variant(_, _)) =>
        variant

      case _ =>
        abortWithError(c)(input.pos, "500 internal error: parse tree isn't a top-level variant")
    }
    extractVariants(appendLetterT(variant))
  }

  /** @return datatype with 'T' appended to every variant header
    *         TypeVars are otherwise left alone
    */
  def appendLetterT(datatype: Datatype): Datatype = datatype everywhere {
    case Variant(TypeVar(name), body) =>
      Variant(TypeVar(name + "T"), body)
  }

  /** @return all variants nested in this datatype declaration
    */
  def extractVariants(datatype: Datatype): Iterator[Variant] = datatype everywhereQ {
    case variant @ Variant(_, _) => variant
  }
}
