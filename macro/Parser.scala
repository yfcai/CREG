import scala.reflect.macros.blackbox.Context

import DatatypeRepresentation._

trait Parser {
    /** @param datatypeDecl
      */
  def parse(c: Context)(datatypeDecl: c.Tree): DataConstructor = {
    import c.universe._
    datatypeDecl match {
      case q"trait $name [..$typeParams] { ..$body }" =>
        import reflect.runtime.universe.typeOf

        // TODO: parse the expression

        // dummy output to test generation
        DataConstructor(Many.empty, Variant("Empty", Many.empty))

      case _ =>
        sys error "incorrect usage"
    }
  }

}
