import scala.reflect.macros.blackbox.Context

trait Parser extends DatatypeRepresentation {
    /** @param datatypeDecl
      */
  def parse(c: Context)(datatypeDecl: c.Tree): Variant = {
    import c.universe._
    datatypeDecl match {
      case q"trait $name [..$typeParams] { ..$body }" =>
        import reflect.runtime.universe.typeOf

        // TODO: parse the expression

        // dummy output to test generation
        Variant("Empty", Many.empty)

      case _ =>
        sys error "incorrect usage"
    }
  }

}
