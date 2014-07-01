import scala.language.experimental.macros
import scala.reflect.macros.blackbox.Context
import scala.annotation.StaticAnnotation

import DatatypeRepresentation._

object datatype extends Parser with DeclarationGenerator {
  def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._

    // parser parses DSL
    // preprocessor appends T & add Fix
    // declaration generator generates template classes
    // synonym generator generates synonyms

    c.Expr(q"") // TODO: generate synonyms & functor instances too
  }
}

class datatype extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro datatype.impl
}
