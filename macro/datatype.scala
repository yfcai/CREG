import scala.language.experimental.macros
import scala.reflect.macros.blackbox.Context
import scala.annotation.StaticAnnotation

import DatatypeRepresentation._

object datatype extends Parser with DeclarationGenerator {
  def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._

    val datatypeDecl: Tree = annottees.head.tree
    val datatype: Variant = parse(c)(datatypeDecl)
    val declaration: Tree = generateDeclaration(c)(datatype)

    c.Expr[Any](declaration) // TODO: generate functor instances too
  }
}

class datatype extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro datatype.impl
}
