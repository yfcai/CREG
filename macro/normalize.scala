import scala.reflect.macros.blackbox.Context
import scala.language.experimental.macros
import scala.annotation.StaticAnnotation

object normalize {
  def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._
    val q"type $normalized = $synonym" = annottees.head.tree
    val tpe = c.typecheck(q"??? : $synonym").tpe
    val name = TermName(normalized.toString)
    val result = q"""object $name { override def toString: String = ${tpe.dealias.toString} }"""
    c.Expr[Any](result)
  }
}

class normalize extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro normalize.impl
}
