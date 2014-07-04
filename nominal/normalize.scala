package nominal

import scala.reflect.macros.blackbox.Context
import scala.language.experimental.macros
import scala.annotation.StaticAnnotation

object normalize {
  def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._
    val q"type $normalized [..$params] = $rhs" = annottees.head.tree

    val result: c.Tree =
      if (params.isEmpty) {
        // rhs is a concrete type
        val tpe = c.typecheck(q"??? : $rhs").tpe
        val name = TermName(normalized.toString)
        q"""object $name { override def toString: String = ${tpe.dealias.toString} }"""
      }
      else {
        // rhs may mention abstract types
        val member = TypeName("__TYPE__")
        val wrapper = c.typecheck(q"new { type $member[..$params] = $rhs }").tpe
        val tpe = wrapper.decl(member).asType.toType.dealias
        // up to (lack of) name capturing, tpe is the thing we want.

        val name = TermName(normalized.toString)
        val Name = TypeName(normalized.toString.capitalize)
        q"""
          object $name {
            override def toString: String = ${tpe.toString}

            type InnerType [..$params] = $tpe
            // PROBLEMATIC: OLD TYPE REF IN tpe DOES NOT CARRY OVER HERE!
          }
        """
      }

    c.Expr[Any](result)
  }
}

class normalize extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro normalize.impl
}
