package creg
package experiment

import scala.reflect.macros.blackbox.Context
import scala.language.experimental.macros
import scala.annotation.StaticAnnotation

class defData extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro defData.impl
}

object defData {
  def impl(c: Context)(annottees: c.Tree*): c.Tree = {
    import c.universe._
    annottees match {
      case Seq(ast @ q"def $name[..$typeParams] = $body") =>
        val code = "\n" + showCode(ast)
        q"val $name: String = $code"
    }
  }
}
