package creg
package util

import scala.reflect.macros.blackbox.Context
import scala.tools.reflect.ToolBoxError

private[creg]
trait ExpectCompilerError {
  def expectCompilerError(c: Context)(tree: c.Tree): c.Expr[String] = {
    import c.universe._
    try {
      c eval c.Expr(c.untypecheck(tree.duplicate))
    }
    catch {
      case e: ToolBoxError =>
        return c.Expr(q"${e.getMessage}")

      case e: Throwable =>
        throw new java.lang.AssertionError(s"expect compilation error, got " + e)
    }
    throw new java.lang.AssertionError(s"expect compilation error, got nothing")
  }
}
