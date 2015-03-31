package creg
package util

import scala.reflect.macros.blackbox.Context

private[creg]
trait AbortWithError {
  def abortWithError(c: Context)(pos: c.Position, message: String): Nothing = {
    c.error(pos, message)
    sys error s"error aborted macro expansion"
  }
}
