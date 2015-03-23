package creg
package util

import scala.reflect.runtime.universe
import scala.tools.reflect.ToolBox

private[creg]
trait EvalScala {
  def evalScala(scopeObject: Any, scalaCode: String): Any = {
    val toolbox = getToolBox(scopeObject)
    toolbox.eval(toolbox.parse(scalaCode))
  }

  def getToolBox(scopeObject: Any) =
    universe.runtimeMirror(scopeObject.getClass.getClassLoader).mkToolBox()
}
