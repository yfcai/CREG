package creg
package util

import java.util.regex.{Pattern, Matcher}
import compiler.DatatypeRepresentation.Name

private[creg]
trait TupleIndex {
  def tupleIndex(name: Name): Option[Int] = {
    val pattern = Pattern compile """_(\d+)"""
    val matcher = pattern matcher name
    if (matcher.matches)
      Some(matcher.group(1).toInt - 1)
    else
      None
  }
}
