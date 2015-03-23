package creg
package annotation

import scala.language.experimental.macros
import scala.reflect.macros.blackbox.Context
import scala.annotation.StaticAnnotation

import compiler._
import DatatypeRepresentation._

private[creg]
object synonym
extends Parsers
   with DeclarationGenerator
   with SynonymGenerator
{
  def impl(c: Context)(annottees: c.Tree*): c.Tree = {
    import c.universe._

    val Seq(input) = annottees
    val datadecl  = parseOrAbort(c)(DataDeclP, input)
    val synonyms  = generateSynonyms(c)(datadecl)

    q"..$synonyms"
  }
}
