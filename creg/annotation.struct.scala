package creg
package annotation

import scala.language.experimental.macros
import scala.reflect.macros.blackbox.Context
import scala.annotation.StaticAnnotation

import compiler._
import DatatypeRepresentation._

object struct
extends Parsers
   with DeclarationGenerator
   with SynonymGenerator
{
  def impl(c: Context)(annottees: c.Tree*): c.Tree = {
    import c.universe._

    val Seq(input)   = annottees
    val struct       = parseOrAbort(c)(StructVariantP, input)
    val supers       = parseOrAbort(c)(supersP(c), input)

    val imports      = scalaLanguageFeatureImports(c)
    val declarations = generateDeclarations(c)(struct, supers)

    val result       = imports ++ declarations

    q"..$result"
  }
}
