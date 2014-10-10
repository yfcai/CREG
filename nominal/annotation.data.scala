package nominal
package annotation

import scala.language.experimental.macros
import scala.reflect.macros.blackbox.Context
import scala.annotation.StaticAnnotation

import compiler._
import DatatypeRepresentation._

object data
extends Parsers
   with DeclarationGenerator
   with SynonymGenerator
{
  def expandData(c: Context)(annottees: c.Tree*): c.Tree = {
    import c.universe._

    val Seq(input)   = annottees
    val datadecl     = parseOrAbort(c)(DataDeclP, input)
    val imports      = scalaLanguageFeatureImports(c)
    val declarations = generateDeclarations(c)(datadecl.body, Many.empty)
    val synonyms     = Many.empty // TODO: still to do
    val result       = imports ++ declarations ++ synonyms

    q"..$result"
  }

  /** @return (input-syntax-tree, companion-object)
    *
    * annoying operation; duplicates parser...
    */
  def extractInput(c: Context)(annottees: Seq[c.Expr[Any]]): (c.Tree, Option[c.Tree]) = {
    import c.universe._
    def giveUp: Nothing =
      abortWithError(c)(annottees.head.tree.pos,
        "Bad use of @datatype. Usage example:\n\n  @datatype trait List[+A] {\n" +
          "    Nil\n    Cons(head = A, tail = List)\n  }\n.")

    annottees.size match {
      case 0 => giveUp
      case n if n > 2 => giveUp

      case 1 =>
        val input = annottees.head.tree
        getNameOfTrait(c)(input).fold[(c.Tree, Option[c.Tree])](giveUp)(name => (input, None))

      case 2 =>
        val (fst, snd) = (annottees.head.tree, annottees.last.tree)
        (getNameOfTrait(c)(fst), getNameOfTrait(c)(snd)) match {
          case (Some(_), None) => (fst, Some(snd))
          case (None, Some(_)) => (snd, Some(fst))
          case _ => giveUp
        }
    }
  }

  def injectIntoObject(c: Context)(obj: c.Tree, newDecls: Seq[c.Tree]): c.Tree = {
    import c.universe._
    obj match {
      case q"..$attributes object $objectName extends ..$superClasses { ..$existingDecls }" =>
        // hack to put attributes back in the object
        q"object $objectName extends ..$superClasses { ..${newDecls ++ existingDecls} }" match {
          case ModuleDef(_, a, b) => ModuleDef(attributes, a, b)
        }

      case _ =>
        abortWithError(c)(obj.pos, "malformed companion object")
    }
  }
}
