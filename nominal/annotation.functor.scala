/** Unsweetened functor DSL, where fixed points have to be explicit
  * and there is no separate syntax distinguishing variants from
  * records.
  *
  * Upside   = easy to parse
  *            straightforward denotational semantics
  *            (see nominal.compiler.Denotation)
  * 
  * Downside = declaration of functors does NOT mimic use:
  *            variants are declared using braces { } but
  *            they are used in the body of functors just
  *            like records with parentheses ( )
  */

package nominal
package annotation

import scala.reflect.macros.blackbox.Context
import compiler._

object functor extends Parsers with Denotation with util.AbortWithError {
  def impl(c: Context)(annottees: c.Tree*): c.Tree = {
    import c.universe._
    annottees match {
      case Seq(DefDef(mods, name, params, args, returnType, body)) =>
        val input = parseOrAbort(c)(DataDeclP, annottees.head)
        val instance = evalFunctor(c)(input.injectTuples)
        val name = TermName(input.name)
        ValDef(mods, name, returnType, instance)
    }
  }
}
