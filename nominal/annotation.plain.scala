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
package plain

import scala.reflect.macros.blackbox.Context
import compiler._

object functor extends ParserOfFunctorRep with Denotation with util.AbortWithError {
  def impl(c: Context)(annottees: c.Tree*): c.Tree = {
    import c.universe._
    annottees match {
      case Seq(ValDef(mods, name, emptyTree @ TypeTree(), tree)) =>
        val input = parseOrAbort(c)(DeclP, tree)
        val instance = evalFunctor(c)(input)
        ValDef(mods, name, emptyTree, instance)

      case _ =>
        abortWithError(c)(annottees.head.pos,
          s"expect: val functorName = typeParams => resultDataType, got: $annottees")
    }
  }
}
