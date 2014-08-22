package nominal
package annotation

import scala.language.experimental.macros
import scala.reflect.macros.blackbox.Context
import scala.annotation.StaticAnnotation

import compiler._

/** at class level, have to say:
  * val someFunctor = { @functor val _ = TypeParams => ResultDatatype }
  * // BUG: this does not work; block expr evaluates to unit.
  *
  * at block level, can simply say:
  * @functor val someFunctor = TypeParams => ResultDatatype
  */

object functor extends Parser with TraversableGenerator with util.AbortWithError {
  private[this] def classLevelSignal(c: Context)(name: c.TermName): Boolean =
    name.toString == c.universe.termNames.WILDCARD.toString

  def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._
    annottees match {
      case Seq(Expr(ValDef(mods, name, emptyType @ TypeTree(), tree))) =>
        val input = parseOrAbort(c)(FunctorP, tree)
        val rep = fleshOut(c)(input)
        val instance = generateTraversable(c)(rep)

        if (classLevelSignal(c)(name))
          c.Expr(instance) // BUG: see above: { @functor val _ = ... }
        else
          c.Expr(ValDef(mods, name, emptyType, instance))

      case _ =>
        abortWithError(c)(annottees.head.tree.pos,
          s"expect: val functorName = typeParams => resultDataType, got: $annottees")
    }
  }
}

class functor extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro functor.impl
}
