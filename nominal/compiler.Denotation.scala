/** The denotational semantics of functor representations
  *
  *
  * decl := params => body
  * 
  * params := typevar
  *         | (typevar, typevar, ..., typevar)
  * 
  * body := typevar
  *       | Fix(typevar => body)
  *       | scala-functor(body, body, ..., body)
  *       | scala-constant
  *
  *
  * ⟦ params => body ⟧ = ⟦ body ⟧ params
  * 
  * ⟦ typevar ⟧ params = projection-functor(i, n)
  *   where
  *     i = lookup typevar params
  *     n = length params
  * 
  * ⟦ Fix(x => body) ⟧ params = λ args. μ (⟦ body ⟧ (params :+ x) args)
  *   where
  *     assert(length args == length params)
  * 
  * ⟦ scala-functor(bodies: _*) ⟧ params =
  *   λ args. scala-functor(bodies map (body => ⟦ body ⟧ params args))
  *     where
  *       assert(length args == length params)
  * 
  * ⟦ scala-constant ⟧ params = n-nary-constant-functor n scala-constant
  *   where
  *     n = length params
  */

package nominal
package compiler

import scala.reflect.macros.blackbox.Context
import Functor._

trait Denotation extends KIRV {
  private[this] type Env = Many[Name]

  def evalFunctor(c: Context)(functor: Functor.Decl): c.Tree =
    evalFunctorBody(c)(functor.body, functor.params).get

  def evalFunctorBody(c: Context)(body: Body, env: Env): KIRV[c.Tree] = body match {
    case TypeVar(x) =>
      val i = env indexOf x
      if (i < 0) // case constant
        constK(c, env.length)(x)
      else // case variable
        projectK(c, i, env.length)

    case FixedPoint(x, body) =>
      fixK(c, env.length)(evalFunctorBody(c)(body, x +: env))

    case Application(functor, args) =>
      compositeK(c, env.length)(
        c parse functor,
        args map (x => evalFunctorBody(c)(x, env)))
  }
}
