/** An experiment in encoding equirecursion in Scala's type system
  * Scalac loops on it.
  */

import language.{higherKinds, existentials}
import nominal.functors._
import nominal.lib._

object Equirecursion {
  // recursive datatype
  @data def TermF[term] = TermT {
    Var(name = String)
    Abs(param = String, body = term)
    App(operator = term, operand = term)
  }

  // sends scalac into infinite loop
  type Term = term with TermF[term] forSome { type term <: TermF[term] }

  sealed trait CanonTerm extends TermF[CanonTerm]

  /** a pointless no-op traversal */
  def roll(t0: TermF[Term]): Term = {
    def loop(t: TermF[Term]): CanonTerm = t match {
      case Var(x) => new Var(x) with CanonTerm
      case Abs(x, b) => new Abs(x, loop(b)) with CanonTerm
      case App(f, t) => new App(loop(f), loop(t)) with CanonTerm
    }
    loop(t0)
  }

  object avoidF extends Traversable2 {
    type Cat0 = Any
    type Cat1 = Abs[Any, Any]

    type Map[+name, +abs <: Cat1] =
      TermT[Var[name], abs, App[term, term]] forSome {
        type term <: TermT[Var[name], abs, App[term, term]]
      }

    def traverse[A, B <: Cat1, C, D <: Cat1](G: Applicative)(
      f: A => G.Map[C],
      g: B => G.Map[D]
    ): Map[A, B] => G.Map[Map[C, D]] = {
      import G.{pure, call}
      _ match {
        case Var(x) =>
          call(
            pure[C => Var[C]](x => Var(x)),
            f(x))

        case abs @ Abs(x, b) =>
          // unavoidable cast, just like before
          g(abs).asInstanceOf[G.Map[Map[C, D]]]

        case App(h, y) =>
          call(call(
            pure[Map[C, D] => Map[C, D] => App[Map[C, D], Map[C, D]]](
              x => y => App(x, y)),
            traverse(G)(f, g)(h)),
            traverse(G)(f, g)(y))
      }
    }
  }

  val id: Term = roll(Abs("x", Var("x")))

  val idy: Term = roll(App(id, Var("y")))

  val app: Term = roll(Abs("f", roll(Abs("x", App(Var("f"), Var("x"))))))

  val f_xy: Term = roll(App(Var("f"), App(Var("x"), Var("y"))))

  val fx_y: Term = roll(App(App(Var("f"), Var("x")), Var("y")))

  def freshName(default: String, forbidden: Set[String]): String = {
    var i = 0
    var x = default
    while(forbidden(default)) {
      i += 1
      x = s"$default$i"
    }
    x
  }

  def avoidCapture(t: Term, subst: Map[String, String]): Term =
    avoidF(t).map[String, Abs[String, Term]]({
      subst withDefault identity
    }, {
      case Abs(x, body) =>
        val y = freshName(x, subst.keySet)
        // scalac loops on this line.
        // Abs(y, avoidCapture(body, subst updated (x, y)))
        ???
    })

  val idView = avoidF(id)
}
