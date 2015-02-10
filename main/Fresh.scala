// how to thread a monad correctly
// (global name refreshment)

import nominal.lib._
import nominal.functors._

object Fresh {
  import Compos2.{stateMonad, StateMonadView,
                  readState, writeState, evalState,
                  getNameStream}

  import Banana.{cataWith => cata}

  private[this] // necessary to make inner type λ covariant
  type State[S] = {
    type λ[+A] = S => (A, S)
  }

  @data def Term = Fix(T => TermT {
    Var(x = String)
    Abs(x = String, t = T)
    App(f = T, y = T)
  })

  @functor def termF[T] = TermT {
    Var(x = String)
    Abs(x = String, t = T)
    App(f = T, y = T)
  }

  type Names = Stream[String]

  type Subst = Map[String, String]

  type FreshM[+T] = Subst => State[Names]#λ[T]

  implicit object FreshM extends MonadWithBind {
    type Map[+T] = FreshM[T]
    def pure[A](x: A): Map[A] = _ => stateMonad pure x
    def bind[A, B](m: Map[A], f: A => Map[B]): Map[B] =
      env => for { x <- m(env) ; y <- f(x)(env) } yield y
  }


  def refresh: Term => FreshM[Term] =
    cata[FreshM[Term]](termF) {
      case Var(x) => env => stateMonad.pure{
        coerce(Var(env.applyOrElse(x, identity[String])))
      }

      case Abs(x, body) => env => for {
        ys <- readState[Names]
        _  <- writeState(ys.tail)
        y = ys.head
        newBody <- body(env.updated(x, y))
      }
      yield coerce { Abs(y, newBody) }

      case App(f, u) => env => for {
        g <- f(env)
        v <- u(env)
      }
      yield coerce { App(g, v) }
    }

  def run() {
    val omega: Term = coerce {
      App(
        Abs("x", App(Var("x"), Var("x"))),
        Abs("x", App(Var("x"), Var("x"))))
    }

    val omg: Term = evalState(refresh(omega)(Map.empty), getNameStream)

    println(omg)
  }
}
