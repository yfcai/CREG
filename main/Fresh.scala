// how to thread a monad correctly
// (global name refreshment)

import nominal.lib._
import nominal.functors._

object Fresh {
  import Compos2.{stateMonad, StateMonadView, getNameStream}

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

    def pure[A](x: A): Map[A] =
      subst => names => (x, names)

    def bind[A, B](m: Map[A], f: A => Map[B]): Map[B] =
      subst => names => {
        val (x, newNames) = m(subst)(names)
        f(x)(subst)(newNames)
      }
  }

  def ask: FreshM[Subst] = env => stateMonad pure env
  def local[A](f: (Subst => Subst))(m: FreshM[A]): FreshM[A] =
    m compose f

  def readState: FreshM[Names] = env => Compos2.readState
  def writeState(names: Names): FreshM[Unit] = env => Compos2 writeState names

  implicit class FreshMonadView[T](x: FreshM.Map[T])
      extends Monad.View[FreshM, T](x)

  def refresh: Term => FreshM[Term] =
    cata[FreshM[Term]](termF) {
      case Var(x) => for {
        env <- ask
      } yield coerce {
        Var(env.withDefault(identity[String])(x))
      }

      case Abs(x, s) => for {
        ys <- readState
        _  <- writeState(ys.tail)
        y  =  ys.head
        t  <- local(_ + (x -> y))(s)
      }
      yield coerce { Abs(y, t) }

      case s =>
        for { t <- termF(s).traverse(FreshM)(x => x) } yield coerce(t)
    }

  val omega: Term = coerce {
    App(
      Abs("x", App(Var("x"), Var("x"))),
      Abs("x", App(Var("x"), Var("x"))))
  }

  val omg: Term = refresh(omega)(Map.empty)(getNameStream)._1

  def run() {
    println(omg)
  }
}
