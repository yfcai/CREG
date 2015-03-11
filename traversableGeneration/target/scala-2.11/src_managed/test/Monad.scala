package creg
package lib

import language.higherKinds

object Monad {
  object State {
    type State[S, +A] = S => (A, S)

    private[this] // necessary to make inner type λ covariant
    type CurriedState[S] = {
      type λ[+A] = State[S, A]
    }

    implicit def stateMonad[S] = new MonadWithBind {
      type Map[+A] = CurriedState[S]#λ[A]
      def pure[A](x: A): Map[A] = s => (x, s)
      def bind[A, B](m: Map[A], f: A => Map[B]): Map[B] =
        s0 => m(s0) match { case (a, s1) => f(a)(s1) }
    }

    implicit class CurriedStateMonadView[A, S](x: CurriedState[S]#λ[A])
        extends Monad.View[CurriedState[S]#λ, A](x)

    def readState [S]: State[S, S]                 = s => (s, s)
    def writeState[S](s: S): State[S, Unit]        = _ => ((), s)
    def evalState [S, A](sm: State[S, A], s: S): A = sm(s)._1
  }

  // for-comprehension support for monads
  class View[M[+_]: Monad.ic, A](x: M[A]) {
    val monad = implicitly[Monad.ic[M]]
    import monad._
    def flatMap[B](f: A => M[B]): M[B] = bind(x, f)
    def map[B](f: A => B): M[B] = bind(x, pure[B] _ compose f)
  }

  // e. g.,  Monad.ic[Identity]   where   type Identity[+A] = A
  type ic[M[+_]] = Monad { type Map[+X] = M[X] }
}

trait Monad extends Applicative {
  type Map[+X]

  // inherited from applicative
  def pure[A](x: A): Map[A]
  def call[A, B](f: Map[A => B], x: Map[A]): Map[B]

  // idiosyncratic to monad
  def join[A](x: Map[Map[A]]): Map[A]
  def bind[A, B](m: Map[A], f: A => Map[B]): Map[B]
}

trait MonadWithBind extends Monad {
  def pure[A](x: A): Map[A]
  def bind[A, B](m: Map[A], f: A => Map[B]): Map[B]

  def call[A, B](f: Map[A => B], x: Map[A]): Map[B] =
    bind(f, (f: A => B) => bind(x, (x: A) => pure(f(x))))

  def join[A](x: Map[Map[A]]): Map[A] =
    bind(x, (y: Map[A]) => y)
}
