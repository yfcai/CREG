package creg
package lib

import language.higherKinds

trait Monad extends Applicative {
  type Map[+X]

  // inherited from applicative
  def pure[A](x: A): Map[A]
  def call[A, B](f: Map[A => B], x: Map[A]): Map[B]

  // idiosyncratic to monad
  def join[A](x: Map[Map[A]]): Map[A]
  def bind[A, B](m: Map[A], f: A => Map[B]): Map[B]
}

object Monad {
  class View[M[+_]: Monad.ic, A](x: M[A]) {
    val monad = implicitly[Monad.ic[M]]
    import monad._
    def flatMap[B](f: A => M[B]): M[B] = bind(x, f)
    def map[B](f: A => B): M[B] = bind(x, pure[B] _ compose f)
  }

  type ic[M[+_]] = Monad { type Map[+X] = M[X] }
}

trait MonadWithBind extends Monad {
  def pure[A](x: A): Map[A]
  def bind[A, B](m: Map[A], f: A => Map[B]): Map[B]

  def call[A, B](f: Map[A => B], x: Map[A]): Map[B] =
    bind(f, (f: A => B) => bind(x, (x: A) => pure(f(x))))

  def join[A](x: Map[Map[A]]): Map[A] =
    bind(x, (y: Map[A]) => y)
}
