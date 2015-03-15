package creg

import functors._
import language.higherKinds

trait Applicative extends Functor { self =>
  // Applicative functors are only defined on the entire Scala category.
  // It's hard to define applicative functors on subcategories because
  // a subcategory may not have exponentials (used in `call`).
  type Map[+X]
  def pure[A](x: A): Map[A]
  def call[A, B](f: Map[A => B], x: Map[A]): Map[B]

  def fmap[A, B](f: A => B): Map[A] => Map[B] = x => call(pure(f), x)

  def roll[F[+_]](x: Map[F[Fix[F]]]): Map[Fix[F]] =
    call(
      pure[F[Fix[F]] => Fix[F]](y => Roll(y)),
      x)

  def compose(that: Applicative):
      Applicative { type Map[+X] = self.Map[that.Map[X]] } =
    new Applicative {
      type Map[+X] = self.Map[that.Map[X]]

      def pure[A](x: A): Map[A] = self.pure(that.pure(x))

      def call[A, B](f: Map[A => B], x: Map[A]): Map[B] =
        self.call(self.call(
          self pure {
            (f: that.Map[A => B]) => (x: that.Map[A]) => that.call(f, x)
          },
          f),
          x)
    }
}

// specific applicative functors
// beware SI-2089
object Applicative {
  type Of[F[+_]] = Applicative { type Map[+X] = F[X] }

  // identity applicative functor
  type Identity[+X] = X

  implicit object Identity extends Applicative {
    type Map[+X] = Identity[X]
    def pure[A](x: A): A = x
    def call[A, B](f: A => B, x: A): B = f(x)
  }

  // constant applicative functor
  type Const[A] = { type λ[+X] = A }

  def Const[A](default: A, combine: (A, A) => A): Applicative { type Map[+X] = A } =
    new Applicative {
      type Map[+X] = A
      def pure[X](x: X): A = default
      def call[X, Y](f: A, x: A): A = combine(f, x)
    }

  def FreeMonoid[A]: Applicative { type Map[+X] = List[A] } =
    Const[List[A]](Nil, _ ++ _)

  def Maybe[A]: Applicative { type Map[+X] = Option[X] } =
    new Applicative {
      type Map[+A] = Option[A]
      def pure[A](x: A): Option[A] = Some(x)
      def call[A, B](f: Option[A => B], x: Option[A]): Option[B] = (f, x) match {
        case (Some(f), Some(x)) => Some(f(x))
        case _ => None
      }
    }
}
