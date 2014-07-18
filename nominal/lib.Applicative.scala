package nominal
package lib

import language.higherKinds

trait Applicative {
  // Applicative functors are only defined on the entire Scala category.
  // It's hard to define applicative functors on subcategories because
  // a subcategory may not have exponentials (used in `call`).
  type Map[X]
  def pure[A](x: A): Map[A]
  def call[A, B](f: Map[A => B], x: Map[A]): Map[B]
}

// specific applicative functors
// beware SI-2089
object Applicative {
  type Endofunctor[F[_]] = Applicative { type Map[X] = F[X] }

  // identity applicative functor
  type Identity[+X] = X

  implicit object Identity extends Applicative {
    type Map[X] = Identity[X]
    def pure[A](x: A): A = x
    def call[A, B](f: A => B, x: A): B = f(x)
  }

  // constant applicative functor
  type Const[A] = { type λ[+X] = A }

  def Const[A](default: A, combine: (A, A) => A): Applicative { type Map[+X] = A } =
    new Applicative {
      type Map[X] = A
      def pure[X](x: X): A = default
      def call[X, Y](f: A, x: A): A = combine(f, x)
    }
}