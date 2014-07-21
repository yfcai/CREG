package nominal
package lib

import language.higherKinds

object Traversable {
  // fixed-point of a functor is only guaranteed to exist in the entire scala category
  // in other words, it's only permissible to take the fixed point of a traversable endofunctor
  type Endofunctor[F[+_]] = Traversable {
    type Cat = Any
    type Map[+X] = F[X]
  }
}

trait Traversable {
  // traversable functors can be defined on a subcategory
  type Cat
  type Map[+A <: Cat]

  // McBride & Paterson's traverse
  def traverse[F[+_]: Applicative.Endofunctor, A <: Cat, B <: Cat](f: A => F[B], mA: Map[A]): F[Map[B]]

  // reinterpret `x` in the light of `Map` being a traversable functor
  def apply[A <: Cat](mA: Map[A]): View[A] = new View(mA)

  class View[A <: Cat](mA: Map[A]) {
    def traverse[F[+_]: Applicative.Endofunctor, B <: Cat](f: A => F[B]): F[Map[B]] = Traversable.this.traverse(f, mA)

    // fmap
    def map[B <: Cat](f: A => B): Map[B] = this.traverse[Applicative.Identity, B](f)

    // McBride & Paterson's reduce
    def reduce(monoidId: A, monoidOp: (A, A) => A): A =
      this.traverse[Applicative.Const[A]#λ, A](identity)(
        new Applicative {
          type Map[+X] = A
          def pure[X](x: X): A = monoidId
          def call[X, Y](f: A, x: A): A = monoidOp(f, x)
        })
  }
}

// Traversable2, Traversable3, Traversable4, ..., Traversable22
trait Traversable2 {
  type Cat1
  type Cat2
  type Map[+A <: Cat1, +B <: Cat2]

  def traverse[F[+_]: Applicative.Endofunctor, A <: Cat1, B <: Cat2, C <: Cat1, D <: Cat2]
              (f: A => F[C], g: B => F[D], mAB: Map[A, B]): F[Map[C, D]]

  def apply[A <: Cat1, B <: Cat2](mAB: Map[A, B]): View[A, B] = new View(mAB)

  class View[A <: Cat1, B <: Cat2](mAB: Map[A, B]) {
    def traverse[F[+_]: Applicative.Endofunctor, C <: Cat1, D <: Cat2]
                (f: A => F[C], g: B => F[D]): F[Map[C, D]] = Traversable2.this.traverse(f, g, mAB)

    def map[C <: Cat1, D <: Cat2](f: A => C, g: B => D): Map[C, D] = this.traverse[Applicative.Identity, C, D](f, g)
  }
}
