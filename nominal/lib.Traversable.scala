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

  def compose[F[+_], G[+_]](f: Endofunctor[F], g: Endofunctor[G]):
      Endofunctor[({ type λ[+X] = F[G[X]] })#λ] =
    new Traversable {
      type Cat = Any
      type Map[+X] = F[G[X]]
      def traverse[H[+_]: Applicative.Endofunctor, A, B](h: A => H[B], m: F[G[A]]): H[F[G[B]]] =
        f.traverse[H, G[A], G[B]](ga => g.traverse(h, ga), m)
    }
}

trait Traversable { thisFunctor =>
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

  // if you want to have named parameters, e. g.,
  //
  //   avoidF(term).map(_var = rename, abs = avoidCapture)
  //
  // then the View trait gotta be generated. it looks
  // more trouble due to possible name clashes than
  // it's worth, though.
  class View[A <: Cat1, B <: Cat2](mAB: Map[A, B]) {
    def traverse[F[+_]: Applicative.Endofunctor, C <: Cat1, D <: Cat2]
                (f: A => F[C], g: B => F[D]): F[Map[C, D]] = Traversable2.this.traverse(f, g, mAB)

    def map[C <: Cat1, D <: Cat2](f: A => C, g: B => D): Map[C, D] = this.traverse[Applicative.Identity, C, D](f, g)
  }
}

trait Traversable3 {
  type Cat1
  type Cat2
  type Cat3
  type Map[+A <: Cat1, +B <: Cat2, +C <: Cat3]

  def traverse[F[+_]: Applicative.Endofunctor,
    A <: Cat1, B <: Cat2, W <: Cat3, C <: Cat1, D <: Cat2, Y <: Cat3]
              (f: A => F[C], g: B => F[D], h: W => F[Y],
                mAB: Map[A, B, W]): F[Map[C, D, Y]]

  def apply[A <: Cat1, B <: Cat2, W <: Cat3](mAB: Map[A, B, W]): View[A, B, W] = new View(mAB)

  class View[A <: Cat1, B <: Cat2, W <: Cat3](mAB: Map[A, B, W]) {
    def traverse[F[+_]: Applicative.Endofunctor, C <: Cat1, D <: Cat2, Y <: Cat3]
                (f: A => F[C], g: B => F[D], h: W => F[Y]): F[Map[C, D, Y]] =
      Traversable3.this.traverse(f, g, h, mAB)

    def map[C <: Cat1, D <: Cat2, Y <: Cat3](f: A => C, g: B => D, h: W => Y): Map[C, D, Y] =
      this.traverse[Applicative.Identity, C, D, Y](f, g, h)
  }
}

trait Traversable4 {
  type Cat1
  type Cat2
  type Cat3
  type Cat4
  type Map[+A <: Cat1, +B <: Cat2, +C <: Cat3, +D <: Cat4]

  def traverse[F[+_]: Applicative.Endofunctor,
    A <: Cat1, B <: Cat2, W <: Cat3, X <: Cat4, C <: Cat1, D <: Cat2, Y <: Cat3, Z <: Cat4]
              (f: A => F[C], g: B => F[D], h: W => F[Y], k: X => F[Z],
                mAB: Map[A, B, W, X]): F[Map[C, D, Y, Z]]

  def apply[A <: Cat1, B <: Cat2, W <: Cat3, X <: Cat4](mAB: Map[A, B, W, X]): View[A, B, W, X] = new View(mAB)

  class View[A <: Cat1, B <: Cat2, W <: Cat3, X <: Cat4](mAB: Map[A, B, W, X]) {
    def traverse[F[+_]: Applicative.Endofunctor, C <: Cat1, D <: Cat2, Y <: Cat3, Z <: Cat4]
                (f: A => F[C], g: B => F[D], h: W => F[Y], k: X => F[Z]): F[Map[C, D, Y, Z]] =
      Traversable4.this.traverse(f, g, h, k, mAB)

    def map[C <: Cat1, D <: Cat2, Y <: Cat3, Z <: Cat4](f: A => C, g: B => D, h: W => Y, k: X => Z): Map[C, D, Y, Z] =
      this.traverse[Applicative.Identity, C, D, Y, Z](f, g, h, k)
  }
}
