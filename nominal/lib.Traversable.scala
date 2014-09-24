package nominal
package lib

import language.higherKinds

object Traversable {
  // fixed-point of a functor is only guaranteed to exist in the entire scala category
  // in other words, it's only permissible to take the fixed point of a traversable endofunctor
  type Endofunctor[F[+_]] = Traversable {
    type Map[+X] = F[X]
  }
}

trait Traversable { thisFunctor =>
  type Map[+A]

  // McBride & Paterson's traverse
  def traverse[A, B](G: Applicative)(f: A => G.Map[B]): this.Map[A] => G.Map[this.Map[B]]

  // reinterpret `x` in the light of `Map` being a traversable functor
  def apply[A](mA: Map[A]): View[A] = new View(mA)

  class View[A](mA: Map[A]) {
    def traverse[B](G: Applicative)(f: A => G.Map[B]): G.Map[Map[B]] =
        Traversable.this.traverse(G)(f)(mA)

    // fmap
    def map[B](f: A => B): Map[B] =
      this.traverse(Applicative.Identity)(f)

    // McBride & Paterson's reduce
    def reduce(monoidId: A, monoidOp: (A, A) => A): A =
      mapReduce(identity)(monoidId, monoidOp)

    def mapReduce[B](f: A => B)(monoidId: B, monoidOp: (B, B) => B): B =
      this.traverse(Applicative.Const(monoidId, monoidOp))(f)
  }

  // compose with another functor
  def compose(that: Traversable) =
    new Traversable {
      type Map[+A] = thisFunctor.Map[that.Map[A]]
      def traverse[A, B](G: Applicative)(f: A => G.Map[B]): this.Map[A] => G.Map[this.Map[B]] =
        thisFunctor.traverse(G)(that.traverse(G)(f))
    }
}

// Traversable2, Traversable3, Traversable4, ..., Traversable22
trait Traversable2 {
  type Map[+A, +B]

  def traverse[A, B, C, D]
              (G: Applicative)
              (f: A => G.Map[C], g: B => G.Map[D]):
      Map[A, B] => G.Map[Map[C, D]]

  def apply[A, B](mAB: Map[A, B]): View[A, B] = new View(mAB)

  // if you want to have named parameters, e. g.,
  //
  //   avoidF(term).map(_var = rename, abs = avoidCapture)
  //
  // then the View trait gotta be generated. it looks
  // more trouble due to possible name clashes than
  // it's worth, though.
  class View[A, B](mAB: Map[A, B]) {
    def traverse[C, D]
                (G: Applicative)
                (f: A => G.Map[C], g: B => G.Map[D]): G.Map[Map[C, D]] =
      Traversable2.this.traverse(G)(f, g)(mAB)

    def map[C, D](f: A => C, g: B => D): Map[C, D] = this.traverse(Applicative.Identity)(f, g)
  }
}

trait Traversable3 {
  type Map[+A, +B, +C]

  def traverse[A, B, W, C, D, Y]
              (G: Applicative)
              (f: A => G.Map[C], g: B => G.Map[D], h: W => G.Map[Y]):
      Map[A, B, W] => G.Map[Map[C, D, Y]]

  def apply[A, B, W](mAB: Map[A, B, W]): View[A, B, W] = new View(mAB)

  class View[A, B, W](mAB: Map[A, B, W]) {
    def traverse[C, D, Y]
      (G: Applicative)
      (f: A => G.Map[C], g: B => G.Map[D], h: W => G.Map[Y]): G.Map[Map[C, D, Y]] =
      Traversable3.this.traverse(G)(f, g, h)(mAB)

    def map[C, D, Y](f: A => C, g: B => D, h: W => Y): Map[C, D, Y] =
      this.traverse(Applicative.Identity)(f, g, h)
  }
}

trait Traversable4 {
  type Map[+A, +B, +C, +D]

  def traverse[A, B, W, X, C, D, Y, Z]
              (G: Applicative)
              (f: A => G.Map[C], g: B => G.Map[D], h: W => G.Map[Y], k: X => G.Map[Z]):
      Map[A, B, W, X] => G.Map[Map[C, D, Y, Z]]

  def apply[A, B, W, X](mAB: Map[A, B, W, X]): View[A, B, W, X] = new View(mAB)

  class View[A, B, W, X](mAB: Map[A, B, W, X]) {

    def traverse[C, D, Y, Z]
      (G: Applicative)
      (f: A => G.Map[C], g: B => G.Map[D], h: W => G.Map[Y], k: X => G.Map[Z]):
        G.Map[Map[C, D, Y, Z]] =
      Traversable4.this.traverse(G)(f, g, h, k)(mAB)

    def map[C, D, Y, Z](f: A => C, g: B => D, h: W => Y, k: X => Z): Map[C, D, Y, Z] =
      this.traverse(Applicative.Identity)(f, g, h, k)
  }
}
