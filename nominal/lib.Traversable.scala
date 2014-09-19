package nominal
package lib

import language.higherKinds

object Traversable {
  // fixed-point of a functor is only guaranteed to exist in the entire scala category
  // in other words, it's only permissible to take the fixed point of a traversable endofunctor
  type Endofunctor = Traversable {
    type Cat = Any
    type Map[+X]
  }

  type EndofunctorOf[F[+_]] = Endofunctor {
    type Map[+X] = F[X]
  }
}

trait Traversable { thisFunctor =>
  // traversable functors can be defined on a subcategory
  type Cat
  type Map[+A <: Cat]

  // McBride & Paterson's traverse
  def traverse[A <: Cat, B <: Cat](G: Applicative)(f: A => G.Map[B], mA: this.Map[A]): G.Map[this.Map[B]]

  // reinterpret `x` in the light of `Map` being a traversable functor
  def apply[A <: Cat](mA: Map[A]): View[A] = new View(mA)

  class View[A <: Cat](mA: Map[A]) {
    trait Traversal[G[+_]] { def apply[B <: Cat](f: A => G[B]): G[Map[B]] }

    def traverse(G: Applicative): Traversal[G.Map] = new Traversal[G.Map] {
      def apply[B <: Cat](f: A => G.Map[B]): G.Map[Map[B]] =
        Traversable.this.traverse(G)(f, mA)
    }

    // fmap
    def map[B <: Cat](f: A => B): Map[B] =
      Traversable.this.traverse(Applicative.Identity)(f, mA)

    // McBride & Paterson's reduce
    def reduce(monoidId: A, monoidOp: (A, A) => A): A =
      Traversable.this.traverse(Applicative.Const(monoidId, monoidOp))(identity[A], mA)

    def mapReduce[B <: Cat](f: A => B)(monoidID: B, monoidOp: (B, B) => B): B =
      thisFunctor(map(f)) reduce (monoidID, monoidOp)
  }

  // compose with another functor
  def compose(that: Traversable { type Map[+X] <: thisFunctor.Cat }) =
    new Traversable {
      type Cat = that.Cat
      type Map[+A <: Cat] = thisFunctor.Map[that.Map[A]]
      def traverse[A <: Cat, B <: Cat](G: Applicative)(f: A => G.Map[B], mA: this.Map[A]): G.Map[this.Map[B]] =
        thisFunctor.traverse[that.Map[A], that.Map[B]](G)(x => that.traverse(G)(f, x), mA)
    }
}

// Traversable2, Traversable3, Traversable4, ..., Traversable22
trait Traversable2 {
  type Cat1
  type Cat2
  type Map[+A <: Cat1, +B <: Cat2]

  def traverse[A <: Cat1, B <: Cat2, C <: Cat1, D <: Cat2]
              (G: Applicative)
              (f: A => G.Map[C], g: B => G.Map[D], mAB: Map[A, B]): G.Map[Map[C, D]]

  def apply[A <: Cat1, B <: Cat2](mAB: Map[A, B]): View[A, B] = new View(mAB)

  // if you want to have named parameters, e. g.,
  //
  //   avoidF(term).map(_var = rename, abs = avoidCapture)
  //
  // then the View trait gotta be generated. it looks
  // more trouble due to possible name clashes than
  // it's worth, though.
  class View[A <: Cat1, B <: Cat2](mAB: Map[A, B]) {
    def traverse[C <: Cat1, D <: Cat2]
                (G: Applicative)
                (f: A => G.Map[C], g: B => G.Map[D]): G.Map[Map[C, D]] =
      Traversable2.this.traverse(G)(f, g, mAB)

    def map[C <: Cat1, D <: Cat2](f: A => C, g: B => D): Map[C, D] = this.traverse(Applicative.Identity)(f, g)
  }
}

trait Traversable3 {
  type Cat1
  type Cat2
  type Cat3
  type Map[+A <: Cat1, +B <: Cat2, +C <: Cat3]

  def traverse[A <: Cat1, B <: Cat2, W <: Cat3, C <: Cat1, D <: Cat2, Y <: Cat3]
              (G: Applicative)
              (f: A => G.Map[C], g: B => G.Map[D], h: W => G.Map[Y], mAB: Map[A, B, W]): G.Map[Map[C, D, Y]]

  def apply[A <: Cat1, B <: Cat2, W <: Cat3](mAB: Map[A, B, W]): View[A, B, W] = new View(mAB)

  class View[A <: Cat1, B <: Cat2, W <: Cat3](mAB: Map[A, B, W]) {
    def traverse[C <: Cat1, D <: Cat2, Y <: Cat3]
      (G: Applicative)
      (f: A => G.Map[C], g: B => G.Map[D], h: W => G.Map[Y]): G.Map[Map[C, D, Y]] =
      Traversable3.this.traverse(G)(f, g, h, mAB)

    def map[C <: Cat1, D <: Cat2, Y <: Cat3](f: A => C, g: B => D, h: W => Y): Map[C, D, Y] =
      this.traverse(Applicative.Identity)(f, g, h)
  }
}

trait Traversable4 {
  type Cat1
  type Cat2
  type Cat3
  type Cat4
  type Map[+A <: Cat1, +B <: Cat2, +C <: Cat3, +D <: Cat4]

  def traverse[A <: Cat1, B <: Cat2, W <: Cat3, X <: Cat4, C <: Cat1, D <: Cat2, Y <: Cat3, Z <: Cat4]
              (G: Applicative)
              (f: A => G.Map[C], g: B => G.Map[D], h: W => G.Map[Y], k: X => G.Map[Z],
                mAB: Map[A, B, W, X]): G.Map[Map[C, D, Y, Z]]

  def apply[A <: Cat1, B <: Cat2, W <: Cat3, X <: Cat4](mAB: Map[A, B, W, X]): View[A, B, W, X] = new View(mAB)

  class View[A <: Cat1, B <: Cat2, W <: Cat3, X <: Cat4](mAB: Map[A, B, W, X]) {

    def traverse[C <: Cat1, D <: Cat2, Y <: Cat3, Z <: Cat4]
      (G: Applicative)
      (f: A => G.Map[C], g: B => G.Map[D], h: W => G.Map[Y], k: X => G.Map[Z]):
        G.Map[Map[C, D, Y, Z]] =
      Traversable4.this.traverse(G)(f, g, h, k, mAB)

    def map[C <: Cat1, D <: Cat2, Y <: Cat3, Z <: Cat4](f: A => C, g: B => D, h: W => Y, k: X => Z): Map[C, D, Y, Z] =
      this.traverse(Applicative.Identity)(f, g, h, k)
  }
}
