package nominal
package lib

import language.higherKinds

object Traversable {
  type EndofunctorOf[F[+_]] = Endofunctor {
    type Map[+X] = F[X]
  }

  type Endofunctor = Traversable {
    type Cat0 = Any
    type Map[+X]
  }

  type Endofunctor2 = Traversable2 {
    type Cat0 = Any ; type Cat1 = Any
    type Map[+A, +B]
  }

  type Endofunctor3 = Traversable3 {
    type Cat0 = Any ; type Cat1 = Any ; type Cat2 = Any
    type Map[+A, +B, +C]
  }

  type Endofunctor4 = Traversable4 {
    type Cat0 = Any ; type Cat1 = Any ; type Cat2 = Any ; type Cat3 = Any
    type Map[+A, +B, +C, +D]
  }

  trait EndofunctorTrait0 extends Traversable0

  trait EndofunctorTrait extends Traversable {
    type Cat0 = Any
    type Map[+A]
  }

  trait EndofunctorTrait2 extends Traversable2 {
    type Cat0 = Any ; type Cat1 = Any
    type Map[+A, +B]
  }

  trait EndofunctorTrait3 extends Traversable3 {
    type Cat0 = Any ; type Cat1 = Any ; type Cat2 = Any
    type Map[+A, +B, +C]
  }

  trait EndofunctorTrait4 extends Traversable4 {
    type Cat0 = Any ; type Cat1 = Any ; type Cat2 = Any ; type Cat3 = Any
    type Map[+A, +B, +C, +D]
  }
}

trait Traversable0 {
  type Map >: this.type
  type Range = Map
  def traverse(G: Applicative): G.Map[Map] = G pure (this: Map)
}

trait Traversable { thisFunctor =>
  // traversable functors can be defined on a subcategory
  type Cat0
  type Map[+A <: Cat0]
  type Range = Map[Cat0]

  // McBride & Paterson's traverse
  def traverse[A <: Cat0, B <: Cat0](G: Applicative)(f: A => G.Map[B]): this.Map[A] => G.Map[this.Map[B]]

  // reinterpret `x` in the light of `Map` being a traversable functor
  def apply[A <: Cat0](mA: Map[A]): View[A] = new View(mA)

  class View[A <: Cat0](mA: Map[A]) {
    trait Traversal[G[+_]] { def apply[B <: Cat0](f: A => G[B]): G[Map[B]] }

    def traverse(G: Applicative): Traversal[G.Map] = new Traversal[G.Map] {
      def apply[B <: Cat0](f: A => G.Map[B]): G.Map[Map[B]] =
        Traversable.this.traverse(G)(f)(mA)
    }

    // fmap
    def map[B <: Cat0](f: A => B): Map[B] =
      traverse(Applicative.Identity)(f)

    // McBride & Paterson's reduce
    def reduce(monoidId: A, monoidOp: (A, A) => A): A =
      mapReduce(identity)(monoidId, monoidOp)

    def mapReduce[B <: Cat0](f: A => B)(monoidId: B, monoidOp: (B, B) => B): B =
      traverse(Applicative.Const(monoidId, monoidOp))(f)
  }

  // compose with another functor
  def compose(that: Traversable { type Map[+X] <: thisFunctor.Cat0 }) =
    new Traversable {
      type Cat0 = that.Cat0
      type Map[+A <: Cat0] = thisFunctor.Map[that.Map[A]]
      def traverse[A <: Cat0, B <: Cat0](G: Applicative)(f: A => G.Map[B]): this.Map[A] => G.Map[this.Map[B]] =
        thisFunctor.traverse[that.Map[A], that.Map[B]](G)(that.traverse(G)(f))
    }
}

// Traversable2, Traversable3, Traversable4, ..., Traversable22
trait Traversable2 {
  type Cat0
  type Cat1
  type Map[+A <: Cat0, +B <: Cat1]
  type Range = Map[Cat0, Cat1]

  def traverse[A <: Cat0, B <: Cat1, C <: Cat0, D <: Cat1]
              (G: Applicative)
              (f: A => G.Map[C], g: B => G.Map[D]): Map[A, B] => G.Map[Map[C, D]]

  def apply[A <: Cat0, B <: Cat1](mAB: Map[A, B]): View[A, B] = new View(mAB)

  // if you want to have named parameters, e. g.,
  //
  //   avoidF(term).map(_var = rename, abs = avoidCapture)
  //
  // then the View trait gotta be generated. it looks
  // more trouble due to possible name clashes than
  // it's worth, though.
  class View[A <: Cat0, B <: Cat1](mAB: Map[A, B]) {
    def traverse[C <: Cat0, D <: Cat1]
                (G: Applicative)
                (f: A => G.Map[C], g: B => G.Map[D]): G.Map[Map[C, D]] =
      Traversable2.this.traverse(G)(f, g)(mAB)

    def map[C <: Cat0, D <: Cat1](f: A => C, g: B => D): Map[C, D] = this.traverse(Applicative.Identity)(f, g)
  }
}

trait Traversable3 {
  type Cat0
  type Cat1
  type Cat2
  type Map[+A <: Cat0, +B <: Cat1, +C <: Cat2]
  type Range = Map[Cat0, Cat1, Cat2]

  def traverse[A <: Cat0, B <: Cat1, W <: Cat2, C <: Cat0, D <: Cat1, Y <: Cat2]
              (G: Applicative)
              (f: A => G.Map[C], g: B => G.Map[D], h: W => G.Map[Y]): Map[A, B, W] => G.Map[Map[C, D, Y]]

  def apply[A <: Cat0, B <: Cat1, W <: Cat2](mAB: Map[A, B, W]): View[A, B, W] = new View(mAB)

  class View[A <: Cat0, B <: Cat1, W <: Cat2](mAB: Map[A, B, W]) {
    def traverse[C <: Cat0, D <: Cat1, Y <: Cat2]
      (G: Applicative)
      (f: A => G.Map[C], g: B => G.Map[D], h: W => G.Map[Y]): G.Map[Map[C, D, Y]] =
      Traversable3.this.traverse(G)(f, g, h)(mAB)

    def map[C <: Cat0, D <: Cat1, Y <: Cat2](f: A => C, g: B => D, h: W => Y): Map[C, D, Y] =
      this.traverse(Applicative.Identity)(f, g, h)
  }
}

trait Traversable4 {
  type Cat0
  type Cat1
  type Cat2
  type Cat3
  type Map[+A <: Cat0, +B <: Cat1, +C <: Cat2, +D <: Cat3]
  type Range = Map[Cat0, Cat1, Cat2, Cat3]

  def traverse[A <: Cat0, B <: Cat1, W <: Cat2, X <: Cat3, C <: Cat0, D <: Cat1, Y <: Cat2, Z <: Cat3]
              (G: Applicative)
              (f: A => G.Map[C], g: B => G.Map[D], h: W => G.Map[Y], k: X => G.Map[Z]):
                Map[A, B, W, X] => G.Map[Map[C, D, Y, Z]]

  def apply[A <: Cat0, B <: Cat1, W <: Cat2, X <: Cat3](mAB: Map[A, B, W, X]): View[A, B, W, X] = new View(mAB)

  class View[A <: Cat0, B <: Cat1, W <: Cat2, X <: Cat3](mAB: Map[A, B, W, X]) {

    def traverse[C <: Cat0, D <: Cat1, Y <: Cat2, Z <: Cat3]
      (G: Applicative)
      (f: A => G.Map[C], g: B => G.Map[D], h: W => G.Map[Y], k: X => G.Map[Z]):
        G.Map[Map[C, D, Y, Z]] =
      Traversable4.this.traverse(G)(f, g, h, k)(mAB)

    def map[C <: Cat0, D <: Cat1, Y <: Cat2, Z <: Cat3](f: A => C, g: B => D, h: W => Y, k: X => Z): Map[C, D, Y, Z] =
      this.traverse(Applicative.Identity)(f, g, h, k)
  }
}
