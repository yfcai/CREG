package creg
package lib

import language.higherKinds

object TraversableBounded {

  // TODO: Delete these synonyms
  type Endofunctor = TraversableBounded {
    type Cat0 = Any
    type Map[+X]
  }

  type Endofunctor2 = TraversableBounded2 {
    type Cat0 = Any ; type Cat1 = Any
    type Map[+A, +B]
  }

  type Endofunctor3 = TraversableBounded3 {
    type Cat0 = Any ; type Cat1 = Any ; type Cat2 = Any
    type Map[+A, +B, +C]
  }

  type Endofunctor4 = TraversableBounded4 {
    type Cat0 = Any ; type Cat1 = Any ; type Cat2 = Any ; type Cat3 = Any
    type Map[+A, +B, +C, +D]
  }

  type EndofunctorOf[F[+_]] = EndofunctorOf1[F]
  type EndofunctorOf1[F[+_]] = Endofunctor { type Map[+X] = F[X] }
  type EndofunctorOf2[F[+_, +_]] = Endofunctor2 { type Map[+X1, +X2] = F[X1, X2] }
  type EndofunctorOf3[F[+_, +_, +_]] = Endofunctor3 { type Map[+X1, +X2, +X3] = F[X1, X2, X3] }
  type EndofunctorOf4[F[+_, +_, +_, +_]] = Endofunctor4 { type Map[+X1, +X2, +X3, +X4] = F[X1, X2, X3, X4] }
}

trait Traversable0 extends TraversableBounded0

trait Traversable extends TraversableBounded with Functor {
  type Cat0 = Any
  type Map[+A]
}

trait Traversable2 extends TraversableBounded2 {
  type Cat0 = Any ; type Cat1 = Any
  type Map[+A, +B]
}

trait Traversable3 extends TraversableBounded3 {
  type Cat0 = Any ; type Cat1 = Any ; type Cat2 = Any
  type Map[+A, +B, +C]
}

trait Traversable4 extends TraversableBounded4 {
  type Cat0 = Any ; type Cat1 = Any ; type Cat2 = Any ; type Cat3 = Any
  type Map[+A, +B, +C, +D]
}


trait TraversableBounded0 {
  type Map >: this.type
  type Range = Map
  def traverse(G: Applicative)(): Map => G.Map[Map] = G pure _
}

trait TraversableBounded { thisFunctor =>
  // traversable functors can be defined on a subcategory
  type Cat0
  type Map[+A <: Cat0]
  type Range = Map[Cat0]

  // McBride & Paterson's traverse
  def traverse[A <: Cat0, B <: Cat0](G: Applicative)(f: A => G.Map[B]): this.Map[A] => G.Map[this.Map[B]]

  def fmap[A <: Cat0, B <: Cat0](f: A => B): Map[A] => Map[B] =
    traverse[A, B](Applicative.Identity)(f)

  def mapReduce[A <: Cat0, B <: Cat0](f: A => B)(
    default: B, combine: (B, B) => B):
      Map[A] => B =
    traverse[A, B](Applicative.Const(default, combine))(f)

  def crush[A <: Cat0](z: A, op: (A, A) => A): Map[A] => A = mapReduce(identity[A])(z, op)

  // reinterpret `x` in the light of `Map` being a traversable functor
  def apply[A <: Cat0](mA: Map[A]): View[A] = new View(mA)

  class View[A <: Cat0](mA: Map[A]) {
    trait Traversal[G[+_]] { def apply[B <: Cat0](f: A => G[B]): G[Map[B]] }

    def traverse(G: Applicative): Traversal[G.Map] = new Traversal[G.Map] {
      def apply[B <: Cat0](f: A => G.Map[B]): G.Map[Map[B]] =
        TraversableBounded.this.traverse(G)(f)(mA)
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

  // reinterpret 't' as the fixed point of this functor.
  // not really possible due to subcategory bounds. ugh!
  // def apply(t: Fix[Map]): Foldable[Map] = new Foldable[Map](t)(this)

  // compose with another functor
  def compose(that: TraversableBounded { type Map[+X] <: thisFunctor.Cat0 }) =
    new TraversableBounded {
      type Cat0 = that.Cat0
      type Map[+A <: Cat0] = thisFunctor.Map[that.Map[A]]
      def traverse[A <: Cat0, B <: Cat0](G: Applicative)(f: A => G.Map[B]): this.Map[A] => G.Map[this.Map[B]] =
        thisFunctor.traverse[that.Map[A], that.Map[B]](G)(that.traverse(G)(f))
    }
}

// TraversableBounded2, TraversableBounded3, TraversableBounded4, ..., TraversableBounded22
trait TraversableBounded2 {
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
      TraversableBounded2.this.traverse(G)(f, g)(mAB)

    def map[C <: Cat0, D <: Cat1](f: A => C, g: B => D): Map[C, D] = this.traverse(Applicative.Identity)(f, g)

    def mapReduce[C](f: A => C, g: B => C)(default: C, combine: (C, C) => C): C =
      traverse(Applicative.Const(default, combine))(f, g)
  }
}

trait TraversableBounded3 {
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
      TraversableBounded3.this.traverse(G)(f, g, h)(mAB)

    def map[C <: Cat0, D <: Cat1, Y <: Cat2](f: A => C, g: B => D, h: W => Y): Map[C, D, Y] =
      this.traverse(Applicative.Identity)(f, g, h)
  }
}

trait TraversableBounded4 {
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
      TraversableBounded4.this.traverse(G)(f, g, h, k)(mAB)

    def map[C <: Cat0, D <: Cat1, Y <: Cat2, Z <: Cat3](f: A => C, g: B => D, h: W => Y, k: X => Z): Map[C, D, Y, Z] =
      this.traverse(Applicative.Identity)(f, g, h, k)
  }
}
