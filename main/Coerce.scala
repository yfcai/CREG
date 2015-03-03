/** Example of code generated by `coerce` */

import creg.functors._
import creg.lib._

object Coerce {
  // the binary tree datatype
  @data def Tree[A] = Fix(X => TreeT { Leaf(get = A) ; Fork(_1 = X, _2 = X) })

  // S = μX. Int + Fork(X, X)
  type S = Fix[SF.Map]
  @functor def SF[X] = TreeT { Leaf(get = Int) ; Fork(_1 = X, _2 = X) }

  // T = μY. Any + Fork(Y, μZ. Int + Fork(Z, Z))
  type T = Fix[TF.Map]
  @functor def TF[Y] = TreeT { Leaf(get = Any) ; Fork(_1 = Y, _2 = S) }

  val theWitness = new (S => T) {
    def apply(x: S): T = f0(x)

    // witness(S, T)
    private[this] def f0(x: S): T = f1(x.unroll)

    // witness(Int + Fork(S, S), T)
    private[this] def f1(x: S1): T = Roll[TF.Map](f2(x))
    private[this] type S1 = SF.Map[S]

    // witness(Int + Fork(S, S), Any + Fork(T, S))
    private[this] def f2(x: S1): T2 = TreeT(x).map(identity, f3)
    private[this] type T2 = TF.Map[T]

    // witness(Fork(S, S), Fork(T, S))
    private[this] def f3(x: S3): T3 = Fork(x).map(f0, identity)
    private[this] type S3 = Fork[S, S]
    private[this] type T3 = Fork[T, S]
  }

  // moreover, S and T have the same runtime objects.
  implicit def toLeaf(x: Int): S = Roll[SF.Map](Leaf(x))

  def run() {
    val s: S = coerce {
      Fork(Fork(1, 2), Fork(Fork(3, 4), Fork(5, 6)))
    }

    val t: T = theWitness(s)

    println(s"\nBefore:\n$s\n")
    println(s"\nAfter:\n$t\n")

    assert(s == t)
  }


  // possible slowdowns
  import Banana._ // for lists & *-morphisms
  import TraversableBase.Endofunctor

  // pattern functor of
  // incompatible representation of lists:
  // μX. listF (listF X)
  def listF2[A]: Endofunctor { type Map[+L] = ListF[A, ListF[A, L]] } = {
    val F = listF[A]
    F compose F
  }

  val intsF2 = listF2[Int]

  // lists of integers of even length
  // like List[Int], except with half as many Rolls
  type Ints2 = Fix[intsF2.Map]

  // list constructed from listF2 by anamorphism
  val pairs: Int => Ints2 =
    ana[Int](intsF2) { i =>
      if (i <= 0)
        Nil
      else
        Cons(i, Cons(i, i - 1))
    }

  // big list of pairs: 50, 50, 49, 49, 48, 48, ..., 1, 1
  val xs = pairs(50)

  def isEmpty(ns: List[Int]): Boolean = ns.unroll match {
    case Nil => true
    case Cons(_, _) => false
  }


  // expected time: constant
  //   actual time: linear
  def isEmpty2_slow(ns: Ints2): Boolean =

    // isEmpty( coerce(ns) )

    ??? // triggers bug in `coerce`!


  // non-solution: duplicate `isEmpty`
  def isEmpty2_dupe(ns: Ints2): Boolean = ns.unroll match {
    case Nil => true
    case Cons(_, _) => false
  }


  // non-solution: think of List[Int] as canonical;
  // never produce incompatible datatypes like Ints
  //
  // drawback: lose expressive power: can't express
  // "lists of even length" as a datatype
  val pairs_canon: Int => List[Int] =

    // n => coerce[Ints2, List[Int]] { pairs(n) }

    ??? // triggers bug in `coerce`!


  // solution: make precondition of isEmpty the weakest possible
  def isEmpty_good(xs: ListT[Any, Any]): Boolean = xs match {
    case Nil => true
    case Cons(_, _) => false
  }

  // expected time: constant
  //   actual time: constant
  def isEmpty_List(xs: List[Any]): Boolean =
    isEmpty_good(coerce(xs))

  // expected time: constant
  //   actual time: constant
  def isEmpty_Ints2(xs: Ints2): Boolean =
    isEmpty_good(coerce(xs))
}
