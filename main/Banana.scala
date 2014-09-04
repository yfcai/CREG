/** Console demo script for:
  *
  * Meijer, Fokkinga, Paterson.
  * Functional programming with bananas, lenses, envelopes and barbed wire.
  */

import language.higherKinds
import nominal.functors._
import nominal.lib._
import nominal.lib.Traversable.{Endofunctor => Functor, _}

object Banana {
  @datatype trait List[A] {
    Nil
    Cons(A, List[A])
  }

  val xs1: List[Int] = coerce( Cons(1, Cons(2, Cons(3, Cons(4, Nil)))) )

  implicit class ListIsMappable[A](xs: List[A]) {
    def map[B](f: A => B): List[B] = {
      @functor val elemF = elem => List { Nil ; Cons(elem, List) }

      // alternatively:
      //@functor val list = Elem => List[Elem]

      elemF(xs) map f
    }
  }

  // pattern functor
  def listF[A] = {
    @functor val fun = rec => List { Cons(A, rec) }
    fun
  }

  // type List[A] = Fix[listF[A].Map]

  def cataWith[F[+_], T](functor: Functor[F])(algebra: F[T] => T): Fix[F] => T =
    xs => algebra( functor(xs.unroll) map cataWith(functor)(algebra) )

  implicit class ListIsFoldable[A](xs: List[A]) {
    val patternFunctor = listF[A]

    def fold[T](algebra: patternFunctor.Map[T] => T): T =
      cataWith[patternFunctor.Map, T](patternFunctor)(algebra)(xs)
  }

  def sum(xs: List[Int]): Int = xs.fold[Int] {
    case Nil => 0
    case Cons(head, tail) => head + tail
  }

  def anaWith[F[+_], T](functor: Functor[F])(coalgebra: T => F[T]): T => Fix[F] =
    seed => Roll[F](functor(coalgebra(seed)) map anaWith(functor)(coalgebra))

  def mkList[A, T](seed: T)(coalgebra: T => ListF[A, T]): List[A] = {
    val functor = listF[A]
    anaWith[functor.Map, T](functor)(coalgebra)(seed)
  }

  def incrementCoalgebra(n: Int): Int => ListF[Int, Int] = i =>
    if (i > n)
      Nil
    else
      Cons(i, i + 1)

  def upTo(n: Int): List[Int] =
    mkList[Int, Int](1)(incrementCoalgebra(n))

  def hyloWith[F[+_], T, R](functor: Functor[F])(coalgebra: T => F[T])(algebra: F[R] => R): T => R =
    seed =>
      cataWith(functor)(algebra)(
        anaWith(functor)(coalgebra)(seed)
      )

  def hylo[A, T, R](seed: T)(coalgebra: T => ListF[A, T])(algebra: ListF[A, R] => R): R = {
    val functor = listF[A]
    hyloWith[functor.Map, T, R](functor)(coalgebra)(algebra)(seed)
  }

  def hyloFactorial(n: Int): Int =
    hylo[Int, Int, Int](1)(incrementCoalgebra(n)) {
      case Nil => 1
      case Cons(m, n) => m * n
    }

  // paramorphism is just a hylomorphism

  // show this after the type signature of `paraWith`
  @datatype trait Pair[A, B] { MkPair(A, B) }

  def paraWith[F[+_], T](functor: Functor[F])(psi: F[Pair[Fix[F], T]] => T): Fix[F] => T = {

    type Paired[+X] = F[Pair[Fix[F], X]]

    @functor val sndF = y => Pair { MkPair(Fix[F], y) }
    // but not: Y => Pair[Fix[F], Y]. should investigate.

    val pairingF = compose[F, sndF.Map](functor, sndF)

    implicitly[ pairingF.Map[Any] =:= Paired[Any] ]

    val pairingCoalgebra: Fix[F] => Paired[Fix[F]] =
      data => functor(data.unroll) map {
        child => MkPair(child, child)
      }

    hyloWith[Paired, Fix[F], T](pairingF)(pairingCoalgebra)(psi)
  }

  @datatype trait Nat { Zero ; Succ(Nat) }

  val natF = {
    @functor val fun = n => Nat { Succ(n) }
    fun
  }

  val natToInt: Nat => Int =
    cataWith[natF.Map, Int](natF) {
      case Zero => 0
      case Succ(n) => n + 1
    }

  val intToNat: Int => Nat =
    anaWith[natF.Map, Int](natF) { i =>
      if (i == 0)
        Zero
      else
        Succ(i - 1)
    }

  def paraFactorial: Int => Int =
    paraWith[natF.Map, Int](natF) {
      case Zero => 1
      case Succ(MkPair(n, i)) => (natToInt(n) + 1) * i
    } compose intToNat
}

import Banana._
