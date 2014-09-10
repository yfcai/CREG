/** Console demo script for:
  *
  * Meijer, Fokkinga, Paterson.
  * Functional programming with bananas, lenses, envelopes and barbed wire.
  */

import language.higherKinds
import nominal.functors._
import nominal.lib._
import nominal.lib.Traversable.{Endofunctor, compose}

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

  def cataWith[T](fun: Endofunctor)(algebra: fun.Map[T] => T): Fix[fun.Map] => T =
    xs => algebra( fun(xs.unroll) map cataWith(fun)(algebra) )

  implicit class ListIsFoldable[A](xs: List[A]) {
    val patternFunctor = listF[A]

    def fold[T](algebra: patternFunctor.Map[T] => T): T =
      cataWith(patternFunctor)(algebra)(xs)
  }

  def sum(xs: List[Int]): Int = xs.fold[Int] {
    case Nil => 0
    case Cons(head, tail) => head + tail
  }

  def anaWith[T](fun: Endofunctor)(coalgebra: T => fun.Map[T]): T => Fix[fun.Map] =
    seed => Roll[fun.Map]( fun(coalgebra(seed)) map anaWith(fun)(coalgebra) )

  def mkList[A, T](seed: T)(coalgebra: T => ListF[A, T]): List[A] =
    anaWith(listF[A])(coalgebra)(seed)

  def incrementCoalgebra(n: Int): Int => ListF[Int, Int] = i =>
    if (i > n)
      Nil
    else
      Cons(i, i + 1)

  def upTo(n: Int): List[Int] =
    mkList[Int, Int](1)(incrementCoalgebra(n))

  def hyloWith[T, R](fun: Endofunctor)(coalgebra: T => fun.Map[T])(algebra: fun.Map[R] => R): T => R =
    cataWith(fun)(algebra) compose anaWith(fun)(coalgebra)

  def hylo[A, T, R](seed: T)(coalgebra: T => ListF[A, T])(algebra: ListF[A, R] => R): R = {
    val functor = listF[A]
    hyloWith(functor)(coalgebra)(algebra)(seed)
  }

  def hyloFactorial(n: Int): Int =
    hylo[Int, Int, Int](1)(incrementCoalgebra(n)) {
      case Nil => 1
      case Cons(m, n) => m * n
    }

  // paramorphism is just a hylomorphism

  // show this after the type signature of `paraWith`
  @datatype trait Pair[A, B] { MkPair(A, B) }

  def paraWith0[T](fun: Endofunctor)(psi: fun.Map[Pair[Fix[fun.Map], T]] => T): Fix[fun.Map] => T = {
    type F[+X] = fun.Map[X]
    xs => cataWith[Pair[Fix[fun.Map], T]](fun)({
      (input: F[Pair[Fix[F], T]]) => MkPair(
        Roll(fun(input) map { case MkPair(subterm, result) => subterm }),
        psi(input)
      )
    })(xs) match {
      case MkPair(xs, result) => result
    }
  }

  def paraWith[T](fun: Endofunctor)(psi: fun.Map[Pair[Fix[fun.Map], T]] => T): Fix[fun.Map] => T = {

    type F[+X]      = fun.Map[X]
    type Paired[+X] = F[Pair[Fix[F], X]]

    @functor val sndF = y => Pair { MkPair(Fix[F], y) }

    val pairingF = compose(fun, sndF)

    implicitly[ pairingF.Map[Any] =:= Paired[Any] ]

    val pairingCoalgebra: Fix[F] => Paired[Fix[F]] =
      xs => fun(xs.unroll) map { child => MkPair(child, child) }

    hyloWith(pairingF)(pairingCoalgebra)(psi)
  }

  @datatype trait Nat { Zero ; Succ(Nat) }

  val natF = {
    @functor val fun = n => Nat { Succ(n) }
    fun
  }

  val natToInt: Nat => Int =
    cataWith[Int](natF) {
      case Zero => 0
      case Succ(n) => n + 1
    }

  val intToNat: Int => Nat =
    anaWith[Int](natF) { i =>
      if (i == 0)
        Zero
      else
        Succ(i - 1)
    }

  def paraFactorial0: Int => Int =
    paraWith0[Int](natF) {
      case Zero => 1
      case Succ(MkPair(n, i)) => (natToInt(n) + 1) * i
    } compose intToNat

  def paraFactorial: Int => Int =
    paraWith[Int](natF) {
      case Zero => 1
      case Succ(MkPair(n, i)) => (natToInt(n) + 1) * i
    } compose intToNat
}

import Banana._
