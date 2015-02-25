/** Console demo script for:
  *
  * Meijer, Fokkinga, Paterson.
  * Functional programming with bananas, lenses, envelopes and barbed wire.
  */

import language.higherKinds
import nominal.functors._
import nominal.lib._
import nominal.lib.Traversable.Endofunctor

object Banana {
  @data def List[A] = Fix(list => ListT {
    Nil
    Cons(head = A, tail = list)
  })

  val xs1: List[Int] = coerce( Cons(1, Cons(2, Cons(3, Cons(4, Nil)))) )

  @functor def elemF[elem] = Fix(list => ListT { Nil ; Cons(head = elem, tail = list) })

  implicit class ListIsMappable[A](xs: List[A]) {
    def map[B](f: A => B): List[B] =
      elemF(xs) map f
  }

  // pattern functor
  def listF[A] = {
    @functor def patternFunctor[list] = ListT {
      Nil
      Cons(head = A, tail = list)
    }
    patternFunctor
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
  @data def _Pair[A, B] = Pair(_1 = A, _2 = B)

  def paraWith0[T](fun: Endofunctor)(psi: fun.Map[Pair[Fix[fun.Map], T]] => T): Fix[fun.Map] => T = {
    type F[+X] = fun.Map[X]
    xs => cataWith[Pair[Fix[fun.Map], T]](fun)({
      (input: F[Pair[Fix[F], T]]) => Pair(
        Roll(fun(input) map { case Pair(subterm, result) => subterm }),
        psi(input)
      )
    })(xs) match {
      case Pair(xs, result) => result
    }
  }

  def paraWith[T](fun: Endofunctor)(psi: fun.Map[Pair[Fix[fun.Map], T]] => T): Fix[fun.Map] => T = {
    type F[+X]      = fun.Map[X]
    type Paired[+X] = F[Pair[Fix[F], X]]
    type FixedPoint = Fix[F]

    @functor def pairingF[x] = fun apply Pair(_1 = FixedPoint, _2 = x)

    implicitly[ pairingF.Map[Any] =:= Paired[Any] ]

    val pairingCoalgebra: Fix[F] => Paired[Fix[F]] =
      xs => fun(xs.unroll) map { child => Pair(child, child) }

    hyloWith(pairingF)(pairingCoalgebra)(psi)
  }

  def cakeWith[T](fun: Endofunctor)(psi: Pair[Fix[fun.Map], fun.Map[T]] => T): Fix[fun.Map] => T = {
    type F[+X]      = fun.Map[X]
    type FixedPoint = Fix[F]

    @functor def pairingF[x] = Pair(_1 = FixedPoint, _2 = fun apply x)

    val pairingCoalgebra = (xs: Fix[F]) => Pair(xs, xs.unroll)

    hyloWith(pairingF)(pairingCoalgebra)(psi)
  }

  @data def Nat = Fix(nat => NatT { Zero ; Succ(pred = nat) })

  @functor def natF[n] = NatT { Zero ; Succ(pred = n) }

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
      case Succ(Pair(n, i)) => (natToInt(n) + 1) * i
    } compose intToNat

  def paraFactorial: Int => Int =
    paraWith[Int](natF) {
      case Zero => 1
      case Succ(Pair(n, i)) => (natToInt(n) + 1) * i
    } compose intToNat
}

import Banana._
