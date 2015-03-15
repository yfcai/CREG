/** Console demo script for:
  *
  * Meijer, Fokkinga, Paterson.
  * Functional programming with bananas, lenses, envelopes and barbed wire.
  */

package creg.example

import language.higherKinds
import creg._
import lib._

object Banana {
  @struct def ListT { Nil ; Cons(head, tail) }

  type List [+A]     = List.Map[A]
  type ListF[+A, +L] = ListT[Nil, Cons[A, L]]

  // Alternative to @struct followed by synonyms, one can use
  // @data List[A] = Fix(list => ListT { ... }) to generate the synonyms
  // together with the variant ListT of polymorphic records Nil, Cons.

  val xs1: List[Int] = coerce( Cons(1, Cons(2, Cons(3, Cons(4, Nil)))) )

  @functor def List[elem] = Fix(list => ListT { Nil ; Cons(head = elem, tail = list) })

  implicit class ListIsMappable[A](xs: List[A]) {
    def map[B](f: A => B): List[B] =
      List(xs) map f
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

  def cata[T](fun: Traversable)(algebra: fun.Map[T] => T): Fix[fun.Map] => T =
    xs => algebra( fun(xs.unroll) map cata(fun)(algebra) )

  implicit class ListIsFoldable[A](xs: List[A]) {
    val patternFunctor = listF[A]

    def fold[T](algebra: patternFunctor.Map[T] => T): T =
      cata(patternFunctor)(algebra)(xs)
  }

  def sum(xs: List[Int]): Int = xs.fold[Int] {
    case Nil => 0
    case Cons(head, tail) => head + tail
  }

  def ana[T](fun: Traversable)(coalgebra: T => fun.Map[T]): T => Fix[fun.Map] =
    seed => Roll[fun.Map]( fun(coalgebra(seed)) map ana(fun)(coalgebra) )

  def mkList[A, T](seed: T)(coalgebra: T => ListF[A, T]): List[A] =
    ana(listF[A])(coalgebra)(seed)

  def incrementCoalgebra(n: Int): Int => ListF[Int, Int] = i =>
    if (i > n)
      Nil
    else
      Cons(i, i + 1)

  def upTo(n: Int): List[Int] =
    mkList[Int, Int](1)(incrementCoalgebra(n))

  def hylo[T, R](fun: Traversable)(coalgebra: T => fun.Map[T])(algebra: fun.Map[R] => R): T => R =
    cata(fun)(algebra) compose ana(fun)(coalgebra)

  def hyloFactorial(n: Int): Int =
    hylo[Int, Int](listF[Int])(incrementCoalgebra(n))({
      case Nil => 1
      case Cons(m, n) => m * n
    })(1)

  // paramorphism is just a hylomorphism

  // show this after the type signature of `para`
  @data def _Pair[A, B] = Pair(_1 = A, _2 = B)

  def para0[T](fun: Traversable)(psi: fun.Map[Pair[Fix[fun.Map], T]] => T): Fix[fun.Map] => T = {
    type F[+X] = fun.Map[X]
    xs => cata[Pair[Fix[fun.Map], T]](fun)({
      (input: F[Pair[Fix[F], T]]) => Pair(
        Roll(fun(input) map { case Pair(subterm, result) => subterm }),
        psi(input)
      )
    })(xs) match {
      case Pair(xs, result) => result
    }
  }

  def para[T](fun: Traversable)(psi: fun.Map[Pair[Fix[fun.Map], T]] => T): Fix[fun.Map] => T = {
    type F[+X]      = fun.Map[X]
    type Paired[+X] = F[Pair[Fix[F], X]]
    type FixedPoint = Fix[F]

    @functor def pairingF[x] = fun apply Pair(_1 = FixedPoint, _2 = x)

    implicitly[ pairingF.Map[Any] =:= Paired[Any] ]

    val pairingCoalgebra: Fix[F] => Paired[Fix[F]] =
      xs => fun(xs.unroll) map { child => Pair(child, child) }

    hylo(pairingF)(pairingCoalgebra)(psi)
  }

  def cake[T](fun: Traversable)(psi: Pair[Fix[fun.Map], fun.Map[T]] => T): Fix[fun.Map] => T = {
    type F[+X]      = fun.Map[X]
    type FixedPoint = Fix[F]

    @functor def pairingF[x] = Pair(_1 = FixedPoint, _2 = fun apply x)

    val pairingCoalgebra: Fix[F] => pairingF.Map[Fix[F]] =
      xs => Pair(xs, coerce { xs })

    hylo(pairingF)(pairingCoalgebra)(psi)
  }

  def cakeWithCoerce[F[+_]](implicit F: Traversable { type Map[+A] = F[A] }) = new {
    type FixedPoint = Fix[F]

    // BUG: does not work if inline FixedPoint here.
    @functor def pairingF[x] = Pair(_1 = FixedPoint, _2 = F apply x)

    // coercion works with an abstract functor if it is in the implicit
    // scope and its type constructor is bounded by a type parameter.
    // (the inner coercion is superfluous; it's there to ensure that
    // F.fmap is called.)
    val pairingCoalgebra: Fix[F] => pairingF.Map[Fix[F]] =
      xs => coerce { Pair(xs, coerce { xs } : F[Fix[F]]) }

    def apply[T](psi: Pair[Fix[F], F[T]] => T): Fix[F] => T =
      hylo(pairingF)(pairingCoalgebra)(psi)
  }

  @data def Nat = Fix(nat => NatT { Zero ; Succ(pred = nat) })

  @functor implicit def natF[n] = NatT { Zero ; Succ(pred = n) }

  val natToInt: Nat => Int =
    cata[Int](natF) {
      case Zero => 0
      case Succ(n) => n + 1
    }

  val intToNat: Int => Nat =
    ana[Int](natF) { i =>
      if (i == 0)
        Zero
      else
        Succ(i - 1)
    }

  def paraFactorial0: Int => Int =
    para0[Int](natF) {
      case Zero => 1
      case Succ(Pair(n, i)) => (natToInt(n) + 1) * i
    } compose intToNat

  def paraFactorial: Int => Int =
    para[Int](natF) {
      case Zero => 1
      case Succ(Pair(n, i)) => (natToInt(n) + 1) * i
    } compose intToNat

  import language.reflectiveCalls
  def cakeWithCoerceFactorial: Int => Int =
    cakeWithCoerce[natF.Map].apply[Int] {
      case Pair(zero, Zero) => 1
      case Pair(n, Succ(nMinusOneFactorial)) => natToInt(n) * nMinusOneFactorial
    } compose intToNat
}

import Banana._
