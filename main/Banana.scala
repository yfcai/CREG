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

  // a catamorphism is the unique morphism from an initial algebra to a given algebra.
  // conceptually, the implicit initial algebra is (Fix[F], id).
  def cata[T](fun: Endofunctor)(algebra: fun.Map[T] => T): Fix[fun.Map] => T =
    xs => algebra( fun(xs.unroll) map cata(fun)(algebra) )

  val sum: List[Int] => Int =
    cata[Int](listF[Int]) {
      case Nil => 0
      case Cons(head, tail) => head + tail
    }

  def ana[T](fun: Endofunctor)(coalgebra: T => fun.Map[T]): T => Fix[fun.Map] =
    seed => Roll[fun.Map]( fun(coalgebra(seed)) map ana(fun)(coalgebra) )

  def decrement: Int => ListF[Int, Int] =
    i => {
      if (i < 1)
        Nil
      else
        Cons(i, i - 1)
    }

  def downFrom: Int => List[Int] =
    ana[Int](listF[Int])(decrement)

  def hylo[T, R](fun: Endofunctor)(coalgebra: T => fun.Map[T])(algebra: fun.Map[R] => R): T => R =
    cata(fun)(algebra) compose ana(fun)(coalgebra)

  def hyloFactorial: Int => Int =
    hylo[Int, Int](listF[Int])(decrement) {
      case Nil => 1
      case Cons(m, n) => m * n
    }

  // paramorphism is just a hylomorphism with respect to some other functor

  // show this after the type signature of `paraWith`
  @datatype trait Pair[A, B] { MkPair(A, B) }

  // paramorphism agreeing with the traditional implementation in Haskell
  def para0[T](fun: Endofunctor)(psi: fun.Map[Pair[Fix[fun.Map], T]] => T): Fix[fun.Map] => T = {
    type F[+X] = fun.Map[X]
    xs => cata[Pair[Fix[fun.Map], T]](fun)({
      (input: F[Pair[Fix[F], T]]) => MkPair(
        Roll(fun(input) map { case MkPair(subterm, result) => subterm }),
        psi(input)
      )
    })(xs) match {
      case MkPair(xs, result) => result
    }
  }

  // paramorphism as a hypomorphism
  def para[T](fun: Endofunctor)(psi: fun.Map[Pair[Fix[fun.Map], T]] => T): Fix[fun.Map] => T = {

    type F[+X]      = fun.Map[X]
    type Paired[+X] = F[Pair[Fix[F], X]]

    @functor val sndF = y => Pair { MkPair(Fix[F], y) }

    val pairingF = compose(fun, sndF)

    implicitly[ pairingF.Map[Any] =:= Paired[Any] ]

    val pairingCoalgebra: Fix[F] => Paired[Fix[F]] =
      xs => fun(xs.unroll) map { child => MkPair(child, child) }

    hylo(pairingF)(pairingCoalgebra)(psi)
  }

  // Factorial as a paramorphism

  @datatype trait Nat { Zero ; Succ(Nat) }

  val natF = {
    @functor val fun = n => Nat { Succ(n) }
    fun
  }

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
      case Succ(MkPair(n, i)) => (natToInt(n) + 1) * i
    } compose intToNat

  def paraFactorial: Int => Int =
    para[Int](natF) {
      case Zero => 1
      case Succ(MkPair(n, i)) => (natToInt(n) + 1) * i
    } compose intToNat
}

import Banana._
