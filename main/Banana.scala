/** Console demo script for:
  *
  * Meijer, Fokkinga, Paterson.
  * Functional programming with bananas, lenses, envelopes and barbed wire.
  */

import language.higherKinds
import nominal.functors._
import nominal.lib._
import nominal.lib.Traversable.{Endofunctor => Functor, compose}

object Banana extends App {
  /*
   data List a = Nil
               | Cons a (List a)
   */

  @datatype trait List[A] {
    Nil
    Cons(A, List[A])
  }

  val xs1: List[Int] = coerce {
    Cons(1, Cons(2, Cons(3, Cons(4, Nil))))
  }

  // why coerce?
  println(s"\nxs1 = $xs1\n")
  // because List is the fixed point of a functor.

  def listF[A] = {
    @functor val fun =
      r => List { Nil ; Cons(A, r) }
    fun
  }

  // intListF is a functor.
  // mapping on types: intListF.Map
  // mapping on arrow: intListF.fmap

  val intListF = listF[Int]

  implicitly[  List[Int] =:= Fix[ intListF.Map ]  ]

  // computing catamorphism: (F[T] => T) => Fix[F] => T
  def cata[T](F: Functor)(algebra: F.Map[T] => T): Fix[F.Map] => T = {
    xs => algebra( F(xs.unroll) map cata(F)(algebra) )
  }

  val sum: List[Int] => Int =
    cata[Int](listF[Int]) {
      case Cons(m, n) => m + n
      case Nil => 0
    }

  println(s"sum(xs1) = ${sum(xs1)}\n")

  // computing anamorphism: (T => F[T]) => T => Fix[F]
  def ana[T](F: Functor)(coalgebra: T => F.Map[T]): T => Fix[F.Map] =
    seed => {
      // coalgebra(seed) : F.Map[T]
      // F(coalgebra(seed)) map ana(F)(coalgebra) : F.Map[Fix[F.Map]]
      Roll(F(coalgebra(seed)) map ana(F)(coalgebra))
    }

  def downFrom: Int => List[Int] =
    ana[Int](listF[Int]) { n =>
      if (n <= 0)
        coerce { Nil }
      else
        coerce { Cons(n, n - 1) }
    }

  val xs2 = downFrom(4)
  println(s"xs2 = $xs2\n")

  // computing hylomorphism: (T => F[T]) => (F[R] => R) => T => R
  def hylo[T, R](F: Functor)(coalgebra: T => F.Map[T])(algebra: F.Map[R] => R): T => R =
    cata(F)(algebra) compose ana(F)(coalgebra)

  val hyloFactorial: Int => Int =
    hylo[Int, Int](listF[Int]) { n =>
      if (n <= 0)
        coerce { Nil }
      else
        coerce { Cons(n, n - 1) }
    } {
      case Cons(m, n) => m * n
      case Nil => 1
    }

  println(s"4! = ${hyloFactorial(4)}")
  println(s"5! = ${hyloFactorial(5)}\n")

  // computing paramorphism: (F[ Pair[ Fix[F], T ] ] => T) => Fix[F] => T

  // data Pair a b = mkPair a b
  @datatype trait Pair[A, B] { MkPair(A, B) }

  def para[T](F: Functor)(psi: F.Map[Pair[Fix[F.Map], T]] => T): Fix[F.Map] => T =
    xs => cata[Pair[Fix[F.Map], T]](F)({
      // algebra: F.Map[Pair[Fix[F.Map], T]] => Pair[Fix[F.Map], T]
      input => MkPair(
        Roll { F(input) map { case MkPair(subterm, subresult) => subterm } },
        psi(input)
      )
    })(xs) match {
      case MkPair(xs, result) => result
    }

  def tail[A]: List[A] => List[A] =
    para[List[A]](listF[A]) {
      case Nil => coerce { Nil }
      case Cons(head, MkPair(tail, tailOfTail)) => tail
    }

  println(s"tail(xs2) = ${tail(xs2)}\n")

  // but psi : F[ Pair[ Fix[F], T ] ] => T looks like an algebra!
  // can `para` be written as a hylomorphism?

  def para2[T](F: Functor)(psi: F.Map[Pair[Fix[F.Map], T]] => T): Fix[F.Map] => T = {
    // FIRST question: to which functor is `psi` an algebra?
    type PsiF[+T] = F.Map[Pair[Fix[F.Map], T]]

    // psiF is the composition of F and a pairing functor.
    type PairingF[+T] = Pair[Fix[F.Map], T]

    @functor val pairingF = t => Pair { MkPair(Fix[F.Map], t) }

    val psiF = compose(F, pairingF)

    // SECOND question: what's the coalgebra?
    // want: Fix[PsiF]
    // have: Fix[F.Map]
    val coalgebra: Fix[F.Map] => PsiF[Fix[F.Map]] =
      // coalgebra: Fix[F.Map] => F.Map[Pair[Fix[F.Map], Fix[F.Map]]]
      xs => F(xs.unroll) map { child => MkPair(child, child) }

    hylo(psiF)(coalgebra)(psi)
  }

  def tail2[A]: List[A] => List[A] =
    para2[List[A]](listF[A]) {
      case Nil => coerce { Nil }
      case Cons(head, MkPair(tail, tailOfTail)) => tail
    }

  println(s"tail2(xs2) = ${tail2(xs2)}\n")
}
