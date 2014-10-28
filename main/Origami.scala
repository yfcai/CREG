/** Origami pattern as discussed in:
  *
  * Moors, Piessens, Joosen.
  * An object-oriented approach to datatype-generic programming.
  *
  * Oliveira and Gibbons.
  * Scala for generic programmers.
  */

import nominal.functors._
import nominal.lib._
import language.higherKinds

object Origami {
/*
  type Bifunctor = Traversable2 { type Cat0 = Any ; type Cat1 = Any ; type Map[+X, +Y] }

  type Fix2[F[+_, +_], T] = Fix[ ({ type λ[+X] = F[T, X] })#λ ]

  def roll2[F[+_, +_], T](unrolled: F[T, Fix2[F, T]]): Fix2[F, T] =
    Roll[ ({ type λ[+X] = F[T, X] })#λ ](unrolled)

  def bimap[A, B, C, D](F: Bifunctor)(f: A => B, g: C => D): F.Map[A, C] => F.Map[B, D] =
    xs => F(xs) map (f, g)

  def fmap2[A, C, D](F: Bifunctor)(g: C => D): F.Map[A, C] => F.Map[A, D] = bimap(F)(identity, g)

  def map[A, B](F: Bifunctor)(f: A => B): Fix2[F.Map, A] => Fix2[F.Map, B] =
    xs => roll2 { bimap(F)(f, map(F)(f))(xs.unroll) }

  def cata[A, R](F: Bifunctor)(f: F.Map[A, R] => R): Fix2[F.Map, A] => R =
    xs => f( fmap2(F)(cata(F)(f))(xs.unroll) )

  def ana[A, R](F: Bifunctor)(f: R => F.Map[A, R]): R => Fix2[F.Map, A] =
    seed => roll2 { fmap2(F)(ana(F)(f))( f(seed) ) }

  def hylo[A, B, C](F: Bifunctor)(f: A => F.Map[C, A])(g: F.Map[C, B] => B): A => B =
    cata(F)(g) compose ana(F)(f)

  trait Church2[F[+_, +_], A] { def apply[B](f: F[A, B] => B): B }

  // called `build` in paper
  def churchDecode2[A](F: Bifunctor)(fold: Church2[F.Map, A]): Fix2[F.Map, A] = fold(roll2)


  trait Church[F[+_]] { def apply[T](algebra: F[T] => T): T }

  def churchDecode(F: Traversable.Endofunctor)(fold: Church[F.Map]): Fix[F.Map] = fold(Roll.apply)

  @data def List[A] = Fix(list => ListT {
    Nil
    Cons(head = A, tail = list)
  })

  @functor def listB[a, r] = ListT { Nil ; Cons(head = a, tail = r) }

  val sum: List[Int] => Int =
    cata[Int, Int](listB) {
      case Nil => 0
      case Cons(m, n) => m + n
    }

  def mapList[A, B](f: A => B): List[A] => List[B] =
    cata[A, List[B]](listB) {
      case Nil => coerce { Nil }
      case Cons(x, xs) => coerce { Cons(f(x), xs) }
    }
 */
}
