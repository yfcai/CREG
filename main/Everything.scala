/** Everything is an n-nary functor
  */

import nominal.functors._
import nominal.lib._
import language.higherKinds

object Everything {
  @datatype trait List[+A] {
    Nil
    Cons(A, List[A])
  }

  object Cons extends Traversable2 {
    type Cat1 = Any
    type Cat2 = Any
    type Map[+A, +B] = Cons[A, B]
    def traverse[A, B, C, D](G: Applicative)(f: A => G.Map[C], g: B => G.Map[D], mAB: Map[A, B]):
        G.Map[Map[C, D]] =
      mAB match {
        case Cons(a, b) =>
          import G.{pure, call}
          call(call(
            pure[C => D => Map[C, D]](c => d => Cons(c, d)),
            f(a)), g(b))
      }
  }

  type Bifunctor = Traversable2 { type Cat1 = Any ; type Cat2 = Any }

  case class Cons2(_1: Bifunctor, _2: Bifunctor) extends Traversable2 {
    type Cat1 = Any ; type Cat2 = Any
    type Map[+A, +B] = Cons[_1.Map[A, B], _2.Map[A, B]]

    def traverse[A, B, X, Y](G: Applicative)
      (f: A => G.Map[X], g: B => G.Map[Y], m: Map[A, B]): G.Map[Map[X, Y]] =
      Cons.traverse[
        _1.Map[A, B], _2.Map[A, B],
        _1.Map[X, Y], _2.Map[X, Y]
      ](G)(x => _1.traverse(G)(f, g, x), x => _2.traverse(G)(f, g, x), m)
  }

  /* This is what you felt you knew & forgot about:
   * sealing trait List guarantees that whenever
   * ListT[A, B] is supplied, then A is a subtype
   * of Nil and B is a subtype of Cons[Any, Any].
   * Thus, there's no need to restrict arguments to
   * some non-cartesian-closed subcategory.
   */
  object List extends Traversable2 {
    type Cat1 = Any
    type Cat2 = Any
    type Map[+A, +B] = ListT[A, B]
    def traverse[A, B, C, D](G: Applicative)
      (f: A => G.Map[C], g: B => G.Map[D], mAB: Map[A, B]):
        G.Map[Map[C, D]] =
      mAB match {
        case Nil              => f(Nil).asInstanceOf[G.Map[Map[C, D]]]
        case con @ Cons(_, _) => g(con).asInstanceOf[G.Map[Map[C, D]]]
      }
  }

  case class List2(_1: Bifunctor, _2: Bifunctor) extends Traversable2 {
    type Cat1 = Any
    type Cat2 = Any
    type Map[+A, +B] = ListT[_1.Map[A, B], _2.Map[A, B]]
    def traverse[A, B, X, Y](G: Applicative)
      (f: A => G.Map[X], g: B => G.Map[Y], m: Map[A, B]): G.Map[Map[X, Y]] =
      List.traverse[
        _1.Map[A, B], _2.Map[A, B],
        _1.Map[X, Y], _2.Map[X, Y]
      ](G)(x => _1.traverse(G)(f, g, x), x => _2.traverse(G)(f, g, x), m)
  }

  case class Fix2(patternFunctor: Traversable2 { type Cat1 = Any ; type Cat2 = Any }) extends Traversable {
    type Cat = Any

    private[this]
    type F[+X] = { type λ[+Y] = patternFunctor.Map[X, Y] }

    type Map[+X ] = Fix[F[X]#λ]
    def traverse[A , B](G: Applicative)(f: A => G.Map[B], mA: Map[A]): G.Map[Map[B]] = {
      import G.{pure, call}

      object loop extends (Map[A] => G.Map[Map[B]]) {
        def apply(x: Map[A]): G.Map[Map[B]] =
          call(
            pure[patternFunctor.Map[B, Map[B]] => Map[B]](x => Roll[F[B]#λ](x)),
            patternFunctor.traverse(G)(f, this, x.unroll))
      }

      loop(mA)
    }
  }

  object Proj1 extends Traversable2 {
    type Cat1 = Any
    type Cat2 = Any
    type Map[+A, +B] = A
    def traverse[A, B, C, D](G: Applicative)
      (f: A => G.Map[C], g: B => G.Map[D], mAB: A): G.Map[C] = f(mAB)
  }

  object Proj2 extends Traversable2 {
    type Cat1 = Any
    type Cat2 = Any
    type Map[+A, +B] = B
    def traverse[A, B, C, D](G: Applicative)
      (f: A => G.Map[C], g: B => G.Map[D], mAB: B): G.Map[D] = g(mAB)
  }

  object ConstNil extends Traversable2 {
    type Cat1 = Any
    type Cat2 = Any
    type Map[+A, +B] = Nil
    def traverse[A, B, C, D](G: Applicative)
      (f: A => G.Map[C], g: B => G.Map[D], mAB: Nil): G.Map[Nil] = G pure Nil
  }

  val elemF = new Traversable {
    type Cat = Any
    type Map[+A] = List[A]
    val delegate = Fix2(List2(ConstNil, Cons2(Proj1, Proj2)))
    def traverse[A, B](G: Applicative)(f: A => G.Map[B], mA: Map[A]): G.Map[Map[B]] =
      // casts because Scala's type checker gets very confused.
      delegate.traverse(G)(f, mA.asInstanceOf[delegate.Map[A]]).asInstanceOf[G.Map[Map[B]]]
  }

  val xs: List[Int] =
    coerce { Cons(1, Cons(2, Cons(3, Cons(4, Nil)))) }

  val xsPlus1: List[Int] =
    coerce { Cons(2, Cons(3, Cons(4, Cons(5, Nil)))) }

  // assert(elemF(xs).map(_ + 1) == xsPlus1)
}
