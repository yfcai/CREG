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

  // object Nil // not possible yet (Nil defined as case object)

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

  object List extends Traversable2 {
    type Cat1 = Nil
    type Cat2 = Cons[Any, Any]
    type Map[+A <: Cat1, +B <: Cat2] = ListT[A, B]
    def traverse[A <: Cat1, B <: Cat2, C <: Cat1, D <: Cat2](G: Applicative)
      (f: A => G.Map[C], g: B => G.Map[D], mAB: Map[A, B]):
        G.Map[Map[C, D]] =
      mAB match {
        case Nil              => f(Nil).asInstanceOf[G.Map[Map[C, D]]]
        case con @ Cons(_, _) => g(con).asInstanceOf[G.Map[Map[C, D]]]
      }
  }

  class Fix2(val patternFunctor: Traversable2 { type Cat2 = Any }) extends Traversable {
    type Cat = patternFunctor.Cat1

    private[this]
    type F[+X <: Cat] = { type λ[+Y] = patternFunctor.Map[X, Y] }

    type Map[+X <: Cat] = Fix[F[X]#λ]
    def traverse[A <: Cat, B <: Cat](G: Applicative)(f: A => G.Map[B], mA: Map[A]): G.Map[Map[B]] = {
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
}
