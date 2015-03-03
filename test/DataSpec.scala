import org.scalatest._
import nominal.functors._
import nominal.lib._

class DataSpec extends FlatSpec {
  it should "generate enough scala types for the list example" in {
    @struct def ListT { Nil ; Cons(head, tail) }

    type List[+A] = Fix[({ type λ[+L] = ListF[A, L] })#λ]
    type ListF[+A, +L] = ListT[Nil, Cons[A, L]]

    def listF[A]: Traversable.Endofunctor {
      type Map[+L] = ListF[A, L]
    } = new Traversable.EndofunctorTrait {
      type Map[+L] = ListF[A, L]

      def traverse[M, N](G: Applicative)(f: M => G.Map[N]):
          Map[M] => G.Map[Map[N]] =
      {
        case Nil         => G.pure[Map[N]](Nil)
        case Cons(x, xs) => G.call(G.pure[N => Map[N]](ys => Cons(x, ys)), f(xs))
      }
    }

    // List is a synonym and has no companion object recognizable to scalac.
    // therefore the implicit conversion has to be outside.
    implicit class ListIsFoldable[A](xs: List[A]) {
      val patternF = listF[A]
      def fold[T](f: ListF[A, T] => T): T = f(patternF(xs.unroll) map (_ fold f))
    }

    val firstNinePrimes: List[Int] =
      coerce {
        Cons(2, Cons(3, Cons(5, Cons(7, Cons(11,
          Cons(13, Cons(17, Cons(19, Cons(23, Nil)))))))))
      }

    def sum(xs: List[Int]) = xs.fold[Int] {
      case Nil => 0
      case Cons(x, xs) => x + xs
    }

    val theSum = sum(firstNinePrimes)

    assert(theSum == 100)
    info("The sum of the first nine primes is " + theSum)
  }

  it should "permit tagging datatypes" in {
    trait A
    trait B[R, S, T]
    trait C
    @struct def TaggedT: A with B[Int, String, Boolean] with C = { Tagged }
    implicitly[TaggedT[Any] <:< A with B[Int, String, Boolean] with C]
  }
}
