import org.scalatest._
import nominal._
import nominal.lib._

class DataSpec extends FlatSpec {
  import language.implicitConversions
  import language.higherKinds

  // traits to be included in nominal.functor._

  trait Applicative[F[_]] {
    def pure[A](x: A): F[A]
    def call[A, B](f: F[A => B], x: F[A]): F[B]
  }

  // this may need to go into object Functor
  type ID[X] = X

  implicit object ID extends Applicative[ID] {
    def pure[A](x: A): A = x
    def call[A, B](f: A => B, x: A): B = f(x)
  }

  implicit class Foldable[F[+_]](t: Fix[F]) {
    def fold[T](f: F[T] => T)(implicit functor: FunctorOf[F]): T =
      f(functor.map[Fix[F], T](_.fold(f))(t.unroll))
  }

  trait Functor {
    type Map[+T]

    def map[A, B]: (A => B) => Map[A] => Map[B] = gcompos[ID].apply

    def gfoldl[A](default: A, combine: (A, A) => A): Map[A] => A = {
      type CA[X] = A
      gcompos[CA](new Applicative[CA] {
        def pure[X](x: X): A = default
        def call[X, Y](f: A, x: A): A = combine(f, x)
      })(identity)
    }

    def gcompos[F[_]: Applicative]: GCompos[F]

    abstract class GCompos[F[_]: Applicative] {
      def apply[A, B](f: A => F[B]): Map[A] => F[Map[B]]
    }
  }

  type FunctorOf[F[+_]] = Functor { type Map[T] = F[T] }

  // RecursivePolynomialFunctor is isomorphic to trait Functor.
  // It is friendlier to scalac 2.11.1's type inferencer than trait Functor.
  trait RecursivePolynomialFunctor {
    type Map[+T]

    // reinterpret `x` in the light of `Map` being a recursive polynomial functor
    def apply[A](x: Map[A]): RecursivePolynomial[A]

    trait RecursivePolynomial[A] {
      def gcompos[F[_]: Applicative]: GCompos[F]
      abstract class GCompos[F[_]](implicit protected[this] val applicative: Applicative[F]) {
        def apply[B](f: A => F[B]): F[Map[B]]
      }

      private[this] type CA[X] = A
      def map[B](f: A => B): Map[B] = gcompos[ID].apply(f)
      def gfoldl(default: A, combine: (A, A) => A): A = gcompos[CA](new Applicative[CA] {
        def pure[X](x: X): A = default
        def call[X, Y](f: A, x: A): A = combine(f, x)
      })(identity)
    }
  }



  "data macro" should "generate enough scala types for the case study" in {
    @datatype trait Term {
      Void
      Var(String)
      Abs(param = String, body = Term)
      App(Term, Term)
    }

    def void: Term = Roll[TermF](Void)
    implicit def _var(x: String): Term = Roll[TermF](Var(x))
    def abs(x: String, body: Term): Term = Roll[TermF](Abs(x, body))
    def app(f: Term, y: Term): Term = Roll[TermF](App(f, y))

    implicit val termF = new Functor {
      type Map[+T] = TermF[T]

      def gcompos[F[_]: Applicative] = new GCompos[F] {
        def apply[A, B](f: A => F[B]): Map[A] => F[Map[B]] = {
          val applicative = implicitly[Applicative[F]]
          import applicative._
          {
            case Void =>
              pure[Map[B]](Void)

            case Var(v) =>
              pure[Map[B]](Var(v))

            case Abs(x, t) =>
              call(
                call(
                  pure[String => B => Map[B]](x => t => Abs(x, t)),
                  pure[String](x)), // somehow type annotation is necessary here
                f(t))

            case App(t1, t2) =>
              call(
                call(
                  pure[B => B => Map[B]](t1 => t2 => App(t1, t2)),
                  f(t1)),
                f(t2))
          }
        }
      }
    }

    // @return (pretty-printed-string, precedence-of-top-level-operator)
    def prettyVisitor(t: Term) = new Foldable[TermF](t).fold[(String, Int)] {
      case Void =>
        ("()", Int.MaxValue)

      case Var(x) =>
        (x, Int.MaxValue)

      case Abs(x, b) =>
        (s"\\$x -> ${b._1}", Int.MinValue)

      case App(f, y) =>
        val myPrecedence = 9
        val leftTolerance = 9 // left associative
        val rightTolerance = 10
        def parenthesize(s: (String, Int), tolerance: Int): String =
          if (s._2 >= tolerance) s._1 else s"(${s._1})"
        val lhs = parenthesize(f, leftTolerance)
        val rhs = parenthesize(y, rightTolerance)
        (s"$lhs $rhs", myPrecedence)
    }

    def pretty(t: Term): String = prettyVisitor(t)._1

    val namesF = new Functor {
      private[this] type TF[+N] = {
        type λ[+T] = TermT[Void, Var[N], Abs[N, T], App[T, T]]
      }

      type Map[+N] = Fix[TF[N]#λ]

      def gcompos[F[_]: Applicative] = new GCompos[F] {
        def apply[A, B](f: A => F[B]): Map[A] => F[Map[B]] = {
          val applicative = implicitly[Applicative[F]]
          import applicative._
          _.unroll match {
            case Void =>
              pure(Roll[TF[B]#λ](Void))

            case Var(x) =>
              call(
                pure[B => Map[B]](x => Roll[TF[B]#λ](Var(x))),
                f(x))

            case Abs(x, b) =>
              call(
                call(
                  pure[B => Map[B] => Map[B]](x => b => Roll[TF[B]#λ](Abs(x, b))),
                  f(x)),
                apply(f)(b))

            case App(g, y) =>
              call(
                call(
                  pure[Map[B] => Map[B] => Map[B]](g => y => Roll[TF[B]#λ](App(g, y))),
                  apply(f)(g)),
                apply(f)(y))
          }
        }
      }
    }

    def prependUnderscore: Term => Term = namesF map ("_" + _)

    def freevars(t: Term): Set[String] =
      new Foldable[TermF](t).fold[Set[String]] {
        case Var(v) =>
          Set(v)

        case Abs(x, body) =>
          body - x

        case other =>
          termF.gfoldl[Set[String]](Set.empty, _ ++ _)(other)
      }

    def fresh(default: String, avoid: Set[String]): String = {
      var index = -1
      var y = default
      while (avoid(y)) {
        index += 1
        y = default + index
      }
      y
    }

    trait Bifunctor {
      type Bound1 // these bounds are for replacing variants wholesale.
      type Bound2 // we may need subtype bounds in trait Functor at some point, too.
      type Bimap[+T1 <: Bound1, +T2 <: Bound2]

      def bimap[A <: Bound1, B <: Bound2, C <: Bound1, D <: Bound2](f: A => C, g: B => D):
          Bimap[A, B] => Bimap[C, D] = bicompos[ID].apply(f, g)

      // bicompos: binary extrapolation of gcompos
      def bicompos[F[_]: Applicative]: Bicompos[F]

      abstract class Bicompos[F[_]: Applicative] {
        def apply
          [A <: Bound1, B <: Bound2, C <: Bound1, D <: Bound2]
          (f: A => F[C], g: B => F[D]):
            Bimap[A, B] => F[Bimap[C, D]]
      }
    }

    val avoidF = new Bifunctor {
      private[this] type H[+V, +A] = {
        type λ[+T] = TermT[Void, Var[V], A, App[T, T]]
      }

      type Bound1 = Any
      type Bound2 = Abs[_, _]

      type Bimap[+V, +A <: Abs[_, _]] = Fix[H[V, A]#λ]


      def bicompos[F[_]: Applicative]: Bicompos[F] = new Bicompos[F] {
        def apply
          [A, B <: Abs[_, _], C, D <: Abs[_, _]]
          (f: A => F[C], g: B => F[D]):
            Bimap[A, B] => F[Bimap[C, D]] =
        {
          val applicative = implicitly[Applicative[F]]
          import applicative._
          _.unroll match {
            case Void =>
              pure(Roll[H[C, D]#λ](Void))

            case Var(x) =>
              call(
                pure[C => Bimap[C, D]](x => Roll[H[C, D]#λ](Var(x))),
                f(x))

            case abs @ Abs(_, _) =>
              call(
                pure[D => Bimap[C, D]](abs => Roll[H[C, D]#λ](abs.asInstanceOf[H[C, D]#λ[Bimap[C, D]]])),
                g(abs.asInstanceOf[B])) // scalac's typing knowledge become weaker.

            case App(t1, t2) =>
              call(
                call(
                  pure[Bimap[C, D] => Bimap[C, D] => Bimap[C, D]](t1 => t2 => Roll[H[C, D]#λ](App(t1, t2))),
                  apply(f, g)(t1)),
                apply(f, g)(t2))
          }
        }
      }
    }

    val varF = new Functor {
      private[this] type H[+V] = {
        type λ[+T] = TermT[Void, Var[V], Abs[String, T], App[T, T]]
      }

      type Map[+V] = Fix[H[V]#λ]

      def gcompos[F[_]: Applicative] = new GCompos[F] {
        def apply[A, B](f: A => F[B]): Map[A] => F[Map[B]] = {
          val applicative = implicitly[Applicative[F]]
          import applicative._
          _.unroll match {
            case Void =>
              pure(Roll[H[B]#λ](Void))

            case Var(x) =>
              call(
                pure[B => Map[B]](x => Roll[H[B]#λ](Var(x))),
                f(x))

            case Abs(x, b) =>
              call(
                call(
                  pure[String => Map[B] => Map[B]](x => b => Roll[H[B]#λ](Abs(x, b))),
                  pure[String](x)),
                apply(f)(b))

            case App(t1, t2) =>
              call(
                call(
                  pure[Map[B] => Map[B] => Map[B]](t1 => t2 => Roll[H[B]#λ](App(t1, t2))),
                  apply(f)(t1)),
                apply(f)(t2))
          }
        }
      }
    }

    def avoidCapture(avoid: Set[String], alias: Map[String, String], t: Term): Term =
      avoidF.bimap(
        alias withDefault identity
          ,
        (abs: Abs[String, Term]) => {
          val Abs(x, body) = abs
          val y = fresh(x, avoid)
          if (x == y)
            Abs(x, avoidCapture(avoid, alias, body))
          else
            Abs(y, avoidCapture(avoid + y, alias + (x -> y), body))
        }
      )(t.asInstanceOf[avoidF.Bimap[String, Abs[String, Term]]]).asInstanceOf[Term]

    // capture-avoiding substitution
    def subst(x: String, xsub: Term, t: Term): Term =
      new Foldable[TermF](avoidCapture(freevars(xsub) + x, Map.empty, t)).fold[Term] {
        case Var(y) if x == y =>
          xsub

        case other =>
          Roll[TermF](other)
      }

    // USE

    // \x -> x
    val id = abs("x", "x")

    // (\x -> x) y
    val idy = app(id, "y")

    // \x -> f (x y)
    val f_xy = abs("x", app("f", app("x", "y")))

    // \y -> (f x) y
    val fx_y = abs("y", app(app("f", "x"), "y"))

    // \f -> f (\z -> ())
    val fzv = abs("f", app("f", abs("z", void)))

    def put (name: String, obj : Any ) = info(s"$name = $obj")
    def show(name: String, term: Term) = put(name, pretty(term))

    List(
      ("id", id), ("idy", idy), ("f_xy", f_xy), ("fx_y", fx_y),
      ("fzv", fzv)
    ).foreach {
      case (name, term) =>
        show(name, term)
        put(s"freevars($name)", freevars(term))
        show(s"prependUnderscore($name)", prependUnderscore(term))
        List(
          ("y", app("x", "x")),
          ("y", app("x", "y"))
        ).foreach {
          case (y, ysub) =>
            val s1 = subst(y, ysub, term)
            show(s"subst($y, ${pretty{ysub}}, $name)", s1)
        }
        info("")
    }

  }

  it should "generate enough scala types for the list example" in {
    // since GADT not surpported anyway, recursion is marked by name

    @datatype trait List[+A] { Nil ; Cons(A, tail = List) }

    // superclass of object List is nonsensical on purpose
    // it's there to test that attributes got passed around
    final case object List extends Set[Int] {
      // nonsensical implementation of Set[Int] interface
      def -(x: Int) = Set.empty
      def +(x: Int) = this - x
      def contains(x: Int) = false
      def iterator = Iterator.empty

      def patternFunctor[Elem] = new RecursivePolynomialFunctor {
        type Map[+T] = ListF[Elem, T]
        def apply[A](xs: Map[A]): RecursivePolynomial[A] = new RecursivePolynomial[A] {
          def gcompos[F[_]: Applicative]: GCompos[F] = new GCompos[F] {
            import applicative._
            def apply[B](f: A => F[B]): F[Map[B]] = xs match {
              case Nil => pure(Nil)
              case Cons(head, tail) =>
                call(
                  call(
                    pure[Elem => B => Map[B]](x => b => Cons(x, b)),
                    pure[Elem](head)),
                  f(tail))
            }
          }
        }
      }
    }

    // test that attributes of companion objects are passed around correctly
    (List: Set[Int]) match {
      case List => ()
    }

    // List is a synonym and has no companion object recognizable to scalac.
    // therefore the implicit conversion has to be outside.
    implicit class ListIsFoldable[A](xs: List[A]) {
      def fold[T](f: ListF[A, T] => T): T = f(List patternFunctor xs.unroll map (_ fold f))
    }

    val nil: List[Nothing] = Roll[({ type λ[+T] = ListF[Nothing, T] })#λ](Nil)
    def cons[A](x: A, xs: List[A]): List[A] = Roll[({ type λ[+T] = ListF[A, T] })#λ](Cons(x, xs))

    val firstNinePrimes: List[Int] =
      cons(2, cons(3, cons(5, cons(7, cons(11, cons(13, cons(17, cons(19, cons(23, nil)))))))))

    def sum(xs: List[Int]) = xs.fold[Int] {
      case Nil => 0
      case Cons(x, xs) => x + xs
    }

    val theSum = sum(firstNinePrimes)

    assert(theSum == 100)
    info("The sum of the first nine primes is " + theSum)
  }
}
