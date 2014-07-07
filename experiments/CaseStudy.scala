/** Case study:
  *
  * Datatype generic programming with maps and folds,
  * made feasible by nominal functor declarations
  * and pseudo-equirecursive datatypes
  *
  * Usage examples:
  *
  *   - pretty printing visitor
  *   - prepend "_" to all variable names
  *   - compute free variables
  *   - capture-avoiding substitution
  *
  * Functors in code that should be generated:
  *
  *   - termF
  *   - namesF
  *   - varF
  *   - avoidF
  *
  * Implementation ideas of required features:
  *
  *   - macro system remembers structure of all datatypes
  *     in scope to generate map/bimap/trimap etc. as
  *     appropriate
  *
  *   - implicit macro tests equivalence of equirecursive
  *     types to know where to insert safe casts/conversions
  *
  *   - inline `fold` with a def macro to avoid covariance
  *     problem
  */


import language.{higherKinds, implicitConversions}

trait CaseStudy {
  trait Datatype

  // DATA DECLARATION

  /* User writes:

   datatype Term {
     Void()
     Var(String)
     Abs(param: String, body: Term)
     App(Term, Term)
   }

   */

  // System generates:

  // expanded shape template for datatype Term

  type ⊥ = Nothing

  sealed trait TermT[+Void, +Var, +Abs, +App] extends Datatype
  sealed trait Void extends TermT[Void, ⊥, ⊥, ⊥] // ill-founded inheritance
  case object Void extends Void
  sealed case class Var[+T1](_1: T1) extends TermT[⊥, Var[T1], ⊥, ⊥]
  sealed case class Abs[+Param, +Body](param: Param, body: Body) extends TermT[⊥, ⊥, Abs[Param, Body], ⊥]
  sealed case class App[+T1, +T2](_1: T1, _2: T2) extends TermT[⊥, ⊥, ⊥, App[T1, T2]]

  def dontcare = sys error "don't care"

  trait Applicative[F[_]] {
    def pure[A](x: A): F[A]
    def call[A, B](f: F[A => B], x: F[A]): F[B]
  }

  type ID[X] = X

  implicit object ID extends Applicative[ID] {
    def pure[A](x: A): A = x
    def call[A, B](f: A => B, x: A): B = f(x)
  }

  trait Functor {
    // mapping between objects (scala types)
    type Bound
    type Map[+T <: Bound]

    // reinterpret `x` in the light of `Map` being a recursive polynomial functor
    def apply[A <: Bound](x: Map[A]): RecursivePolynomial[A]

    trait RecursivePolynomial[A <: Bound] {
      // Nominal-functor-enabled generalization of `compos` in:
      //
      // Bringert and Ranta.
      // A pattern for almost compositional functions.
      //
      //
      // Let F be an applicative functor.
      //
      // gcompos[F] = gcompose[F] ∘ functor[Map].map, where
      //
      //   functor[Map].map : (A => B) => Map[A] => Map[B]
      //
      //   gcompose : ∀X. Map[F[X]] => F[Map[X]]
      //
      // gcompose is a natural transformation from Map ∘ F  to  F ∘ Map.
      // is it canonical in some way?

      // underlying type:  ∀ F : * → *.  ∀ A B.  (A → F B) → Map A → F (Map B)
      def gcompos[F[_]: Applicative, B <: Bound](f: A => F[B]): F[Map[B]]

      // `flip fmap`: mapping with morphisms, `compos` with identity applicative functor
      def map[B <: Bound](f: A => B): Map[B] = gcompos[ID, B](f)

      // projecting to the free monoid on `A`, `compos` with the functor mapping everything to A
      private[this] type CA[X] = A
      def gfoldl(default: A, combine: (A, A) => A): A =
        gcompos[CA, A](identity)(
          new Applicative[CA] {
            def pure[X](x: X): A = default
            def call[X, Y](f: A, x: A): A = combine(f, x)
          })
    }
  }

  // sugar
  type FunctorOf[F[+_]] = Functor { type Map[T] = F[T] ; type Bound = Any }

  // fixed point of functor, featuring ill-founded inheritance
  sealed trait Fix[+F[+_]] { def unroll: F[Fix[F]] }

  // cannot have case class Fix[F[_](unroll: Fix[F]) directly: illegal inheritance
  case class Roll[+F[+_]](unroll: F[Fix[F]]) extends Fix[F]

  // `fold` cannot be inside trait Fix, for it violates covariance.
  class Foldable[F[+_]: FunctorOf](t: Fix[F]) {
    def fold[T](f: F[T] => T): T =
      f(implicitly[FunctorOf[F]].apply(t.unroll).map[T](x => new Foldable(x) fold f))
  }

  // Term as the fixed point of the functor TermF

  // named here, because TermF is particularly important to users
  type TermF[+T] = TermT[Void, Var[String], Abs[String, T], App[T, T]]

  type Term = Fix[TermF]

  // Eventually there will be constructor/destructor objects Void, Var, Abs, App.
  // For now, we use smart constructors.
  def void: Term = Roll[TermF](Void)
  implicit def _var(x: String): Term = Roll[TermF](Var(x))
  def abs(x: String, body: Term): Term = Roll[TermF](Abs(x, body))
  def app(f: Term, y: Term): Term = Roll[TermF](App(f, y))

  val termF = new Functor {
    type Map[+X] = TermF[X]
    type Bound = Any

    def apply[A](t0: TermF[A]) = new RecursivePolynomial[A] {
      def gcompos[F[_]: Applicative, B](f: A => F[B]): F[Map[B]] = {
        val applicative = implicitly[Applicative[F]]
        import applicative._
        t0 match {
          case Void =>
            pure[Map[B]](Void)

          case Var(v) =>
            pure[Map[B]](Var(v))

          case Abs(x, t) =>
            call(
              call(
                pure[String => B => Map[B]](x => t => Abs(x, t)),
                pure[String](x)),
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

  implicit class TermIsFoldable(t: Term) extends Foldable[TermF](t)(termF)

  // USAGE: PRETTY PRINTING VISITOR

  /* User writes: */

  // @return (pretty-printed-string, precedence-of-top-level-operator)
  def prettyVisitor(t: Term) = t.fold[(String, Int)] {
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


  // USAGE: PREPEND "_" TO ALL VARIABLE NAMES

  // User writes:

  def prependUnderscore(t: Term): Term = namesF(t) map ("_" + _)

  // val namesF = functor( T => Term { Var(T) ; Abs(param = T) } )

  // System generates:

  val namesF = new Functor {
    namesF =>

    private[this] type TF[+N] = {
      type λ[+T] = TermT[Void, Var[N], Abs[N, T], App[T, T]]
    }

    type Bound = Any
    type Map[+N] = Fix[TF[N]#λ]

    def apply[A](x: Map[A]) = new RecursivePolynomial[A] {
      def gcompos[F[_]: Applicative, B](f: A => F[B]): F[Map[B]] = {
        val applicative = implicitly[Applicative[F]]
        import applicative._
        x.unroll match {
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
              namesF(b) gcompos f)

          case App(g, y) =>
            call(
              call(
                pure[Map[B] => Map[B] => Map[B]](g => y => Roll[TF[B]#λ](App(g, y))),
                namesF(g) gcompos f),
              namesF(y) gcompos f)
        }
      }
    }
  }


  // USAGE: COMPUTE FREE VARIABLES

  // User writes:

  def freevars(t: Term): Set[String] =
    t.fold[Set[String]] {
      case Var(v) =>
        Set(v)

      case Abs(x, body) =>
        body - x

      case other =>
        termF(other).gfoldl(Set.empty, _ ++ _)
    }


  // USAGE: CAPTURE-AVOIDING SUBSTITUTION

  // User writes:

  def fresh(default: String, avoid: Set[String]): String = {
    var index = -1
    var y = default
    while (avoid(y)) {
      index += 1
      y = default + index
    }
    y
  }

  // @param avoid   set of names to avoid
  //
  // @param alias   pending variable renamings
  //
  // @return        a term alpha-equivalent to renaming of t according to `alias`
  //                containing no bound or binding occurrence of names in `avoid`
  def avoidCapture(avoid: Set[String], alias: Map[String, String], t: Term): Term =
    avoidF(t.asInstanceOf[avoidF.Bimap[String, Abs[String, Term]]]).bimap(
      alias withDefault identity
        ,
      (abs: Abs[String, Term]) => {
        val Abs(x, body) = abs
        val y = fresh(x, avoid)
        if (x == y)
          Abs(x, avoidCapture(avoid, alias, body))
        else
          Abs(y, avoidCapture(avoid + y, alias + (x -> y), body))
      }).asInstanceOf[Term]
  // System should infer these casts, they are safe up to erasure:
  //
  //   Term               = μ T. TermT[Void, Var[String], Abs[String, T], App[T, T]]
  //
  //   avoidF.Bimap[V, A] = μ T. TermT[Void, Var[V],      A,              App[T, T]]
  //
  // Thus,
  //
  //   Term === avoidF.Bimap[String, Abs[String, Term]].
  //

  // capture-avoiding substitution
  def subst(x: String, xsub: Term, t: Term): Term =
    avoidCapture(freevars(xsub) + x, Map.empty, t).fold[Term] {
      case Var(y) if x == y =>
        xsub

      case other =>
        Roll[TermF](other) // System should roll automatically
    }

  // val avoidF = bifunctor( (V, A) => Term { Var = Var(V), Abs = A } )

  // val varF = functor( N => Term { Var(N) } )

  // System generates:

  trait Bifunctor {
    type Bound1 // these bounds are for replacing variants wholesale.
    type Bound2 // we may need subtype bounds in trait Functor at some point, too.
    type Bimap[+T1 <: Bound1, +T2 <: Bound2]

    def apply[A <: Bound1, B <: Bound2](t: Bimap[A, B]): RecursivePolynomial[A, B]

    trait RecursivePolynomial[A <: Bound1, B <: Bound2] {
      def bimap[C <: Bound1, D <: Bound2](f: A => C, g: B => D): Bimap[C, D] = bicompos[ID, C, D](f, g)

      // bicompos: binary extrapolation of gcompos
      def bicompos[F[_]: Applicative, C <: Bound1, D <: Bound2](f: A => F[C], g: B => F[D]): F[Bimap[C, D]]
    }
  }

  val avoidF = new Bifunctor {
    avoidF =>

    private[this] type H[+V, +A] = {
      type λ[+T] = TermT[Void, Var[V], A, App[T, T]]
    }

    type Bound1 = Any
    type Bound2 = Abs[_, _]

    type Bimap[+V, +A <: Abs[_, _]] = Fix[H[V, A]#λ]

    def apply[A, B <: Abs[_, _]](x: Bimap[A, B]) = new RecursivePolynomial[A, B] {
      def bicompos[F[_], C, D <: Abs[_, _]]
        (f: A => F[C], g: B => F[D])(implicit applicative: Applicative[F]): F[Bimap[C, D]] =
      {
        import applicative._
        x.unroll match {
          case Void =>
            pure(Roll[H[C, D]#λ](Void))

          case Var(x) =>
            call(
              pure[C => Bimap[C, D]](x => Roll[H[C, D]#λ](Var(x))),
              f(x))

          case abs @ Abs(_, _) =>
            call(
              pure[D => Bimap[C, D]](abs => Roll[H[C, D]#λ](abs.asInstanceOf[H[C, D]#λ[Bimap[C, D]]])),
              g(abs))

          case App(t1, t2) =>
            call(
              call(
                pure[Bimap[C, D] => Bimap[C, D] => Bimap[C, D]](t1 => t2 => Roll[H[C, D]#λ](App(t1, t2))),
                avoidF(t1) bicompos (f, g)),
              avoidF(t2) bicompos (f, g))
        }
      }
    }
  }

  val varF = new Functor {
    varF =>

    private[this] type H[+V] = {
      type λ[+T] = TermT[Void, Var[V], Abs[String, T], App[T, T]]
    }

    type Bound = Any
    type Map[+V] = Fix[H[V]#λ]

    def apply[A](x: Map[A]) = new RecursivePolynomial[A] {
      def gcompos[F[_]: Applicative, B](f: A => F[B]): F[Map[B]] = {
        val applicative = implicitly[Applicative[F]]
        import applicative._
        x.unroll match {
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
                pure(x)),
              varF(b) gcompos f)

          case App(t1, t2) =>
            call(
              call(
                pure[Map[B] => Map[B] => Map[B]](t1 => t2 => Roll[H[B]#λ](App(t1, t2))),
                varF(t1) gcompos f),
              varF(t2) gcompos f)
        }
      }
    }
  }
}

object CaseStudyApp extends CaseStudy with App {
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

  def put (name: String, obj : Any ) = println(s"$name = $obj")
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
      println()
  }
}
