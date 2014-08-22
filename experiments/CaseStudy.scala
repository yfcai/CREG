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

  // applicative functors
  trait Applicative {
    type Map[+X]
    def pure[A](x: A): Map[A]
    def call[A, B](f: Map[A => B], x: Map[A]): Map[B]
  }

  type IsApplicative[F[_]] = Applicative { type Map[X] = F[X] }

  type Identity[+X] = X

  implicit object Identity extends Applicative {
    type Map[+X] = Identity[X]
    def pure[A](x: A): A = x
    def call[A, B](f: A => B, x: A): B = f(x)
  }

  type Const[A] = { type λ[+X] = A }

  def Const[A](default: A, combine: (A, A) => A): Applicative { type Map[+X] = A } =
    new Applicative {
      type Map[+X] = A
      def pure[X](x: X): A = default
      def call[X, Y](f: A, x: A): A = combine(f, x)
    }

  // traversable functors
  // http://www.soi.city.ac.uk/~ross/papers/Applicative.pdf
  trait Traversable {
    // mapping between objects (scala types)
    type Cat // this is a functor from some full subcategory of Scala to the full subcategory induced by Map[Cat].
    type Map[+T <: Cat]

    def traverse[F[_]: IsApplicative, A <: Cat, B <: Cat](f: A => F[B], x: Map[A]): F[Map[B]]

    // reinterpret `x` in the light of `Map` being a traversable functor
    def apply[A <: Cat](x: Map[A]): View[A] = new View(x)

    // a value of type Map[A] supports almost-compositionality and map-reduce
    class View[A <: Cat](get: Map[A]) {
      def compos[F[_]: IsApplicative, B <: Cat](f: A => F[B]): F[Map[B]] = traverse(f, get)

      def map[B <: Cat](f: A => B): Map[B] = compos[Identity, B](f)

      def reduce(default: A, combine: (A, A) => A): A =
        compos[Const[A]#λ, A](identity)(
          new Applicative {
            type Map[+X] = A
            def pure[X](x: X): A = default
            def call[X, Y](f: A, x: A): A = combine(f, x)
          })
    }
  }


  // The category of all scala types is identical to the full subcategory
  // induced by `Any`, the supertype of all types. Since this category is
  // the biggest full subcategory, functors defined on it are endofunctors.
  trait TraversableEndofunctor extends Traversable { type Cat = Any }

  // sugar
  type IsTraversableEndofunctor[F[+_]] = TraversableEndofunctor { type Map[T] = F[T] }

  // fixed point of functor, featuring ill-founded inheritance
  sealed trait Fix[+F[+_]] { def unroll: F[Fix[F]] }

  // cannot have case class Fix[F[_](unroll: Fix[F]) directly: illegal inheritance
  case class Roll[+F[+_]](unroll: F[Fix[F]]) extends Fix[F]

  // `fold` cannot be inside trait Fix, for it violates covariance.
  class Foldable[F[+_]: IsTraversableEndofunctor](t: Fix[F]) {
    def fold[T](f: F[T] => T): T =
      f(implicitly[IsTraversableEndofunctor[F]].apply(t.unroll).map[T](x => new Foldable(x) fold f))
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

  val termF = new TraversableEndofunctor {
    type Map[+X] = TermF[X]

    def traverse[F[_]: IsApplicative, A, B](f: A => F[B], t0: Map[A]): F[Map[B]] = {
      val applicative = implicitly[IsApplicative[F]]
      import applicative.{pure, call}
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

  val namesF = new TraversableEndofunctor {
    namesF =>

    private[this] type TF[+N] = {
      type λ[+T] = TermT[Void, Var[N], Abs[N, T], App[T, T]]
    }

    type Map[+N] = Fix[TF[N]#λ]

    def traverse[F[_]: IsApplicative, A, B](f: A => F[B], x: Map[A]): F[Map[B]] = {
      val applicative = implicitly[IsApplicative[F]]
      import applicative.{pure, call}
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
            traverse(f, b))

        case App(g, y) =>
          call(
            call(
              pure[Map[B] => Map[B] => Map[B]](g => y => Roll[TF[B]#λ](App(g, y))),
              traverse(f, g)),
            traverse(f, y))
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
        termF(other) reduce (Set.empty, _ ++ _)
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
  def subst1(x: String, xsub: Term, t: Term): Term =
    avoidCapture(freevars(xsub) + x, Map.empty, t).fold[Term] {
      case Var(y) if x == y =>
        xsub

      case other =>
        Roll[TermF](other) // System should roll automatically
    }

  // alternative capture-avoiding substitution by monad
  def subst2(x: String, xsub: Term, t: Term): Term =
    varF.join(varF(avoidCapture(freevars(xsub) + x, Map.empty, t)).map {
      y => if (x == y) xsub else varF pure y
    })

  // val avoidF = bifunctor( (V, A) => Term { Var = Var(V), Abs = A } )

  // val varF = functor( N => Term { Var(N) } )

  // System generates:

  trait TraversableBifunctor {
    // due to subtyping, each scala type (or, each object in Scala category) induces a full subcategory.
    type Cat1 // full subcategory 1
    type Cat2 // full subcategory 2
    type Bimap[+T1 <: Cat1, +T2 <: Cat2]

    def traverse[F[+_]: IsApplicative, A <: Cat1, B <: Cat2, C <: Cat1, D <: Cat2]
      (f: A => F[C], g: B => F[D], x: Bimap[A, B]): F[Bimap[C, D]]

    def apply[A <: Cat1, B <: Cat2](x: Bimap[A, B]): View[A, B] = new View(x)

    class View[A <: Cat1, B <: Cat2](get: Bimap[A, B]) {
      def bicompos[F[+_]: IsApplicative, C <: Cat1, D <: Cat2]
        (f: A => F[C], g: B => F[D]): F[Bimap[C, D]] = traverse(f, g, get)

      def bimap[C <: Cat1, D <: Cat2](f: A => C, g: B => D): Bimap[C, D] = bicompos[Identity, C, D](f, g)
    }
  }

  val avoidF = new TraversableBifunctor {
    avoidF =>

    private[this] type H[+V, +A <: Abs[_, _]] = {
      type λ[+T] = TermT[Void, Var[V], A, App[T, T]]
    }

    type Cat1 = Any
    type Cat2 = Abs[_, _] // a named product subcategory of Scala

    type Bimap[+V, +A <: Abs[_, _]] = Fix[H[V, A]#λ]

    def traverse[F[+_], A, B <: Abs[_, _], C, D <: Abs[_, _]]
        (f: A => F[C], g: B => F[D], x: Bimap[A, B])(implicit applicative: IsApplicative[F]): F[Bimap[C, D]] =
    {
      import applicative._
      /*
       call(
       // the cast on g_abs is because scalac lacks the knowledge that
       //
       // ∀ A <: Abs[Any, Any].  ∃ B C.  A =:= Abs[B, C].
       //
       // and thus  A <: TermT[⊥, ⊥, A, ⊥].
       //
       // Declaring `case class Abs` as `final` does not help.
       //
       pure[D => Bimap[C, D]](g_abs => Roll[H[C, D]#λ](g_abs.asInstanceOf[H[C, D]#λ[Bimap[C, D]]])),
       g(abs))
       */

      // argData = fixedpoint rename mangleA
      type MA = Fix[({
        type λ[+T] = TermT[Void, Var[A], B, App[T, T]]
      })#λ]

      // mBData = fixedpoint rename mangleB
      type MB = Fix[({
        type λ[+T] = TermT[Void, Var[C], D, App[T, T]]
      })#λ]

      type PatternFunctor[+T] = TermT[Void, Var[C], D, App[T, T]]

      // mBData.body with `T` bound to `MB`
      type Unrolled = TermT[Void, Var[C], D, App[MB, MB]]

      // applicative.Map[mBType]
      type Result = F[MB]

      def recurse(mA: MA): Result =
        applicative.call(
          applicative.pure[Unrolled => MB](Roll.apply[PatternFunctor] _),
          mA.unroll match {
            case Void =>
              pure[Void](Void)

            case Var(x) =>
              call(
                pure[C => Unrolled](x => Var(x)),
                f(x))

            case App(t1, t2) =>
              call(
                call(
                  pure[MB => MB => Unrolled](t1 => t2 => App(t1, t2)),
                  recurse(t1)),
                recurse(t2))

            case abs @ Abs(_, _) =>
              // expect: F[Unrolled] = F[TermT[Void, Var[C], D, App[MB, MB]]]
              // has: F[D]
              // fail to deduce: D <: Unrolled
              val has: F[D] = g(abs)
              has.asInstanceOf[F[Unrolled]]
          }
        )

      recurse(x)
    }
  }

  trait TraversableMonad extends TraversableEndofunctor with Applicative {
    type Map[+X]

    def pure[A](x: A): Map[A]
    def join[A](x: Map[Map[A]]): Map[A]
    def traverse[F[_]: IsApplicative, A, B](f: A => F[B], x: Map[A]): F[Map[B]]

    def bind[A, B](m: Map[A], f: A => Map[B]): Map[B] = join(this(m) map f)
    def call[A, B](f: Map[A => B], x: Map[A]): Map[B] = bind[A => B, B](f, f => bind[A, B](x, x => pure(f(x))))

    override def apply[A](x: Map[A]): View[A] = new View(x)

    class View[A](get: Map[A]) extends super.View[A](get) {
      def flatMap[B](f: A => Map[B]): Map[B] = bind(get, f)
      // `map` is given by `traverse` already
      // if the monadic & traversable laws hold, then `map` defined in terms of `compos`
      // should be equal to `map` defined in terms of `bind` and `pure`.
    }
  }

  val varF = new  TraversableMonad {
    private[this] type H[+V] = {
      type λ[+T] = TermT[Void, Var[V], Abs[String, T], App[T, T]]
    }

    type Map[+V] = Fix[H[V]#λ]

    def pure[A](x: A): Map[A] = Roll[H[A]#λ](Var(x))

    def join[A](x: Map[Map[A]]): Map[A] = x.unroll match {
      case Void => Roll[H[A]#λ](Void)
      case Var(t) => t
      case Abs(x, b) => Roll[H[A]#λ](Abs(x, join(b)))
      case App(t1, t2) => Roll[H[A]#λ](App(join(t1), join(t2)))
    }

    def traverse[F[_]: IsApplicative, A, B](f: A => F[B], x: Map[A]): F[Map[B]] = {
      val ap = implicitly[IsApplicative[F]]
      x.unroll match {
        case Void =>
          ap.pure(Roll[H[B]#λ](Void))

        case Var(x) =>
          ap.call(
            ap.pure[B => Map[B]](x => Roll[H[B]#λ](Var(x))),
            f(x))

        case Abs(x, b) =>
          ap.call(
            ap.call(
              ap.pure[String => Map[B] => Map[B]](x => b => Roll[H[B]#λ](Abs(x, b))),
              ap.pure(x)),
            traverse(f, b))

        case App(t1, t2) =>
          ap.call(
            ap.call(
              ap.pure[Map[B] => Map[B] => Map[B]](t1 => t2 => Roll[H[B]#λ](App(t1, t2))),
              traverse(f, t1)),
            traverse(f, t2))
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
          val s1 = subst1(y, ysub, term)
          val s2 = subst2(y, ysub, term)
          show(s"subst1($y, ${pretty{ysub}}, $name)", s1)
          show(s"subst2($y, ${pretty{ysub}}, $name)", s2)
      }
      println()
  }
}
