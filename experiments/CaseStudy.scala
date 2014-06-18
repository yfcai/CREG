/** Case study:
  *
  * Datatype generic programming with maps and folds,
  * made feasible by nominal functor declarations
  * and equirecursive datatypes
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

  sealed trait TermT[+Void, +Var, +Abs, +App]
  sealed trait Void extends TermT[Void, ⊥, ⊥, ⊥] // ill-founded inheritance
  // case classes/objects should be final. For now they ain't, due to SI-4440.
  case object Void extends Void
  case class Var[+T1](_1: T1) extends TermT[⊥, Var[T1], ⊥, ⊥]
  case class Abs[+Param, +Body](param: Param, body: Body) extends TermT[⊥, ⊥, Abs[Param, Body], ⊥]
  case class App[+T1, +T2](_1: T1, _2: T2) extends TermT[⊥, ⊥, ⊥, App[T1, T2]]

  def dontcare = sys error "don't care"

  trait Functor {
    // mapping between objects (scala types)
    type Map[+T]

    // mapping between morphisms
    def map[A, B]: (A => B) => Map[A] => Map[B]

    // de-facto flattening projection to the free group A (i. e., Bag[A])
    // to supports SYBP-style gmapQ
    def gfoldl[A](default: A, combine: (A, A) => A): Map[A] => A
  }

  // sugar
  type FunctorOf[F[+_]] = Functor { type Map[T] = F[T] }

  // fixed point of functor, featuring ill-founded inheritance
  sealed trait Fix[+F[+_]] { def unroll: F[Fix[F]] }

  // cannot have case class Fix[F[_](unroll: Fix[F]) directly: illegal inheritance
  case class Roll[+F[+_]](unroll: F[Fix[F]]) extends Fix[F]

  // `fold` cannot be inside trait Fix, for it violates covariance.
  implicit class Foldable[F[+_]](t: Fix[F]) {
    def fold[T](f: F[T] => T)(implicit functor: FunctorOf[F]): T =
      f(functor.map[Fix[F], T](_.fold(f))(t.unroll))
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

  implicit val termF = new Functor {
    type Map[+T] = TermF[T]

    def map[A, B]: (A => B) => Map[A] => Map[B] = f => {
      case Void => Void
      case Var(v) => Var(v)
      case Abs(x, t) => Abs(x, f(t))
      case App(t1, t2) => App(f(t1), f(t2))
    }

    def gfoldl[A](default: A, combine: (A, A) => A): Map[A] => A = {
      case Void => default
      case Var(v) => default
      case Abs(x, t) => t
      case App(t1, t2) => combine(t1, t2)
    }
  }


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

  def prependUnderscore: Term => Term = namesF map ("_" + _)

  // val namesF = functor( T => Term { Var(T) ; Abs(x = T) } )

  // System generates:

  val namesF = new Functor {
    private[this] type TF[+N] = {
      type λ[+T] = TermT[Void, Var[N], Abs[N, T], App[T, T]]
    }

    private[this] implicit def tfF[N] = new Functor {
      type Map[+T] = TF[N]#λ[T]
      def map[A, B] = f => {
        case Void => Void
        case Var(v) => Var(v)
        case Abs(x, body) => Abs(x, f(body))
        case App(g, y) => App(f(g), f(y))
      }

      def gfoldl[A](default: A, combine: (A, A) => A) = dontcare
    }

    type Map[+N] = Fix[TF[N]#λ]

    // System should infer type argument of Foldable (scalac 2.11.0 can't)
    def map[A, B] =
      f => t => new Foldable[TF[A]#λ](t).fold[Fix[TF[B]#λ]] {
        case Void => Roll[TF[B]#λ](Void)
        case Var(v) => Roll[TF[B]#λ](Var(f(v))) // f is called
        case Abs(x, b) => Roll[TF[B]#λ](Abs(f(x), b)) // f is called
        case App(g, y) => Roll[TF[B]#λ](App(g, y))
      }

    // System should infer `new Foldable[...]`
    def gfoldl[A](default: A, combine: (A, A) => A) =
      t => new Foldable[TF[A]#λ](t).fold[A] {
        case Void => default
        case Var(v) => v
        case Abs(x, b) => combine(x, b) // tricky!
        case App(g, y) => combine(g, y)
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
        termF.gfoldl[Set[String]](Set.empty, _ ++ _)(other)
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
        // System should infer these casts, they are safe up to erasure.
    )(t.asInstanceOf[avoidF.Bimap[String, Abs[String, Term]]]).asInstanceOf[Term]

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

    def bimap[A <: Bound1, B <: Bound2, C <: Bound1, D <: Bound2](f: A => C, g: B => D):
        Bimap[A, B] => Bimap[C, D]
  }

  val avoidF = new Bifunctor {
    private[this] type F[+V, +A] = {
      type λ[+T] = TermT[Void, Var[V], A, App[T, T]]
    }

    private implicit def fF[V, A] = new Functor {
      type Map[+T] = F[V, A]#λ[T]

      def map[A, B] = f => {
        case Void => Void
        case Var(v) => Var(v)
        case Abs(x, b) => Abs(x, b)
        case App(g, y) => App(f(g), f(y))
      }

      def gfoldl[A](default: A, combine: (A, A) => A) = dontcare
    }

    type Bound1 = Any
    type Bound2 = Abs[_, _]

    type Bimap[+V, +A <: Abs[_, _]] = Fix[F[V, A]#λ]

    def bimap[A, B <: Abs[_, _], C, D <: Abs[_, _]](f: A => C, g: B => D): Bimap[A, B] => Bimap[C, D] =
      t => new Foldable[F[A, B]#λ](t).fold[Bimap[C, D]] {
        case Void => Roll[F[C, D]#λ](Void)
        case Var(v) => Roll[F[C, D]#λ](Var(f(v)))
        case abs @ Abs(_, _) => Roll[F[C, D]#λ](g(abs).asInstanceOf[F[C, D]#λ[Bimap[C, D]]])
        case App(g, y) => Roll[F[C, D]#λ](App(g, y))
      }
  }

  val varF = new Functor {
    private[this] type F[+V] = {
      type λ[+T] = TermT[Void, Var[V], Abs[String, T], App[T, T]]
    }

    implicit def patternFunctor[V] = new Functor {
      type Map[+T] = F[V]#λ[T]

      def map[A, B] = f => {
        case Void => Void
        case Var(v) => Var(v)
        case Abs(x, b) => Abs(x, f(b))
        case App(g, y) => App(f(g), f(y))
      }

      def gfoldl[A](default: A, combine: (A, A) => A) = dontcare
    }

    type Map[+V] = Fix[F[V]#λ]

    def map[A, B] = f => t => new Foldable[F[A]#λ](t).fold[Map[B]] {
      case Void => Roll[F[B]#λ](Void)
      case Var(v) => Roll[F[B]#λ](Var(f(v))) // f called
      case Abs(x, b) => Roll[F[B]#λ](Abs(x, b))
      case App(g, y) => Roll[F[B]#λ](App(g, y))
    }

    def gfoldl[A](default: A, combine: (A, A) => A): Map[A] => A =
      t => new Foldable[F[A]#λ](t).fold[A] {
        case Void => default
        case Var(v) => v
        case Abs(x, b) => b
        case App(g, y) => combine(g, y)
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
