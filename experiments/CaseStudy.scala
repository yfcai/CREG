/** Case study:
  *
  * Datatype generic programming with maps and folds,
  * made feasible by nominal functor declarations
  *
  * Usage examples:
  *   - prepend "_" to all variable names
  *   - compute free variables
  *   - capture-avoiding substitution
  *
  * Functors in code that should be generated:
  *   def termF
  *   val namesF
  */


import language.{higherKinds, implicitConversions}

trait CaseStudy {

  // DATA DECLARATION

  /* User writes:

   sealed trait Term
   case class Void() extends Term
   case class Var(v: String) extends Term
   case class Abs(x: String, body: Term) extends Term
   case class App(f: Term, y: Term) extends Term

   */

  // System generates:

  sealed trait TermT[V, X, B, F, Y]
  case class Void[V, X, B, F, Y]() extends TermT[V, X, B, F, Y]
  case class Var[V, X, B, F, Y](v: V) extends TermT[V, X, B, F, Y]
  case class Abs[V, X, B, F, Y](x: X, body: B) extends TermT[V, X, B, F, Y]
  case class App[V, X, B, F, Y](f: F, y   : Y) extends TermT[V, X, B, F, Y]

  trait Functor {
    type Map[T]

    def map[A, B]: (A => B) => Map[A] => Map[B]

    def gfoldl[A](default: A, combine: (A, A) => A): Map[A] => A
  }

  type FunctorOf[F[_]] = Functor { type Map[T] = F[T] }

  sealed trait Fix[F[_]] {
    def unroll: F[Fix[F]]

    def fold[T](f: F[T] => T)(implicit functor: FunctorOf[F]): T =
      f(functor.map[Fix[F], T](_.fold(f))(unroll))
  }

  case class Roll[F[_]](unroll: F[Fix[F]]) extends Fix[F]
/*
  type TermF[V, X] = {
    type λ[T] = TermT[V, X, T, T, T]
  }

  type Term = Fix[TermF[String, String]#λ]

  // Eventually there will be constructor/destructor objects Void, Var, Abs, App.
  // For now, we use smart constructors.
  def void(): Term = Roll[TermF[String, String]#λ](Void())
  implicit def _var(x: String): Term = Roll[TermF[String, String]#λ](Var(x))
  def abs(x: String, body: Term): Term = Roll[TermF[String, String]#λ](Abs(x, body))
  def app(f: Term, y: Term): Term = Roll[TermF[String, String]#λ](App(f, y))

  implicit def termF[V, X] = new Functor {
    type Map[T] = TermT[V, X, T, T, T]

    def map[A, B]: (A => B) => Map[A] => Map[B] = f => {
      case Void() => Void()
      case Var(v) => Var(v)
      case Abs(x, t) => Abs(x, f(t))
      case App(t1, t2) => App(f(t1), f(t2))
    }

    def gfoldl[A](default: A, combine: (A, A) => A): Map[A] => A = {
      case Void() => default
      case Var(v) => default
      case Abs(x, t) => t
      case App(t1, t2) => combine(t1, t2)
    }
  }


  // USAGE: PRETTY PRINTING VISITOR

  /* User writes: */

  // @return (pretty-printed-string, precedence-of-top-level-operator)
  def prettyVisitor(t: Term) = t.fold[(String, Int)] {
    case Void() =>
      ("void", Int.MaxValue)

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
    type Map[T] = Fix[TermF[T, T]#λ]

    def map[A, B] = f => _.fold[Fix[TermF[B, B]#λ]] {
      case Void() => Roll[TermF[B, B]#λ](Void())
      case Var(v) => Roll[TermF[B, B]#λ](Var(f(v))) // f is called
      case Abs(x, b) => Roll[TermF[B, B]#λ](Abs(f(x), b)) // f is called
      case App(g, y) => Roll[TermF[B, B]#λ](App(g, y))
    }

    def gfoldl[A](nil: A, combine: (A, A) => A) = _.fold[A] {
      case Void() => nil
      case Var(v) => v
      case Abs(x, b) => combine(x, b)
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
        // System should infer type arguments of gfoldl
        // and keep [String, String] as the default type arguments of termF
        termF[String, String].gfoldl[Set[String]](Set.empty, _ ++ _)(other)
    }


  // USAGE: CAPTURE-AVOIDING SUBSTITUTION

  // User writes:

  // val substF = bifunctor( (V, A) => Term { Var = Var(V), Abs = A } )

  // System generates:

  trait Bifunctor {
    type Bimap[A, B]

    def bimap[A, B, C, D](f: A => C, g: B => D): Bimap[A, B] => Bimap[C, D]
  }

  val substF = new Bifunctor {
    type Bimap[A, B] = ???
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

  def put (name: String, obj : Any ) = println(s"$name = $obj")
  def show(name: String, term: Term) = put(name, pretty(term))

  List(("id", id), ("idy", idy), ("f_xy", f_xy), ("fx_y", fx_y)).foreach {
    case (name, term) =>
      show(name, term)
      put(s"freevars($name)", freevars(term))
      show(s"prependUnderscore($name)", prependUnderscore(term))
      println()
  }
 */
}
