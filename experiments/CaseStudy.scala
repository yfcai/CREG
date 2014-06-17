/** Case study:
  *
  * Datatype generic programming with maps and folds,
  * made feasible by nominal functor declarations
  *
  * Examples: search for "val namesF"
  */


import language.higherKinds

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

    def fmap[A, B]: (A => B) => Map[A] => Map[B]

    def gfoldl[A](default: A, combine: (A, A) => A): Map[A] => A
  }

  type FunctorOf[F[_]] = Functor { type Map[T] = F[T] }

  sealed trait Fix[F[_]] {
    def unroll: F[Fix[F]]

    def fold[T](f: F[T] => T)(implicit functor: FunctorOf[F]): T =
      f(functor.fmap[Fix[F], T](_.fold(f))(unroll))
  }

  case class Roll[F[_]](unroll: F[Fix[F]]) extends Fix[F]

  type TermF[V, X] = {
    type λ[T] = TermT[V, X, T, T, T]
  }

  type Term = Fix[TermF[String, String]#λ]

  implicit def FunctorTermF[V, X] = new Functor {
    type Map[T] = TermF[V, X]#λ[T]

    def fmap[A, B]: (A => B) => Map[A] => Map[B] = f => {
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

  type TermQ[R] = TermT[R, R, R, R, R]


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
      def paren(s: (String, Int), tolerance: Int): String =
        if (s._2 >= tolerance) s._1 else s"(${s._1})"
      (s"${paren(f, leftTolerance)} ${paren(y, rightTolerance)}", myPrecedence)
  }

  def pretty(t: Term): String = prettyVisitor(t)._1


  // USAGE: PREPEND "_" TO ALL VARIABLE NAMES

  // User writes:

  def prependUnderscore: Term => Term = namesF fmap ("_" + _)

  // val namesF = functor( T => Term { Var(T) ; Abs(T, _) } )

  // System generates:

  val namesF = new Functor {
    type Map[T] = Fix[TermF[T, T]#λ]

    def fmap[A, B] = f => _.fold[Fix[TermF[B, B]#λ]] {
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
    // System should infer argument type of the first argument of fmap
    varsF.fmap( (x: String) => Set(x) )(t).
      fold[Set[String]] {
        case Abs(x, body) =>
          body - x

        case other =>
          // System should infer type arguments of gfoldl
          varsTF.gfoldl[Set[String]](Set.empty, _ ++ _)(other)
      }

  // val varsF = functor( T => Term { Var(T) } )

  // val varsTF = functor( T => TermF[T] { Var(T) }

  // System generates:

  val varsF = new Functor {
    type Map[T] = Fix[TermF[T, String]#λ]

    def fmap[A, B] = f => _.fold[Fix[TermF[B, String]#λ]] {
      case Void() => Roll[TermF[B, String]#λ](Void())
      case Var(v) => Roll[TermF[B, String]#λ](Var(f(v))) // f is called
      case Abs(x, b) => Roll[TermF[B, String]#λ](Abs(x, b))
      case App(g, y) => Roll[TermF[B, String]#λ](App(g, y))
    }

    def gfoldl[A](nil: A, combine: (A, A) => A) = _.fold[A] {
      case Void() => nil
      case Var(v) => v
      case Abs(x, b) => b
      case App(g, y) => combine(g, y)
    }
  }

  val varsTF = new Functor {
    type Map[T] = TermF[T, String]#λ[T]

    def fmap[A, B] = f => {
      case Void() => Void()
      case Var(v) => Var(f(v))
      case Abs(x, b) => Abs(x, f(b))
      case App(g, y) => App(f(g), f(y))
    }

    def gfoldl[A](nil: A, combine: (A, A) => A) = {
      case Void() => nil
      case Var(v) => v
      case Abs(x, b) => b
      case App(g, y) => combine(g, y)
    }
  }
}

object CaseStudyApp extends CaseStudy with App {
  // it's pretty annoying to write terms right now.
  // Björn's macro contains something to make it less annoying.
  // Under that technique, one would write
  //
  // val id = Abs("x", Var("x"))
  // val idy = App(id, Var("y"))
  // val f_xy = Abs("x", App(Var("f"), App(Var("x"), Var("y"))))
  // val fx_y = Abs("x", App(App(Var("f"), Var("x")), Var("y")))

  type TF[X] = TermF[String, String]#λ[X]

  // \x -> x
  val id: Term = Roll[TF](Abs("x", Roll[TF](Var("x"))))

  // (\x -> x) y
  val idy: Term = Roll[TF](App(id, Roll[TF](Var("y"))))

  // \x -> f (x y)
  val f_xy: Term = Roll[TF](Abs("x",
    Roll[TF](App(Roll[TF](Var("f")), Roll[TF](App(Roll[TF](Var("x")), Roll[TF](Var("y"))))))))

  // \x -> (f x) y
  val fx_y: Term = Roll[TF](Abs("x",
    Roll[TF](App(Roll[TF](App(Roll[TF](Var("f")), Roll[TF](Var("x")))), Roll[TF](Var("y"))))))

  def put (name: String, obj : Any ) = println(s"$name = $obj")
  def show(name: String, term: Term) = put(name, pretty(term))

  List(("id", id), ("idy", idy), ("f_xy", f_xy), ("fx_y", fx_y)).foreach {
    case (name, term) =>
      show(name, term)
      put(s"freevars($name)", freevars(term))
      show(s"prependUnderscore($name)", prependUnderscore(term))
      println()
  }
}
