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


import language.{higherKinds, implicitConversions, existentials}

trait CaseStudy {
  // DATA DECLARATION

  /* User writes:

   datatype Term {
     Void()
     Var(name =String)
     Abs(param = String, body = Term)
     App(operator = Term, operand = Term)
   }

   */

  // System generates:

  // expanded shape template for datatype Term

  class HashMe(private val child: Any) extends Serializable {
    override def toString: String = s"${getClass.getSimpleName}$child"

    override def hashCode: Int =
      util.hashing.MurmurHash3.mix(getClass.hashCode, child.hashCode)

    override def equals(that: Any) = that match {
      case that: HashMe =>
        this.getClass == that.getClass & this.child == that.child

      case _ =>
        false
    }
  }

  trait Curried[F[_]] {
    def apply[T](x: T): F[T]
    def curried[T]: T => F[T] = apply _
  }

  object Tuple2 {
    def curried[A, B]: A => B => (A, B) = x => y => (x, y)
    def andThen[A, B, C](f: ((A, B)) => C): A => B => C = x => y => f((x, y))
  }

  type ⊥ = Nothing

  sealed trait TermT[+Void, +Var, +Abs, +App]

  sealed trait Void extends TermT[Void, ⊥, ⊥, ⊥]
  case object Void extends Void

  sealed case class Var[+T1](name: T1) extends TermT[⊥, Var[T1], ⊥, ⊥]
  object Var extends Curried[Var]

  sealed class Abs[+Get](val get: Get) extends HashMe(get) with TermT[⊥, ⊥, Abs[Get], ⊥]

  object Abs extends Curried[Abs] {
    def apply[T](get: T): Abs[T] = new Abs(get)
    def apply[A, B](param: A, body: B): Abs[(A, B)] = new Abs((param, body))
    def unapply[T](abs: Abs[T]): Option[T] = Some(abs.get)
  }

  sealed class App[+Get](val get: Get) extends HashMe(get) with TermT[⊥, ⊥, ⊥, App[Get]]
  object App extends Curried[App] {
    def apply[T](get: T): App[T] = new App(get)
    def apply[A, B](f: A, x: B): App[(A, B)] = App((f, x))
    def unapply[T](app: App[T]): Option[T] = Some(app.get)
  }

  // smart/default constructors
  implicit def whateverToVar[T](x: T): Var[T] = Var(x)
  val abs = Abs.apply[String, Term] _
  val app = App.apply[Term, Term] _

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

  def Const[A](default: A, combine: (A, A) => A): IsApplicative[Const[A]#λ] =
    new Applicative {
      type Map[+X] = A
      def pure[X](x: X): A = default
      def call[X, Y](f: A, x: A): A = combine(f, x)
    }

  // traversable functors
  // http://www.soi.city.ac.uk/~ross/papers/Applicative.pdf
  trait Traversable {
    traversableTrait =>

    // mapping between objects (scala types)
    type Map[+T]

    def traverse[A, B](G: Applicative)(f: A => G.Map[B]): Map[A] => G.Map[Map[B]]

    def map[A, B](f: A => B): Map[A] => Map[B] = traverse(Identity)(f)

    implicit class Foldable(t0: Fix[Map]) {
      def fold[T](f: Map[T] => T): T = {
        new (Fix[Map] => T) {
          def apply(t: Fix[Map]): T = f(map(this)(t))
        } apply t0
      }
    }

    // reinterpret `x` in the light of `Map` being a traversable functor
    def apply[A](x: Map[A]): View[A] = new View(x)

    // a value of type Map[A] supports almost-compositionality and map-reduce
    class View[A](self: Map[A]) {
      def traverse[B](G: Applicative)(f: A => G.Map[B]): G.Map[Map[B]] =
        traversableTrait.traverse(G)(f)(self)

      // traversal with respect to the identity functor
      def map[B](f: A => B): Map[B] = traversableTrait.map(f)(self)

      // traversal with respect to a constant functor
      def mapReduce[B](f: A => B)(default: B, combine: (B, B) => B): B =
        traverse(Const(default, combine))(f)

      def reduce(default: A, combine: (A, A) => A): A =
        mapReduce[A](identity)(default, combine)
    }
  }

  // sugar
  type IsTraversable[F[+_]] = Traversable { type Map[T] = F[T] }

  type Fix[+F[+_]] = F[fixedPoint] forSome { type fixedPoint <: F[fixedPoint] }

  // Term as the fixed point of the functor TermF

  // named here, because TermF is particularly important to users
  type TermF[+T] = TermT[Void, Var[String], Abs[(String, T)], App[(T, T)]]

  type Term = Fix[TermF]

  object TermF extends Traversable {
    type Map[+X] = TermF[X]

    def traverse[A, B](G: Applicative)(f: A => G.Map[B]): Map[A] => G.Map[Map[B]] = {
      case Void =>
        G.pure(Void)

      case Var(v) =>
        G.pure(Var(v))

      case Abs(x, t) =>
        G.call(
          G.call(
            G.pure[String => B => Map[B]](x => t => Abs(x, t)),
            G.pure(x)),
          f(t))

      case App(t1, t2) =>
        G.call(
          G.call(
            G.pure[B => B => Map[B]](t1 => t2 => App(t1, t2)),
            f(t1)),
          f(t2))
    }
  }


  // USAGE: PRETTY PRINTING VISITOR

  /* User writes: */

  import TermF.Foldable

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

  val namesF = new Traversable {
    private[this] type MapF[+N, +T] = TermT[Void, Var[N], Abs[(N, T)], App[(T, T)]]

    type Map[+N] = MapF[N, T] forSome { type T <: MapF[N, T] }

    def traverse[A, B](G: Applicative)(f: A => G.Map[B]): Map[A] => G.Map[Map[B]] = {
      case Void =>
        G pure Void

      case Var(x) =>
        G.call(
          G.pure(Var.curried[B]),
          f(x))

      case Abs(x, b) =>
        G.call(
          G.call(
            G.pure(Tuple2.andThen[B, Map[B], Map[B]](Abs.curried)),
            f(x)),
          traverse(G)(f)(b))

      case App(g, y) =>
        G.call(
          G.call(
            G.pure(Tuple2.andThen[Map[B], Map[B], Map[B]](App.curried)),
            traverse(G)(f)(g)),
          traverse(G)(f)(y))
    }
  }


  // USAGE: COMPUTE FREE VARIABLES

  // User writes:

  def freevars(t: Term): Set[String] =
    avoidF(t).mapReduce[Set[String]](
      x => Set(x),
      { case (x, body) => freevars(body) - x }
    )(Set.empty, _ ++ _)


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
  def avoidCapture(alias: Map[String, String], t: Term): Term = {

    val rawResult: avoidF.Map[String, (String, Term)] =
      avoidF[String, (String, Term)](t).map (
        alias withDefault identity,
        {
          case (x, body) =>
            val avoid = freevars(body) & alias.keySet
            if (avoid.nonEmpty) {
              val y = fresh(x, avoid)
              (y, avoidCapture(alias updated (x, y), body))
            }
            else
              (x, avoidCapture(alias, body))
        })

    // SCALA-BUG

    // without defining a result of type `Any` and doing a cast,
    // scalac will crash with StackOverflowError.

    // uncomment for stack overflow:
    // (rawResult: Term)

    // However, that `avoidF(t)` typechecks means that Scalac *can*
    // prove, in finite time, that
    // Term <:< avoidF.Map[String, (String, Term)].

    val result: Any = rawResult

    result.asInstanceOf[Term]
  }

  // capture-avoiding substitution
  def subst1(x: String, xsub: Term, t: Term): Term = {
    val avoid = freevars(xsub) + x
    val alias = Map.empty[String, String] ++ avoid.zip(avoid)
    avoidCapture(alias, t).fold[Term] {
      case Var(y) if x == y =>
        xsub

      case other =>
        other: Term // rejected by scalac without ascription
    }
  }

  // alternative capture-avoiding substitution by monad
  def subst2(x: String, xsub: Term, t: Term): Term = {
    val avoid = freevars(xsub) + x
    val alias = Map.empty[String, String] ++ avoid.zip(avoid)
    varF.join(varF(avoidCapture(alias, t)).map {
      y => if (x == y) xsub else varF pure y
    })
  }


  // val avoidF = bifunctor( (V, A) => Term { Var = Var(V), Abs = A } )

  // val varF = functor( N => Term { Var(N) } )

  // System generates:

  trait Traversable2 {
    type Map[+T1, +T2]

    def traverse[A, B, C, D](G: Applicative)(f: A => G.Map[C], g: B => G.Map[D]):
        Map[A, B] => G.Map[Map[C, D]]

    def map[A, B, C, D](f: A => C, g: B => D): Map[A, B] => Map[C, D] = traverse(Identity)(f, g)

    def mapReduce[A, B, T](f: A => T, g: B => T)(default: T, combine: (T, T) => T):
        Map[A, B] => T =
      traverse(Const(default, combine))(f, g)

    def apply[A, B](x: Map[A, B]): View[A, B] = new View(x)

    class View[A, B](t0: Map[A, B]) {
      def traverse[C, D](G: Applicative)(f: A => G.Map[C], g: B => G.Map[D]):
          G.Map[Map[C, D]] =
        Traversable2.this.traverse(G)(f, g)(t0)

      def map[C, D](f: A => C, g: B => D): Map[C, D] = Traversable2.this.map(f, g)(t0)

      def mapReduce[T](f: A => T, g: B => T)(default: T, combine: (T, T) => T): T =
        Traversable2.this.mapReduce(f, g)(default, combine)(t0)
    }
  }

  val avoidF = new Traversable2 {
    private[this] type H[+V, +A] = {
      type λ[+T] = TermT[Void, Var[V], Abs[A], App[(T, T)]]
    }

    type Map[+V, +A] = Fix[H[V, A]#λ]

    def traverse[A, B, C, D](G: Applicative)(f: A => G.Map[C], g: B => G.Map[D]):
        Map[A, B] => G.Map[Map[C, D]] = {
      case Void =>
        G pure Void

      case Var(x) =>
        G.call(
          G.pure(Var.curried[C]),
          f(x))

      case Abs(get) =>
        G.call(
          G.pure(Abs.curried[D]),
          g(get))

      case App(op, arg) =>
        G.call(G.call(
          G.pure(Tuple2.andThen[Map[C, D], Map[C, D], Map[C, D]](App.curried)),
          traverse(G)(f, g)(op)),
          traverse(G)(f, g)(arg))
    }
  }

  trait TraversableMonad extends Traversable with Applicative {
    type Map[+X]

    def pure[A](x: A): Map[A]
    def join[A](x: Map[Map[A]]): Map[A]
    def traverse[A, B](G: Applicative)(f: A => G.Map[B]): Map[A] => G.Map[Map[B]]

    def bind[A, B](m: Map[A], f: A => Map[B]): Map[B] = join(this(m) map f)
    def call[A, B](f: Map[A => B], x: Map[A]): Map[B] =
      bind[A => B, B](f, f => bind[A, B](x, x => pure(f(x))))

    override def apply[A](x: Map[A]): View[A] = new View(x)

    class View[A](get: Map[A]) extends super.View[A](get) {
      def flatMap[B](f: A => Map[B]): Map[B] = bind(get, f)
      // `map` is given by `traverse` already
      // if the monadic & traversable laws hold, then `map` defined in terms of `compos`
      // should be equal to `map` defined in terms of `bind` and `pure`.
    }
  }

  val varF = new  TraversableMonad {
    private[this]
    type H[+V, +T] = TermT[Void, Var[V], Abs[(String, T)], App[(T, T)]]

    type Map[+V] = H[V, T] forSome { type T <: H[V, T] }

    def pure[A](x: A): Map[A] = Var(x)

    def join[A](x: Map[Map[A]]): Map[A] = x match {
      case Void => Void
      case Var(t) => t
      case Abs(x, b) => Abs(x, join(b))
      case App(t1, t2) =>

        // SCALA-BUG

        // App(join(t1), join(t2)): Map[A] // does not work
        // The 2-step ascription is necessary.
        // Thus, scala ascription is not transitive.
        (App(join(t1), join(t2)):
            TermT[Void, Var[A], Abs[(String, Map[A])], App[(Map[A], Map[A])]]
        ): Map[A]
    }

    def traverse[A, B](G: Applicative)(f: A => G.Map[B]): Map[A] => G.Map[Map[B]] = {
      case Void =>
        G pure Void

      case Var(x) =>
        G call (G pure Var.curried[B], f(x))

      case Abs(x, body) =>
        G call (G call (
          G pure Tuple2.andThen[String, Map[B], Map[B]](Abs.curried),
          G pure x),
          traverse(G)(f)(body))

      case App(op, arg) =>
        G call (G call (
          G pure Tuple2.andThen[Map[B], Map[B], Map[B]](App.curried),
          traverse(G)(f)(op)),
          traverse(G)(f)(arg))
    }
  }
}

object CaseStudyApp extends CaseStudy with App {
  // \x -> x
  val id: Term = abs("x", "x")

  // (\x -> x) y
  val idy: Term = app(id, "y")

  // \x -> f (x y)
  val f_xy: Term = abs("x", app("f", app("x", "y")))

  // \y -> (f x) y
  val fx_y: Term = abs("y", app(app("f", "x"), "y"))

  // \f -> f (\z -> ())
  val fzv: Term = abs("f", app("f", abs("z", Void)))

  def put (name: String, obj : Any ) = println(s"$name = $obj")
  def show(name: String, term: Term) = put(name, pretty(term))

  List[(String, Term)](
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
