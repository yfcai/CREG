/** Alternative console demo script for:
  *
  * Bringert and Ranta.
  * A pattern for almost compositional functions.
  *
  * The type of Exp is different.
  */

import language.higherKinds
import language.implicitConversions
import nominal.functors._
import nominal.lib._
import nominal.lib.Applicative._

object Compos {
  import Banana.{List, Nil, Cons}

  @data def Var = V(name = String)
  // @data is shorthand for:
  // @struct def <anonymous> { V(name = String) }
  // type Var = V[String]


  @struct def StmT { Assign(lhs, rhs) ; Return(exp) }
  type StmF[Exp] = StmT[Assign[Var, Exp], Return[Exp]]
  type Stm       = StmF[Exp]
  // Alternatively:
  // @data def Stm = StmT { Assign(lhs = Var, rhs = Exp) ; Return(exp = Exp) }

  @data def Exp = Fix(exp => ExpT {
    Ident(x = Var)
    Abs(param = Var, body = exp)
    App(op = exp, arg = exp)
    Block(stms = List[StmF[exp]])
  })

  implicit def stringToVar(x: String): Var = V(x)
  implicit def stringToFixExp(x: String): Exp = coerce { Ident(x) }

  val fst: Exp = coerce { Abs("x", Abs("y", "x")) }

  sealed trait Syntactic[_]
  implicit case object Exp extends Syntactic[Exp]
  implicit case object Stm extends Syntactic[Stm]
  implicit case object Var extends Syntactic[Var]

  // operation on the entire type family
  // T[_]: type family
  // G[_]: the applicative functor
  trait Op[T[_], G[_]] {
    def apply[A: T](x: A): G[A]

    // to cope with dependent types
    def etaExpand[A: T]: A => G[A] = x => apply(x)
  }

  trait Compos[Family[_]] {
    def compos[A: Family](G: Applicative)(f: Op[Family, G.Map], data: A): G.Map[A]
  }

  def composOp[T[_]: Compos, A: T](f: Op[T, Identity], data: A): A =
    implicitly[Compos[T]].compos[A](Identity)(f, data)

  // monoid; it's a trait and not a case class for presentation's sake.
  trait Monoid[O] {
    def empty: O
    def plus(x: O, y: O): O
  }

  implicit def monadOfUnitIsMonoid[M[+_]: Monad.ic]: Monoid[M[Unit]] = new Monoid[M[Unit]] {
    val monad = implicitly[Monad.ic[M]]
    def empty: M[Unit] = monad.pure(())
    def plus(x: M[Unit], y: M[Unit]): M[Unit] = monad.bind[Unit, Unit](x, _ => y)
  }

  def composFold[T[_]: Compos, C: T, O: Monoid](f: Op[T, Const[O]#λ], data: C): O = {
    val constF = Const(implicitly[Monoid[O]].empty, implicitly[Monoid[O]].plus)
    implicitly[Compos[T]].compos(constF)(f, data)
  }

  def composM[T[_]: Compos, M[+_]: Monad.ic, A: T](f: Op[T, M], data: A): M[A] =
    implicitly[Compos[T]].compos(implicitly[Monad.ic[M]])(f, data)

  def composM_[T[_]: Compos, M[+_]: Monad.ic, A: T](f: Op[T, Const[M[Unit]]#λ], data: A): M[Unit] =
    composFold(f, data)

  implicit val composSyntactic: Compos[Syntactic] = new Compos[Syntactic] {
    @functor def expC[exp, stm, _var] = ExpT {
      Ident(x = _var)
      Abs(param = _var, body = exp)
      App(operator = exp, operand = exp)
      Block(stms = List apply stm)
    }

    @functor def stmC[exp, _var] = StmT {
      Assign(lhs = _var, rhs = exp)
      Return(exp = exp)
    }

    def compos[A: Syntactic](G: Applicative)(f: Op[Syntactic, G.Map], syntax: A): G.Map[A] =
      implicitly[Syntactic[A]] match {
        case Exp =>
          G.roll[ExpF] {
            expC(syntax.unroll).traverse(G)(
              f.etaExpand[Exp],
              f.etaExpand[Stm],
              f.etaExpand[Var])
          }

        case Stm =>
          stmC(syntax).traverse(G)(
            f.etaExpand[Exp],
            f.etaExpand[Var])

        case Var =>
          G pure syntax
      }
  }

  val prependUnderscore: Op[Syntactic, Identity] = new  Op[Syntactic, Identity] {
    def apply[A: Syntactic](syntax: A): A = implicitly[Syntactic[A]] match {
      // Type variable `A` is refined to `Var` in this case.
      case Var =>
        V("_" + syntax.name)

      case other =>
        composOp(this, syntax)
    }
  }

  @functor def nameExpInStmF[name, exp] = StmT {
    Assign(lhs = V apply name, rhs = exp)
    Return(exp = exp)
  }

  @functor def nameF[name] = Fix(exp => ExpT {
    Ident(x = V apply name)
    Abs(param = V apply name, body = exp)
    App(op = exp, arg = exp)
    Block(stms = List apply (nameExpInStmF apply (name, exp)))
  })

  def prependUnderscore2(e: Exp): Exp = nameF(e) map ("_" + _)


  // MAKE NAMES GLOBALLY UNIQUE //

  private[this] // necessary to make inner type λ covariant
  type State[S] = {
    type λ[+A] = S => (A, S)
  }

  implicit def stateMonad[S] = new MonadWithBind {
    type Map[+A] = State[S]#λ[A]
    def pure[A](x: A): Map[A] = s => (x, s)
    def bind[A, B](m: Map[A], f: A => Map[B]): Map[B] =
      s0 => m(s0) match { case (a, s1) => f(a)(s1) }
  }

  implicit class StateMonadView[A, S](x: State[S]#λ[A]) extends Monad.View[State[S]#λ, A](x)

  def readState[S]: State[S]#λ[S] = s => (s, s)
  def writeState[S](s: S): State[S]#λ[Unit] = _ => ((), s)
  def evalState[S, A](sm: State[S]#λ[A], s: S): A = sm(s)._1

  // infinite lists of hopefully fresh names
  type Names = Stream[String]

  def getNameStream: Names = Stream from 0 map ("_" + _)

  // substitution defined by an association sequence
  type Subst = collection.immutable.Map[String, String]

  object Subst {
    def empty: Subst =
      collection.immutable.Map.empty[String, String].withDefault(identity)
  }

  def fresh(e: Exp): Exp = {
    import Monad._

    def f(subst: Subst): Op[Syntactic, State[Names]#λ] = new Op[Syntactic, State[Names]#λ] {
      def apply[A: Syntactic](e: A): State[Names]#λ[A] =
        implicitly[Syntactic[A]] match {
          case Var =>
            stateMonad[Names].pure(V(subst(e.name)))

          case Exp => e.unroll match {
            case Abs(V(x), b) =>
              for {
                freshNames <- readState[Names]
                _ <- writeState(freshNames.tail)
                x2 = freshNames.head
                b2 <- f(subst updated (x, x2))(b)
              }
              yield coerce { Abs(V(x2), b2) }: Exp

            case _ =>
              composM[Syntactic, State[Names]#λ, A](this, e)
          }

          case _ =>
            composM[Syntactic, State[Names]#λ, A](this, e)
        }
    }

    evalState(f(Subst.empty)(e), getNameStream)
  }

  // MUTUAL RECURSION EXAMPLES //

  // {
  //   x = y z
  //   return x
  // }
  val assignExp: Exp = coerce {
    Abs("x", Abs("y", Abs("z",
      Block(Cons(
        Assign("x", App("y", "z")), Cons(
          Return("x"), Nil))))))
  }

  def vars(e: Exp): Set[String] =
    nameF(nameF(e) map (x => Set(x))) reduce (Set.empty, _ ++ _)

  // vars(assignExp)
  // vars(prependUnderscore(assignExp))
}

import Compos._
