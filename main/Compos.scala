/** Console demo script for:
  *
  * Bringert and Ranta.
  * A pattern for almost compositional functions.
  */

import language.higherKinds
import language.implicitConversions
import nominal.functors._
import nominal.lib._
import nominal.lib.Applicative._

object Compos {
  import BuiltInFunctors._

  // BUG: DataDecl doesn't know to resolve imports.
  //      If I import List from Scrap instead of redefining them here,
  //      then get error "not found: type Nil".
  @data def List[A] = Fix(list => ListT {
    Nil
    Cons(head = A, tail = list)
  })

  @functor implicit def List[a] = Fix(list => ListT { Nil ; Cons(head = a, tail = list) })

  @data def Syntax = SyntaxT {

    def Exp = ExpT {
      def Identifier = Ident(x = Var)
      def Abstraction = Abs(param = Var, body = Fix[ExpF])
      def Application = App(operator = Fix[ExpF], operand = Fix[ExpF])
      def BlockExpression = Block(stms = List apply Stm)
    }

    def Stm = StmT {
      Assign(lhs = Var, rhs = Fix[ExpF])
      Return(exp = Fix[ExpF])
    }

    def Var = V(name = String)
  }

  implicit def stringToVar(x: String): Var = V(x)
  implicit def stringToFixExp(x: String): Fix[ExpF] = coerce { Ident(x) }

  val fst: Exp = coerce { Abs("x", Abs("y", "x")) }

  @synonym def ExpF[exp] = ExpT {
    Ident(x = Var)
    Abs(param = Var, body = exp)
    App(operator = exp, operand = exp)

    Block(stms = List apply StmT {
      Assign(lhs = Var, rhs = exp)
      Return(exp = exp)
    })
  }

  // COMPOS TYPE CLASS //

  // This version of `prependUnderscore` looks good,
  // but scalac doesn't do enough type refinement
  // to typecheck it.
  //
  // Scalac is missing the following knowledge: Since
  // the trait SyntaxT is sealed and the case class V
  // is final, whatever matches V(x: T) has the exact
  // type V[T].
  //
  //   trait Op[Family, F[_]] {
  //     def apply[A <: Family](x: A): F[A]
  //   }
  //
  //   val prependUnderscore: Op[Syntax, Identity] =
  //     new Op[Identity, Syntax] {
  //       def apply[A <: Syntax](x: A): A = x match {
  //         case V(y: String) => V("_" + y)
  //         case _            => ???
  //       }
  //     }
  //
  // We help scalac by encoding type families with
  // heavier notations.

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
          expC(syntax).traverse(G)(
            muExp => G.roll[ExpF] { f(muExp.unroll) },
            f.etaExpand[Stm],
            f.etaExpand[Var])

        case Stm =>
          stmC(syntax).traverse(G)(
            muExp => G.roll[ExpF] { f(muExp.unroll) },
            f.etaExpand[Var])

        case Var =>
          G pure syntax
      }
  }


  // PREPEND UNDERSCORE EXAMPLE //

  val prependUnderscore: Op[Syntactic, Identity] = new  Op[Syntactic, Identity] {
    def apply[A: Syntactic](syntax: A): A = implicitly[Syntactic[A]] match {
      // Type variable `A` is refined to `Var` in this case.
      case Var =>
        V("_" + syntax.name)

      case other =>
        composOp(this, syntax)
    }
  }

  @functor implicit def nameStmF[name, exp] = StmT {
    Assign(lhs = V(name = name), rhs = exp)
    Return(exp = exp)
  }

  @functor implicit def nameExpF[name, exp] = ExpT {
    Ident(x = V(name = name))

    Abs(param = V(name = name), body = exp)

    App(operator = exp, operand = exp)

    Block(stms = List apply (nameStmF apply (name, exp)))
  }

  @functor def nameF[name] = nameExpF apply (name, Fix(exp => nameExpF apply (name, exp)))

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

  // substitution defined by an association sequence
  type Subst = Seq[(String, String)]

  // lookup key in associative sequence
  def findWithDefault[A, B](key: A, default: B, seq: Seq[(A, B)]): B =
    seq find (_._1 == key) map (_._2) getOrElse default

  def fresh(e: Exp): Exp = {
    import Monad._

    // infinite list of fresh names
    val names: Names = Stream from 0 map ("_" + _)

    def f(vs: Subst): Op[Syntactic, State[Names]#λ] = new Op[Syntactic, State[Names]#λ] {
      def apply[A: Syntactic](e: A): State[Names]#λ[A] =
        (implicitly[Syntactic[A]], e) match {
          case (Exp, Abs(V(x), b)) =>
            for {
              freshNames <- readState[Names]
              _ <- writeState(freshNames.tail)
              x2 = freshNames.head
              b2 <- f((x, x2) +: vs)(b.unroll)
            }
            yield coerce { Abs(V(x2), b2) }: Exp

          case (Var, V(x)) =>
            stateMonad[Names].pure(V(findWithDefault(x, x, vs)))

          case _ =>
            composM[Syntactic, State[Names]#λ, A](this, e)
        }
    }

    evalState(f(Seq.empty)(e), names)
  }

  @functor implicit def freshExpF[abs, name, exp] = ExpT {
    Ident(x = V(name = name))
    Abs(param, body) = abs // `abs` overrides abstractions
    App(operator = exp, operand = exp)
    Block(stms = List apply (nameStmF apply (name, exp)))
  }

/*
  @functor def freshF[abs, name] =
    freshExpF apply (abs, name, Fix(exp => freshExpF apply (abs, name, exp)))

  def fresh2(e: Exp): Exp = {
    // infinite list of fresh names
    val names: Names = Stream.from(0).map("_" + _)

    // name the range of freshF we care about
    // it is isomorphic to Exp, but not exactly the same.
    type FreshExp = freshF.Map[Abstraction, String]

    def f(vs: Subst)(e: Exp): State[Names]#λ[Exp] =
      freshF[Abstraction, String](coerce(e)).
        traverse[Abstraction, String](stateMonad[Names])(
          // Abstraction => Names => Abstraction
          {
            case Abs(V(x), b) =>
              for {
                freshNames <- readState[Names]
                _ <- writeState(freshNames.tail)
                x2 = freshNames.head
                b2 <- f((x, x2) +: vs)(b.unroll)
              }
              yield Abs(V(x2), b2)
          },

          // String => Names => String
          x => stateMonad[Names] pure findWithDefault(x, x, vs)
        ).asInstanceOf[State[Names]#λ[Exp]] // coercion doesn't work for this case yet

    evalState(f(Seq.empty)(e), names)
  }
 */

  // MUTUAL RECURSION EXAMPLES //

  // {
  //   x = y + z
  //   return x
  // }
  val plusExp: Exp = coerce {
    Block(Cons(
      Assign("x", App("y", "z")), Cons(
        Return("x"), Nil)))
  }

  def vars(e: Exp): Set[String] = nameF(nameF(e) map (x => Set(x))) reduce (Set.empty, _ ++ _)

  // vars(plusExp)
  // vars(prependUnderscore(plusExp))
}

import Compos._
