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

  // COMPOS TYPE CLASS //

  // operation on the entire type family
  // T[_]: type family
  // F[_]: the applicative functor
  trait Op[T[_], F[_]] {
    def apply[A: T](x: A): F[A]
  }

  // monoid
  trait Monoid[O] {
    def empty: O
    def plus(x: O, y: O): O
  }

  implicit def monadOfUnitIsMonoid[M[+_]: Monad.ic]: Monoid[M[Unit]] = new Monoid[M[Unit]] {
    val monad = implicitly[Monad.ic[M]]
    def empty: M[Unit] = monad.pure(())
    def plus(x: M[Unit], y: M[Unit]): M[Unit] = monad.bind[Unit, Unit](x, _ => y)
  }

  trait Compos[Family[_]] {
    def compos[F[+_]: Applicative.Endofunctor, C: Family](f: Op[Family, F], data: C): F[C]
  }

  def composOp[T[_]: Compos, C: T](f: Op[T, Identity], data: C): C =
    implicitly[Compos[T]].compos(f, data)

  def composFold[T[_]: Compos, C: T, O: Monoid](f: Op[T, Const[O]#λ], data: C): O = {
    implicit val constF = Const(implicitly[Monoid[O]].empty, implicitly[Monoid[O]].plus)
    implicitly[Compos[T]].compos[Const[O]#λ, C](f, data)
  }

  def composM[T[_]: Compos, M[+_]: Monad.ic, C: T](f: Op[T, M], data: C): M[C] =
    implicitly[Compos[T]].compos(f, data)

  def composM_[T[_]: Compos, M[+_]: Monad.ic, C: T](f: Op[T, Const[M[Unit]]#λ], data: C): M[Unit] =
    composFold(f, data)

  // EXPRESSION EXAMPLE //

  @datatype trait Term { EAbs(String, Term) ; EApp(Term, Term) ; EVar(String) }
  sealed trait TermFamily[_]
  implicit case object Term extends TermFamily[Term]

  implicit object composTerm extends Compos[TermFamily] {
    val termF = {
      @functor val termF = e => Term { EAbs(String, e) ; EApp(e, e) }
      termF
    }

    def compos[F[+_]: Applicative.Endofunctor, C: TermFamily](f: Op[TermFamily, F], data: C): F[C] = {
      implicitly[TermFamily[C]] match {
        case Term =>
          implicitly[Applicative.Endofunctor[F]].roll[termF.Map](
            termF(data.unroll).traverse(implicitly[Applicative.Endofunctor[F]])(f[Term])
          )
      }
    }
  }

  // PREPEND UNDERSCORE EXAMPLE //

  val rename = new Op[TermFamily, Identity] {
    def apply[A: TermFamily](e: A): A = implicitly[TermFamily[A]] match {
      case Term =>
        e.unroll match {
          case EAbs(x, b) => coerce { EAbs("_" + x, this(b)) }: Term
          case EVar(x)    => coerce { EVar("_" + x) }: Term
          case _          => composOp(this, e)
        }
    }
  }

  def rename2(e: Term): Term = {
    @functor val renameF = n => Term { EAbs(n, Term) ; EVar(n) }
    renameF(e) map ("_" + _)
  }

  val fst: Term = coerce {
    EAbs("x", EAbs("y", EVar("x")))
  }

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

  // type of infinite lists of hopefully fresh names
  type Names = Stream[String]

  // type of substitution
  type Subst = Seq[(String, String)]

  // lookup key in associative sequence
  def findWithDefault[A, B](key: A, default: B, seq: Seq[(A, B)]): B =
    seq find (_._1 == key) map (_._2) getOrElse default

  def fresh(e: Term): Term = {
    import Monad._

    // infinite list of fresh names
    val names: Names = Stream from 0 map ("_" + _)

    // substitutions are assoc list between names
    type Subst = Seq[(String, String)]

    def f(vs: Subst): Op[TermFamily, State[Names]#λ] = new Op[TermFamily, State[Names]#λ] {
      def apply[A: TermFamily](e: A): State[Names]#λ[A] =
        implicitly[TermFamily[A]] match {
          case Term => e.unroll match {
            case EAbs(x, b) =>
              for {
                freshNames <- readState[Names]
                _ <- writeState(freshNames.tail)
                x2 = freshNames.head
                b2 <- f((x, x2) +: vs)(b)
              }
              yield coerce { EAbs(x2, b2) }: Term

            case EVar(x) =>
              stateMonad[Names].pure[Term](coerce {
                EVar(findWithDefault(x, x, vs))
              })

            case _ =>
              composM[TermFamily, State[Names]#λ, Term](this, e)
          }
        }
    }

    evalState(f(Seq.empty)(e), names)
  }

  def fresh2(e: Term): Term = {
    @functor val freshF = (abs, name) => Term { EAbs = abs ; EVar(name) }

    // infinite list of fresh names
    val names: Names = Stream.from(0).map("_" + _)

    // name the record type for the EAbs case
    type RAbs = EAbs[String, Term]

    def f(vs: Subst)(e: Term): State[Names]#λ[Term] =
      freshF[RAbs, String](coerce(e)).traverse[State[Names]#λ, RAbs, String](
        // RAbs => Names => RAbs
        {
          case EAbs(x, b) =>
            for {
              freshNames <- readState[Names]
              _ <- writeState(freshNames.tail)
              x2 = freshNames.head
              b2 <- f((x, x2) +: vs)(b)
            }
            yield EAbs(x2, b2)
        }
          ,
        // String => Names => String
        x => stateMonad[Names] pure findWithDefault(x, x, vs)
      ).asInstanceOf[State[Names]#λ[Term]] // coercion doesn't work for this case yet

    evalState(f(Seq.empty)(e), names)
  }

  // MUTUAL RECURSION EXAMPLE //

  @datatype trait List[A] {
    Nil
    Cons(head = A, tail = List[A])
  }

  @datatype trait Expression[E, S] {
    Block(List[S])
    Var(Variable)
    Add(E, E)
  }

  @datatype trait Statement[Expression] {
    Assign(lhs = Variable, rhs = Expression)
    Return(Expression)
  }

  @datatype trait Variable { V(name = String) }

  type Exp = Fix[expF.Map]
  type Stm = Statement[Exp]

  val expF = {
    @functor val expF = exp => Expression {
      Block(List {
        Cons(head = Statement {
          Assign(String, exp)
          Return(exp)
        })
      })

      Add(exp, exp)
    }
    expF
  }

  sealed trait ExpFamily[T]
  implicit case object Exp extends ExpFamily[Exp]
  implicit case object Stm extends ExpFamily[Stm]
  implicit case object Var extends ExpFamily[Variable]

  implicit def stringToVar(x: String): Variable = V(x)
  implicit def stringToExp(x: String): Exp = coerce { Var(x) }

  implicit object composExp extends Compos[ExpFamily] {
    val expFun = {
      // BUG: does not work if rhs is `Exp { Block(List[stm]) }` instead
      @functor val fun = (exp, stm, _var) => Exp {
        Block(List { Cons(head = stm) })
        Add(exp, exp)
        Var(_var)
      }
      fun
    }

    val stmFun = {
      @functor val fun = (exp, _var) => Stm { Assign(_var, exp) ; Return(exp) }
      fun
    }


    def compos[F[+_]: Applicative.Endofunctor, C: ExpFamily](f: Op[ExpFamily, F], data: C): F[C] = {
      val apl = implicitly[Applicative.Endofunctor[F]]
      implicitly[ExpFamily[C]] match {
        case Exp =>
          apl.roll[expF.Map] {
            expFun(data.unroll) traverse (f[Exp], f[Stm], f[Variable])
          }

        case Stm =>
          stmFun(data) traverse (f[Exp], f[Variable])

        case Var =>
          apl pure data
      }
    }
  }

  // {
  //   x = y + z
  //   return x
  // }
  val plusExp: Exp = coerce {
    Block(Cons(
      Assign("x", Add("y", "z")), Cons(
        Return("x"), Nil)))
  }

  val renameExp = new Op[ExpFamily, Identity] {
    def apply[A: ExpFamily](e: A): A = implicitly[ExpFamily[A]] match {
      case Var =>
        e match { case V(x) => V("_" + x) }

      case _ =>
        composOp(this, e)
    }
  }

  val renameF = {
    // BUG: does not work if I don't mark recursive positions by `Exp` in the body of Stm
    @functor val renameF = x => Exp {
      Var(Variable { V(x) })
      Block(List { Cons(head = Stm {
        Assign(Variable { V(x) }, Exp)
        Return(Exp)
      }) })
    }
    renameF
  }

  def renameExp2(e: Exp): Exp = renameF(e) map ("_" + _)

  def vars(e: Exp): Set[String] = renameF(renameF(e) map (x => Set(x))) reduce (Set.empty, _ ++ _)

  // vars(plusExp)
  // vars(renameExp(plusExp))
  // vars(renameExp2(plusExp))
}

import Compos._
