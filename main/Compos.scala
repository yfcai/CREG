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
      Ident(x = Var)
      Abs(param = Var, body = Fix[ExpF])
      App(operator = Fix[ExpF], operand = Fix[ExpF])
      Block(stms = List apply Stm)
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

  val prependUnderscore: Op[Syntactic, Identity] = new  Op[Syntactic, Identity] {
    def apply[A: Syntactic](syntax: A): A = implicitly[Syntactic[A]] match {
      // Type variable `A` is refined to `Var` in this case.
      case Var =>
        V("_" + syntax.name)

      case other =>
        composOp(this, syntax)
    }
  }

/*
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
      freshF[RAbs, String](coerce(e)).traverse[RAbs, String](stateMonad[Names])(
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
   */

  // MUTUAL RECURSION EXAMPLE //

  /*
  sealed trait SyntaxT
  @data def MuExp: SyntaxT = Fix(exp => {
    def Exp = ExpT {
      Ident(x = Var)

      // blocks of statements
      Block(stms = List apply StmT {
        Assign(lhs = Var, rhs = exp)
        Return(exp = exp)
      })
    }
  })

  @data def Stm: SyntaxT = StmT {
    Assign(lhs = Var, rhs = MuExp)
    Return(exp = MuExp)
  }

  @data def Var: SyntaxT = V(name = String)
  */

  // this doesn't make sense...
  // type Syntax = SyntaxT with (Exp or Stm or Var)

  /*
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
            expFun(data.unroll).traverse(apl)(f[Exp], f[Stm], f[Variable])
          }

        case Stm =>
          stmFun(data).traverse(apl)(f[Exp], f[Variable])

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
   */
}

import Compos._
