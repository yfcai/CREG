import nominal.functors._
import nominal.lib._

/** Lambda calculus example in paper */

object Lambda {
  import Banana.cataWith

  @data def Term = Fix(term => TermT {
    Lit(n = Int)
    Var(x = String)
    Abs(x = String, t = term)
    App(t1 = term, t2 = term)
  })

  implicit def _var(x: String): Term = coerce(Var(x))
  implicit def _lit(n: Int   ): Term = coerce(Lit(n))

  // prepend underscore

  @functor def nameF[s] = Fix(term => TermT {
    Lit(n = Int)
    Var(x = s)
    Abs(x = s, t = term)
    App(t1 = term, t2 = term)
  })

  // making sure code in paper is well-typed
  // CAUTION: we don't have the Functor trait.
  trait Functor {
    type Map[+A]
    def fmap[A, B](f: A => B): Map[A] => Map[B]
  }

  val nameFunctorExpanded = new Functor {
    type Map [+A] = Fix [H [A] # λ]

    private[this] type H [+A] = {
      type λ [+T] = TermT [
        Lit [Int], Var [A], Abs [A, T], App [T, T]
      ]
    }

    def fmap[A, B](f: A => B): Map[A] => Map[B] =

      t => Roll[H[B]#λ](t.unroll match {
        case Lit(n)         => Lit(n)
        case Var(x)         => Var(f(x))
        case Abs(x, t)      => Abs(f(x), fmap(f)(t))
        case App(t_1, t_2)  => App(fmap(f)(t_1), fmap(f)(t_2))
      })
  }

  val rename: Term => Term = nameF.fmap("_" ++ _)

  def rename2(f: String => String): Term => Term =
    cataWith[Term](termF) {
      case Var(x) => Roll[termF.Map](Var(f(x)))
      case t      => Roll[termF.Map](t)
    }

  // count names

  val names: Term => Int = nameF.mapReduce[String, Int](_ => 1)(0, _ + _)

  // count literals

  @functor def litF[n] = Fix(term => TermT {
    Lit(n = n)
    Var(x = String)
    Abs(x = String, t = term)
    App(t1 = term, t2 = term)
  })

  val literals: Term => Int = litF.mapReduce[Int, Int](_ => 1)(0, _ + _)

  // folds

  @functor def termF[t] = TermT {
    Lit(n = Int)
    Var(x = String)
    Abs(x = String, t = t)
    App(t1 = t, t2 = t)
  }

  def foldTerm[T](induction: termF.Map[T] => T):
      Term => T =
    t => induction(termF(t.unroll) map foldTerm(induction))

  val literals3: Term => Int =
    foldTerm[Int] {
      case Lit(n) => 1
      case other  => termF(other) reduce (0, _ + _)
    }

  val freevars: Term => Set[String] =
    foldTerm[Set[String]] {
      case Var(x)    => Set(x)
      case Abs(x, s) => s - x
      case other     => termF(other).reduce(Set(), _ ++ _)
    }

  def getOperator0(t: Term): Term = t.unroll match {
    case App(t1, t2) => getOperator(t1)
    case _           => t
  }

  @functor def opF[t] = TermT {
    Lit(n = Int)
    Var(x = String)
    Abs(x = String, t = Term)
    App(t1 = t, t2 = Term)
  }

  // Convert Term to μσ. opF(σ).
  def termToFixOpF(t: Term): Fix[opF.Map] = Roll[opF.Map] {
    t.unroll match {
      case Lit(n)       => Lit(n)
      case Var(x)       => Var(x)
      case Abs(x, body) => Abs(x, body)
      case App(op, arg) => App(termToFixOpF(op), arg)
    }
  }

  // Convert μσ. opF(σ) to Term.
  def fixOpFToTerm(t: Fix[opF.Map]): Term = Roll[termF.Map] {
    t.unroll match {
      case Lit(n)       => Lit(n)
      case Var(x)       => Var(x)
      case Abs(x, body) => Abs(x, body)
      case App(op, arg) => App(fixOpFToTerm(op), arg)
    }
  }

  def foldOp[T](induction: opF.Map[T] => T): Term => T =
    t => {
      val s = coerce { t }: opF.Map[Term]
      induction(opF(s) map foldOp(induction))
    }

  // (redex, put-back)
  type EvalCtx = (Term, Term => Term)

  // either eval context, or itself
  type ECRslt = Either[EvalCtx, TermF[Term]]

  def cbnEvalCtx(t: Term): Option[EvalCtx] =
    foldForEvalCtx(t).left.toOption

  def foldForEvalCtx: Term => ECRslt =
    foldOp[ECRslt]({
      case App(Left((redex, put_back)), operand) =>
        Left((redex, t => coerce { App(put_back(t), operand) }))

      case App(Right(abs @ Abs(_, _)), operand) =>
        Left((coerce(App(abs, operand)), identity))

      case App(Right(s), operand) =>
        Right(coerce(App(s, operand)))

      case t @ Abs(_, _) => Right(t)
      case t @ Var(_)    => Right(t)
      case t @ Lit(_)    => Right(t)

      // alternatively:
      // case t => Right(opF(t) map (_ => sys error "irrelevant"))
    })

  // extract operator in nested applications
  val getOperator: Term => Term = foldOp[Term] {
    case App(op, arg) => op
    case operator     => coerce(operator)
  }

  // extract operands in nested applications
  val getOperands: Term => Seq[Term] = foldOp[Seq[Term]] {
    case App(precedingOperands, operand) =>
      precedingOperands :+ operand
      // append this operand to preceding operands

    case _ =>
      Seq.empty
  }

  @functor def cbvF[t] = TermT {
    Lit(n = Int)
    Var(name = String)
    Abs(param = String, body = Term)
    App(op = t, arg = t)
  }

  def foldCbv[T](induction: cbvF.Map[T] => T): Term => T =
    t => {
      val s = coerce { t }: cbvF.Map[Term]
      induction(cbvF(s) map foldCbv(induction))
    }

  // optionally returns (redex, put-redex-back)
  def evalContext0(t: Term): Option[(Term, Term => Term)] = t.unroll match {
    case App(op, arg) => op.unroll match {
      case Abs(_, _) =>
        Some((t, identity))

      case _ =>
        val opResult = evalContext0(op).map[(Term, Term => Term)] {
          case (redex, put) =>
            (redex, s => coerce { App(put(s), arg) })
        }
        val argResult = evalContext0(arg).map[(Term, Term => Term)] {
          case (redex, put) =>
            (redex, s => coerce { App(op, put(s)) })
        }
        opResult orElse argResult
    }

    case _ =>
      None
  }

  import Banana.{ Pair, cakeWith, paraWith }

  // this needs paramorphism. needs arg to reconstruct term in eval context.
  val evalContext: Term => Option[(Term, Term => Term)] =
    t => cakeWith[Option[(Term, Term => Term)]](cbvF)({
      case Pair(t, App(opCtx, argCtx)) => t.unroll match {
        case App(op, arg) if op.unroll.isInstanceOf[Abs[_, _]] =>
          Some((coerce(t), identity))

        case App(op, arg) =>
          val opResult = opCtx.map[(Term, Term => Term)]({
            case (redex, put) =>
              (redex, s => coerce { App(put(s), coerce(arg): Term) })
          })
          val argResult = argCtx.map[(Term, Term => Term)]({
            case (redex, put) =>
              (redex, s => coerce { App(coerce(op): Term, put(s)) })
          })
          opResult orElse argResult
      }

      case _ =>
        None
    })(coerce(t))

  // present this after paramorphism
  val evalContext2: Term => Option[(Term, Term => Term)] =
    t => paraWith[Option[(Term, Term => Term)]](cbvF)({
      case App(Pair(op, opCtx), Pair(arg, argCtx)) => op.unroll match {
        case Abs(_, _) =>
          Some((coerce { App(coerce(op): Term, coerce(arg): Term) }, identity))

        case _ =>
          val opResult = opCtx.map[(Term, Term => Term)]({
            case (redex, put) =>
              (redex, s => coerce { App(put(s), coerce(arg): Term) })
          })
          val argResult = argCtx.map[(Term, Term => Term)]({
            case (redex, put) =>
              (redex, s => coerce { App(coerce(op): Term, put(s)) })
          })
          opResult orElse argResult
      }

      case _ =>
        None
    })(coerce(t))

  def sexp0(t: Term): Seq[Term] = t.unroll match {
    case App(op, arg) => sexp0(op) :+ arg
    case _            => Seq(t)
  }

  val toSExp: Term => Seq[Term] =
    foldOp[Seq[Term]] {
      case App(precedingTerms, operand) =>
        precedingTerms :+ operand

      case Lit(n)    => Seq(coerce { Lit(n) })
      case Var(x)    => Seq(coerce { Var(x) })
      case Abs(x, t) => Seq(coerce { Abs(x, t) })
    }

  @functor def bodyF[t] = TermT {
    Lit(n = Int)
    Var(x = String)
    Abs(x = String, t = t)
    App(t1 = Term, t2 = Term)
  }

  def params(t: Term): Seq[String] =
    cataWith[Seq[String]](bodyF)({
      case Abs(x, innerParams) => x +: innerParams
      case _ => Seq.empty
    })(coerce { t })
}
