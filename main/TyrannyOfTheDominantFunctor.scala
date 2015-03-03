/** All the code in paper */

import language.{higherKinds, implicitConversions}
import nominal.functors._
import nominal.lib._

object TyrannyOfTheDominantFunctor {

  object S1_Introduction {
    sealed trait Term
    case class Lit(number: Int)                   extends Term
    case class Var(name: String)                  extends Term
    case class Abs(param: String, body: Term)     extends Term
    case class App(operator: Term, operand: Term) extends Term

    def rename(f: String => String): Term => Term = {
      case Lit(n)      => Lit(n)
      case Var(x)      => Var(f(x))
      case Abs(x, t)   => Abs(f(x), rename(f)(t))
      case App(t1, t2) => App(rename(f)(t1), rename(f)(t2))
    }
  }

  object S2_Tyranny {

    object SS1_Functors {
      trait Functor {
        type Map[+A]
        def fmap[A, B](f : A => B) : Map[A] => Map[B]
      }
    }

    import SS1_Functors._

    object SS2_Renaming {
      sealed trait NameF[+S]
      case class Lit [+S] (number : Int) extends NameF[S]
      case class Var [+S] (name : S) extends NameF[S]
      case class Abs [+S] (param : S, body : NameF[S])
          extends NameF[S]
      case class App [+S] (param : NameF[S], body : NameF[S])
          extends NameF[S]

      val nameF = new Functor {
        type Map[+A] = NameF[A]
        def fmap[A,B](f : A => B) : Map[A] => Map[B] = {
          case Lit(n)      => Lit(n)
          case Var(x)      => Var(f(x))
          case Abs(x, t)   => Abs(f(x), fmap(f)(t))
          case App(t1, t2) => App(fmap(f)(t1), fmap(f)(t2))
        }
      }

      type Term2 = nameF.Map[String]
      def rename(f : String => String) : Term2 => Term2 = nameF.fmap(f)
    }

    object SS3_0_FreevarsWithBoilerplate {
      import S1_Introduction._
      def freevars : Term => Set[String] = {
        case Lit(n)      => Set.empty
        case Var(x)      => Set(x)
        case Abs(x, t)   => freevars(t) - x
        case App(t1, t2) => freevars(t1) ++ freevars(t2)
      }
    }

    object SS3_FreeVariables {
      sealed trait TermF[+T]
      case class Lit [+T] (number : Int) extends TermF[T]
      case class Var [+T] (name : String) extends TermF[T]
      case class Abs [+T] (param : String, body : T)
          extends TermF[T]
      case class App [ +T ] (operator : T, operand : T)
          extends TermF[T]

      val termF = new Functor {
        type Map[+A] = TermF[A]
        def fmap[A,B](f : A => B) : Map[A] => Map[B] = {
          case Lit(n)      => Lit(n)
          case Var(x)      => Var(x)
          case Abs(x, t)   => Abs(x, f(t))
          case App(t1, t2) => App(f(t1), f(t2))
        }
      }

      sealed trait Fix[+F [+_ ]] {def unroll : F[Fix[F]]}
      case class Roll[+F [+_ ]](unroll : F[Fix[F]]) extends Fix[F]
      type Term3 = Fix[TermF]

      def cata[A](F : Functor)(visitor : F.Map [A] => A) : Fix[F.Map] => A =
        t => {
          val loop = cata[A](F)(visitor)
          visitor(F.fmap(loop)(t.unroll))
        }

      val freevars : Term3 => Set[String] =
        cata[Set[String]](termF) {
          case Lit(n)      => Set.empty
          case Var(x)      => Set(x)
          case Abs(x, t)   => t - x
          case App(t1, t2) => t1 ++ t2
        }
    }

    object SS4_0_NormalFormWithRecursion {
      import S1_Introduction._

      def getOperator(t: Term): Term = t match {
        case App(op, _) => getOperator(op)
        case t          => t
      }
    }

    object SS4_GetOperator {
      import SS3_FreeVariables.{Fix, Roll, cata}

      sealed trait OpF[+T]
      case class Lit[+T](number: Int) extends OpF[T]
      case class Var[+T](name: String) extends OpF[T]
      case class Abs[+T](param: String, body: Term4) extends OpF[T]
      case class App[+T](operator: T, operand: Term4) extends OpF[T]

      type Term4 = Fix[OpF]

      val opF = new Functor {
        type Map[+A] = OpF[A]
        def fmap[A,B](f : A => B) : Map[A] => Map[B] = {
          case Lit(n)      => Lit(n)
          case Var(x)      => Var(x)
          case Abs(x, t)   => Abs(x, t)
          case App(t1, t2) => App(f(t1), t2)
        }
      }

      val getOperator: Term4 => Term4 =
        cata[Term4](opF) {
          case App(op, _) => op
          case op         => Roll[OpF](op)
        }
    }

    object SS4_alt_NormalForm {

      // Challenge: Capture the recursion scheme in the test
      // whether a term is in call-by-value beta-normal-form
      // or not.

      import SS3_FreeVariables.{Fix, Roll, cata}

      sealed trait CbvF[+S, +T]
      case class Lit[+S, +T](number: Int) extends CbvF[S, T]
      case class Var[+S, +T](name: String) extends CbvF[S, T]
      case class Abs[+S, +T](param: String, body: Term4) extends CbvF[S, T]
      case class App[+S, +T](operator: S, operand: T) extends CbvF[S, T]

      type Term4 = Fix[({ type λ[+T] = Fix[({ type λ[+S] = CbvF[S, T] })#λ] })#λ]

      private[this] type ArgF[+T] = Fix[OpF[T]#λ]
      private[this] type OpF [+T] = { type λ[+S] = CbvF[S, T] }

      val argF = new Functor {
        type Map[+A] = ArgF[A]
        def fmap[A,B](f : A => B) : Map[A] => Map[B] = ???
      }

      def opF[T] = new Functor {
        type Map[+S] = OpF[T]#λ[S]
        def fmap[A,B](f : A => B) : Map[A] => Map[B] = ???
      }

      def isNormalForm: Term4 => Boolean =
        cata[Boolean](argF) { _.unroll match {
          case App(op, arg) =>
            val testOp: Any => Boolean = ???
            arg && testOp(op)

          case _ => true
        }}
    }
  }

  object F1_RenamingFreeVariables {
    @data def TermStruct = TermT {
      Lit(number = Nothing)
      Var(name = Nothing)
      Abs(param = Nothing, body = Nothing)
      App(operator = Nothing, operand = Nothing)
    }

    @functor def nameF[N] = Fix (T => TermT {
      Lit (number = Int)
      Var (name = N)
      Abs (param = N, body = T)
      App (operator = T, operand = T)
    })

    @functor def termF[T] = TermT {
      Lit (number = Int)
      Var (name = String)
      Abs (param = String, body = T)
      App (operator = T, operand = T)
    }

    type Term = nameF.Map[String]
    //        = Fix[termF.Map]
    implicitly[ Term =:= Fix[termF.Map] ]

    def rename(f : String => String) : Term => Term =
      nameF.fmap(f)

    // copy of S2_Tyranny.SS3_FreeVariables.cata
    // some types are subtly different
    def cata[A](F : Traversable.Endofunctor)(visitor : F.Map [A] => A) : Fix[F.Map] => A =
      t => {
        val loop = cata[A](F)(visitor)
        visitor(F.fmap(loop)(t.unroll))
      }

    val freevars : Term => Set[String] =
      cata[Set[String]](termF) {
        case Var (x)   => Set(x)
        case Abs (x,t) => t - x
        case other     => termF.crush[Set[String]](Set.empty , _ ++ _ )(other)
      }

    //t = λf.f (g 1)(h 2)
    val t:Term = coerce {
      Abs("f",
        App(App(Var("f"), App(Var("g"), Lit(1))),
          App(Var("h"), Lit(2))))
    }

    def runAssertions(): Unit = {
      assert(freevars(t) == Set("g","h"))
      assert(rename(_.toUpperCase)(t) == (
        coerce {
          Abs("F",
            App(App(Var("F"), App(Var("G"), Lit(1))),
              App(Var("H"), Lit(2)))) }:Term
      ))
    }
  }

  F1_RenamingFreeVariables.runAssertions()
  import F1_RenamingFreeVariables._

  object S3_Emancipation {
    object SS1_PolymorphicRecords {
      // ⊥ is a subtype of all other types
      type ⊥ = Nothing
      sealed trait TermT[ +L, +V, +Ab, +Ap ]
      case class Lit[+N](number : N)
          extends TermT[Lit[N], Var[⊥], Abs[⊥, ⊥], App[⊥, ⊥]]
      case class Var[+X](name : X)
          extends TermT[Lit[⊥], Var[X], Abs[⊥, ⊥], App[⊥, ⊥]]
      case class Abs[+P, +B](param : P, body : B)
          extends TermT[Lit[⊥], Var[⊥], Abs[P, B], App[⊥, ⊥]]
      case class App[+F, +Y](operator : F, operand : Y)
          extends TermT[Lit[⊥], Var[⊥], Abs[⊥, ⊥], App[F, Y]]
    }

    class SS1_1_PolymorphicRecordsCompileTimeAssertions[T] {
      implicitly[ termF.Map[T] =:=
        TermT[Lit[Int], Var[String], Abs[String, T], App[T, T]]
      ]
    }

    object SS2_RecursiveTypes {
      val omega : Term =
        Roll[ termF .Map ](App(
          Roll[ termF .Map ](Abs("x",
            Roll[ termF .Map ](App(
              Roll[ termF .Map ](Var("x")), Roll[ termF .Map ](Var("x")))))),
          Roll[ termF .Map ](Abs("x", Roll[ termF .Map ](App(
            Roll[ termF .Map ](Var("x")), Roll[ termF .Map ](Var("x"))))))))
    }

    val omegaPrime : Term = coerce {
      App(
        Abs("x", App(Var("x"), Var("x"))),
        Abs("x", App(Var("x"), Var("x"))))
    }

    class SS3_RegularFunctorsCompileTimeAssertions[N] {
      implicitly[ nameF.Map[N] =:=
        Fix[({
          type λ[+T] = TermT[
            Lit[Int], Var[N], Abs[N, T], App[T, T]
          ]
        })#λ]
      ]
    }
  }

  object S4_ModularityBenefits {

    object SS1_RecursionSchemes {
      @functor def opF[A] = TermT {
        Lit (number = Int)
        Var (name = String)
        Abs (param = String, body = Term)
        App (operator = A, operand = Term)
      }

      def getOperator (t : Term) : Term =
        cata[Term](opF)({
          case App(op, s) => op
          case op         => coerce { op }
        })(coerce {t})
    }

    object SS2_ContainerViews {
      def listMonoid[A] = new Applicative {
        type Map[+X] = List[A]
        def pure[X](x : X) = List.empty
        def call[X,Y](xs:List[A],ys:List[A])= xs ++ ys
      }

      trait MyTraversable extends Traversable {

        def toList[A <: Cat0](t: Map[A]): List[A] =
          traverse(listMonoid[A])((x: A) => List(x))(t)

        def crush[A <: Cat0](z: A, s: (A, A) => A)(t: Map[A]) =
          toList(t).fold(z)(s)
      }

      // see main/Fresh.scala for the refreshM example
      val refreshExample = Fresh
    }
  }


  /** old examples for reference. include evaluation contexts */
  object Lambda {
    import Banana.cata

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
      cata[Term](termF) {
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
      t => induction(termF.fmap(foldTerm(induction))(t.unroll))

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

    // Can we write termToFixOpF using coerce? Yes!
    def termToFixOpF2(t: Term): Fix[opF.Map] = coerce(t)

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

    import Banana.{ Pair, cakeWith, para }

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
      t => para[Option[(Term, Term => Term)]](cbvF)({
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
      cata[Seq[String]](bodyF)({
        case Abs(x, innerParams) => x +: innerParams
        case _ => Seq.empty
      })(coerce { t })
  }
}
