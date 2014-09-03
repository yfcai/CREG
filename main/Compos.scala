/** Console demo script for:
  *
  * Bringert and Ranta.
  * A pattern for almost compositional functions.
  */

import language.higherKinds
import language.implicitConversions
import nominal.functors._
import nominal.lib._
import nominal.lib.Applicative.{Endofunctor => _, _}
import nominal.lib.Traversable.{Endofunctor => Functor}

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

  @datatype trait Exp { EAbs(String, Exp) ; EApp(Exp, Exp) ; EVar(String) }
  sealed trait ExpFamily[_]
  implicit case object ExpFamily extends ExpFamily[Exp]

  implicit object composExp extends Compos[ExpFamily] {
    val expF = {
      @functor val expF = e => Exp { EAbs(String, e) ; EApp(e, e) }
      expF
    }

    def compos[F[+_]: Applicative.Endofunctor, C: ExpFamily](f: Op[ExpFamily, F], data: C): F[C] = {
      implicitly[ExpFamily[C]] match {
        case ExpFamily =>
          implicitly[Applicative.Endofunctor[F]].roll[expF.Map](
            expF(data.unroll) traverse f[Exp]
          )
      }
    }
  }

  def singletonT[T[_]: Compos, C: T](f: C => C): Op[T, Identity] = singletonOp[T, Identity, C](f)

  def singletonOp[T[_]: Compos, F[_], C: T](f: C => F[C]): Op[T, F] = new Op[T, F] {
    def apply[A: T](x: A): F[A] = {
      val (tagA, tagC) = (implicitly[T[A]], implicitly[T[C]])
      if (tagA == tagC)
        f(x.asInstanceOf[C]).asInstanceOf[F[A]]
      else
        sys error s"singletonOp called between nonsingleton family members $tagA and $tagC}"
    }
  }

  // PREPEND UNDERSCORE EXAMPLE //

  def rename(e: Exp): Exp = e.unroll match {
    case EAbs(x, b) => coerce( EAbs("_" + x, rename(b)) )
    case EVar(x)    => coerce( EVar("_" + x) )
    case _          => composOp(singletonT(rename), e)
  }

  def rename2(e: Exp): Exp = {
    @functor val renameF = n => Exp { EAbs(n, Exp) ; EVar(n) }
    renameF(e) map ("_" + _)
  }

  val fst: Exp = coerce {
    EAbs("x", EAbs("y", EVar("x")))
  }

  assert(rename(fst) == (coerce { EAbs("_x", EAbs("_y", EVar("_x"))) }: Exp))
  assert(rename(fst) == rename2(fst))

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
  def runState[S, A](s: S, sm: State[S]#λ[A]): (A, S) = sm(s)

  // type of infinite lists of hopefully fresh names
  type Names = Stream[String]

  // type of substitution
  type Subst = Seq[(String, String)]

  // lookup key in associative sequence
  def findWithDefault[A, B](key: A, default: B, seq: Seq[(A, B)]): B =
    seq find (_._1 == key) map (_._2) getOrElse default

  def fresh(e: Exp): Exp = {
    import Monad._

    // infinite list of fresh names
    val names: Names = Stream.from(0).map("_" + _)

    // locate a possible substitution
    type Subst = Seq[(String, String)]

    // carry out the global uniquification
    def f(vs: Subst)(e: Exp): State[Names]#λ[Exp] = e.unroll match {
      case EAbs(x, b) =>
        for {
          freshNames <- readState[Names]
          _ <- writeState(freshNames.tail)
          x2 = freshNames.head
          b2 <- f((x, x2) +: vs)(b)
        } yield coerce {
          EAbs(x2, b2)
        }

      case EVar(x) =>
        stateMonad[Names].pure[Exp](coerce {
          EVar(findWithDefault(x, x, vs))
        })

      case _ =>
        composM[ExpFamily, State[Names]#λ, Exp](
          singletonOp[ExpFamily, State[Names]#λ, Exp](f(vs)),
          e)
    }

    runState(names, f(Seq.empty)(e))._1
  }

  // functor for capture avoidance
  val avoidF = {
    @functor val avoidF = (abs, name) => Exp { EAbs = abs ; EVar(name) }
    avoidF
  }

  def fresh2(e: Exp): Exp = {
    val names: Names = Stream.from(0).map("_" + _)

    // name the record type for the EAbs case
    type RAbs = EAbs[String, Exp]

    def f(vs: Subst)(e: Exp): State[Names]#λ[Exp] =
      avoidF[RAbs, String](coerce(e)).traverse[State[Names]#λ, RAbs, String](
        {
          case EAbs(x, b) =>
            ???
            /*
            for {
              freshNames <- readState[Names]
              //_ <- writeState(freshNames.tail)
              //x2 = freshNames.head
              //b2 <- f((x, x2) +: vs)(b)
            }
            yield EAbs("x", coerce(EVar("x"))) //EAbs(x2, b2)
             */
        }
          ,
        // String => State[String]#λ[Exp]
        //x => stateMonad[Names] pure findWithDefault(x, x, vs)
        _ => _ => ??? // TODO: FIXME: stackoverflow
      )(stateMonad).asInstanceOf[State[Names]#λ[Exp]] // coercion doesn't work for this case yet

    runState(names, f(Seq.empty)(e))._1
  }

  assert(fresh(fst) == (coerce { EAbs("_0", EAbs("_1", EVar("_0"))) }: Exp))
  //assert(fresh(fst) == fresh2(fst))
}

import Compos._
