/** All the code in paper, with typos corrected
  *
  * Interesting things:
  * - F3_Preview is Figure 3 (rename, freevars, getOperator)
  * - F4_Grammar is Figure 4 (grammar of regular functors)
  */

import language.{higherKinds, implicitConversions}
import creg.functors._
import creg.lib._

object TyrannyOfTheDominantFunctor {

  def main(args: Array[String]) {
    {
      import F3_Preview._
      println()
      println(caption)
      println(s"""|                       t = ${pretty(t)}
                  |rename(_.toUpperCase)(t) = ${pretty(rename(_.toUpperCase)(t))}
                  |             freevars(t) = ${freevars(t)}
                  |          getOperator(t) = ${pretty(getOperator(t))}
                  |""".stripMargin)
    }
  }

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

    object SS3_0_FreeVariablesWithBoilerplate {
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

    object SS4_OperatorExtraction {
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
  }

  object F3_Preview {
    val caption =
      """|Figure 3:
         |Renaming, free-variable computation and operator
         |extraction in Creg.
         |""".stripMargin

    @struct def TermT {
      Lit(number)
      Var(name)
      Abs(param, body)
      App(operator, operand)
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

    @functor def opF[T] =
      TermT {
        Lit(number = Int)
        Var(name = String)
        Abs(param = String, body = Term)
        App(operator = T, operand = Term)
      }

    type Term = nameF.Map[String]
    //        = Fix[termF.Map]
    implicitly[ Term =:= Fix[termF.Map] ]

    def rename(f : String => String) : Term => Term =
      nameF.fmap(f)

    // copy of S2_Tyranny.SS3_FreeVariables.cata
    // some types are subtly different
    def cata[A](F : Functor)(visitor : F.Map [A] => A) : Fix[F.Map] => A =
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

    def getOperator(t : Term): Term =
      cata[Term](opF)({
        case App(op, s) => op
        case op         => coerce { op }
      })(coerce { t })

    //t = f (g 1) (λh. h 2)
    val t : Term = coerce {
      App(App(Var("f"), App(Var("g"), Lit(1))),
        Abs("h", App (Var("h"), Lit(2))))
    }

    // assertions in figure
    def runAssertions(): Unit = {
      assert(freevars(t) == Set("f","g"))
      assert(freevars(rename(_.toUpperCase)(t)) == Set("F", "G"))

      assert(rename(_.toUpperCase)(t) == (
        coerce {
          App(App(Var("F"), App(Var("G"), Lit(1))),
            Abs("H", App (Var("H"), Lit(2))))
        }:Term
      ))

      assert(getOperator(t) == (coerce { Var("f") }: Term))
    }

    // pretty printer for fun
    def pretty(t: Term): String = {

      def paren(child: (String, Int), myPrecedence: Int): String =
        if (child._2 > myPrecedence)
          child._1
        else
          s"(${child._1})"

      cata[(String, Int)](termF)({
        case Lit(n) => (n.toString, Int.MaxValue)
        case Var(x) => (x,          Int.MaxValue)

        case Abs(x, body) =>
          val precedence = 0
          (s"\\$x -> ${paren(body, precedence)}", precedence)

        case App(operator, operand) =>
          val precedence = 10
          ( paren(operator, precedence - 1) + " " +
            paren(operand , precedence),
            precedence
          )
      })(t)._1
    }
  }

  F3_Preview.runAssertions()
  import F3_Preview._

  object F4_Grammar {
    val caption =
      "The grammar of regular functors and the corresponding syntax in Creg."

    // constant functors are regular.
    @functor def intF[A, B, C] = Int

    // extractions (functors returning one of their arguments) are regular.
    @functor def fstF[A, B, C] = A

    // disjoint-union functors are regular.
    @struct  def EitherT { Left(get) ; Right(get) }
    @functor def eitherF[A, B] = EitherT { Left(get = A) ; Right(get = B) }

    // tupling functors are regular.
    @struct  def PairT { Pair(_1, _2) }
    @functor def pairF[A, B] = Pair(_1 = A, _2 = B)

    // compositions of regular functors are regular.
    @functor def compositeF[A, B, C] =
      pairF apply (
        intF apply (A, B, C),
        fstF apply (A, B, C)
      )

    // taking the fixed point of a regular functor with respect to
    // an argument results in a regular functor

    // bottomF.Map[B, C] is uninhabited
    @functor def bottomF[B, C] = Fix(A => fstF apply (A, B, C))

    // isoIntF.Map[A, B] is isomorphic to Int
    @functor def isoIntF[A, B] = Fix(C => intF apply (A, B, C))
  }

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

      def getOperator(t : Term) : Term =
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

      trait MyTraversableBounded extends TraversableBounded {

        def toList[A <: Cat0](t: Map[A]): List[A] =
          traverse(listMonoid[A])((x: A) => List(x))(t)

        def crush[A <: Cat0](z: A, s: (A, A) => A)(t: Map[A]) =
          toList(t).fold(z)(s)
      }

      // see main/Fresh.scala for the refreshM example
      val refreshExample = Fresh
    }
  }
}
