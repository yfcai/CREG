/** case study */

import nominal.functors._

// maybe should include .lib in .functors?
import nominal.lib._

object Main extends App {
  @data def Term = Fix(term => TermT {
    Void
    Var(name = String)
    Abs(param = String, body = term)
    App(operator = term, operand = term)
  })

  @functor implicit def termF[term] =
    TermT {
      Void
      Var(name = String)
      Abs(param = String, body = term)
      App(operator = term, operand = term)
    }

  // implicits
  implicit def _var(x: String): Term = coerce(Var(x))

  // 2nd argument `termF` of `Foldable` provided implicitly
  implicit class TermIsFoldable(t: Term) extends Foldable[TermF](t)

  val t: Term = coerce(Void)


  // USAGE: PRETTY PRINTING

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


  // USAGE: FREE VARIABLES

  def freevars(t: Term): Set[String] = t.fold[Set[String]] {
    case Var(v)       => Set(v)
    case Abs(x, body) => body - x
    case other        => termF(other) reduce (Set.empty, _ ++ _)
  }


  // USAGE: PREPEND UNDERSCORE

  @functor def namesF[name] = Fix(term => TermT {
    Void
    Var(name = name)
    Abs(param = name, body = term)
    App(operator = term, operand = term)
  })

  def prependUnderscore(t: Term): Term = namesF(t) map ("_" + _)


  // USAGE: CAPTURE-AVOIDING SUBSTITUTION

  @functor def avoidF[bound, binding] = Fix(term => TermT {
    Void
    Var(name = bound)
    Abs(param, body) = binding
    App(operator = term, operand = term)
  })

  def fresh(default: String, avoid: Set[String]): String = {
    var index = -1
    var y = default
    while (avoid(y)) {
      index += 1
      y = default + index
    }
    y
  }

  def avoidCapture(avoid: Set[String], alias: Map[String, String], t: Term): Term = coerce(
    avoidF[String, Abs[String, Term]](
      coerce(t)
    ).map(
      alias withDefault identity,
      (abs: Abs[String, Term]) => {
        val Abs(x, body) = abs
        val y = fresh(x, avoid)
        Abs(y, avoidCapture(avoid + y, alias + (x -> y), body))
      }
    )
  )

  // avoidCapture is better written as a fold.
  // caution: subst should test for binders.
  def avoidCapture2(avoid: Map[String, Set[String]], alias: Map[String, String])(t: Term): Term =
    t.unroll match {
      case Var(x) =>
        (alias withDefault identity)(x)

      case abs @ Abs(x, body) =>
        val occursFree = freevars(t)

        val avoidInThisCase =
          avoid.filter({
            case (replaced, shouldAvoid) => occursFree(replaced)
          }).foldLeft[Set[String]](Set.empty) {
            case (acc, (replaced, shouldAvoid)) => acc ++ shouldAvoid
          }

        if (avoidInThisCase(x)) {
          val y = fresh(x, avoidInThisCase)
          val newBody = avoidCapture2(avoid + (x -> Set(y)), alias + (x -> y))(body)
          coerce { Abs(y, newBody) }
        }
        else
          coerce { termF(abs) map avoidCapture2(avoid, alias) }

      case other =>
        coerce { termF(other) map avoidCapture2(avoid, alias) }
    }

  def subst2(x: String, xsub: Term, t0: Term): Term = {
    def loop(t: Term): Term = t.unroll match {
      case Var(y) if x == y =>
        xsub

      case Abs(y, body) if x == y =>
        t

      case other =>
        coerce { termF(other) map (s => subst2(x, xsub, s)) }
    }

    loop(avoidCapture2(Map(x -> freevars(xsub)), Map.empty)(t0))
  }

  def subst1(x: String, xsub: Term, t: Term): Term =
    avoidCapture(freevars(xsub) + x, Map.empty, t).fold[Term] {
      case Var(y) if x == y =>
        xsub

      case other =>
        coerce(other)
    }


  // AN UNUSUAL FUNCTOR (to replace avoidF as argument for equirecursion)

  @functor def H[sigma] = TermT {
    Void
    Var(name = String)
    Abs(param = String, body = Term)
    App(op = sigma, arg = Term)
  }

  def foldH[T](f: H.Map[T] => T): Term => T =
    t => f( H(coerce { t }: H.Map[Term]) map foldH(f) )

  // Convert `Term` to `μσ. H(σ)`.
  def termToFixH(t: Term): Fix[H.Map] = Roll[H.Map] {
    t.unroll match {
      case Void         => Void
      case Var(x)       => Var(x)
      case Abs(x, body) => Abs(x, body)
      case App(op, arg) => App(termToFixH(op), arg)
    }
  }

  // Convert `μσ. H(σ)` to `Term`.
  // Recall that `termF` is the pattern functor of `Term`.
  def fixHToTerm(t: Fix[H.Map]): Term = Roll[termF.Map] {
    t.unroll match {
      case Void         => Void
      case Var(x)       => Var(x)
      case Abs(x, body) => Abs(x, body)
      case App(op, arg) => App(fixHToTerm(op), arg)
    }
  }

  // flatten application tree
  val flatten: Term => Seq[Term] =
    foldH[Seq[Term]] {
      case App(flattenedOp, arg) =>
        flattenedOp :+ arg

      case Void         => Seq(coerce(Void))
      case Var(x)       => Seq(coerce(Var(x)))
      case Abs(x, body) => Seq(coerce(Abs(x, body)))
    }


  // Execution begins

  // \x -> x
  val id: Term = coerce(Abs("x", "x"))

  // (\x -> x) y
  val idy: Term = coerce(App(id, "y"))

  // \x -> f (x y)
  val f_xy: Term = coerce(Abs("x", App("f", App("x", "y"))))

  // \y -> (f x) y
  val fx_y: Term = coerce(Abs("y", App(App("f", "x"), "y")))

  // \f -> f (\z -> ())
  val fzv: Term = coerce(Abs("f", App("f", Abs("z", Void))))

  def put (name: String, obj : Any ) = println(s"$name = $obj")
  def show(name: String, term: Term) = put(name, pretty(term))


  List(
    ("id", id), ("idy", idy), ("f_xy", f_xy), ("fx_y", fx_y),
    ("fzv", fzv)
  ).foreach {
    case (name, term) =>
      show(name, term)
      put(s"freevars($name)", freevars(term))
      show(s"prependUnderscore($name)", prependUnderscore(term))
      List[(String, Term)](
        ("y", coerce(App("x", "x"))),
        ("y", coerce(App("x", "y")))
      ).foreach {
        case (y, ysub) =>
          //show(s"subst($y, ${pretty{ysub}}, $name)", subst1(y, ysub, term))
          show(s"substs($y, ${pretty{ysub}}, $name)", subst2(y, ysub, term))
      }
      println()
  }
}
