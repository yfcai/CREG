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

  // DEBUG: test standalone records // wow!
  @data def r1 = R1(r1 = Int, r2 = String)
  @functor def r1F[r2] = R1(r1 = Int, r2 = r2)
  val x2: r1 = coerce { R1(nominal.lib.Tuple._2(5, "hi")) }


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

  // TODO: switch to using avoidF
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
    Abs = binding
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
    avoidF[String, (String, Term)](
      // coercion works because tuples happen to look like records:
      // they are non-nullary and are not abstract.
      // this is fragile.
      coerce(t)
    ) map (
      alias withDefault identity,
      {
        case (x, body) =>
          val y = fresh(x, avoid)
          (y, avoidCapture(avoid + y, alias + (x -> y), body))
      }
    )
  )

  def subst1(x: String, xsub: Term, t: Term): Term =
    avoidCapture(freevars(xsub) + x, Map.empty, t).fold[Term] {
      case Var(y) if x == y =>
        xsub

      case other =>
        coerce(other)
    }

/* BUG: COERCIONS TO TERM DOES NOT WORK!
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
          val s1 = subst1(y, ysub, term)
          show(s"subst($y, ${pretty{ysub}}, $name)", s1)
      }
      println()
  }
 */
}
