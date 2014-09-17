/** case study */

import nominal.functors._

// maybe should include .lib in .functors?
import nominal.lib._

object Main extends App with MainTrait {
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
          // val s2 = subst2(y, ysub, term)
          // assert(s1 == s2)
          show(s"subst($y, ${pretty{ysub}}, $name)", s1)
          //show(s"subst2($y, ${pretty{ysub}}, $name)", s2)
      }
      println()
  }
}

trait MainTrait {

  @datatype trait Term {
    Void
    Var(name = String)
    Abs(param = String, body = Term)
    App(operator = Term, operand = Term)
  }

  // @functor only works in block scope >_<
  implicit val termF = {
    @functor implicit val termF = x => TermF[x]
    termF
  }

  // implicits
  implicit def _var(x: String): Term = coerce(Var(x))

  // 2nd argument `termF` of `Foldable` provided implicitly
  implicit class TermIsFoldable(t: Term) extends Foldable[TermF](t)

  val t: Term = coerce(Void)

  // USAGE: COUNTING VARIABLE OCCURRENCES

  // typecheck folding
  def foldTerm[T](inductiveStep: termF.Map[T] => T): Term => T =
    t => inductiveStep(termF(t.unroll) map foldTerm(inductiveStep))

  val variables: Term => Int =
    foldTerm[Int] {
      case Var(n) => 1
      case other  => termF(other) reduce (0, _ + _)
    }

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

  // compos-style explicit recursion
  def freevars1(t: Term): Set[String] = t.unroll match {
    case Var(v)       => Set(v)
    case Abs(x, body) => freevars(body) - x
    case other        => termF(other).traverse(Applicative.Const[Set[String]](Set.empty, _ ++ _))(freevars1)
  }

  val avoidF = {
    @functor val avoidF = (bound, binding) => Term {
      Var(bound)
      Abs = binding
    }
    avoidF
  }

  def freevars2(t: Term): Set[String] =
    avoidF[String, Abs[String, Term]](
      coerce(t)
    ).traverse(Applicative.Const[Set[String]](Set.empty, _ ++ _))(
      x => Set(x),
      { case Abs(x, body) => freevars2(body) - x }
    )

  // USAGE: PREPEND UNDERSCORE

  def prependUnderscore(t: Term): Term = {
    @functor val namesF = name => Term { Var(name) ; Abs(param = name) }
    namesF(t) map ("_" + _)
  }


  // USAGE: CAPTURE-AVOIDING SUBSTITUTION

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
      {
        case Abs(x, body) =>
          val y = fresh(x, avoid)
          Abs(y, avoidCapture(avoid + y, alias + (x -> y), body))
      }
    )
  )

  def subst1(x: String, xsub: Term, t: Term): Term =
    avoidCapture(freevars(xsub) ++ freevars(t) + x, Map.empty, t).fold[Term] {
      case Var(y) if x == y =>
        xsub

      case other =>
        coerce(other)
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
}
