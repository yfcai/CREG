package creg.example

import creg._

import scala.language.{implicitConversions}

object DeBruijn {
  sealed trait Name
  case class Free(get: String) extends Name
  case class Bound(idx: Int) extends Name

  @data def Term = Fix(term => TermT {
    Var(name = Name)
    Abs(param = String, body = term)
    App(op = term, arg = term)
  })

  @functor def termF[term] = TermT {
    Var(name = Name)
    Abs(param = String, body = term)
    App(op = term, arg = term)
  }

  implicit class termIsFoldable(t0: Term) extends Foldable[TermF](t0)(termF)

  @functor def bindF[bound, binding] = Fix(term => TermT {
    Var(name = bound)
    Abs(param = String, body = binding)
    App(op = term, arg = term)
  })

  def close(name: String, level: Int = 0): Term => Term =
    t => coerce {
      bindF[Name, Term](coerce(t)).map(
        {
          case Free(x) if x == name => Bound(level)
          case other                => other
        },
        close(name, level + 1)
      )
    }

  def open(name: String, level: Int = 0): Term => Term =
    t => coerce {
      bindF[Name, Term](coerce(t)).map(
        {
          case Bound(n) if n == level => Free(name)
          case other                  => other
        },
        open(name, level + 1)
      )
    }

  implicit def _var(x: String): Term =
    coerce { Var(Free(x)) }

  def abs(name: String, body: Term): Term =
    coerce { Abs(name, close(name)(body)) }

  def app(op: Term, arg: Term): Term =
    coerce { App(op, arg) }

  val id = abs("x", "x")
  val fst = abs("x", abs("y", "x"))
  val ap = abs("f", abs("x", app("f", "x")))
  //
}
