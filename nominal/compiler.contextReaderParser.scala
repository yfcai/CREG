package nominal
package compiler
package contextReaderParser

import scala.reflect.macros.blackbox.Context

// trait Result: a variant of maybe monad
//
// remark: for scalac to deal with path-dependent types adequately,
// the object whose type member is in question must be visible at
// type level. for that reason, Failure takes the position type
// as a type argument. The parse result w.r.t. context c will have
// type `Result[A, c.Position]`.

sealed case class Success[+A](get: A) extends Result[A, Nothing]
sealed case class Failure[+Position](pos: Position, message: String) extends Result[Nothing, Position] {
  def get: Nothing = sys error s"Failure.get\n\n$pos\n\n$message\n"
}

sealed trait Result[+A, +Pos] {
  def get: A

  // monadic return & bind

  def _return[A]: A => Result[A, Pos] = a => Success(a)

  // note the encoding of use-site variance of Pos
  def >>= [B, P >: Pos] (f: A => Result[B, P]): Result[B, P] = this match {
    case Success(a) => f(a)
    case fail @ Failure(_, _) => fail
  }

  // syntax sugar for for-comprehension

  def flatMap[B, P >: Pos](f: A => Result[B, P]): Result[B, P] = this >>= f
  def map[B](f: A => B): Result[B, Pos] = this >>= (_return[B] compose f)

  // deterministic choice
  // note the encoding of use-site variance of A and Pos
  def orElse [B >: A, P >: Pos](alternative: => Result[B, P]): Result[B, P] = this match {
    case Success(_) => this
    case Failure(_, _) => alternative
  }
}

trait Parser[+A] {
  self =>

  // parse, or conventionally, runM
  // unfortunately return type is path-dependent & cannot be a synonym.
  def parse(c: Context)(input: c.Tree): Result[A, c.Position]

  // sequencing <* does not make sense for tree parsers

  // deterministic choice <+
  // featuring use-site variance
  def <+ [B >: A] (that: Parser[B]): Parser[B] = new Parser[B] {
    def parse(c: Context)(input: c.Tree): Result[B, c.Position] =
      self.parse(c)(input) orElse that.parse(c)(input)
  }

  def map[B](f: A => B): Parser[B] = new Parser[B] {
    def parse(c: Context)(input: c.Tree): Result[B, c.Position] =
      self.parse(c)(input) map f
  }
}

trait MultiParser[+A] {
  def parse(c: Context)(inputs: List[c.Tree]): Result[List[A], c.Position]
}

case class ZeroOrMore[+A](parser: Parser[A]) extends MultiParser[A] {
  def parse(c: Context)(inputs: List[c.Tree]): Result[List[A], c.Position] = {
    import c.universe._
    inputs match {
      case Nil =>
        Success(Nil)

      case head :: tail =>
        for {
          a <- parser.parse(c)(head)
          as <- this.parse(c)(tail)
        }
        yield a :: as
    }
  }
}
