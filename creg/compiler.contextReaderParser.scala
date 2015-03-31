package creg
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

private[creg]
sealed case class Success[+A](get: A) extends Result[A, Nothing]

private[creg]
sealed case class Failure[+Position](pos: Position, message: String) extends Result[Nothing, Position] {
  def get: Nothing = sys error s"Failure.get\n\n$pos\n\n$message\n"
}

private[creg]
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

private[creg]
trait Parser[Gamma, +A] {
  self =>

  private[this] type ParserG[B] = Parser[Gamma, B]

  def parse(c: Context, gamma: Gamma)(input: c.Tree): Result[A, c.Position]

  def orElse[B >: A](that: ParserG[B]): ParserG[B] = new Parser[Gamma, B] {
    def parse(c: Context, gamma: Gamma)(input: c.Tree): Result[B, c.Position] =
      self.parse(c, gamma)(input) orElse that.parse(c, gamma)(input)
  }

  def map[B](f: A => B): ParserG[B] = new Parser[Gamma, B] {
    def parse(c: Context, gamma: Gamma)(input: c.Tree): Result[B, c.Position] =
      self.parse(c, gamma)(input) map f
  }
}

private[creg]
trait MultiParser[Gamma, +A] {
  def parse(c: Context, gamma: Gamma)(inputs: List[c.Tree]): Result[List[A], c.Position]
}

private[creg]
case class ZeroOrMore[Gamma, +A](parser: Parser[Gamma, A])
    extends MultiParser[Gamma, A]
{
  def parse(c: Context, gamma: Gamma)(inputs: List[c.Tree]): Result[List[A], c.Position] = {
    import c.universe._
    inputs match {
      case Nil =>
        Success(Nil)

      case head :: tail =>
        for {
          a <- parser.parse(c, gamma)(head)
          as <- this.parse(c, gamma)(tail)
        }
        yield a :: as
    }
  }
}

private[creg]
case class OneOrMore[Gamma, A](things: String, parser: Parser[Gamma, A])
    extends MultiParser[Gamma, A]
{
  val zeroOrMore = ZeroOrMore(parser)

  def parse(c: Context, gamma: Gamma)(inputs: List[c.Tree]): Result[List[A], c.Position] = {
    import c.universe._
    inputs match {
      case Nil =>
        Failure(c.enclosingPosition, s"expect one or more $things, got zero of them")

      case head :: tail =>
        for {
          a <- parser.parse(c, gamma)(head)
          as <- zeroOrMore.parse(c, gamma)(tail)
        }
        yield a :: as
    }
  }
}
