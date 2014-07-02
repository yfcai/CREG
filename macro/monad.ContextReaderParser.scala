package monad

import scala.reflect.macros.blackbox.Context

trait ContextReaderParser[A] {
  private[this] type Parser[X] = ContextReaderParser[X]

  // parse, or conventionally, runContextReaderParser
  // unfortunately return type is path-dependent & cannot be a synonym.
  def parse(c: Context)(input: List[c.Tree]): Either[(c.Position, String), (A, List[c.Tree])]

  def >== [B] (f: A => Parser[B]): Parser[B] = new ContextReaderParser[B] {
    def parse(c: Context)(input: List[c.Tree]): Either[(c.Position, String), (B, List[c.Tree])] =
      ContextReaderParser.this.parse(c)(input).right.flatMap {
        case (a, rest) => f(a).parse(c)(rest)
      }
  }

  def flatMap[B](f: A => Parser[B]): Parser[B] = this >== f
  def map[B](f: A => B): Parser[B] = this >== (ContextReaderParser.unit[B] compose f)

  // monad combinators following Kiama
  // https://code.google.com/p/kiama/wiki/Rewriting

  // sequencing with 1 side ignored: <*
  def <* [B] (that: Parser[B]): Parser[A] = for { a <- this ; b <- that } yield a
  def *> [B] (that: Parser[B]): Parser[B] = for { a <- this ; b <- that } yield b

  // deterministic choice: <+
  def <+ (that: Parser[A]): Parser[A] = new ContextReaderParser[A] {
    def parse(c: Context)(input: List[c.Tree]): Either[(c.Position, String), (A, List[c.Tree])] =
      ContextReaderParser.this.parse(c)(input).left.flatMap(_ => that.parse(c)(input))
  }
}


abstract class SingletonContextReaderParser[A](whatToExpect: String) extends ContextReaderParser[A] {
  def parseSingleton(c: Context)(input: c.Tree): Either[(c.Position, String), (A, List[c.Tree])]

  def fail(c: Context)(input: c.Tree): Either[(c.Position, String), (A, List[c.Tree])] =
    Left((input.pos, s"expect $whatToExpect"))

  def parse(c: Context)(input: List[c.Tree]): Either[(c.Position, String), (A, List[c.Tree])] =
    input match {
      case head :: tail =>
        parseSingleton(c)(head)

      case Nil =>
        // unexpected EOF.
        //
        // TENTATIVE: feeding a dummy error position for now.
        // the hope is that this case will never trigger,
        // because things triggering it shouldn't be syntax-correct scala code.
        //
        // Ideally, the position of the previous tree should be here.
        import c.universe._
        Left((q"".pos, s"unexpected <EOF> while parsing $whatToExpect"))
    }
}

object ContextReaderParser {
  def unit[A]: A => ContextReaderParser[A] = a => new ContextReaderParser[A] {
    def parse(c: Context)(input: List[c.Tree]): Either[(c.Position, String), (A, List[c.Tree])] = Right((a, input))
  }

  def apply[A](a: A): ContextReaderParser[A] = unit(a)
}
