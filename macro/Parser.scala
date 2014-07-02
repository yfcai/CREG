import scala.reflect.macros.blackbox.Context

import DatatypeRepresentation._
import monad.contextReaderParser._

trait Parser {

  // Grammar
  // =======
  //
  //      Start := DataDecl
  //             | FamilyDecl
  //
  //   DataDecl := trait Variant
  //
  // FamilyDecl := trait Name { Datatype* }
  //
  //   Datatype := TypeVar
  //             | Record
  //             | Variant
  //             | Function
  //             | Intersect
  //
  //    Variant := Name { Case* }
  //
  //       Case := Record
  //             | Name = Datatype -- use "=" for labelling to keep Datatype in scala term expr
  //
  //     Record := Name ( Field* )
  //
  //      Field := Datatype
  //             | Name = Datatype -- use "=" for labelling to keep Datatype in scala term expr
  //
  //     Reader := TypeVar =>: Datatype
  //
  //  Intersect := Datatype WITH Datatype
  //
  //
  // Reserved names
  // ==============
  //
  // __.* (all names starting with two underscores)
  // =>:  (term-level name of reader constructor)
  // WITH (term-level name of keyword `with`)
  //

  // shadow trait Parser by Parser[A]
  private[this] type Parser[A] = monad.contextReaderParser.Parser[A]

  // KEYWORDS
  final val keywordWITH : String = "WITH"
  final val keyword_=>: : String = "=>:"

  // parsers must be lazy val because they're mutually recursive
  lazy val DatatypeP: Parser[Datatype] = ???

  lazy val VariantP: Parser[Variant] = ???

  lazy val RecordP: Parser[Record] = ???

  /** matching a named param against q"$lhs = $rhs" succeeds,
    *  meaning we can match fields one by one
    */
  lazy val FieldP: Parser[PossiblyAnonymousField] = new Parser[PossiblyAnonymousField] {
    def parse(c: Context)(input: c.Tree): Result[PossiblyAnonymousField, c.Position] = {
      import c.universe._
      input match {
        case q"$lhs = $rhs" =>
          for {
            label <- IdentifierP.parse(c)(lhs)
            body <- DatatypeP.parse(c)(rhs)
          }
          yield NamedField(Field(label, body))

        case _ =>
          for { data <- DatatypeP.parse(c)(input) }
          yield AnonymousField(data)
      }
    }
  }

  sealed trait PossiblyAnonymousField
  sealed case class NamedField(get: Field) extends PossiblyAnonymousField
  sealed case class AnonymousField(get: Datatype) extends PossiblyAnonymousField

  lazy val ReaderP: Parser[Reader] = new Parser[Reader] {
    def parse(c: Context)(input: c.Tree): Result[Reader, c.Position] = {
      import c.universe._
      input match {
        case q"$domain.${ keyword_=>: }($range)" =>
          for {
            domainRes <- TypeVarP.parse(c)(domain)
            rangeRes <- DatatypeP.parse(c)(range)
          }
          yield Reader(domainRes, rangeRes)

        case _ =>
          Failure(input.pos, s"expect (X ${ keyword_=>: } Y)")
      }
    }
  }

  lazy val IntersectP: Parser[Intersect] = new Parser[Intersect] {
    def parse(c: Context)(input: c.Tree): Result[Intersect, c.Position] = {
      import c.universe._
      input match {
        case q"$lhs.$keywordWITH($rhs)" =>
          for {
            lhsRes <- DatatypeP.parse(c)(lhs)
            rhsRes <- DatatypeP.parse(c)(rhs)
          }
          yield Intersect(lhsRes, rhsRes)

        case _ =>
          Failure(input.pos, s"expect (X $keywordWITH Y)")
      }
    }
  }

  // TypeVarP succeeds on code that can be interpreted as scala type.
  //
  // will branching-by-exception cause performance issues?
  //
  lazy val TypeVarP: Parser[TypeVar] = new Parser[TypeVar] {
    def parse(c: Context)(input: c.Tree): Result[TypeVar, c.Position] = {
      import c.universe._
      try {
        val code = input.toString
        c.parse(s"??? : ($code)")
        Success(TypeVar(code))
      }
      catch {
        case e: reflect.macros.ParseException =>
          Failure(input.pos, "expect scala type or type variable")
      }
    }
  }

  // parses a scala identifier
  lazy val IdentifierP: Parser[String] = new Parser[String] {
    def parse(c: Context)(input: c.Tree): Result[String, c.Position] = {
      import c.universe._
      input match {
        case Ident(name) =>
          Success(name.toString)

        case _ =>
          Failure(input.pos, "expect identifier")
      }
    }
  }

}
