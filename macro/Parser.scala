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
  //   DataDecl := trait VariantName [ GenericTypeParam* ] { Case* }
  //
  // FamilyDecl := trait FamilyName [ GenericTypeParam* ] { DataDecl* }
  //
  //   Datatype := Variant           -- note the absence of `Record`
  //             | Reader
  //             | Intersect
  //             | TypeVar           -- TypeVar can designate any scala type
  //
  //    Variant := TypeVar { Case* } -- entry point from scala types
  //
  //       Case := Record
  //             | Name = TypeVar
  //
  //     Record := Name              -- record without fields, a single case object
  //             | Name ( Field+ )   -- record with fields
  //
  //      Field := Datatype
  //             | Name = Datatype   -- use "=" for labelling to keep Datatype in scala term expr
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

  //lazy val DataDeclP: Parser[

  // parsers must be lazy val because they're mutually recursive
  lazy val DatatypeP: Parser[Datatype] =
    VariantP <+ ReaderP <+ IntersectP <+ TypeVarP

  lazy val VariantP: Parser[Variant] = new Parser[Variant] {
    def parse(c: Context)(input: c.Tree): Result[Variant, c.Position] = {
      import c.universe._
      input match {
        case q"$variantHeader { ..$cases }" =>
          for {
            typeVar <- TypeVarP.parse(c)(variantHeader)
            cases <- CasesP.parse(c)(cases)
          }
          yield Variant(typeVar, Many(cases: _*))

        case _ =>
          Failure(input.pos, "expect Variant { Case* }")
      }
    }
  }

  lazy val CasesP: MultiParser[Nominal] = ZeroOrMore(CaseP)

  lazy val CaseP: Parser[Nominal] = new Parser[Nominal] {
    def parse(c: Context)(input: c.Tree): Result[Nominal, c.Position] = {
      import c.universe._
      input match {
        case q"$lhs = $rhs" =>
          for {
            label <- IdentifierP.parse(c)(lhs)
            data <- TypeVarP.parse(c)(rhs)
          }
          yield Field(label, data) // labelled data: Name = TypeVar

        case _ =>
          RecordP.parse(c)(input) // Record
      }
    }
  }

  lazy val RecordP: Parser[Record] = RecordWithoutFieldsP <+ RecordWithFieldsP

  lazy val RecordWithoutFieldsP: Parser[Record] = new Parser[Record] {
    def parse(c: Context)(input: c.Tree): Result[Record, c.Position] =
      for { recordName <- IdentifierP.parse(c)(input) } yield Record(recordName, Many.empty)
  }

  lazy val RecordWithFieldsP: Parser[Record] = new Parser[Record] {
    val FieldsP: MultiParser[PossiblyAnonymousField] = ZeroOrMore(FieldP)

    def parse(c: Context)(input: c.Tree): Result[Record, c.Position] = {
      import c.universe._
      input match {
        case q"$recordName ( ..$fields )" =>
          if (fields.isEmpty)
            Failure(input.pos, "error: if this record has no field, do not put parentheses after it.")
          else
            for {
              name <- IdentifierP.parse(c)(recordName)
              possiblyAnonymousFields <- FieldsP.parse(c)(fields)
            }
            yield Record(
              name,
              Many(possiblyAnonymousFields: _*).zipWithIndex.map {
                case (AnonymousField(data), i) =>
                  val label = s"_${i + 1}" // "_1", "_2", "_3" etc; scala will make sure named follows anonymous
                  Field(label, data)

                case (NamedField(field), _) =>
                  field
              }
            )

        case _ =>
          Failure(input.pos, "expect record with fields")
      }
    }
  }

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
        case q"$range.${ keyword_=>: }($domain)" =>
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
  lazy val IdentifierP: Parser[Name] = new Parser[Name] {
    def parse(c: Context)(input: c.Tree): Result[Name, c.Position] = {
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


object Parser {
  object Tests extends Parser with AssertEqual {
    import scala.language.experimental.macros
    import scala.annotation.StaticAnnotation

    class record extends StaticAnnotation { def macroTransform(annottees: Any*): Any = macro record.impl }
    object record {
      def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
        import c.universe._

        val q"trait $tag { $input }" = annottees.head.tree
        val actual = RecordP.parse(c)(input).get

        val expected = tag.toString match {
          case "WithoutFields" =>
            Record("SomeRecord", Many.empty)

          case "WithFields" =>
            Record("SomeRecord", Many(
              Field("_1", TypeVar("Field1")),
              Field("_2", TypeVar("Field2")),
              Field("field3", TypeVar("Field3")),
              Field("field4", TypeVar("Field4")),
              Field("_5", TypeVar("Field5"))))
        }

        assertEqualObjects(expected, actual)
        c.Expr(q"")
      }
    }

  }
}
