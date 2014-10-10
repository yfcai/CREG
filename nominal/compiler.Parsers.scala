package nominal
package compiler

import scala.reflect.macros.blackbox.Context

import contextReaderParser._

trait Parsers extends util.AbortWithError {
  /** GRAMMAR FOR DATATYPE DECL WITH EXPLICIT FIXED POINTS
    *
    * EXAMPLE:
    *
    * @data    def List [A] = Fix(list => ListT { Nil ; Cons(head = A, tail = list) })
    *
    * @functor def elemF[A] = Fix(list => ListT { Nil ; Cons(head = A, tail = list) })
    *
    */
  import compiler.DatatypeRepresentation._

  def parseOrAbort[A](c: Context)(parser: contextReaderParser.Parser[A], input: c.Tree): A =
    parser.parse(c)(input) match {
      case Success(a) => a
      case Failure(pos, message) => abortWithError(c)(pos, message)
    }

  lazy val FunctorP: Parser[Functor.Decl] = DataDeclP map {
    case DataConstructor(name, params, body) =>
      Functor.Decl(name, params map (_.name), forgetRecordsVariants(body))
  }

  def forgetRecordsVariants(data: Datatype): Functor.Body =
    data match {
      case Variant(name, cases) if cases.nonEmpty =>
        Functor.Application(name, cases map forgetRecordsVariants)

      case Record(name, fields) if fields.nonEmpty =>
        Functor.Application(name, fields map (x => forgetRecordsVariants(x.get)))

      case noMembers: VariantCase =>
        Functor.TypeVar(noMembers.name)

      case FixedPoint(x, body) =>
        Functor.FixedPoint(x, forgetRecordsVariants(body))

      case TypeVar(x) => Functor.TypeVar(x)
    }

  lazy val DataDeclP: Parser[DataConstructor] = new Parser[DataConstructor] {
    def parse(c: Context)(input: c.Tree): Result[DataConstructor, c.Position] = {
      import c.universe._
      input match {
        case q"def $name[..$params] = $body" =>
          for { datatype <- DatatypeP.parse(c)(body) }
          yield DataConstructor(name.toString, mkGenericTypeParams(c)(params), datatype)

        case _ =>
          Failure(input.pos,
            """|expect something like:
               |
               |  def List[A] =
               |    Fix(list =>
               |      ListT {
               |        Nil
               |        Cons(head = A, tail = list)
               |      })
               |
               |.""".stripMargin)
      }
    }
  }

  lazy val DatatypeP: Parser[Datatype] = FixedPointP orElse CaseP

  lazy val FixP: Parser[Unit] = new Parser[Unit] {
    val expected = "Fix"

    def parse(c: Context)(input: c.Tree): Result[Unit, c.Position] =
      IdentifierP.parse(c)(input) flatMap { identifier =>
        if (identifier != expected)
          Failure(input.pos, s"expect the identifier `$expected` ")
        else
          Success(())
      }
  }

  lazy val FixedPointP: Parser[FixedPoint] = new Parser[FixedPoint] {
    def parse(c: Context)(input: c.Tree): Result[FixedPoint, c.Position] = {
      import c.universe._
      input match {
        case q"$fixCode($paramCode => $bodyCode)" =>
          for {
            _ <- FixP.parse(c)(fixCode)
            param <- OneParamP.parse(c)(paramCode)
            body <- CaseP.parse(c)(bodyCode)
          }
          yield FixedPoint(param, body)

        case _ =>
          Failure(input.pos, "expect Fix(param => body)")
      }
    }
  }

  // parse one parameter
  lazy val OneParamP: Parser[Name] = new Parser[Name] {
    def parse(c: Context)(input: c.Tree): Result[Name, c.Position] = {
      import c.universe._
      input match {
        case ValDef(modifiers, TermName(name), TypeTree(), EmptyTree) =>
          Success(name)

        case _ =>
          Failure(input.pos, s"expect ONE closure parameter, got ${showRaw(input)}")
      }
    }
  }

  lazy val VariantP: Parser[Variant] = new Parser[Variant] {
    lazy val CasesP: MultiParser[VariantCase] = OneOrMore("variant cases", CaseP)

    def parse(c: Context)(input: c.Tree): Result[Variant, c.Position] = {
      import c.universe._
      input match {
        case q"$variantHeader { ..$cases }" =>
          for {
            name  <- IdentifierP.parse(c)(variantHeader)
            cases <- CasesP.parse(c)(cases)
          }
          yield Variant(name, cases)

        case _ =>
          Failure(input.pos, "expect Variant { Case* }")
      }
    }
  }

  lazy val CaseP: Parser[VariantCase] = RecordP orElse VariantP

  lazy val RecordP = RecordWithoutFieldsP orElse RecordWithFieldsP

  lazy val RecordWithoutFieldsP: Parser[Record] = new Parser[Record] {
    def parse(c: Context)(input: c.Tree): Result[Record, c.Position] =
      for { recordName <- IdentifierP.parse(c)(input) } yield Record(recordName, Many.empty)
  }

  lazy val RecordWithFieldsP: Parser[Record] = new Parser[Record] {
    val FieldsP: MultiParser[Field] = ZeroOrMore(FieldP)

    def parse(c: Context)(input: c.Tree): Result[Record, c.Position] = {
      import c.universe._
      input match {
        case q"$recordName ( ..$fields )" =>
          if (fields.isEmpty)
            Failure(input.pos, "error: if this record has no field, do not put parentheses after it.")
          else {
            for {
              name <- IdentifierP.parse(c)(recordName)
              fields <- FieldsP.parse(c)(fields)
            }
            yield Record(name, fields)
          }

        case _ =>
          Failure(input.pos, "expect record with fields")
      }
    }
  }

  lazy val FieldP: Parser[Field] = new Parser[Field] {
    def parse(c: Context)(input: c.Tree): Result[Field, c.Position] = {
      import c.universe._
      input match {
        case q"$lhs = $rhs" =>
          for {
            label <- IdentifierP.parse(c)(lhs)
            body <- TypeVarP.parse(c)(rhs)
          }
          yield Field(label, body)

        case _ =>
          Failure(input.pos, "record fields must be named: <field-name> = <field-type>")
      }
    }
  }

  // TypeVarP succeeds on everything.
  lazy val TypeVarP: Parser[TypeVar] = new Parser[TypeVar] {
    def parse(c: Context)(input: c.Tree): Result[TypeVar, c.Position] =
      Success(TypeVar(c.universe.showCode(input)))
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

  def mkGenericTypeParams(c: Context)(params: List[c.Tree]): Many[Param] = {
    import c.universe._
    params.map {
      case typeDef @ TypeDef(mods, _, _, _) =>
        val name = typeDef.name.toString
        Param covariant name
    }
  }
}


object Parsers extends util.Persist with Parsers {
  import scala.language.experimental.macros
  import scala.annotation.StaticAnnotation

  /** parse a record */
  class record extends StaticAnnotation {
    def macroTransform(annottees: Any*): Any = macro recordImpl
  }

  def recordImpl(c: Context)(annottees: c.Tree*): c.Tree = {
    import c.universe._
    val q"def $tag = $input" = annottees.head
    val actual = parseOrAbort(c)(RecordP, input)
    q"val ${TermName(tag.toString)} = ${persist(c)(actual)}"
  }

  /** parse a datatype */
  class data extends StaticAnnotation {
    def macroTransform(annottees: Any*): Any = macro dataImpl
  }

  def dataImpl(c: Context)(annottees: c.Tree*): c.Tree = {
    import c.universe._
    val actual = parseOrAbort(c)(DataDeclP, annottees.head)
    q"val ${TermName(actual.name)} = ${persist(c)(actual)}"
  }

  /* TODO: restore testing macro for data families
    class familydecl extends StaticAnnotation {
      def macroTransform(annottees: Any*): Any =
        macro familydeclImpl
    }

    def familydeclImpl(c: Context)(annottees: c.Tree*): c.Tree = {
      import c.universe._
      val actual = parseOrAbort(c)(FamilyDeclP, annottees.head)
      q"val ${TermName(actual.name)} = ${persist(c)(actual)}"
    }
  */
}
