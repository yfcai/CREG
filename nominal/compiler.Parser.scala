package nominal
package compiler

import scala.reflect.macros.blackbox.Context

import DatatypeRepresentation._
import contextReaderParser._

trait Parser extends util.AbortWithError {

  // Grammar: Datatype
  // =================
  //
  //      Start := DataDecl
  //             | FamilyDecl
  //
  //   DataDecl := trait VariantName [ GenericTypeParam* ] { Case* }   -- annotated @datatype
  //
  // FamilyDecl := trait FamilyName [ GenericTypeParam* ] { Variant* } -- annotated @datafamily
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
  // Grammar: Functor
  // ================
  //
  //    Functor := ParamList => Datatype
  //
  //  ParamList := Name | (Name, Name, ...)  -- both cases are identical on AST level
  //
  //
  // Reserved names
  // ==============
  //
  // =>:  (term-level name of reader constructor)
  // WITH (term-level name of keyword `with`)
  //

  // shadow trait Parser by Parser[A]
  private[this] type Parser[A] = contextReaderParser.Parser[A]

  def parseOrAbort[A](c: Context)(parser: Parser[A], input: c.Tree): A =
    parser.parse(c)(input) match {
      case Success(a) => a
      case Failure(pos, message) => abortWithError(c)(pos, message)
    }

  lazy val FunctorP: Parser[DataConstructor] = new Parser[DataConstructor] {
    def parse(c: Context)(input: c.Tree): Result[DataConstructor, c.Position] = {
      import c.universe._
      input match {
        case Function(valDefs, body) =>
          for { datatype <- DatatypeP.parse(c)(body) }
          yield
            DataConstructor(
              valDefs map {
                case ValDef(modifiers, TermName(name), typeTree, emptyTree) =>
                  Param covariant name // all functor params are covariant
              },
              datatype)

        case _ =>
          Failure(input.pos, "expect a functor of the form  (TypeParam..) => Datatype")
      }
    }
  }

  lazy val DataDeclP: Parser[DataConstructor] = new Parser[DataConstructor] {
    def parse(c: Context)(input: c.Tree): Result[DataConstructor, c.Position] = {
      import c.universe._
      input match {
        // this quasiquote matches all decls with nonempty cases
        // and possibly empty genericTypeParams
        case q"trait $variantName [ ..$params ] { ..$cases }" =>
          for { cases <- CasesP.parse(c)(cases) }
          yield
            DataConstructor(
              mkGenericTypeParams(c)(params),
              Variant(
                mkVariantHeader(c)(variantName),
                Many(cases: _*)))

        // matches decls with empty cases & trailing braces
        case q"trait $variantName [ ..$params ] {}" =>
          Success(mkEmptyVariant(c)(variantName, params))

        // matches decls with neither cases nor trailing braces
        case q"trait $variantName [ ..$params ]" =>
          Success(mkEmptyVariant(c)(variantName, params))

        case _ =>
          Failure(input.pos, "expect trait Variant { Record* }")
      }
    }
  }

  def mkVariantHeader(c: Context)(name: c.TypeName): TypeVar = TypeVar(name.toString)

  def mkEmptyVariant(c: Context)(name: c.TypeName, params: List[c.Tree]): DataConstructor =
    DataConstructor(mkGenericTypeParams(c)(params), Variant(mkVariantHeader(c)(name), Many.empty))

  def mkGenericTypeParams(c: Context)(params: List[c.Tree]): Many[Param] = {
    import c.universe._
    Many(params.map(_ match {
      case typeDef @ TypeDef(mods, _, _, _) =>
        val name = typeDef.name.toString
        if (mods hasFlag Flag.COVARIANT)
          Param covariant name
        else if (mods hasFlag Flag.CONTRAVARIANT)
          Param contravariant name
        else
          Param invariant name
    }): _*)
  }

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
        case q"$domain =>: $range" => // keyword =>: has to be inlined in quasiquote...
          for {
            domainRes <- TypeVarP.parse(c)(domain)
            rangeRes <- DatatypeP.parse(c)(range)
          }
          yield Reader(domainRes, rangeRes)

        case _ =>
          Failure(input.pos, s"expect (X =>: Y)")
      }
    }
  }

  lazy val IntersectP: Parser[Intersect] = new Parser[Intersect] {
    def parse(c: Context)(input: c.Tree): Result[Intersect, c.Position] = {
      import c.universe._
      input match {
        case q"$lhs WITH $rhs" => // keyword WITH has to be inlined in quasiquote...
          for {
            lhsRes <- DatatypeP.parse(c)(lhs)
            rhsRes <- DatatypeP.parse(c)(rhs)
          }
          yield Intersect(lhsRes, rhsRes)

        case _ =>
          Failure(input.pos, s"expect (X WITH Y)")
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
  object Tests extends Parser with util.AssertEqual with util.Persist {
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

    class datadecl extends StaticAnnotation { def macroTransform(annottees: Any*): Any = macro datadecl.impl }
    object datadecl {
      def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
        import c.universe._

        val actual = parseOrAbort(c)(DataDeclP, annottees.head.tree)
        val DataConstructor(_, Variant(TypeVar(tag), _)) = actual

        val expected = tag.toString match {
          case "Empty1" | "Empty2" =>
            DataConstructor(Many.empty, Variant(TypeVar(tag), Many.empty))

          case "Empty3" | "Empty4" =>
            DataConstructor(
              Many(
                Param.invariant("W"),
                Param.invariant("X"),
                Param.covariant("Y"),
                Param.contravariant("Z")),
              Variant(TypeVar(tag), Many.empty))

          case "IntList" =>
            DataConstructor(
              Many.empty,
              Variant(TypeVar("IntList"), Many(
                Record("Nil", Many.empty),
                Record("Cons", Many(
                  Field("_1", TypeVar("Int")),
                  Field("_2", TypeVar("IntList")))))))

          case "WeirdList" =>
            DataConstructor(
              Many(
                Param.contravariant("A"),
                Param.covariant("B")),
              Variant(TypeVar("WeirdList"), Many(
                Field("Nil", TypeVar("B")),
                Record("Cons", Many(
                  Field("head", TypeVar("B")),
                  Field("tail", TypeVar("WeirdList[A, B]")))),
                Record("With", Many(
                  Field("_1", Intersect(TypeVar("WeirdList[A, B]"), TypeVar("B"))))),
                Record("More", Many(
                  Field("reader",
                    Reader(
                      TypeVar("A"),
                      Intersect(TypeVar("WeirdList[A, B]"), TypeVar("B")))))),
                Record("Over", Many(
                  Field("intersect",
                    Intersect(
                      Reader(TypeVar("A"), TypeVar("WeirdList[A, B]")),
                      TypeVar("B"))))))))

          case "Dept" =>
            DataConstructor(
              Many.empty,
              Variant(TypeVar("Dept"), Many(
                Record("D", Many(
                  Field("name", TypeVar("String")),
                  Field("manager",
                    Variant(TypeVar("Manager"), Many(
                      Record("E", Many(
                        Field("name", TypeVar("String")),
                        Field("salary",
                          Variant(TypeVar("Salary"), Many(
                            Record("S", Many(Field("_1", TypeVar("Float")))))))))))))))))
        }

        assertEqualObjects(expected, actual)
        c.Expr(q"")
      }
    }

    class functor extends StaticAnnotation { def macroTransform(annottees: Any*): Any = macro functorImpl }
    def functorImpl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
      import c.universe._
      annottees.head.tree match {
        case ValDef(mods, name, tpe, tree) =>
          c.Expr(ValDef(mods, name, tpe, persist(c)(parseOrAbort(c)(FunctorP, tree))))
      }
    }

  }
}
