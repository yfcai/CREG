package nominal
package compiler

import scala.reflect.macros.blackbox.Context

import contextReaderParser._

trait ParserBase extends util.AbortWithError {
  def parseOrAbort[A](c: Context)(parser: contextReaderParser.Parser[A], input: c.Tree): A =
    parser.parse(c)(input) match {
      case Success(a) => a
      case Failure(pos, message) => abortWithError(c)(pos, message)
    }
}

object ParserOfDatatypeRep {
  import DatatypeRepresentation._

  // put everything we want to serialize in an object
  // if it's an inner class of some trait, then it includes a back pointer
  // to the trait, which probably have nonserializable members.
  case class DataFamily(name: Name, params: Many[Name], members: Many[Variant])
}

trait ParserOfDatatypeRep extends ParserBase with util.TupleIndex with util.Traits {
  // ====================================
  // GRAMMARS FOR DATATYPE REPRESENTATION
  // ====================================
  //
  // Grammar: Datatype
  // =================
  //
  //      Start := DataDecl
  //             | FamilyDecl
  //
  //   DataDecl := trait VariantName [ GenericTypeParam* ] extends Supertraits { Case* }
  //
  // FamilyDecl := trait FamilyName [ GenericTypeParam* ] extends Supertraits { Variant* }
  //
  //    Variant := TypeVar { Case* } -- entry point from scala types
  //
  //       Case := Record
  //             | Name = TypeVar
  //
  //     Record := Name              -- record without fields, a single case object
  //             | Name ( Field+ )   -- record with fields
  //
  //      Field := TypeVar
  //             | Name = TypeVar    -- use "=" for labelling to keep Datatype in scala term expr
  //
  //
  // Reserved names
  // ==============
  //
  // _\d+ (tuple components _1, _2, _3, ...; _i must be the (i - 1)th field)

  import DatatypeRepresentation._
  import ParserOfDatatypeRep._

  // shadow trait Parser by Parser[A]
  private[this] type Parser[A] = contextReaderParser.Parser[A]

  lazy val FamilyDeclP: Parser[DataFamily] = new Parser[DataFamily] {
    val VariantsP: MultiParser[Variant] = ZeroOrMore(VariantP)

    def parse(c: Context)(input: c.Tree): Result[DataFamily, c.Position] = {
      import c.universe._
      nameParamsSupersMembers(c)(input) match {
        case Some((familyName, params, supers, members)) =>
          for { variants <- VariantsP.parse(c)(members) }
          yield
            DataFamily(
              familyName.toString,
              getNamesOfTypeDefs(c)(params),
              variants)

        case _ =>
          Failure(input.pos, "expect trait Family { Variant* }")
      }
    }
  }

  lazy val DataDeclP: Parser[DataConstructor] = new Parser[DataConstructor] {
    def parse(c: Context)(input: c.Tree): Result[DataConstructor, c.Position] = {
      import c.universe._
      nameParamsSupersMembers(c)(input) match {
        case Some((variantName, params, supers, cases)) =>
          for { cases <- CasesP.parse(c)(cases) }
          yield
            DataConstructor(
              mkGenericTypeParams(c)(params),
              Variant(
                TypeVar(variantName.toString),
                Many(cases: _*)))

        case _ =>
          Failure(input.pos, "expect trait Variant { Record* }")
      }
    }
  }

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
          else {
            for {
              name <- IdentifierP.parse(c)(recordName)
              possiblyAnonymousFields <- FieldsP.parse(c)(fields)
            }
            yield Record(
              name,
              possiblyAnonymousFields.zipWithIndex.map {
                case (AnonymousField(data), i) =>
                  val label = s"_${i + 1}" // "_1", "_2", "_3" etc; scala will make sure named follows anonymous
                  Field(label, data)

                case (NamedField(field), i) =>
                  // test that no field violates naming convention
                  // that _i occurs only at the (i - 1)th position
                  val wellFormed = tupleIndex(field.name).map(_ == i).getOrElse(true)
                  if (! wellFormed) {
                    val j = i + 1
                    val th = (j % 10) match {
                      case 1 => "st"
                      case 2 => "nd"
                      case 3 => "rd"
                      case _ => "th"
                    }
                    abortWithError(c)(
                      fields(i).pos,
                      s"if the $j$th field's name has to begin with an underscore, " +
                        s"then it must be _$j.")
                  }

                  field
              }
            )
          }

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
            body <- TypeVarP.parse(c)(rhs)
          }
          yield NamedField(Field(label, body))

        case _ =>
          for { data <- TypeVarP.parse(c)(input) }
          yield AnonymousField(data)
      }
    }
  }

  sealed trait PossiblyAnonymousField
  sealed case class NamedField(get: Field) extends PossiblyAnonymousField
  sealed case class AnonymousField(get: Datatype) extends PossiblyAnonymousField

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
}

trait ParserOfFunctorRep extends ParserBase {
  // ============================================================================
  // GRAMMAR FOR FUNCTOR REPRESENTATION (NOT TO BE CONFUSED WITH DATACONSTRUCTOR)
  // ============================================================================
  //
  // decl := params => body
  //
  // params := typevar
  //         | (typevar, typevar, ..., typevar)
  //
  // body := typevar
  //       | fixed-point
  //       | application
  //       | constant
  //
  // fixed-point := Fix(typevar => body)
  //
  // application := scala-functor(body, body, ..., body)
  //
  // scala-functor := code
  //
  // constant := code
  //
  // code := a scala identifier

  import nominal.compiler.Functor._
  private[this] type Parser[A] = contextReaderParser.Parser[A]

  lazy val DeclP: Parser[Decl] = new Parser[Decl] {
    def parse(c: Context)(input: c.Tree): Result[Decl, c.Position] = {
      import c.universe._
      input match {
        case Function(valDefs, bodyCode) =>
          for { body <- BodyP.parse(c)(bodyCode) }
          yield Decl(valDefs map { case ValDef(_, TermName(name), _, _) => name }, body)
      }
    }
  }

  // sadly, constants and type variables are indistinguishable bottom-up
  lazy val BodyP: Parser[Body] = TypeVarP <+ FixedPointP <+ ApplicationP

  lazy val FixedPointP: Parser[FixedPoint] = new Parser[FixedPoint] {
    def parse(c: Context)(input: c.Tree): Result[FixedPoint, c.Position] = {
      import c.universe._
      input match {
        case q"$fixCode($paramCode => $bodyCode)" =>
          for {
            _ <- FixP.parse(c)(fixCode)
            param <- OneParamP.parse(c)(paramCode)
            body <- BodyP.parse(c)(bodyCode)
          }
          yield FixedPoint(param, body)

        case _ =>
          Failure(input.pos, "expect Fix(param => body)")
      }
    }
  }

  // parse the identifier "Fix" and nothing else
  lazy val FixP: Parser[Unit] = new Parser[Unit] {
    val expected = "Fix"

    def parse(c: Context)(input: c.Tree): Result[Unit, c.Position] =
      CodeP.parse(c)(input) flatMap { identifier =>
          if (identifier != expected)
            Failure(input.pos, s"expect the identifier `$expected` ")
          else
            Success(())
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

  lazy val ApplicationP: Parser[Application] = new Parser[Application] {
    // ArgsP has to be lazy coz it's a part of the recursion cycle
    // if it weren't, then it will force a cycle, ending up throwing StackOverflowError
    lazy val ArgsP: MultiParser[Body] = ZeroOrMore(BodyP)

    def parse(c: Context)(input: c.Tree): Result[Application, c.Position] = {
      import c.universe._
      input match {
        case q"$functorCode(..$argsCode)" =>
          for {
            functor <- CodeP.parse(c)(functorCode)
            args <- ArgsP.parse(c)(argsCode)
          }
          yield Application(functor, args)

        case _ =>
          Failure(input.pos, "expect functor application")
      }
    }
  }

  lazy val TypeVarP: Parser[TypeVar] = CodeP map TypeVar

  lazy val CodeP: Parser[Code] = new Parser[Code] {
    def parse(c: Context)(input: c.Tree): Result[Code, c.Position] = {
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
  object Tests extends ParserOfDatatypeRep with util.AssertEqual with util.Persist {
    import scala.language.experimental.macros
    import scala.annotation.StaticAnnotation
    import DatatypeRepresentation._

    class record extends StaticAnnotation {
      def macroTransform(annottees: Any*): Any = macro recordImpl
    }

    def recordImpl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
      import c.universe._

      val q"trait $tag { $input }" = annottees.head.tree
      val actual = RecordP.parse(c)(input).get

      c.Expr(q"val ${TermName(tag.toString)} = ${persist(c)(actual)}")
    }

    class datadecl extends StaticAnnotation {
      def macroTransform(annottees: Any*): Any = macro datadeclImpl
    }

    def datadeclImpl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
      import c.universe._

      val actual = parseOrAbort(c)(DataDeclP, annottees.head.tree)
      val DataConstructor(_, Variant(TypeVar(tag), _)) = actual

      c.Expr(q"val ${TermName(tag.toString)} = ${persist(c)(actual)}")
    }

    class familydecl extends StaticAnnotation {
      def macroTransform(annottees: Any*): Any =
        macro familydeclImpl
    }

    def familydeclImpl(c: Context)(annottees: c.Tree*): c.Tree = {
      import c.universe._
      val actual = parseOrAbort(c)(FamilyDeclP, annottees.head)
      q"val ${TermName(actual.name)} = ${persist(c)(actual)}"
    }
  }
}
