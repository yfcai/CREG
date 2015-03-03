package nominal
package compiler

import scala.reflect.macros.blackbox.Context

import contextReaderParser._

trait Parsers extends util.AbortWithError with util.Paths {
  /** GRAMMAR FOR DATATYPE DECL WITH EXPLICIT FIXED POINTS
    *
    * EXAMPLE:
    *
    * @data    def List [A] = Fix(list => ListT { Nil ; Cons(head = A, tail = list) })
    *
    * @functor def elemF[A] = Fix(list => ListT { Nil ; Cons(head = A, tail = list) })
    *
    * @synonym def ElemF[A] = Fix(list => ListT { Nil ; Cons(head = A, tail = list) })
    *
    */
  import compiler.DatatypeRepresentation._

  trait ParserC[+A] extends Parser[Set[Name], A]

  def parseOrAbort[A](c: Context)(parser: Parser[Set[Name], A], input: c.Tree): A =
    parser.parse(c, Set.empty)(input) match {
      case Success(a) => a
      case Failure(pos, message) => abortWithError(c)(pos, message)
    }

  // convert returnType of DefDef into a series of traits to extend
  def supersP(c: Context): ParserC[Many[c.Tree]] = new ParserC[Many[c.Tree]] {
    def parse(d: Context, gamma: Set[Name])(input: d.Tree): Result[Many[c.Tree], d.Position] = {
      import c.universe._
      input.asInstanceOf[c.Tree] match {
        case DefDef(mods, name, params, args, returnType, body) => Success(returnType match {
          case CompoundTypeTree(Template(supers, selfType, stuff)) =>
            supers

          case tq"" =>
            Many.empty

          case other =>
            Many(other)
        })

        case _ =>
          Failure(input.pos, s"expect `def lhs: supers = rhs`, got $input")
      }
    }
  }

  lazy val StructVariantP: ParserC[Variant] =
    new ParserC[Variant]
  {
    lazy val CasesP = OneOrMore("variant cases", StructRecordP)

    def parse(c: Context, gamma: Set[Name])(input: c.Tree):
        Result[Variant, c.Position] =
      {
        import c.universe._
        input match {
        case DefDef(mods, name, params, args, returnType, q"{ ..$body }") =>
          val newGamma = gamma ++ getInitialGamma(c)(params)
            for { records <- CasesP.parse(c, newGamma)(body) }
            yield Variant(name.toString, records)

          case _ =>
            Failure(input.pos, "expect variant with records with field names")
        }
      }
  }

  lazy val DataDeclP: ParserC[DataConstructor] = new ParserC[DataConstructor] {
    def parse(c: Context, gamma: Set[Name])(input: c.Tree): Result[DataConstructor, c.Position] = {
      import c.universe._
      input match {
        case DefDef(mods, name, params, args, returnType, body) =>
          val newGamma = gamma ++ getInitialGamma(c)(params)
          for { datatype <- DatatypeP.parse(c, newGamma)(body) }
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

  lazy val DatatypeP: Parser[Set[Name], Datatype] = {
    FixedPointP orElse VariantP orElse
    FunctorApplicationP orElse
    LetBindingP orElse LetBindingBlockP orElse
    TypeVarP orElse
    // at top level, unknown names are interpretated as constants.
    // inside a variant, unknown names are interpreted as nullary records.
    // beware: TypeConstP succeeds on EVERYTHING.
    RecordWithFieldsP orElse TypeConstP
  }

  lazy val FixedPointP: ParserC[FixedPoint] = new ParserC[FixedPoint] {
    def parse(c: Context, gamma: Set[Name])(input: c.Tree): Result[FixedPoint, c.Position] = {
      import c.universe._
      input match {
        case q"$fixCode($paramCode => $bodyCode)" =>
          for {
            _ <- FixP.parse(c, gamma)(fixCode)
            param <- OneParamP.parse(c, gamma)(paramCode)
            bodyGamma = gamma + param
            body <- DatatypeP.parse(c, bodyGamma)(bodyCode)
          }
          yield FixedPoint(param, body)

        case _ =>
          Failure(input.pos, "expect Fix(param => body")
      }
    }
  }

  lazy val FixP: ParserC[Name] =
    mkContextSensitiveNameParser {
      (fix, _) => fix == "Fix"
    } {
      _ => "keyword `Fix`"
    }

  // parse one parameter
  lazy val OneParamP: ParserC[Name] = new ParserC[Name] {
    def parse(c: Context, gamma: Set[Name])(input: c.Tree): Result[Name, c.Position] = {
      import c.universe._
      input match {
        case ValDef(modifiers, TermName(name), TypeTree(), EmptyTree) =>
          Success(name)

        case _ =>
          Failure(input.pos, s"expect ONE closure parameter, got ${showRaw(input)}")
      }
    }
  }

  lazy val VariantP: ParserC[Variant] = new ParserC[Variant] {
    lazy val CasesP = OneOrMore("variant cases", CaseP)

    def parse(c: Context, gamma: Set[Name])(input: c.Tree): Result[Variant, c.Position] = {
      import c.universe._
      input match {
        case q"$variantName { ..$cases }" =>
          for {
            name <- UnboundNameP.parse(c, gamma)(variantName)
            cases <- CasesP.parse(c, gamma)(cases)
          }
          yield Variant(name, cases)

        case _ =>
          Failure(input.pos, "expect Variant { Case+ }")
      }
    }
  }

  lazy val CaseP: Parser[Set[Name], VariantCase] =
    RecordP orElse VariantP orElse AssignmentP orElse LetBindingP

  lazy val StructRecordP = RecordWithoutFieldsP orElse StructRecordWithFieldsP

  lazy val StructRecordWithFieldsP: ParserC[Record] = new ParserC[Record] {
    val FieldsP = OneOrMore("fields", WhateverNameP)

    def parse(c: Context, gamma: Set[Name])(input: c.Tree):
        Result[Record, c.Position] =
    {
      import c.universe._
      input match {
        case q"$recordName(..$fields)" =>
          for {
            name <- UnboundNameP.parse(c, gamma)(recordName)
            fields <- FieldsP.parse(c, gamma)(fields)
          }
          yield Record(name, fields map { x =>
            Field(x, TypeConst("Nothing"))
          })

        case _ =>
          Failure(input.pos, "expect record with field names")
      }
    }
  }

  lazy val RecordP = RecordWithoutFieldsP orElse RecordWithFieldsP

  lazy val RecordWithoutFieldsP = UnboundNameP map (name => Record(name, Many.empty))

  lazy val RecordWithFieldsP: ParserC[Record] = new ParserC[Record] {
    val FieldsP = OneOrMore("fields", FieldP)

    def parse(c: Context, gamma: Set[Name])(input: c.Tree): Result[Record, c.Position] = {
      import c.universe._
      input match {
        case q"$recordName(..$fields)" =>
          for {
            name <- UnboundNameP.parse(c, gamma)(recordName)
            fields <- FieldsP.parse(c, gamma)(fields)
          }
          yield Record(name, fields)

        case _ =>
          Failure(input.pos, "expect record with fields")
      }
    }
  }

  lazy val AssignmentP: ParserC[RecordAssignment] = new ParserC[RecordAssignment] {
    def parse(c: Context, gamma: Set[Name])(input: c.Tree): Result[RecordAssignment, c.Position] = {
      import c.universe._
      input match {
        case q"$recordIdent(..$fieldIdents) = $typeVarIdent" =>

          def failure[T](r: Result[T, c.Position]): Boolean = r match {
            case Failure(_, _) => true
            case Success(_)    => false
          }

          for {
            rcdName <- UnboundNameP.parse(c, gamma)(recordIdent)
            typevar <- TypeVarP.parse(c, gamma)(typeVarIdent)
            fieldNames = fieldIdents map (ident => WhateverNameP.parse(c, gamma)(ident))
            result <- {
              if (fieldNames exists failure)
                fieldNames.view.filter(failure).head.map(_ => sys error "IS_CAST")
              else
                Success(RecordAssignment(
                  Record(rcdName, fieldNames.map(r => Field(r.get, TypeConst(anyType)))),
                  typevar))
            }
          } yield result

        case _ =>
          Failure(input.pos, s"expect record assignment like Cons(head, tail) = tau, got $input")
      }
    }
  }

  lazy val LetBindingBlockP: ParserC[LetBinding] = new ParserC[LetBinding] {
    def parse(c: Context, gamma: Set[Name])(input: c.Tree): Result[LetBinding, c.Position] = {
      import c.universe._
      input match {
        case Block(List(letBinding), Literal(Constant(()))) =>
          LetBindingP.parse(c, gamma)(letBinding)

        case _ =>
          Failure(input.pos, s"expect { def lhs = rhs }, got $input")
      }
    }
  }

  lazy val LetBindingP: ParserC[LetBinding] = new ParserC[LetBinding] {
    def parse(c: Context, gamma: Set[Name])(input: c.Tree): Result[LetBinding, c.Position] = {
      import c.universe._
      input match {
        case q"def $lhs = $rhs" =>
          for { body <- CaseP.parse(c, gamma)(rhs) }
          yield LetBinding(lhs.toString, body)

        case _ =>
          Failure(input.pos, s"expect `def lhs = rhs`, got $input")
      }
    }
  }

  lazy val FieldP: ParserC[Field] = new ParserC[Field] {
    def parse(c: Context, gamma: Set[Name])(input: c.Tree): Result[Field, c.Position] = {
      import c.universe._
      input match {
        case q"$lhs = $rhs" =>
          for {
            label <- WhateverNameP.parse(c, gamma)(lhs)
            body <- FieldBodyP.parse(c, gamma)(rhs)
          }
          yield Field(label, body)

        case _ =>
          Failure(input.pos, "record fields must be named: <field-name> = <field-type>")
      }
    }
  }

  // basically DatatypeP, but instead of 0-nary records we have type constants
  lazy val FieldBodyP = {
    FixedPointP orElse VariantP orElse RecordWithFieldsP orElse
    FunctorApplicationP orElse
    TypeVarP orElse TypeConstP
  }

  // context-sensitive type constant
  // a type constant must NOT be bound in the context gamma
  lazy val TypeConstP: ParserC[TypeConst] = new ParserC[TypeConst] {
    def parse(c: Context, gamma: Set[Name])(input: c.Tree): Result[TypeConst, c.Position] = {
      import c.universe._
      input match {
        case Ident(name) if gamma(name.toString) =>
          Failure(input.pos, "type constant must NOT be bound")

        case other =>
          Success(TypeConst(c.universe showCode input))
      }
    }
  }

  // parser of whatever names, useful for field labels
  lazy val WhateverNameP: ParserC[Name] =
    mkContextSensitiveNameParser {
      (_, _) => true
    } {
      _ => "whatever name"
    }

  // parser of unbound name, useful for record/variant declarations
  lazy val UnboundNameP: ParserC[Name] =
    mkContextSensitiveNameParser {
      (name, gamma) => ! gamma(name)
    } {
      _ => "unbound name"
    }

  // context-sensitive type variable
  // a type variable must be bound in the context gamma
  lazy val TypeVarP: Parser[Set[Name], TypeVar] =
    mkContextSensitiveNameParser {
      (name, gamma) => gamma(name)
    } {
      _ => "bound type variable"
    } map TypeVar

  lazy val FunctorApplicationP: ParserC[FunctorApplication] = new ParserC[FunctorApplication] {
    lazy val ArgsP = OneOrMore("functor arguments", DatatypeP)

    def parse(c: Context, gamma: Set[Name])(input: c.Tree): Result[FunctorApplication, c.Position] = {
      import c.universe._
      input match {
        case q"$functorName apply (..$functorArgs)" =>
          for {
            functor <- TypeConstP.parse(c, gamma)(functorName)
            args <- ArgsP.parse(c, gamma)(functorArgs)
          }
          yield FunctorApplication(functor, args)

        case _ =>
          Failure(input.pos, s"expect functor application `f apply (x, y, ...)`; got ${showCode(input)}")
      }
    }
  }

  def mkContextSensitiveNameParser(
    predicate: (Name, Set[Name]) => Boolean)(
    expected: Set[Name] => String):
      ParserC[Name] =
    new ParserC[Name] {
      def parse(c: Context, gamma: Set[Name])(input: c.Tree): Result[Name, c.Position] = {
        import c.universe._
        input match {
          case Ident(name) if predicate(name.toString, gamma) =>
            Success(name.toString)

          case _ =>
            //DEBUG
            if (input.toString == "binding") {
              println
              println(showRaw(input))
              println
              println(gamma)
              println
            }
            Failure(input.pos, s"expect ${expected(gamma)}, got $input")
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

  def getInitialGamma(c: Context)(params: List[c.Tree]): Set[Name] = {
    import c.universe._
    Set(params map {
      case TypeDef(mods, name, params, rhs) =>
        name.toString
    }: _*)
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

  /** parse a struct decl */
  class struct extends StaticAnnotation {
    def macroTransform(annottees: Any*): Any = macro structImpl
  }

  def structImpl(c: Context)(annottees: c.Tree*): c.Tree = {
    import c.universe._
    val actual = parseOrAbort(c)(StructVariantP, annottees.head)
    q"val ${TermName(actual.name)} = ${persist(c)(actual)}"
  }

  class oneparser extends StaticAnnotation {
    def macroTransform(annottees: Any*): Any = macro oneparserImpl
  }

  lazy val OneParser = FixedPointP

  def oneparserImpl(c: Context)(annottees: c.Tree*): c.Tree = {
    import c.universe._
    annottees.head match {
      case DefDef(mods, name, params, args, returnType, body) =>
        val gamma = getInitialGamma(c)(params)
        val actual = OneParser.parse(c, gamma)(body).get
        q"val $name = ${persist(c)(actual)}"
    }
  }
}
