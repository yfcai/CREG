import scala.reflect.macros.blackbox.Context

import DatatypeRepresentation._

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
  //    Variant := Name { (Record | TypeVar)* }
  //
  //     Record := Name ( Field* )
  //
  //      Field := Datatype
  //             | Name : Datatype
  //
  //     Reader := TypeVar => Datatype
  //
  //  Intersect := Datatype with Datatype
  //
  //
  // Reserved names
  // ==============
  //
  // __.* (all names starting with two underscores)

  private[this] type Parser[A] = monad.ContextReaderParser[A]
  private[this] type Singleton[A] = monad.SingletonContextReaderParser[A]

  // parsers must be lazy val because they're mutually recursive
  lazy val DatatypeP: Parser[Datatype] = ???

  lazy val VariantP: Parser[Variant] = ???

  lazy val RecordP: Parser[Record] = ???

  lazy val FieldP: Parser[Field] = ???

  lazy val ReaderP: Parser[Reader] = ???

  /*
  lazy val IntersectP: Parser[Intersect] = new Singleton[Intersect]("(X with Y)") {
    def parseSingleton(c: Context)(input: c.Tree): Either[(c.Position, String), (A, List[c.Tree])] = {
      import c.universe._
      q"??? : $input" match {
        case q"??? : ($lhs with $rhs)" =>
          for {
            lres <- DatatypeP.parse(c)(List(lhs)).right
            rres <- DatatypeP.parse(c)(List(rhs)).right
          }
          yield Intersect(lres._1, rres._1)

        case _ =>
          fail(c)(input)
      }
    }
  }
   */

}
