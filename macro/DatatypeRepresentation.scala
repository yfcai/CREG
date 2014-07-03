object DatatypeRepresentation {
  // name of records, variants, fields
  type Name = String

  // data structure for fields
  // kept abstract for performance tuning later
  type Many[T] = Seq[T]
  val Many = Vector


  // datatype representation
  sealed trait Datatype
  sealed trait Nominal { def name: Name }

  case class TypeVar(name: Name) extends Datatype
  case class Record(name: Name, fields: Many[Field]) extends Nominal with Datatype

  // variant is entry point from scala types, hence the header.
  case class Variant(header: TypeVar, cases: Many[Nominal]) extends Datatype

  case class FixedPoint(name: Name, body: Datatype) extends Nominal with Datatype

  // covariant function, produces anonymous types
  case class Reader(domain: TypeVar, range: Datatype) extends Datatype

  // with-composition, produces anonymous types
  case class Intersect(lhs: Datatype, rhs: Datatype) extends Datatype


  // datatype representation helpers
  case class DataConstructor(params: Many[Name], body: Datatype)

  case class Field(name: Name, get: Datatype) extends Nominal
}
