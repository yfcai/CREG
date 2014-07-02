object DatatypeRepresentation {
  // name of records, variants, fields
  type Name = String

  // data structure for fields
  // kept abstract for performance tuning later
  type Many[T] = Seq[T]
  val Many = Vector


  // datatype representation
  sealed trait Datatype

  // scala type, or, free type variable
  case class Scala(get: Name) extends ScalaOrHole
  // hole, or, bound type variable
  case class Hole(name: Name) extends RecordOrHole

  case class Record(name: Name, fields: Many[Field]) extends RecordOrHole with ScalaOrHole
  case class Variant(name: Name, cases: Many[RecordOrHole]) extends Datatype
  case class FixedPoint(cons: DataConstructor) extends Datatype

  // covariant function
  case class CovariantFunction(domain: Scala, range: Datatype) extends Datatype

  // with-composition
  case class Intersect(lhs: Record, rhs: Record) extends Datatype


  // datatype representation helpers
  case class DataConstructor(params: Many[Name], body: Datatype)

  sealed trait RecordOrHole extends Datatype {
    def name: Name
  }

  sealed trait ScalaOrHole extends Datatype

  case class Field(name: Name, get: Datatype)
}
