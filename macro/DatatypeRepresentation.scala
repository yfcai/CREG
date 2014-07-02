object DatatypeRepresentation {
  // name of records, variants, fields
  type Name = String

  // data structure for fields
  // kept abstract for performance tuning later
  type Many[T] = Seq[T]
  val Many = Vector


  // datatype representation
  sealed trait Datatype { def name: Name }

  case class TypeVar(name: Name) extends Datatype
  case class Record(name: Name, fields: Many[Field]) extends Datatype
  case class Variant(name: Name, cases: Many[Datatype]) extends Datatype

  case class FixedPoint(cons: DataConstructor) extends Datatype {
    def name: Name = cons match {
      case DataConstructor(Many(recursiveParam), _) =>
        recursiveParam

      case _ =>
        sys error s"fixed point of non-unary data constructor:\n\n$cons\n"
    }
  }

  // covariant function
  case class CovariantFunction(domain: TypeVar, range: Datatype) extends Datatype {
    def name: Name = s"(${domain.name} => ${range.name}"
  }

  // with-composition
  case class Intersect(lhs: Record, rhs: Record) extends Datatype {
    def name: Name = s"(${lhs.name} with ${rhs.name})"
  }


  // datatype representation helpers
  case class DataConstructor(params: Many[Name], body: Datatype)

  case class Field(name: Name, get: Datatype)
}
