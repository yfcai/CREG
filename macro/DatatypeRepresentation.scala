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
  case class DataConstructor(params: Many[Param], body: Datatype)

  case class Field(name: Name, get: Datatype) extends Nominal

  case class Param(name: Name, variance: Flag.VARIANCE)

  object Param {
    def invariant(name: Name): Param = Param(name, Flag.INVARIANT)
    def covariant(name: Name): Param = Param(name, Flag.COVARIANT)
    def contravariant(name: Name): Param = Param(name, Flag.CONTRAVARIANT)
  }


  // non-path-dependent mirror of Context.universe.Flag
  object Flag {
    sealed trait VARIANCE { def scalaSymbol: String }
    case object INVARIANT     extends VARIANCE { def scalaSymbol = ""  }
    case object COVARIANT     extends VARIANCE { def scalaSymbol = "+" }
    case object CONTRAVARIANT extends VARIANCE { def scalaSymbol = "-" }
  }
}
