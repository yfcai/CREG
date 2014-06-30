object DatatypeRepresentation {
  // name of records, variants, fields
  type Name = String

  // data structure for fields
  // kept abstract for performance tuning later
  type Many[T] = Seq[T]
  val Many = Vector


  // datatype representation
  sealed trait Datatype {
    def typeNames: Set[Name]
  }

  // scala type, or, free type variable
  case class Scala(get: Name) extends ScalaOrHole {
    def sane: Boolean = true
    lazy val typeNames: Set[Name] = Set(get) // all typeNames used
  }

  // hole, or, bound type variable
  case class Hole(name: Name) extends RecordOrHole {
    lazy val typeNames: Set[Name] = Set(name)
  }

  case class Record(name: Name, fields: Many[Field]) extends RecordOrHole with ScalaOrHole {
    lazy val typeNames: Set[Name] = fields.foldLeft(Set.empty[Name])(_ ++ _.typeNames) + name
  }

  case class Variant(name: Name, cases: Many[RecordOrHole]) extends Datatype {
    lazy val typeNames: Set[Name] = cases.foldLeft(Set.empty[Name])(_ ++ _.typeNames) + name
  }

  case class FixedPoint(cons: DataConstructor) extends Datatype {
    def typeNames: Set[Name] = cons.body.typeNames ++ cons.params
  }


  // datatype representation helpers
  case class DataConstructor(params: Many[Name], body: Datatype)

  sealed trait RecordOrHole extends Datatype {
    def name: Name
  }

  sealed trait ScalaOrHole extends Datatype

  case class Field(name: Name, get: Datatype) {
    lazy val typeNames: Set[Name] = get.typeNames
  }
}
