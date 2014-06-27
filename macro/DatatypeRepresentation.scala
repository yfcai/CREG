object DatatypeRepresentation {
  // name of records, variants, fields
  type Name = String

  // data structure for fields
  // kept abstract for performance tuning later
  type Many[T] = Seq[T]
  val Many = Vector


  // datatype representation
  sealed trait Datatype {
    def holes: Set[Name]
  }

  // scala type, or, free type variable
  case class Scala(get: Name) extends ScalaOrHole {
    def sane: Boolean = true
    def holes = Set.empty
  }

  // hole, or, bound type variable
  case class Hole(name: Name) extends RecordOrHole {
    def holes: Set[Name] = Set(name)
  }

  case class Record(name: Name, fields: Many[Field]) extends RecordOrHole with ScalaOrHole {
    def holes: Set[Name] = fields.foldLeft(Set.empty[Name])(_ ++ _.holes)
  }

  case class Variant(name: Name, cases: Many[RecordOrHole]) extends Datatype {
    def holes: Set[Name] = cases.foldLeft(Set.empty[Name])(_ ++ _.holes)
  }

  case class FixedPoint(cons: DataConstructor) extends Datatype {
    def holes: Set[Name] = cons.body.holes -- cons.params
  }

  case class TypeApplication(operator: ScalaOrHole, operands: Many[Datatype]) extends Datatype {
    def holes: Set[Name] = operands.foldLeft(Set.empty[Name])(_ ++ _.holes)
  }


  // datatype representation helpers
  case class DataConstructor(params: Many[Name], body: Datatype)

  trait RecordOrHole extends Datatype {
    def name: Name
  }

  trait ScalaOrHole extends Datatype

  case class Field(name: Name, get: Datatype) {
    def holes: Set[Name] = get.holes
  }
}
