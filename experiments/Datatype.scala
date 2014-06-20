/** Experiment: representation of datatypes
  * - datatype as data
  * - named n-hole context of datatype
  *
  * After migration inside macro:
  * - conversion between scala type and datatype representation
  * - generation of n-nary functor instances from named n-hole contexts
  */

trait Datatypes {
  // name of records, variants, fields
  type Name      = reflect.runtime.universe.Symbol

  // data structure for fields
  // kept abstract for performance tuning later
  type Many[T] = Array[T]
  val Many = Array
  def toMany[T: reflect.ClassTag](c0: collection.GenTraversableOnce[T]): Many[T] = c0.toArray


  // datatype representation
  sealed trait Datatype {
    def holes: Set[Name]
  }

  case class Scala(get: reflect.runtime.universe.Type) extends Datatype {
    def sane: Boolean = true
    def holes = Set.empty
  }

  case class Record(name: Name, fields: Many[Field]) extends RecordOrHole {
    def holes: Set[Name] = fields.foldLeft(Set.empty[Name])(_ ++ _.holes)
  }

  case class Variant(name: Name, cases: Many[RecordOrHole]) extends Datatype {
    def holes: Set[Name] = cases.foldLeft(Set.empty[Name])(_ ++ _.holes)
  }

  case class FixedPoint(cons: DataConstructor) extends Datatype {
    def holes: Set[Name] = cons.body.holes -- cons.params
  }

  case class Hole(name: Name) extends RecordOrHole {
    def holes: Set[Name] = Set(name)
  }


  // datatype representation helpers
  case class DataConstructor(params: Many[Name], body: Datatype)

  trait RecordOrHole extends Datatype {
    def name: Name
  }

  case class Field(name: Name, get: Datatype) {
    def holes: Set[Name] = get.holes
  }
}
