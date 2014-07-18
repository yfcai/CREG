package nominal
package compiler

object DatatypeRepresentation {
  // name of records, variants, fields
  type Name = String

  // data structure for fields
  // kept abstract for performance tuning later
  type Many[T] = Seq[T]
  val Many = Vector


  // datatype representation
  sealed trait Datatype {
    // traversals

    // real type:
    //
    // ∀ T <: Datatype.  T.everywhere : (∀ S <: Datatype.  S → S) → T
    //
    def everywhere(f: PartialFunction[Datatype, Datatype]): Datatype =
            f.applyOrElse(gmapT(_ everywhere f), identity[Datatype])

    def everywhereQ[T](f: PartialFunction[Datatype, T]): Iterator[T] =
      (f lift this).fold[Iterator[T]](Iterator.empty)(x => Iterator(x)) ++ children.flatMap(_ everywhereQ f)


    def gmapT(f: Datatype => Datatype): Datatype = this match {
      case TypeVar(_) =>
        this

      case Record(name, fields) =>
        Record(name, fields map { case Field(name, data) => Field(name, f(data)) })

      case Variant(name, cases) =>
        Variant(name,
          cases map {
            case Field(name, data) => Field(name, f(data))
            case data: Datatype => f(data).asInstanceOf[Nominal] /* unsafe cast */
          })

      case FixedPoint(name, body) =>
        FixedPoint(name, f(body))

      case Reader(domain, range) =>
        Reader(f(domain).asInstanceOf[TypeVar] /* unsafe cast */, f(range))

      case Intersect(lhs, rhs) =>
        Intersect(f(lhs), f(rhs))
    }

    def gmapQ[T](f: PartialFunction[Datatype, T]): Iterator[T] =
      children flatMap (child => f lift child)

    def children: Iterator[Datatype] = this match {
      case TypeVar(_) =>
        Iterator.empty

      case Record(name, fields) =>
        fields.iterator map (_.get)

      case Variant(name, cases) =>
        cases.iterator map {
          case Field(name, data) => data
          case data: Datatype => data
        }

      case FixedPoint(name, body) =>
        Iterator(body)

      case Reader(domain, range) =>
        Iterator(domain, range)

      case Intersect(lhs, rhs) =>
        Iterator(lhs, rhs)
    }
  }

  sealed trait Nominal { def name: Name }

  case class TypeVar(name: Name) extends Datatype

  case class Record(name: Name, fields: Many[Field]) extends Nominal with Datatype

  // variant is entry point from scala types, hence the header.
  case class Variant(header: TypeVar, cases: Many[Nominal]) extends Datatype

  case class FixedPoint(name: Name, body: Datatype) extends Nominal with Datatype {
    def patternFunctor: DataConstructor = DataConstructor(Many(Param covariant name), body)
  }

  // covariant function, produces anonymous types
  case class Reader(domain: TypeVar, range: Datatype) extends Datatype

  // with-composition, produces anonymous types
  case class Intersect(lhs: Datatype, rhs: Datatype) extends Datatype


  // datatype representation helpers

  case class Field(name: Name, get: Datatype) extends Nominal

  case class DataConstructor(params: Many[Param], body: Datatype) {
    def arity: Int = params.size
  }

  case class Param(name: Name, variance: Param.Variance)

  object Param {
    sealed trait Variance { def scalaSymbol: String }
    object Variance {
      case object Invariant     extends Variance { def scalaSymbol = ""  }
      case object Covariant     extends Variance { def scalaSymbol = "+" }
      case object Contravariant extends Variance { def scalaSymbol = "-" }
    }

    def invariant    (name: Name): Param = Param(name, Variance.Invariant)
    def covariant    (name: Name): Param = Param(name, Variance.Covariant)
    def contravariant(name: Name): Param = Param(name, Variance.Contravariant)
  }

}
