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
  sealed trait Datatype extends java.io.Serializable {
    // traversals

    // real type:
    //
    // ∀ T <: Datatype.  T.everywhere : (∀ S <: Datatype.  S → S) → T
    //
    def everywhere(f: PartialFunction[Datatype, Datatype]): Datatype =
            f.applyOrElse(gmapT(_ everywhere f), identity[Datatype])

    def everywhereQ[T](f: PartialFunction[Datatype, T]): Iterator[T] =
      (f lift this).fold[Iterator[T]](Iterator.empty)(x => Iterator(x)) ++ children.flatMap(_ everywhereQ f)

    def subst(x: Name, xdef: Datatype): Datatype = this match {
      case TypeVar(y) if x == y =>
        xdef

      case FixedPoint(y, body) if x == y =>
        this

      case other =>
        other gmapT (t => t.subst(x, xdef))
    }


    def gmapT(f: Datatype => Datatype): Datatype = this match {
      case TypeVar(_) =>
        this

      case Record(name, fields) =>
        Record(name, fields map { case Field(name, data) => Field(name, f(data)) })

      case Variant(name, cases) =>
        Variant(name,
          cases map {
            case Field(name, data) => Field(name, f(data))
            case RecordAssignment(record, typeVar) => RecordAssignment(record, f(typeVar).asInstanceOf[TypeVar])
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
          case RecordAssignment(record, typeVar) => typeVar
          case data: Datatype => data
        }

      case FixedPoint(name, body) =>
        Iterator(body)

      case Reader(domain, range) =>
        Iterator(domain, range)

      case Intersect(lhs, rhs) =>
        Iterator(lhs, rhs)
    }

    // variable renaming
    def rename(table: Map[Name, Name]): Datatype = this match {
      case TypeVar(x) if table contains x => TypeVar(table(x))
      case TypeVar(x) => TypeVar(x)
      case FixedPoint(x, body) => FixedPoint(x, body rename (table - x))
      case other => other gmapT (_ rename table)
    }

    def hasFreeOccurrencesOf(name: Name): Boolean = this match {
      case TypeVar(x) =>
        x == name

      case FixedPoint(x, body) =>
        x != name && body.hasFreeOccurrencesOf(name)

      case other =>
        val trueForChildren = other.gmapQ({ case t => t.hasFreeOccurrencesOf(name) })
        trueForChildren.nonEmpty && trueForChildren.max
    }

    def freevars: Set[Name] = this match {
      case TypeVar(x) =>
        Set(x)

      case FixedPoint(x, body) =>
        body.freevars - x

      case other =>
        other.gmapQ({ case t => t.freevars }).foldLeft(Set.empty[Name])(_ ++ _)
    }

    // unify names bound by fixed points
    def canonize: Datatype = {
      var i = -1
      def next() = { i += 1 ; s"canon$i" }

      def loop(data: Datatype): Datatype = data match {
        case FixedPoint(x, body) =>
          val newBody = loop(body)
          val y = next()
          FixedPoint(y, newBody subst (x, TypeVar(y)))

        case other =>
          other gmapT (child => child.canonize)
      }

      loop(this)
    }
  }

  sealed trait Nominal { def name: Name ; def get: Datatype ; def replaceBody(body: Datatype): Nominal }

  case class TypeVar(name: Name) extends Datatype

  case class Record(name: Name, fields: Many[Field]) extends Nominal with Datatype {
    def get = this
    def replaceBody(body: Datatype): Nominal = body.asInstanceOf[Nominal]
  }

  // variant is entry point from scala types, hence the header.
  case class Variant(header: TypeVar, cases: Many[Nominal]) extends Datatype

  object Variant {
    // overloaded constructor
    def apply(headerName: Name, cases: Many[Nominal]): Variant = Variant(TypeVar(headerName), cases)
  }

  case class FixedPoint(name: Name, body: Datatype) extends Nominal with Datatype {
    def patternFunctor: DataConstructor = DataConstructor(Many(Param covariant name), body)
    def get = this
    def replaceBody(body: Datatype): Nominal = copy(body = body)

    def unrollOnce: Datatype = body subst (name, this)
    def unrollToVariant: Variant = unrollOnce.asInstanceOf[Variant]
  }

  // covariant function, produces anonymous types
  case class Reader(domain: Datatype, range: Datatype) extends Datatype

  // with-composition, produces anonymous types
  case class Intersect(lhs: Datatype, rhs: Datatype) extends Datatype


  // datatype representation helpers

  case class Field(name: Name, get: Datatype) extends Nominal {
    def replaceBody(body: Datatype): Nominal = copy(get = body)
  }

  // pattern assignment
  case class RecordAssignment(record: Record, typeVar: TypeVar) extends Nominal {
    def name = record.name
    def get = typeVar
    def replaceBody(body: Datatype): Nominal = copy(typeVar = body.asInstanceOf[TypeVar])
  }

  case class DataConstructor(params: Many[Param], body: Datatype) {
    def arity: Int = params.size
  }

  case class Param(name: Name, variance: Param.Variance) {
    def toInvariant: Param = copy(variance = Param.Variance.Invariant)
  }

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
