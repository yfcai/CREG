package nominal
package compiler

import lib.Applicative
import lib.Applicative._

object DatatypeRepresentation extends util.Paths {
  // name of records, variants, fields
  type Name = String

  // data structure for fields
  // kept abstract for performance tuning later
  type Many[T] = Seq[T]
  val Many = Vector

  // datatype representation
  sealed trait Datatype extends java.io.Serializable with DatatypeLike[Datatype]

  sealed trait DatatypeLike[+This <: Datatype with DatatypeLike[This]] {
    this: This with java.io.Serializable =>

    type =>:[T, R] = PartialFunction[T, R]

    def children: Iterator[Datatype]

    val construct: Iterator[Datatype] => This

    def gmapT(f: Datatype =>: Datatype): This = construct(children map (x => f.applyOrElse(x, identity[Datatype])))

    def everywhere(f: Datatype =>: Datatype): This =
      f.applyOrElse(gmapT({ case x => x everywhere f }), identity[This]).asInstanceOf[This]

    def gmapQ[R](f: Datatype =>: R): Iterator[R] =
      children.flatMap(x => f.lift(x).iterator)

    def everything[R](f: Datatype =>: R): Iterator[R] =
      (f lift this).iterator ++ children.flatMap(_ everything f)

    def exist(predicate: PartialFunction[Datatype, Unit]): Boolean = everything(predicate).nonEmpty

    def subst(mapping: Map[Name, Datatype]): Datatype =
      if (mapping.isEmpty)
        this
      else (this: Datatype) match {
        case TypeVar(y) if mapping contains y =>
          mapping(y)

        case FixedPoint(y, body) =>
          val newMapping = mapping - y
          FixedPoint(y, body subst newMapping)

        case _ =>
          gmapT { case t => t subst mapping }
      }

    def subst(x: Name, xdef: Datatype): Datatype = subst(Map(x -> xdef))

    def rename(table: Map[Name, Name]): This = ((this: Datatype) match {
      case TypeVar(x) if table contains x =>
        TypeVar(table(x))

      case TypeVar(_) =>
        this

      case FixedPoint(x, body) =>
        val newTable = table - x
        if (newTable.isEmpty)
          this
        else
          FixedPoint(x, body rename newTable)

      case _ =>
        gmapT { case x => x rename table }
    }).asInstanceOf[This]

    def hasFreeOccurrencesOf(name: Name): Boolean = freevars(name)

    lazy val freevars: Set[Name] = (this: Datatype) match {
      case TypeVar(x) => Set(x)
      case FixedPoint(x, body) => body.freevars - x
      case _ => gmapQ({ case t => t.freevars }).foldLeft(Set.empty[Name])(_ ++ _)
    }

    def canonize: Datatype = {
      var i = -1
      def next() = { i += 1 ; s"canon$i" }

      object loop extends (Datatype =>: Datatype) {
        def apply(data: Datatype) = data match {
          case FixedPoint(x, body) =>
            val newBody = loop(body)
            val y = next()
            FixedPoint(y, newBody rename Map(x -> y))

          case other =>
            other gmapT this
        }

        def isDefinedAt(x: Datatype) = true
      }

      loop(this)
    }

    /** inject a tuple into each record */
    def injectTuples: This = everywhere {
      case Record(name, fields) if fields.length > 1 =>
        val n = fields.length
        Record(name, Many(
          Field(getSingleRecordFieldName,
            Record(tuplePath(n), fields))))
    }
  }

  // here to support legacy code in UniverseConstruction.carePackage
  // remove after rewriting reification
  sealed trait Nominal { def name: Name ; def get: Datatype }

  // cases for a variant, can be records or variants
  sealed trait VariantCase extends Datatype with Nominal with DatatypeLike[VariantCase] { def get = this }

  // let-bindings: basically ID with extra synonym request
  case class LetBinding(lhs: Name, rhs: VariantCase) extends VariantCase with DatatypeLike[LetBinding] {
    def name = rhs.name
    def children = Iterator(rhs)
    final val construct: Iterator[Datatype] => LetBinding =
      children => copy(rhs = children.next.asInstanceOf[VariantCase])
  }

  // List { Nil = x, Cons(head, tail) = y }
  case class RecordAssignment(lhs: Record, rhs: TypeVar) extends VariantCase with DatatypeLike[RecordAssignment] {
    def name = lhs.name
    def children = Iterator(rhs)
    final val construct: Iterator[Datatype] => RecordAssignment =
      children => {
        val rhs = children.next.asInstanceOf[TypeVar]
        children.dropWhile(_ => true) // set iterator to empty
        copy(rhs = rhs)
      }

    // modify record assignment behavior
    def toRecord: Record =
      Record(lhs.name, Many(Field(getSingleRecordFieldName, rhs)))
  }

  case class FunctorApplication(functor: TypeConst, args: Many[Datatype])
      extends Datatype with DatatypeLike[FunctorApplication]
  {
    def children = args.iterator
    final val construct: Iterator[Datatype] => FunctorApplication =
      children => copy(args = children.toSeq)

    def functorArity: Int = args.length
  }

  case class TypeVar(name: Name) extends Datatype with DatatypeLike[TypeVar] {
    def children = Iterator.empty
    final val construct = (x: Iterator[Datatype]) => this
  }

  case class TypeConst(code: Name) extends Datatype with DatatypeLike[TypeConst] {
    def children = Iterator.empty
    final val construct = (x: Iterator[Datatype]) => this
  }

  case class Record(name: Name, fields: Many[Field]) extends VariantCase with DatatypeLike[Record] {
    def children = fields.view.map(_.get).iterator
    final val construct = (xs: Iterator[Datatype]) => Record(
      name,
      fields.zip(xs.toSeq) map { case (Field(name, _), data) => Field(name, data) }
    )

    def hasInjectedTuple: Boolean = injectedTuple.nonEmpty

    def injectedTuple: Option[Record] = fields match {
      case Seq(Field(_, tuple @ Record(tupleName, tupleFields)))
          if isTuplePath(tupleName, tupleFields.length)=>
        Some(tuple)

      case _ =>
        None
    }
  }

  case class Variant(name: Name, cases: Many[VariantCase]) extends VariantCase with DatatypeLike[Variant] {
    def children = cases.iterator
    final val construct = (xs: Iterator[Datatype]) => Variant(name, xs.toSeq.asInstanceOf[Many[VariantCase]])
  }

  case class FixedPoint(name: Name, body: Datatype) extends Datatype with DatatypeLike[FixedPoint] {
    def patternFunctor: DataConstructor = DataConstructor(appendF(name), Many(Param covariant name), body)
    def replaceBody(body: Datatype): FixedPoint = copy(body = body)
    def unroll: Datatype = body subst (name, this)

    def children = Iterator(body)
    final val construct = (xs: Iterator[Datatype]) => FixedPoint(name, xs.next)
  }

  def appendF(name: Name): Name = name + "F"


  // datatype representation helpers

  case class DataConstructor(name: Name, params: Many[Param], body: Datatype) {
    def arity: Int = params.size
    def injectTuples = copy(body = body.injectTuples)
  }

  case class DataFamily(name: Name, params: Many[Param], members: Many[Variant])

  case class Field(name: Name, get: Datatype) extends Nominal

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
