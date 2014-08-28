import org.scalatest._
import language.higherKinds
import nominal.compiler._
import nominal.lib._
import DatatypeRepresentation._

import nominal.annotation.datatype

class UniverseConstructionSpec extends FlatSpec with Coercion {
  import UniverseConstruction.Tests._

  @datatype trait List[+A] { Nil ; Cons(A, tail = List) }

  "UniverseConstruction" should "be able to interpret list of integers" in {
    @interpretIntList trait IntList {
      FixedPoint(DataConstructor(Many("L"),
        Variant("ListT", Many(
          Record("Nil", Many.empty),
          Record("Cons", Many(
            Field("head", Scala("Int")),
            Field("tail", Hole("L"))))))))
    }

    val xs: IntList = coerce(Cons(1, Cons(2, Cons(3, Cons(4, Nil)))))

    info(s"xs = $xs")
  }

  it should "interpret generic lists" in {
    def mkMy[A] = new {
      @interpretGenList trait GenList {
        FixedPoint(DataConstructor(Many("L"),
          Variant("ListT", Many(
            Record("Nil", Many.empty),
            Record("Cons", Many(
              Field("head", Scala("A")), // should be bound by my[A]
              Field("tail", Hole("L"))))))))
      }

      type List = GenList
    }

    val my = mkMy[Int]

    val xs: my.List = coerce(Cons(1, Cons(2, Cons(3, Cons(4, Nil)))))

    info(s"xs = $xs")
  }

  @datatype trait Maybe[+A] {
    Nothin_
    Just(get = A)
  }

  @datatype trait Trio[+A, +B, +C] { MkTrio(A, B, C) }

  "UniverseConstruction" should "reify nonrecursive datatypes" in {
    @rep val maybeA = rep [Maybe[A]] (Set("A"))
    @functor val maybeF = A => Maybe { Just(A) }
    assert(maybeA ==
      Variant(TypeVar(this.getClass.getName + ".this.MaybeT"), Many(
        Record("Nothin_", Many.empty),
        Record("Just", Many(
          Field("get", TypeVar("A")))))))
    assert(maybeF.body == maybeA)
  }

  it should "reify naked record" in {
    // remark: naked records cannot be parsed,
    // because a record with no field is just an identifier &
    // indistinguishable from a type variable
    @rep val justA = rep [Just[A]] (Set("A"))
    assert(justA ==
      Record("Just", Many(
        Field("get", TypeVar("A")))))
  }

  it should "take type parameters into consideration" in {
    @rep val maybe2 = rep [Maybe[Maybe[A]]] (Set("A"))
    @functor val maybe2F   = A => Maybe { Just(Maybe { Just(A) }) }
    @functor val maybe2Fv1 = A => Maybe[Maybe[A]] { Nothin_ }
    assert(maybe2 ==
      Variant(TypeVar(this.getClass.getName + ".this.MaybeT"), Many(
        Record("Nothin_", Many.empty),
        Record("Just", Many(
          Field("get",
            Variant(TypeVar(this.getClass.getName + ".this.MaybeT"), Many(
              Record("Nothin_", Many.empty),
              Record("Just", Many(
                Field("get", TypeVar("A"))))))))))))
    assert(maybe2F  .body == maybe2)
    assert(maybe2Fv1.body == maybe2)
  }

  it should "reify nonrecursive datatypes with multiple type parameters" in {
    @functor val trioFv1 = A => Trio { MkTrio(A, A, A) }
    @functor val trioFv2 = A => Trio[A, A, A]
    assert(trioFv1 ==
      DataConstructor(
        Many(Param covariant "A"),
        Variant(TypeVar(this.getClass.getName + ".this.TrioT"), Many(
          Record("MkTrio", Many(
            Field("_1", TypeVar("A")),
            Field("_2", TypeVar("A")),
            Field("_3", TypeVar("A"))))))))
    assert(trioFv1 == trioFv2)
  }

  /** @return
    *   "" if `arg` does not match DataConstructor(..., FixedPoint(...))
    *   name of the fixed point if it does
    */
  def getFixedPointName(arg: DataConstructor): String = arg match {
    case DataConstructor(_, FixedPoint(name, _)) =>
      name

    case _ =>
      ""
  }

  it should "reify recursive datatypes" in {
    @functor val list = A => List[A]
    val listName = getFixedPointName(list)
    assert(list ==
      DataConstructor(
        Many(Param covariant "A"),
        FixedPoint(listName,
          Variant(TypeVar(this.getClass.getName + ".this.ListT"), Many(
            Record("Nil", Many.empty),
            Record("Cons", Many(
              Field("_1", TypeVar("A")),
              Field("tail", TypeVar(listName)))))))))
  }

  it should "permit deleting recursive positions" in {
    // delete recursive position
    @functor val intF = L => List { Cons(Int, L) }
    assert(intF ==
      DataConstructor(
        Many(Param covariant "L"),
        Variant(TypeVar(this.getClass.getName + ".this.ListT"), Many(
          Record("Nil", Many.empty),
          Record("Cons", Many(
            Field("_1", TypeVar("Int")),
            Field("tail", TypeVar("L"))))))))
  }

  // reassigning recursive positions is useful in e. g.
  //
  //   @functor val list = List { Cons(C, List) }
  //
  it should "permit reassigning recursive positions" in {
    @functor val tree = Ignored => List { Cons(_1 = List) }
    val treeName = getFixedPointName(tree)
    assert(tree ==
      DataConstructor(
        Many(Param covariant "Ignored"),
        FixedPoint(treeName,
          Variant(TypeVar(this.getClass.getName + ".this.ListT"), Many(
            Record("Nil", Many.empty),
            Record("Cons", Many(
              Field("_1", TypeVar(treeName)),
              Field("tail", TypeVar(treeName)))))))))
  }

  ignore should "permit introducing recursive positions" in {
    // not sure if this will be useful
    @functor val nat = X => Maybe { Just(Maybe) }

    info(" got: " + nat.toString)
    fail("expect: DataConstructor(..., Fix(...))")
  }


  it should "reify datatypes with parameters as variant cases" in {
    @functor val noth = N => Maybe { Nothin_ = N }
    assert(noth ==
      DataConstructor(
        Many(Param covariant "N"),
        Variant(TypeVar(this.getClass.getName + ".this.MaybeT"), Many(
          RecordAssignment(Record("Nothin_" , Many.empty), TypeVar("N")),
          Record("Just", Many(Field("get", TypeVar("Nothing"))))))))

    @functor val mayhap = N => Maybe { Just(Nothing) ; Nothin_ = N }
    assert(mayhap == noth)
  }

}
