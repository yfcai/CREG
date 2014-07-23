import org.scalatest._
import language.higherKinds
import nominal.compiler._
import nominal.lib._
import DatatypeRepresentation._

import nominal.datatype

class UniverseConstructionSpec extends FlatSpec {
  import UniverseConstruction.Tests._

  @datatype trait List[+A] { Nil ; Cons(A, tail = List) }

  def nil[A]: List[A] = Roll[({ type λ[+L] = ListF[A, L] })#λ](Nil)
  def cons[A](head: A, tail: List[A]): List[A] = Roll[({ type λ[+L] = ListF[A, L] })#λ](Cons(head, tail))

  "UniverseConstruction" should "be able to interpret list of integers" in {
    @interpretIntList trait IntList {
      FixedPoint(DataConstructor(Many("L"),
        Variant("ListT", Many(
          Record("Nil", Many.empty),
          Record("Cons", Many(
            Field("head", Scala("Int")),
            Field("tail", Hole("L"))))))))
    }

    val xs: IntList = cons(1, cons(2, cons(3, cons(4, nil))))

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

    val xs: my.List = cons(1, cons(2, cons(3, cons(4, nil))))

    info(s"xs = $xs")
  }

  @datatype trait Maybe[+A] {
    Nothin_
    Just(get = A)
  }

  "UniverseConstruction" should "reify nonrecursive datatypes" in {
    @rep val maybeA = rep [Maybe[A]] (Set("A"))
    assert(maybeA ==
      Variant(TypeVar(this.getClass.getName + ".MaybeT"), Many(
        Record("Nothin_", Many.empty),
        Record("Just", Many(
          Field("get", TypeVar("A")))))))

    @rep val justA = rep [Just[A]] (Set("A"))
    assert(justA ==
      Record("Just", Many(
        Field("get", TypeVar("A")))))

    @rep val maybe2 = rep [Maybe[Maybe[A]]] (Set("A"))
    assert(maybe2 ==
      Variant(TypeVar(this.getClass.getName + ".MaybeT"), Many(
        Record("Nothin_", Many.empty),
        Record("Just", Many(
          Field("get",
            Variant(TypeVar(this.getClass.getName + ".MaybeT"), Many(
              Record("Nothin_", Many.empty),
              Record("Just", Many(
                Field("get", TypeVar("A"))))))))))))
  }

  it should "reify recursive datatypes" in pending ; {
    // reify[List[Int]]
    //       ==
    // FixedPoint(DataConstructor(Many("L"),
    //   Variant("ListT", Many(
    //     Record("Nil", Many.empty),
    //     Record("Cons", Many(
    //       Field("head", Scala("Int")),
    //       Field("tail", Hole("L"))))))))

    // stub
  }
}
