import org.scalatest._
import language.higherKinds
import nominal.compiler._
import nominal.lib._
import DatatypeRepresentation._

class UniverseConstructionSpec extends FlatSpec {
  import UniverseConstruction.Tests._

  // sample generated datatype
  sealed trait ListT[+Nil, +Cons]
  sealed trait Nil extends ListT[Nil, Nothing]
  case object Nil extends Nil
  sealed case class Cons[+A, +L](head: A, tail: L) extends ListT[Nothing, Cons[A, L]]

  // ListF should NOT be visible to users.
  // the uncurried ListF should be visible to users.
  private[this] type ListF[+A] = { type λ[+L] = ListT[Nil, Cons[A, L]] }

  private[this] type List[+A] = Fix[ListF]

  "UniverseConstruction" should "be able to interpret list of integers" in {
    @interpretIntList trait IntList {
      FixedPoint(DataConstructor(Many("L"),
        Variant("ListT", Many(
          Record("Nil", Many.empty),
          Record("Cons", Many(
            Field("head", Scala("Int")),
            Field("tail", Hole("L"))))))))
    }

    val xs: IntList = {
      val nil: IntList = Roll[ListF[Int]#λ](Nil)
      def cons(x: Int, xs: IntList) = Roll[ListF[Int]#λ](Cons(x, xs))
      cons(1, cons(2, cons(3, cons(4, nil))))
    }

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

    val xs: my.List = {
      val nil: my.List = Roll[ListF[Int]#λ](Nil)
      def cons(x: Int, xs: my.List) = Roll[ListF[Int]#λ](Cons(x, xs))
      cons(1, cons(2, cons(3, cons(4, nil))))
    }

    info(s"xs = $xs")
  }

  "UniverseConstruction" should "be able to reify generated datatypes" in (pending) ; {
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
