import org.scalatest._
import language.higherKinds

class UniverseConstructionSpec extends FlatSpec {
  import UniverseConstruction._

  // sample generated datatype
  sealed trait ListT[+Nil, +Cons]
  sealed trait Nil extends ListT[Nil, Nothing]
  case object Nil extends Nil
  sealed case class Cons[+A, +L](head: A, tail: L) extends ListT[Nothing, Cons[A, L]]

  sealed trait Fix[+F[+_]] { def unroll: F[Fix[F]] }
  sealed case class Roll[+F[+_]](unroll: F[Fix[F]]) extends Fix[F]

  // variance of inner type λ is a menance.
  private[this] type ListF[+A] = { type λ[+L] = ListT[Nil, Cons[A, L]] }

  private[this] type List[+A] = Fix[ListF]

  "UniverseConstruction" should "be able to reify generated datatypes" in {
    // reify[List[Int]]
    //       ==
    // Fix(DataConstructor(Many("L"),
    //   Variant("ListT", Many(
    //     Record("Nil", Many.empty),
    //     Record("Cons", Many(
    //       Field("head", Scala("Int")),
    //       Field("tail", Hole("L"))))))))

    // stub
  }
}
