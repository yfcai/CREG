import language.implicitConversions
import org.scalatest._
import nominal.functors._
import nominal.lib._
import nominal.compiler.UniverseConstruction.Tests._
import nominal.compiler.DatatypeRepresentation._

class ReificationSpec extends FlatSpec {
  @data def List[A] = Fix(list => ListT {
    Nil
    Cons(head = A, tail = list)
  })

  "Reification" should "identify fixed points" in {
    assert(isFix[Fix[({type λ[+X] = X})#λ]] == true)
    assert(isFix[Int] == false)
    assert(isFix[Seq[Int]] == false)
  }

  it should "create representations of types" in {
    assert(reify[Int] == TypeConst("Int"))

    assert(reify[Fix[({ type λ[+A] = A })#λ]] ==
      FixedPoint("canon0", TypeVar("canon0")))

    assert(reify[Array[Int]] ==
      FunctorApplication(TypeConst("Array[Int]"), List(TypeConst("Int"))))
  }

  it should "never create types with unbound names" in {
    assert(unrollFix[Fix[({ type λ[+A] = A })#λ]] == "nominal.lib.Fix[[+A]A]")

    assert(unrollFix[Fix[({ type λ[+A] = Fix[({ type λ[+B] = A })#λ] })#λ]] ==
      "nominal.lib.Fix[[+B]nominal.lib.Fix[[+A]nominal.lib.Fix[[+B]A]]]")

    assert(unrollFix[Fix[({ type λ[+A] = Array[A] })#λ]] ==
      "Array[nominal.lib.Fix[[+A]Array[A]]]")
  }

  it should "dealias properly" in {
    assert(reify[ListF[Int, Any]] ==
      FunctorApplication(
        TypeConst(
          "ReificationSpec.this.ListT[" +
            "ReificationSpec.this.Nil,ReificationSpec.this.Cons[Int,Any]]"),
        List(
          TypeConst("ReificationSpec.this.Nil"),
          FunctorApplication(
            TypeConst("ReificationSpec.this.Cons[Int,Any]"),
            List(TypeConst("Int"), TypeConst("Any")))))
    )
  }
}
