import org.scalatest._
import nominal.experiment._

import scala.language.experimental.macros

class Experiments extends FlatSpec {
  "@hello" should "insert method `hello` and extend `A with B with C`" in {
    @hello object X
    implicitly[X.type <:< (A with B with C)]
    info(X.hello)
  }

  "@defData" should "consume definitions that are ill-typed in Scala" in {
    @defData def IntList =
      Fix(intList =>
        ListT {
          Nil
          Cons(head = Int, tail = intList)
        })

    assert(IntList ==
      """|
         |def IntList = Fix(((intList) => ListT({
         |  Nil;
         |  Cons(head = Int, tail = intList)
         |})))""".stripMargin)

    @defData def List[A] =
      Fix(list =>
        ListT {
          Nil
          Cons(head = A, tail = list)
        })

    assert(List ==
      """|
         |def List[A] = Fix(((list) => ListT({
         |  Nil;
         |  Cons(head = A, tail = list)
         |})))""".stripMargin)
  }
}
