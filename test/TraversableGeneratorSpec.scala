import org.scalatest._
import nominal.compiler._
import nominal.lib._
import nominal.annotation.datatype

import scala.tools.reflect.ToolBoxError

class TraversableGeneratorSpec extends FlatSpec with Coercion with nominal.util.EvalScala {
  import TraversableGenerator.Tests._

  @datatype trait List[+A] {
    Nil
    Cons(head = A, tail = List[A])
  }

  @datatype trait Plus[+A, +B] {
    LHS(get = A)
    RHS(get = B)
  }

  // if this compiles at all, then generated code implements Traversable interface correctly
  @c123 object Dummy

  val x12: List[Int] =
    coerce(Cons(1, Cons(2, Nil)))

  val x14: List2.Map[Int] = coerce(
    Cons(
      Nil, Cons(
        Cons(1, Nil), Cons(
          Cons(1, Cons(2, Nil)), Cons(
            Cons(1, Cons(2, Cons(3, Nil))), Cons(
              Cons(1, Cons(2, Cons(3, Cons(4, Nil)))), Nil)))))
  )

  type TC3 = C3.Map[String, Either[Int, Boolean]]

  "TraversableGenerator" should "generate subcategory bounds" in {
    implicitly[   C1.Cat  =:= Any                 ]
    implicitly[   C2.Cat  =:= Int                 ]
    implicitly[   C3.Cat1 =:= Any                 ]
    implicitly[   C3.Cat2 =:= Either[Int, Boolean]]
    implicitly[List2.Cat  =:= Any                 ]
    implicitly[   LF.Cat  =:= LHS[Any]            ]
    implicitly[ NilT.Cat  =:= Nil                 ]
    implicitly[ NilF.Cat  =:= Nil                 ]
    implicitly[ConsF.Cat  =:= Cons[Any, Any]      ]
  }

  ignore should "generate bounded mapping on objects" in {
    // expect "type arguments [Boolean] do not conform to type Map's type parameter bounds [+X <: Int]"
    // sadly, none of the following produces the expected exception:
    //
    //   evalScala(TraversableGeneratorSpec.this, "??? : TraversableGeneratorSpec.this.C2.Map[Boolean]")
    //   c2MapError // a macro doing the same thing
    //
    // bare code produces the expected error, but it disrupts test compilation & prevents the other tests from running.
    //
    //   def x = ??? : C2.Map[Boolean]
  }

  it should "generate traversals for tuples" in {
    val x: TC3 = ("hello", Left(5))
    val y: TC3 = C3(x).map(_ + " world!", _.left.map(_ + 1))
    assert(y == ("hello world!", Left(6)))
  }

  it should "generate traversals for lists of lists" in {
    val x14_sum = List2(x14) reduce (0, _ + _)
    assert(x14_sum == 1 + (1 + 2) + (1 + 2 + 3) + (1 + 2 + 3 + 4))

    val x25 = List2(x14) map (_ + 1)
    val x25_expected: List[List[Int]] = coerce(
      Cons(
        Nil, Cons(
          Cons(2, Nil), Cons(
            Cons(2, Cons(3, Nil)), Cons(
              Cons(2, Cons(3, Cons(4, Nil))), Cons(
                Cons(2, Cons(3, Cons(4, Cons(5, Nil)))), Nil)))))
    )
    assert(x25 == x25_expected)
  }

  it should "generate traversals for recursion at variant case position" in {
    val hello: Plus[String, Int] = LHS("hello")
    val helloWorld = LF(hello) map (lhs => lhs copy lhs.get + " world")
    assert(helloWorld == LHS("hello world"))

    // count how many times the higher order arg is called during the functors' fmaps
    var (iT0, iT1, iF) = (0, 0, 0)
    val nilT0 = NilT(x12.unroll) map (nil => { iT0 += 1 ; nil })
    val nilT1 = NilT(Nil) map (nil => { iT1 += 1 ; nil })
    val nilF = NilF(x12) map (nil => { iF += 1 ; nil })
    assert(nilT0 == x12.unroll)
    assert(nilT1 == Nil)
    assert(nilF == x12)
    assert(iT0 == 0, ": nilT0")
    assert(iT1 == 1, ": nilT1")
    assert(iF == 1, ": nilF")
  }
}
