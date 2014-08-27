import org.scalatest._
import nominal.functors._
import nominal.lib._
import nominal.annotation.dataWithoutImplicits

import scala.language.experimental.macros

class CoersionSpec extends FlatSpec with Coersion {
  @dataWithoutImplicits trait List[A] {
    Nil
    Cons(head = A, tail = List)
  }

  type ILF[+X] = ListF[Int, X]
  type ILT = ListT[Nil, Cons[Int, List[Int]]]

  // representation of type
  def rep[T](implicit tag: reflect.runtime.universe.TypeTag[T]): String = tag.tpe.toString

  "Coersion" should "know the source and destination types" in {
    val info = collection.mutable.Map.empty[String, String]
    val x0: List[Int] = coerceContextInfo(Nil, info)
    assert(info == Map("expected" -> rep[List[Int]], "actual" -> rep[Nil.type]))

    info.clear
    val x1: Boolean = coerceContextInfo(5, info)
    assert(info == Map("expected" -> rep[Boolean], "actual" -> rep[Int]))
  }

  val nilOfInt: List[Int] = coerce(Nil)
  val consOfInt: List[Int] = coerce( Cons(5, nilOfInt) )

  it should "auto-roll at top level" in {
    assert(nilOfInt == Roll[ILF](Nil))
    assert(consOfInt == Roll[ILF](Cons(5, nilOfInt)))
  }

  it should "auto-unroll at top level" in {
    val nil: ILT = coerce(nilOfInt)
    assert(nil == Nil)

    val cons: ILT = coerce(consOfInt)
    assert(cons == Cons(5, nilOfInt))
  }

  it should "tell whether types are compatible at runtime" in pending
}
