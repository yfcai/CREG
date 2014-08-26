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

  // representation of type
  def rep[T](implicit tag: reflect.runtime.universe.TypeTag[T]): String = tag.tpe.toString

  "Coersion" should "know the source and destination types" in {
    val info = collection.mutable.Map.empty[String, String]
    val x0: List[Int] = coerceContextInfo(Nil, info)
    assert(info == Map("expected" -> rep[List[Int]], "actual" -> rep[Nil.type]))

    info.clear
    val x1: Boolean = coerceContextInfo(5, info)
    assert(info == Map("expected" -> rep[Boolean], "actual" -> rep[Int]))

    // testing if things compile
    val x2: List[Int] = coerce(Nil)
  }
}
