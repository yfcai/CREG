import org.scalatest._

class SynonymGeneratorSpec extends FlatSpec {
  import SynonymGenerator.Tests._
  import fixedpoint._

  "SynonymGenerator" should "generate a synonym for flat datatypes" in {
    @flat trait Person {
      Boss
      Manager(dept: Int)
      Employee(name: String, dept: Int)
    }

    val boss     : Person = Boss
    val manager  : Person = Manager(51)
    val employee : Person = Employee("Julia O'Brien", 1984)
  }

  it should "generate synonyms for recursive datatypes" in {
    @recursive trait IntList {
      Nil
      Cons(Int, IntList)
    }

    val xs: IntList = Roll[({ type λ[+T] = IntListT[Nil, Cons[Int, T]] })#λ](Nil)
    //val xs: IntList = Roll[IntListF](Nil) // to generate: the synonym IntListF
  }

  it should "generate synonyms for generic recursive datatypes" in {
    @generic trait GList[A] {
      Nil
      Cons(A, GList[A])
    }
  }
}
