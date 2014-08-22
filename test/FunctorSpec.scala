import org.scalatest._
import nominal.compiler._
import nominal.lib._
import nominal.functors._

// ISSUE: universe.Type.dealias does not work in class scope
// should post StackOverflow question.

class FunctorSpec extends FlatSpec {
  @datatype trait List[+A] {
    Nil
    Cons(head = A, tail = List)
  }

  def nil[A]: List[A] = Roll[({ type λ[+L] = ListF[A, L] })#λ](Nil)
  def cons[A](head: A, tail: List[A]): List[A] = Roll[({ type λ[+L] = ListF[A, L] })#λ](Cons(head, tail))
  object List {
    def apply[T](elems: T*): List[T] =
      if (elems.isEmpty)
        nil
      else
        cons(elems.head, apply(elems.tail: _*))
  }

  // this should be generated
  implicit class ListIsFoldable[A](xs: List[A]) extends Foldable[({ type λ[+L] = ListF[A, L] })#λ](xs)(listF)


  // Does not work yet. Type of block expr is Unit, not Traversable.Endofunctor[List].
  // val list: Traversable.Endofunctor[List] = { @functor val _ = A => List[A] }

  val list = {
    @functor val list = A => List[A]
    list
  }

  def listF[A] = {
    @functor val listF = L => ListF[A, L]
    listF
  }

  def length[A](xs: List[A]): Int = xs.fold[Int] {
    case Nil => 0
    case Cons(_, n) => n + 1
  }

  val x14: List[Int] = List(1, 2, 3, 4)

  "@functor annotation" should "generate functor instances" in {
    val x25 = list(x14) map (_ + 1)
    assert(x25 == List(2, 3, 4, 5))
  }

  it should "handle override positions" in {
    @functor val list = C => List { Cons(C, List) }
    val x25 = list(x14) map (_ + 1)
    assert(x25 == List(2, 3, 4, 5))
  }

  it should "handle flattened recursive positions" in {
    @functor val tailF = L => List { Cons(Int, L) }
    val tailLength = tailF(tailF(x14.unroll).map(length)).reduce(0, _ + _)
    assert(tailLength == 3)
  }

  it should "handle summand positions" in {
    @functor val consF = C => List { Cons = C } // problem: not flattened if variant is overwritten
    assert(consF(x14.unroll).map(c => c.copy(tail = length(c.tail))) == Cons(1, 3))
  }
}
