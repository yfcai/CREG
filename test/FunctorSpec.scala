import org.scalatest._
import nominal.compiler._
import nominal.lib._
import nominal.functors._

// ISSUE: universe.Type.dealias does not work in class scope
// should post StackOverflow question.

class FunctorSpec extends FlatSpec {
  @data def List[A] = Fix(list => ListT { Nil ; Cons(head = A, tail = list) })

  // TODO: DELETE THESE SCAFFOLDS
  type ListF[+A, +list] = ListT[Nil, Cons[A, list]]
  type List[+A] = Fix[({ type λ[+list] = ListF[A, list] })#λ]

  def list[T](elems: T*): List[T] =
    if (elems.isEmpty)
      coerce(Nil)
    else
      coerce(Cons(elems.head, list(elems.tail: _*)))

  def listF[A] = {
    @functor def listF[list] = ListT { Nil ; Cons(head = A, tail = list) }
    listF
  }

  // this should be generated
  implicit class ListIsFoldable[A](xs: List[A]) extends Foldable[({ type λ[+L] = ListF[A, L] })#λ](xs)(listF)

  @functor def elemF[A] = Fix(list => ListT { Nil ; Cons(head = A, tail = list) })

  def length[A](xs: List[A]): Int = xs.fold[Int] {
    case Nil => 0
    case Cons(_, n) => n + 1
  }

  val x14: List[Int] = list(1, 2, 3, 4)

  "@functor annotation" should "generate functor instances" in {
    val x25 = elemF(x14) map (_ + 1)
    assert(x25 == list(2, 3, 4, 5))
  }

  it should "handle nonrecursive positions" in {
    val tailF = listF[Int]
    val tailLength = tailF(tailF(x14.unroll).map(length)).reduce(0, _ + _)
    assert(tailLength == 3)
  }

  it should "handle summand positions" in {
    @functor def consF[C] = ListT { Nil ; C }
    assert(consF(x14.unroll).map(c => c.copy(tail = length(c.tail))) == Cons(1, 3))
  }
}
