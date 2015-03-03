import org.scalatest._
import creg.compiler._
import creg.lib._
import creg.functors._

class FunctorSpec extends FlatSpec {
  @data def List[A] = Fix(list => ListT { Nil ; Cons(head = A, tail = list) })

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

  @functor implicit def List[A] = Fix(list => ListT { Nil ; Cons(head = A, tail = list) })

  def length[A](xs: List[A]): Int = xs.fold[Int] {
    case Nil => 0
    case Cons(_, n) => n + 1
  }

  val x14: List[Int] = list(1, 2, 3, 4)

  "@functor annotation" should "generate functor instances" in {
    val x25 = List(x14) map (_ + 1)
    assert(x25 == list(2, 3, 4, 5))
  }

  it should "handle nonrecursive positions" in {
    val tailF = listF[Int]
    val tailLength = tailF(tailF(x14.unroll).map(length)).reduce(0, _ + _)
    assert(tailLength == 3)
  }

  it should "permit interspersing with built-in functors" in {
    import BuiltInFunctors.seqF

    @functor def elemSeqF[x] = List apply (seqF apply x)

    val xs: List[Seq[Int]] = coerce {
      Cons(Seq(1), Cons(Seq(1, 2), Cons(Seq(1, 2, 3), Cons(Seq(1, 2, 3, 4), Nil))))
    }

    assert(elemSeqF(xs).reduce(0, _ + _) == 20)
  }
}
