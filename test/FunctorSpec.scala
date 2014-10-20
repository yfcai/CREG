import org.scalatest._
import nominal.compiler._
import nominal.lib._
import nominal.functors._

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

  it should "handle summand positions" in {
    @functor def consF[C] = ListT { Nil ; Cons(head, tail) = C }
    assert(consF(x14.unroll).map(c => c.copy(tail = length(c.tail))) == Cons(1, 3))
  }

  implicit object SeqIsTraversable extends Traversable.EndofunctorTrait {
    type Map[+X] = Seq[X]
    def traverse[A, B](G: Applicative)(f: A => G.Map[B]): Map[A] => G.Map[Map[B]] = xs => {
      val mbs: Seq[G.Map[B]] = xs map f
      val nil: G.Map[Map[B]] = G pure Seq.empty
      val prepend: G.Map[B => Map[B] => Map[B]] = G pure (x => xs => x +: xs)
      mbs.foldRight(nil) { case (mb, acc) => G.call(G.call(prepend, mb), acc) }
    }
  }

  it should "permit interspersing with built-in functors" in {
    @functor def elemSeqF[x] = List apply (Seq apply x)

    val xs: List[Seq[Int]] = coerce {
      Cons(Seq(1), Cons(Seq(1, 2), Cons(Seq(1, 2, 3), Cons(Seq(1, 2, 3, 4), Nil))))
    }

    assert(elemSeqF(xs).reduce(0, _ + _) == 20)
  }
}
