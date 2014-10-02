import org.scalatest._
import nominal.functors._
import nominal.compiler.KIRV._
import nominal.lib.Applicative._

class KIRVSpec extends FlatSpec {

  @datatype trait List[+A] { Nil ; Cons(A, List[A]) }

  val const3 = const[Int](3)
  val nil3   = const[Nil](3)
  val cons3  = const[Cons[Int, Int]](3)
  val proj1  = proj(1, 3)
  val proj2  = proj(2, 3)

  import scala.language.existentials

  val listF2 =
    composite(List, 2)(
      const[Nil](2),
      composite(Cons, 2)(proj(1, 2), proj(0, 2))(1, 0)
    )(2, 2)

  val elemF  = fix(listF2, 1)

  val xs: List[Int] = coerce { Cons(1, Cons(2, Cons(3, Cons(4, Nil)))) }

  "KIRV" should "generate constant functors" in {
    assert(const3(9).traverse(Const[Int](5,
      (_, _) => fail))(
      _ => fail,
        _ => fail,
        _ => fail) == 5)
  }

  it should "generate projection functors" in {
    assert(proj2[String, String, Int](5).map(
      _ => fail,
      _ => fail,
      identity) == 5)
  }

  it should "generate record functors" in {
    val cons = composite(Cons, 3)(const3, const3)(3, 3)
    assert(cons[String, String, String](Cons(1, 2)).map(_ => fail, _ => fail, _ => fail) == Cons(1, 2))

    val fst = composite(Cons, 3)(proj2, const3)(2, 3)
    assert(fst[String, String, Int](Cons(1, 2)).map(_ => fail, _ => fail, _ + 1) == Cons(2, 2))
  }

  it should "generate variant functors" in {
    val cl = composite(List, 3)(nil3, cons3)(3, 3)
    assert(cl[String, String, String](Nil).map(_ => fail, _ => fail, _ => fail) == Nil)

    val il = composite(List, 3)(proj1, proj2)(1, 2)
    assert(il[String, Nil, Cons[Int, Int]](Nil).map(_ => fail, _ => Nil, _ => fail) == Nil)
    assert(il[String, Nil, Cons[Int, Int]](Nil).map(_ => fail, identity, _ => fail) == Nil)

    assert(il[String, Nil, Cons[Int, Int]](Cons(3, 5)).map(
      _ => fail, _ => fail, x => x.copy(x._1.toString, x._2.toString)) == Cons("3", "5"))
  }

  it should "generate fixed point of functors" in {
    val xs2: List[Int] = coerce {
      Cons(2, Cons(4, Cons(6, Cons(8, Nil))))
    }
    assert(elemF(xs).map(_ * 2) == xs2)
  }
}
