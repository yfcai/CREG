import org.scalatest._
import nominal.functors._

class CaseStudiesSpec extends FlatSpec {
  "Banana" should "work" in pending /*{
    import Banana._
    assert(sum(xs1) == 10)
    assert(upTo(4) == xs1)

    val factorials: List[Int] = coerce {
      Cons(1, Cons(2, Cons(6, Cons(24, Nil))))
    }

    assert(xs1.map(hyloFactorial)  == factorials)
    assert(xs1.map(paraFactorial)  == factorials)
    assert(xs1.map(paraFactorial0) == factorials)
  }*/

  "Scrap-your-boilerplate" should "work" in {
    import Scrap._

    val paradise: Company = coerce {
      C(Cons(D("Research", E(P("Ralf",   "Amsterdam"), S(8800)),
          Cons(PU(E(P("Joost",  "Amsterdam"), S(1100))),
            Cons(PU(E(P("Marlow", "Cambridge"), S(2200))), Nil))),
          Cons(D("Strategy", E(P("Blair",  "London"),    S(110000)), Nil),
            Nil)))
    }

    def list[A](seq: A*): List[A] =
      seq.foldRight(coerce(Nil): List[A]) {
        case (x, xs) => coerce { Cons(x, xs) }
      }

    assert(increase(10, genCom) == paradise)
    assert(increase2(10, genCom) == paradise)

    assert(deptNames(genCom) == list("Research", "Strategy"))
    assert(deptNames2(genCom) == deptNames(genCom))

    assert(deptNames(overmanaged) == list("management", "mid-level management", "junior management"))
    assert(deptNames2(overmanaged) == deptNames(overmanaged))

    assert(deptNames(flatten(genCom)) == list("Research", "Strategy"))
    assert(deptNames(flatten2(genCom)) == deptNames(flatten(genCom)))

    assert(deptNames(flatten(overmanaged)) == list("management"))
    assert(deptNames(flatten2(overmanaged)) == deptNames(flatten(overmanaged)))
  }

  "Compos-pattern" should "work" in {
    import Compos._
    assert(prependUnderscore(fst) == (coerce { Abs("_x", Abs("_y", "_x")) }: Exp))
    assert(prependUnderscore2(fst) == prependUnderscore(fst))

    assert(fresh(fst) == (coerce { Abs("_0", Abs("_1", "_0")) }: Exp))
    //assert(fresh(fst) == fresh2(fst))

    assert(prependUnderscore(plusExp) == (coerce {
      Block(Cons(
        Assign("_x", App("_y", "_z")), Cons(
          Return("_x"), Nil)))
    }: Exp))

    assert(prependUnderscore2(plusExp) == prependUnderscore(plusExp))

    assert(vars(plusExp) == Set("x", "y", "z"))
    assert(vars(prependUnderscore(plusExp)) == Set("_x", "_y", "_z"))
    assert(vars(prependUnderscore2(plusExp)) == Set("_x", "_y", "_z"))

    // TODO: test stuff on expressions with inner blocks
  }
}
