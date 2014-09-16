import org.scalatest._
import nominal.functors._

class CaseStudiesSpec extends FlatSpec {
  "Banana" should "work" in {
    import Banana._
    assert(sum(xs1) == 10)

    val xs2: List[Int] = coerce { Cons(4, Cons(3, Cons(2, Cons(1, Nil)))) }
    assert(downFrom(4) == xs2)

    val factorials: List[Int] = coerce {
      Cons(1, Cons(2, Cons(6, Cons(24, Nil))))
    }

    assert(xs1.map(hyloFactorial)  == factorials)
    assert(xs1.map(paraFactorial)  == factorials)
    assert(xs1.map(paraFactorial0) == factorials)
  }

  "Scrap-your-boilerplate" should "work" in {
    import Scrap._
    val paradise: Company = coerce {
      C(
        Cons(D("Research", E(P("Ralf",   "Amsterdam"), S(8800)),
          Cons(PU(E(P("Joost",  "Amsterdam"), S(1100))),
            Cons(PU(E(P("Marlow", "Cambridge"), S(2200))), Nil))),
          Cons(D("Strategy", E(P("Blair",  "London"),    S(110000)), Nil),
            Nil)))
    }

    assert(increase(10, genCom) == paradise)
    assert(increase2(10, genCom) == paradise)

    assert(deptNames(genCom) == List("Research", "Strategy"))
    assert(deptNames2(genCom) == deptNames(genCom))

    assert(deptNames(overmanaged) == List("management", "mid-level management", "junior management"))
    assert(deptNames2(overmanaged) == deptNames(overmanaged))

    assert(deptNames(flatten(genCom)) == List("Research", "Strategy"))
    assert(deptNames(flatten2(genCom)) == deptNames(flatten(genCom)))

    assert(deptNames(flatten(overmanaged)) == List("management"))
    assert(deptNames(flatten2(overmanaged)) == deptNames(flatten(overmanaged)))
  }

  "Compos-pattern" should "work" in {
    import Compos._
    assert(rename(fst) == (coerce { EAbs("_x", EAbs("_y", EVar("_x"))) }: Term))
    assert(rename(fst) == rename2(fst))

    assert(fresh(fst) == (coerce { EAbs("_0", EAbs("_1", EVar("_0"))) }: Term))
    assert(fresh(fst) == fresh2(fst))

    assert(renameExp(plusExp) == (coerce {
      Block(Cons(
        Assign("_x", Add("_y", "_z")), Cons(
          Return("_x"), Nil)))
    }: Exp))

    assert(renameExp(plusExp) == renameExp2(plusExp))

    assert(vars(plusExp) == Set("x", "y", "z"))
    assert(vars(renameExp(plusExp)) == Set("_x", "_y", "_z"))
    assert(vars(renameExp2(plusExp)) == Set("_x", "_y", "_z"))
  }
}
