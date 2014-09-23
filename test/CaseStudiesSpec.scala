import org.scalatest._
import nominal.functors._

class CaseStudiesSpec extends FlatSpec {
  "Main case study" should "work" in {
    object main extends MainTrait
    import main._

    // freevars vs. freevars1 vs. freevars2

    def fvtest(t: Term, fv: Set[String]) {
      assert(freevars(t) == fv)
      assert(freevars1(t) == fv)
      assert(freevars2(t) == fv)
    }

    fvtest(id  , Set())
    fvtest(idy , Set("y"))
    fvtest(f_xy, Set("f", "y"))
    fvtest(fx_y, Set("f", "x"))
    fvtest(fzv , Set())

    // capture-avoidance

    val y0: Term = coerce { Abs("y", App("y0", "x")) }
    val y1: Term = coerce { Abs("y1", App("y0", App("y", "y"))) }
    val y2: Term = coerce { Abs("_0", App("y0", App("y", "y"))) }
    resetFreshNames()
    assert(subst1("x", coerce { App("y", "y") }, y0) == y1)
    assert(subst2("x", coerce { App("y", "y") }, y0) == y2)

    val id1: Term = coerce { Abs("x1", "x1") }
    val id2: Term = coerce { Abs("_0", "_0") }
    resetFreshNames()
    assert(subst1("x0", "x", id) == id1)
    assert(subst2("x0", "x", id) == id2)

    // counting variable occurrences

    def vars(t: Term, n: Int) {
      assert(variables(t) == n)
    }

    vars(id  , 1)
    vars(idy , 2)
    vars(f_xy, 3)
    vars(fx_y, 3)
    vars(fzv , 1)

    // flattening top-level applications

    val x1: Term = coerce { Abs("x", App(App("x", "y"), "z")) }
    val x2: Term = coerce { "y" }
    val x3: Term = coerce { App("y", "z") }
    val xx: Term = coerce { App(App(x1, x2), x3) }

    assert(flatten(xx) == Seq(x1, x2, x3))
  }

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
    assert(xs1.map(cakeFactorial)  == factorials)

    // tails

    val factails: List[Int] = coerce {
      Cons(2, Cons(6, Cons(24, Nil)))
    }

    assert(tail0(factorials) == factails)
    assert(tail (factorials) == factails)

    // suffixes

    val facsufs: List[List[Int]] = coerce {
      Cons(
        Cons(1, Cons(2, Cons(6, Cons(24, Nil)))), Cons(
          Cons(2, Cons(6, Cons(24, Nil))), Cons(
            Cons(6, Cons(24, Nil)), Cons(
              Cons(24, Nil), Cons(
                Nil, Nil)))))
    }

    assert(suffixes0(factorials) == facsufs)
    assert(suffixes (factorials) == facsufs)
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

  "Everything" should "work" in {
    import Everything._
    assert(elemF(xs).map(_ + 1) == xsPlus1)
  }
}
