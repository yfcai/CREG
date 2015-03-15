package creg.example

import org.scalatest._
import creg.functors._

class CaseStudiesSpec extends FlatSpec {
  "Banana" should "work" in {
    import Banana._
    assert(sum(xs1) == 10)
    assert(upTo(4) == xs1)

    val factorials: List[Int] = coerce {
      Cons(1, Cons(2, Cons(6, Cons(24, Nil))))
    }

    assert(xs1.map(hyloFactorial)           == factorials)
    assert(xs1.map(paraFactorial)           == factorials)
    assert(xs1.map(paraFactorial0)          == factorials)
    assert(xs1.map(cakeWithCoerceFactorial) == factorials)
  }

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
    import Banana.{List, ListT, Nil, Cons}
    import Compos._

    assert(prependUnderscore(fst) == (coerce { Abs("_x", Abs("_y", "_x")) }: Exp))
    assert(prependUnderscore2(fst) == prependUnderscore(fst))

    assert(fresh(fst) == (coerce { Abs("_0", Abs("_1", "_0")) }: Exp))

    assert(prependUnderscore(assignExp) == (coerce {
      Abs("_x", Abs("_y", Abs("_z",
        Block(Cons(
          Assign("_x", App("_y", "_z")), Cons(
            Return("_x"), Nil))))))
    }: Exp))

    assert(prependUnderscore2(assignExp) == prependUnderscore(assignExp))

    assert(vars(assignExp) == Set("x", "y", "z"))

    assert(vars(prependUnderscore(assignExp)) == Set("_x", "_y", "_z"))
    assert(prependUnderscore2(assignExp) == prependUnderscore(assignExp))

    assert(vars(fresh(assignExp)) == Set("_0", "_1", "_2"))
  }

  "De-Bruijn indices" should "work" in {
    // manual syntax tree construction
    import DeBruijn._
    import creg.lib._
    val roll = Roll[TermF] _
    val _abs = (x: String, body: Term) => roll(Abs(x, body))
    val _app = (op: Term, arg: Term) => roll(App(op, arg))
    val _atm = (x: String) => roll(Var(Free(x)))
    val _bdd = (idx: Int) => roll(Var(Bound(idx)))

    // test smart constructors _var, abs, app
    assert(id == _abs("x", _bdd(0)))
    assert(fst == _abs("x", _abs("y", _bdd(1))))
    assert(ap == _abs("f", _abs("x", _app(_bdd(1), _bdd(0)))))
  }

  "Fresh" should "work" in {
    import Fresh._
    assert(omg == (coerce {
      App(
        Abs("_0", App(Var("_0"), Var("_0"))),
        Abs("_1", App(Var("_1"), Var("_1"))))
    }: Term))
  }
}
