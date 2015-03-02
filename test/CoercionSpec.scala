import language.implicitConversions
import org.scalatest._
import nominal.functors._
import nominal.lib._

import Coercion.Test._
import Applicative._

class CoercionSpec extends FlatSpec {
  @data def IntFork = Fork(_1 = Int, _2 = Int)

  type F1[+A] = Fork[A, A]
  type F2[+A] = Fork[A, Fix[F1]]
  type F3[+A] = Fork[Fork[A, A], Fork[A, A]]
  type F4[+A] = Const[F1[A]]#λ[A]
  type F5[+A] = Const[Fix[F1]]#λ[A]
  type F6[+A] = Fix[Const[Fork[A, A]]#λ]

  "Coercion" should "detect when two types have same representation" in {
    assert(sameRep[Int, Int])
    assert(sameRep[Fix[Identity], Fix[Identity]])

    assert(sameRep[Fix[F1], Fix[F2]])
    assert(sameRep[Fix[F4], Fix[F1]])
  }

  it should "detect when two types have different representations" in {
    assert(! sameRep[Int, Float])
    assert(! sameRep[Fix[Identity], Fix[Const[Int]#λ]])
    assert(! sameRep[Fix[Const[Int]#λ], Fix[Identity]])

    assert(! sameRep[Fix[F1], Fix[F3]])
    assert(! sameRep[Fix[F3], Fix[F2]])
    assert(! sameRep[Fix[F1], Fix[F5]])
    assert(! sameRep[Fix[F6], Fix[F3]])
    assert(! sameRep[Fix[F5], Fix[F6]])
  }

  it should "never throw ClassCastException" in {
    pending
  }
}
