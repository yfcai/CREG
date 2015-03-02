import language.implicitConversions
import org.scalatest._
import nominal.functors._
import nominal.lib._

import Coercion.Test._
import Applicative._

class CoercionSpec extends FlatSpec {
  @data def Fork[A, B] = ForkT {
    Leaf(i = Int)
    Branch(_1 = A, _2 = B)
  }

  type F1[+A] = Fork[A, A]
  type F2[+A] = Fork[A, Fix[F1]]
  type F3[+A] = Fork[Fork[A, A], Fork[A, A]]
  type F4[+A] = Const[F1[Fix[F1]]]#λ[A]
  type F5[+A] = Const[Fix[F1]]#λ[A]
  type F6[+A] = Fix[Const[Fork[A, A]]#λ]
/*
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
 */

  it should "typecast between types only if safe and necessary" in {
    assert(hasCast[Fix[Const[Fix[Identity]]#λ], Fix[Identity]])

    assert(hasCast[Fix[F1], Fix[F2]])
    assert(hasCast[Fix[F4], Fix[F1]])
  }

  it should "not typecast when unnecessary or unsafe" in {
    assert(! hasCast[Int, Int])
    assert(! hasCast[Fix[Identity], Fix[Identity]])
    assert(! hasCast[Fix[F1], Fix[F3]])
    assert(! hasCast[Fix[F3], Fix[F2]])
    assert(! hasCast[Fix[F1], Fix[F5]])
    assert(! hasCast[Fix[F6], Fix[F3]])
    assert(! hasCast[Fix[F5], Fix[F6]])
  }


  import Banana._

  @functor def f1[A] = ForkT {
    Leaf(i = Int)
    Branch(_1 = A, _2 = A)
  }

  val f3 = f1 compose f1

  // binary tree with a couple hundred nodes
  val tree7: Fix[F3] =
    anaWith[Int](f3)({ i =>
      if (i <= 0)
        Leaf(i)
      else
        Branch(Branch(i - 1, i - 1), Leaf(i))
    })(7)

  it should "not throw ClassCastException" in {
    val t = tree7
    coerce { t } : Fix[F1]
    coerce { t } : Fix[F2]
    coerce { t } : Fix[F3]
    coerce { t } : Fix[F4]
    coerce { t } : Fix[F5]
    coerce { t } : Fix[F6]
  }
}
