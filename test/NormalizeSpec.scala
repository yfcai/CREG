import org.scalatest._

import language.experimental.macros
import language.higherKinds

class NormalizeSpec extends FlatSpec {
  // type synonyms *must* be type members
  // they can't be local to methods
  type S[X[_, _], Y[_], Z] = X[Z, Y[Z]]
  type T = S[Map, List, String]

  type Trial[X] = Map[Int, X]

  "Normalizer macro" should "normalize type synonyms" in {
    @normalize type normalized = T
    val actual = normalized.toString
    val expected = "scala.collection.immutable.Map[String,List[String]]"
    assert(actual == expected)
    info(s"T = S[Map, List, String] = $actual")
  }

  it should "normalize type synonyms in the presence of abstract types" in {
    @normalize type normalized[X] = Trial[X]
    val actual = normalized.toString
    val expected = "scala.collection.immutable.Map[Int,X]"
    assert(actual == expected)
    info(actual)
  }

  /** Try to normalize types with free type variables
    *
    * Ignored because we may never encounter free type variables.
    * For generic functors, users should write e. g.
    *
    *   def listF[A] = functor { L => List[A] { Cons(A, L) } }
    *
    * where the type name A is bound in RHS.
    */
  ignore should "normalize abstract synonyms to a form usable in new definitions" in {
    @normalize type normalized[X] = Trial[X]
    // does not compile
    // val x: normalized.InnerType[String] = Map.empty[Int, String]
  }
}
