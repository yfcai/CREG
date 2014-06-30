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

  it should "normalize abstract synonyms to a form usable in new definitions" is (pending) /* {
    @normalize type normalized[X] = Trial[X]
    // does not compile yet...
    val x: normalized.InnerType[String] = Map.empty[Int, String]
  } */
}
