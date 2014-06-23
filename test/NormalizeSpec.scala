import org.scalatest._

import language.experimental.macros
import language.higherKinds

class NormalizeSpec extends FlatSpec {
  // type synonyms *must* be type members
  // they can't be local to methods
  type S[X[_, _], Y[_], Z] = X[Z, Y[Z]]
  type T = S[Map, List, String]

  "Normalizer macro" should "normalize type synonyms" in {
    @normalize type normalized = T
    val actual = normalized.toString
    val expected = "scala.collection.immutable.Map[String,List[String]]"
    assert(actual == expected)
    info(s"T = S[Map, List, String] = $actual")
  }
}
