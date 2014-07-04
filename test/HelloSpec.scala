import org.scalatest._
import nominal._

import scala.language.experimental.macros

class HelloSpec extends FlatSpec {
  "Hello macro" should "insert method `hello`" in {
    @hello object X
    info(X.hello)
  }
}
