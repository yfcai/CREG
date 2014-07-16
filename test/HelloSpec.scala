import org.scalatest._
import nominal.experiment.hello

import scala.language.experimental.macros

class HelloSpec extends FlatSpec {
  "Hello macro" should "insert method `hello`" in {
    @hello object X
    info(X.hello)
  }
}
