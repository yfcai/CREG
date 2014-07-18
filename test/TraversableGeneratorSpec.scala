import org.scalatest._
import nominal.compiler._

import scala.tools.reflect.ToolBoxError

class TraversableGeneratorSpec extends FlatSpec with nominal.util.EvalScala {
  import TraversableGenerator.Tests._

  // if this compiles at all, then generated code implements Traversable interface correctly
  @c123 object Dummy

  "TraversableGenerator" should "generate subcategory bounds" in {
    implicitly[C1.Cat  =:= Any]
    implicitly[C2.Cat  =:= Int]
    implicitly[C3.Cat1 =:= Any]
    implicitly[C3.Cat2 =:= Either[Int, Boolean]]
  }

  ignore should "generate bounded mapping on objects" in {
    // expect "type arguments [Boolean] do not conform to type Map's type parameter bounds [+X <: Int]"
    // sadly, none of the following produces the expected exception:
    //
    //   evalScala(TraversableGeneratorSpec.this, "??? : TraversableGeneratorSpec.this.C2.Map[Boolean]")
    //   c2MapError // a macro doing the same thing
    //
    // bare code produces the expected error, but it disrupts test compilation & prevents the other tests from running.
    //
    //   def x = ??? : C2.Map[Boolean]
  }
}
