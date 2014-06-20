import org.scalatest._

class DataSpec extends FlatSpec {

  // Fixed point must be present
  import language.higherKinds
  sealed trait Fix[+F[+_]] { def unroll: F[Fix[F]] }
  case class Roll[+F[+_]](unroll: F[Fix[F]]) extends Fix[F]

  "data macro" should "do something?" in {
    @datatype trait List[A] { Nil ; Cons(A, tail: List[A]) }
  }
}
