import org.scalatest._
import nominal.functors._

class SynonymGeneratorSpec extends FlatSpec {
  import nominal.lib._

  "SynonymGenerator" should "generate a synonym for flat datatypes" in {
    @data def Person = PersonT {
      Boss
      Manager(dept = Int)
      Employee(name = String, dept = Int)
    }

    val boss     : Person = Boss
    val manager  : Person = Manager(51)
    val employee : Person = Employee("Julia O'Brien", 1984)
  }

  it should "generate synonyms for recursive datatypes" in {
    @data def IntList = Fix(intList => IntListT {
      Nil
      Cons(head = Int, tail = intList)
    })

    val nil: IntList = Roll[IntListF](Nil)
    def cons(x: Int, xs: IntList): IntList = Roll[IntListF](Cons(x, xs))

    val xs: IntList = cons(1, cons(2, cons(3, cons(4, nil))))
    info(s"xs = $xs")
  }

  it should "generate synonyms for generic recursive datatypes" in {
    @data def GList[A] = Fix(gList => GListT {
      Nil
      Cons(head = A, tail = gList)
    })

    object InnerModuleForTechnicalReasons {
      private[this] type GF[+A] = {
        // covariance in inner type is possible because the synonym GF is local to this file
        // technical detail: only private[this] works. private[SynonymSpec] does not work.
        // this is the technical reason to have InnerModuleForTechnicalReasons.
        type λ[+R] = GListF[A, R]
      }

      def nil[A]: GList[A] = Roll[GF[A]#λ](Nil)
      def cons[A](x: A, xs: GList[A]): GList[A] = Roll[GF[A]#λ](Cons(x, xs))
    }
    import InnerModuleForTechnicalReasons._

    val xs: GList[Int] = cons(1, cons(2, cons(3, cons(4, nil))))
    info(s"xs = $xs")
  }

  it should "generate nested synonyms" in {
    @data def Nat = NatT {
      def Even = EvenT { Zero ; ESuc(pred = Odd) }
      def Odd  = OSuc(pred = Fix(even => EvenT { Zero ; ESuc(pred = OSuc(pred = even)) }))
    }

    // test that the constructors are properly tagged `Record` or `Variant`
    import nominal.lib.Fix.{Record, Variant}
    implicitly[EvenT[Any, Any] <:< Variant]
    implicitly[ESuc[Any] <:< Record]
    implicitly[OSuc[Any] <:< Record]

    // test that synonyms `Odd`, `Even` and `Natz are generated correctly
    type MuEven = Fix[({ type λ[+even] = EvenT[Zero, ESuc[OSuc[even]]] })#λ]
    implicitly[Odd =:= OSuc[MuEven]]
    implicitly[Even =:= EvenT[Zero, ESuc[Odd]]]
    implicitly[Nat =:= NatT[Even, Odd]]
  }
}
