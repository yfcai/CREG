import org.scalatest._
import nominal._

class DeclarationGeneratorSpec extends FlatSpec {
  import compiler.DeclarationGenerator.Tests._

  "DeclarationGenerator" should "generate an empty sealed trait for 0 variants" in {
    @empty trait Empty1T
    @empty trait Empty2T
    val x: Empty1T = null
    val y: Empty2T = null
  }

  it should "generate case object for variant without arguments" in {
    @caseObject trait VariantT { Singleton }
    val singleton: VariantT[Singleton] = Singleton
    singleton match {
      case Singleton => info("success")
    }
  }

  it should "generate multiple variants without arguments" in {
    @fourCaseObjects trait HorsemanT { Conquest ; War ; Famine ; Death }
    val war: HorsemanT[Conquest, War, Famine, Death] = War
    war match {
      case Conquest => fail("War is not Conquest")
      case War      => info("War. War never changes.")
      case Famine   => fail("War is not Famine.")
      case Death    => fail("War is not Death")
    }
  }

  it should "generate case classes for variants with flat arguments" in {
    @flatCaseClasses trait HorsemanT {
      Conquest(A, A, A)
      War(A, A, B)
      Famine(B)
      Death
    }

    type Horseman = HorsemanT[Conquest[Int, Int, Int], War[Int, Int, Boolean], Famine[Boolean], Death]
    val war: Horseman = War(3, 5, true)

    val eight: Int = war match {
      case Conquest(a, b, c) => a + b + c
      case War(a, b, c) => if (c) a + b else a - b
      case Famine(c) => if (c) 1 else 2
      case Death => 0
    }

    assert(eight == 8)
    info(s"3 + 5 = $eight")
  }
}
