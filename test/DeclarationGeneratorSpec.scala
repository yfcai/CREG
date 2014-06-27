import org.scalatest._

class DeclarationGeneratorSpec extends FlatSpec {
  import DeclarationGenerator.Tests._

  "DeclarationGenerator" should "generate an empty sealed trait for 0 variants" in {
    @empty trait Empty1
    @empty trait Empty2
    val x: Empty1T = null
    val y: Empty2T = null
  }

  it should "generate a case object for variant without arguments" in {
    @caseObject trait Variant { Singleton }
    val singleton: VariantT[Singleton] = Singleton
    singleton match {
      case Singleton => info("success")
    }
  }

  it should "generate multiple variants without arguments" in {
    @fourCaseObjects trait Horsemen { Conquest ; War ; Famine ; Death }
    val war: HorsemenT[Conquest, War, Famine, Death] = War
    war match {
      case Conquest => fail("War is not Conquest")
      case War      => info("War. War never changes.")
      case Famine   => fail("War is not Famine.")
      case Death    => fail("War is not Death")
    }
  }

  it should "permit extra covariant type parameters" in {
    @genericCaseObjects trait Horsemen[+Of, +The, +Apocalypse] { Conquest ; War ; Famine ; Death }
    val war: HorsemenT[Int, Boolean, String, Conquest, War, Famine, Death] = War
    war match {
      case Conquest => fail("War is not Conquest")
      case War      => info("War. War never changes.")
      case Famine   => fail("War is not Famine.")
      case Death    => fail("War is not Death")
    }
  }
}
