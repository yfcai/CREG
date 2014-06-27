import org.scalatest._

class DeclarationGeneratorSpec extends FlatSpec {
  import DeclarationGenerator.Tests._

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
    @fourCaseObjects trait HorsemenT { Conquest ; War ; Famine ; Death }
    val war: HorsemenT[Conquest, War, Famine, Death] = War
    war match {
      case Conquest => fail("War is not Conquest")
      case War      => info("War. War never changes.")
      case Famine   => fail("War is not Famine.")
      case Death    => fail("War is not Death")
    }
  }

  it should "permit extra covariant type parameters" in {
    @genericCaseObjects trait HorsemenT[+Of, +The, +Apocalypse] { Conquest ; War ; Famine ; Death }
    val war: HorsemenT[Int, Boolean, String, Conquest, War, Famine, Death] = War
    war match {
      case Conquest => fail("War is not Conquest")
      case War      => info("War. War never changes.")
      case Famine   => fail("War is not Famine.")
      case Death    => fail("War is not Death")
    }
  }

  it should "generate case class for variant with arguments" in {
    @caseClasses trait HorsemenT[+Of, +The, +Apocalypse] {
      Conquest(Of, Int)
      War(The, Boolean)
      Famine(List[Apocalypse])
      Death
    }
  }
}
