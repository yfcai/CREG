import org.scalatest._
import nominal._
import lib._
import Fix.{Record, Variant}

class DeclarationGeneratorSpec extends FlatSpec {
  import compiler.DeclarationGenerator.Tests._

  "DeclarationGenerator" should "generate an empty sealed trait for 0 variants" in {
    @empty trait Empty1
    @empty trait Empty2
    val x: Empty1T = null
    val y: Empty2T = null

    implicitly[Empty1T <:< Variant]
  }

  def show(F: Traversable.Endofunctor)(t: F.Map[Any]): String =
    F(t).mapReduce(_.toString)("", _ + _)

  def show2(F: Traversable.Endofunctor4)(t: F.Map[Any, Any, Any, Any]): String = {
    def err(i: Int): Any => Nothing = _ => fail(s"position 2 expected, position $i triggered")
    F(t).traverse(Applicative.Const[String]("", _ + _))(err(1), _.toString, err(3), err(4))
  }

  // cargo code
  // http://stackoverflow.com/a/16256935/3968633
  implicit class Regex(sc: StringContext) {
    def r = new scala.util.matching.Regex(sc.parts.mkString, sc.parts.tail.map(_ => "x"): _*)
  }

  def show3(F: Traversable.Endofunctor3)(record: F.Map[Any, Any, Any]): String = {
    val head = record.toString match { case r"([^\(]+)$head.*" => head }
    val body = F(record).traverse(Applicative.Const[String]("", _ + " " + _))(_.toString, _.toString, _.toString)
    s"$head($body)"
  }

  it should "generate case object for variant without arguments" in {
    @caseObject trait Variant { Singleton }
    val singleton: VariantT[Singleton] = Singleton
    singleton match {
      case Singleton => info("success")
    }

    implicitly[VariantT[Int] <:< Variant]
    implicitly[Singleton <:< Record]

    // traversable functor generated for variant
    implicitly[Variant.type <:< Traversable]
    implicitly[Variant.Map[Int] =:= VariantT[Int]]
  }

  it should "generate multiple variants without arguments" in {
    @fourCaseObjects trait Horseman { Conquest ; War ; Famine ; Death }
    val war: HorsemanT[Conquest, War, Famine, Death] = War
    war match {
      case Conquest => fail("War is not Conquest")
      case War      => info("War. War never changes.")
      case Famine   => fail("War is not Famine.")
      case Death    => fail("War is not Death")
    }

    implicitly[HorsemanT[Int, Int, Int, Int] <:< Variant]
    implicitly[Conquest <:< Record]
    implicitly[War <:< Record]
    implicitly[Famine <:< Record]
    implicitly[Death <:< Record]

    implicitly[Horseman.type <:< Traversable4]
    implicitly[Horseman.Map[Int, Boolean, String, Double] =:= HorsemanT[Int, Boolean, String, Double]]
  }

  it should "generate case classes for variants with flat arguments" in {
    @flatCaseClasses trait Horseman {
      Conquest(A, A, A)
      War(A, A, B)
      Famine(B)
      Death
    }

    type TheHorseman = HorsemanT[Conquest[Int, Int, Int], War[Int, Int, Boolean], Famine[Boolean], Death]
    val war: TheHorseman = War(3, 5, true)

    val eight: Int = war match {
      case Conquest(a, b, c) => a + b + c
      case War(a, b, c) => if (c) a + b else a - b
      case Famine(c) => if (c) 1 else 2
      case Death => 0
    }

    assert(eight == 8)
    info(s"3 + 5 = $eight")

    implicitly[TheHorseman <:< Variant]
    implicitly[Conquest[Int, Int, Int] <:< Record]
    implicitly[War[Int, Int, Int] <:< Record]
    implicitly[Famine[Int] <:< Record]
    implicitly[Death <:< Record]

    // prototype record functors
    assert(show3(Conquest)(Conquest(1, 2, 3)) == "Conquest( 1 2 3)")
    assert(show3(War)(War(3, 5, true)) == "War( 3 5 true)")
  }

  // test that synonym generation doesn't conflict with declaration generation
  import functors.datatype
  @datatype trait List[A] { Nil ; Cons(A, List[A]) }
}
