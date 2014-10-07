import org.scalatest._
import nominal.compiler._
import DatatypeRepresentation._

class PreprocessorSpec extends FlatSpec with Preprocessor {

  // collection of datatype decls
  // must be written before the tests

  val empty =
    Variant(TypeVar("Empty"), Many.empty)

  val intList =
    Variant(TypeVar("IntList"), Many(
      Record("Nil", Many.empty),
      Record("Cons", Many(
        Field("_1", TypeVar("Int")),
        Field("_2", TypeVar("IntList"))))))

  val weirdList =
    Variant(TypeVar("WeirdList"), Many(
      Field("Nil", TypeVar("B")),
      Record("Cons", Many(
        Field("head", TypeVar("B")),
        Field("tail", TypeVar("WeirdList[A, B]")))),
      Record("With", Many(
        Field("_1", Intersect(TypeVar("WeirdList[A, B]"), TypeVar("B"))))),
      Record("More", Many(
        Field("reader",
          Reader(
            TypeVar("A"),
            Intersect(TypeVar("WeirdList[A, B]"), TypeVar("B")))))),
      Record("Over", Many(
        Field("intersect",
          Intersect(
            Reader(TypeVar("A"), TypeVar("WeirdList[A, B]")),
            TypeVar("B")))))))

  val dept =
    Variant(TypeVar("Dept"), Many(
      Record("D", Many(
        Field("name", TypeVar("String")),
        Field("manager",
          Variant(TypeVar("Manager"), Many(
            Record("E", Many(
              Field("name", TypeVar("String")),
              Field("salary",
                Variant(TypeVar("Salary"), Many(
                  Record("S", Many(Field("_1", TypeVar("Float"))))))))))))))))

  "Preprocessor" should "extract variants" in {
    assert(extractVariants(empty).toList == List(empty))
    assert(extractVariants(intList).toList == List(intList))
    assert(extractVariants(weirdList).toList == List(weirdList))

    assert(extractVariants(dept).toList ==
      List(
        dept,
        Variant(TypeVar("Manager"), Many(
          Record("E", Many(
            Field("name", TypeVar("String")),
            Field("salary",
              Variant(TypeVar("Salary"), Many(
                Record("S", Many(Field("_1", TypeVar("Float"))))))))))),
        Variant(TypeVar("Salary"), Many(
          Record("S", Many(Field("_1", TypeVar("Float"))))))))
  }
}
