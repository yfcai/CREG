import org.scalatest._
import nominal.compiler._

class ParserSpec extends FlatSpec {
  import Parsers._

  "Parser" should "parse records with or without fields" in {
    import DatatypeRepresentation._

    @record def WithoutFields = SomeRecord

    assert(WithoutFields == Record("SomeRecord", Many.empty))

    @record def WithFields =
      SomeRecord(_1 = Field1, _2 = Field2, _3 = Field3, _4 = Field4, _5 = Field5)

    assert(WithFields ==
      Record("SomeRecord", Many(
        Field("_1", TypeConst("Field1")),
        Field("_2", TypeConst("Field2")),
        Field("_3", TypeConst("Field3")),
        Field("_4", TypeConst("Field4")),
        Field("_5", TypeConst("Field5")))))

  }

  it should "parse nonempty data declarations" in {
    import DatatypeRepresentation._

    @data def IntList =
      Fix(intList =>
        IntListT {
          Nil
          Cons(head = Int, tail = intList)
        })

    assert(IntList ==
      DataConstructor(
        "IntList",
        Many.empty,
        FixedPoint("intList",
          Variant("IntListT", Many(
            Record("Nil", Many.empty),
            Record("Cons", Many(
              Field("head", TypeConst("Int")),
              Field("tail", TypeVar("intList")))))))))

    @data def List[A] = Fix(list => ListT { Nil ; Cons(head = A, tail = list) })

    assert(List ==
      DataConstructor(
        "List",
        Many(Param covariant "A"),
        FixedPoint("list",
          Variant("ListT", Many(
            Record("Nil", Many.empty),
            Record("Cons", Many(
              Field("head", TypeVar("A")),
              Field("tail", TypeVar("list")))))))))
  }
/*
  it should "parse families of datatypes" in {
    @familydecl trait Company[P] {
      Dept { D(units = List[Subunit]) }
      Subunit { DU(dept = Dept) ; PU(person = P) }
    }

    assert(Company ==
      DataFamily(
        "Company",
        Many(Param invariant "P"),
        Many(
          Variant("Dept", Many(
            Record("D", Many(Field("units", TypeVar("List[Subunit]")))))),
          Variant("Subunit", Many(
            Record("DU", Many(Field("dept", TypeVar("Dept")))),
            Record("PU", Many(Field("person", TypeVar("P")))))))))
  }
   */
}
