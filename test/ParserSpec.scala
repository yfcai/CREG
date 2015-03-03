import org.scalatest._
import creg.compiler._

class ParserSpec extends FlatSpec {
  import Parsers._
  import DatatypeRepresentation._

  "Parser" should "parse records with or without fields" in {
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

  it should "parse datatypes interlaced with built-in types" in {

    @data def SubUnit = SubUnitT {
      PU(person = String)
      DU(dept = Dept)
    }

    @data def Dept = Fix(dept => D(name = String, subunits = Seq apply (
      SubUnitT {
        PU(person = String)
        DU(dept = dept)
      }
    )))

    assert(Dept ==
      DataConstructor(
        "Dept",
        Many.empty,
        FixedPoint("dept",
          Record("D", Many(
            Field("name",
              TypeConst("String")),
            Field("subunits",
              FunctorApplication(TypeConst("Seq"), Many(
                Variant("SubUnitT", Many(
                  Record("PU", Many(Field("person", TypeConst("String")))),
                  Record("DU", Many(Field("dept", TypeVar("dept"))))))))))))))
  }

  it should "parse struct clarations" in {
    @struct def TermT {
      Lit(number) ; Var(name) ; Abs(param, body) ; App(operator, operand)
    }

    assert(TermT ==
      Variant("TermT", List(
        Record("Lit", List(Field("number", TypeConst("Nothing")))),
        Record("Var", List(Field("name", TypeConst("Nothing")))),
        Record("Abs", List(
          Field("param", TypeConst("Nothing")),
          Field("body", TypeConst("Nothing")))),
        Record("App", List(
          Field("operator", TypeConst("Nothing")),
          Field("operand", TypeConst("Nothing")))))))

    @struct def X { Y ; Z(a) }

    assert(X ==
      Variant("X", List(
        Record("Y", Nil),
        Record("Z", List(Field("a", TypeConst("Nothing")))))))
  }
}
