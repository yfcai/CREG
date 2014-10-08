import org.scalatest._
import nominal.compiler._
import nominal.compiler.DatatypeRepresentation._

class ParserSpec extends FlatSpec {
  import Parser.Tests._

  "Parser" should "parse records with or without fields" in {
    @record trait WithoutFields { SomeRecord }
    assert(WithoutFields == Record("SomeRecord", Many.empty))

    @record trait WithFields {
      SomeRecord(Field1, Field2, field3 = Field3, field4 = Field4, Field5)
    }
    assert(WithFields ==
      Record("SomeRecord", Many(
        Field("_1", TypeVar("Field1")),
        Field("_2", TypeVar("Field2")),
        Field("field3", TypeVar("Field3")),
        Field("field4", TypeVar("Field4")),
        Field("_5", TypeVar("Field5")))))

  }

  it should "parse empty data declarations" in {
    @datadecl trait Empty1
    @datadecl trait Empty2 {}
    @datadecl trait Empty3 [W, X, +Y, -Z]
    @datadecl trait Empty4 [W, X, +Y, -Z] {}

    assert(Empty1 == DataConstructor(Many.empty, Variant("Empty1", Many.empty)))

    assert(Empty2 == DataConstructor(Many.empty, Variant("Empty2", Many.empty)))

    assert(Empty3 ==
      DataConstructor(
        Many(
          Param.invariant("W"), Param.invariant("X"),
          Param.covariant("Y"), Param.contravariant("Z")),
        Variant("Empty3", Many.empty)))

    assert(Empty4 ==
      DataConstructor(
        Many(
          Param.invariant("W"), Param.invariant("X"),
          Param.covariant("Y"), Param.contravariant("Z")),
        Variant("Empty4", Many.empty)))
  }

  it should "parse nonempty data declarations" in {
    @datadecl trait IntList {
      Nil
      Cons(Int, IntList) // CAUTION: recursion! to be handled by preprocessor.
    }

    assert(IntList ==
      DataConstructor(
        Many.empty,
        Variant("IntList", Many(
          Record("Nil", Many.empty),
          Record("Cons", Many(
            Field("_1", TypeVar("Int")),
            Field("_2", TypeVar("IntList"))))))))
  }

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

  // TODO: test ParserOfFunctorRep.
}
