import org.scalatest._
import nominal.compiler._
import nominal.compiler.DatatypeRepresentation._

class ParserSpec extends FlatSpec {
  import Parser.Tests._

  "Parser" should "parse records with or without fields" in {
    @record trait WithoutFields { SomeRecord }
    @record trait WithFields { SomeRecord(Field1, Field2, field3 = Field3, field4 = Field4, Field5) }
  }

  it should "parse empty data declarations" in {
    @datadecl trait Empty1
    @datadecl trait Empty2 {}
    @datadecl trait Empty3 [W, X, +Y, -Z]
    @datadecl trait Empty4 [W, X, +Y, -Z] {}
  }

  it should "parse nonempty data declarations" in {
    @datadecl trait IntList {
      Nil
      Cons(Int, IntList) // CAUTION: recursion! to be handled by preprocessor.
    }

    @datadecl trait WeirdList[-A, +B] {
      Nil = B
      Cons(head = B, tail = WeirdList[A, B])
      With(WeirdList[A, B] WITH B)
      More(reader = A =>: (WeirdList[A, B] WITH B))
      Over(intersect = A =>: WeirdList[A, B]  WITH  B) // `=>:` binds tighter than `WITH`
    }
  }

  it should "parse nested data" in {
    // a part ripped out of the famous Company example
    @datadecl trait Dept {
      D(name = String,
        manager = Manager {
          E(name = String,
            salary = Salary { S(Float) })
        })
    }
  }

  it should "parse functors" in {
    @functor val id = x => x
    assert(id == DataConstructor(Many(Param covariant "x"), TypeVar("x")))

    @functor val list = A => List { Nil ; Cons(head = A, tail = List) }
    assert(list ==
      DataConstructor(
        Many(Param covariant "A"),
        Variant("List", Many( // note that parser does not auto-create fixed points
          Record("Nil", Many.empty),
          Record("Cons", Many(
            Field("head", TypeVar("A")),
            Field("tail", TypeVar("List"))))))))

    // after preprocessing, list2 & list2v1 & list2v2 should generate the same functor.

    @functor val list2 = A => List[List[A]]
    assert(list2 ==
      DataConstructor(
        Many(Param covariant "A"),
        TypeVar("List[List[A]]"))) // note that type applications are not expanded

    @functor val list2v1 = A => List { Cons(head = List { Cons(head = A) }) }
    assert(list2v1 ==
      DataConstructor(
        Many(Param covariant "A"),
        Variant("List", Many(
          Record("Cons", Many(
            Field("head",
              Variant("List", Many(
                Record("Cons", Many(
                  Field("head",
                    TypeVar("A")))))))))))))

    @functor val list2v2 = A => List { Cons(head = List[A]) }
    assert(list2v2 ==
      DataConstructor(
        Many(Param covariant "A"),
        Variant("List", Many(
          Record("Cons", Many(
            Field("head",
              TypeVar("List[A]"))))))))

    @functor val listv = N => List { Nil = N }
    assert(listv ==
      DataConstructor(
        Many(Param covariant "N"),
        Variant("List", Many(
          Field("Nil", TypeVar("N"))))))
  }

  it should "be able to parse functor representations" in {
    import nominal.compiler.Functor._
    @fun val id = x => x
    assert(id == Decl(Many("x"), TypeVar("x")))

    @fun val constInt = x => Int
    assert(constInt == Decl(Many("x"), TypeVar("Int")))

    @fun val intListF = x => List(Nil, Cons(Int, x))
    assert(intListF ==
      Decl(Many("x"),
        Application("List", Many(
          TypeVar("Nil"),
          Application("Cons", Many(TypeVar("Int"), TypeVar("x")))))))

    @fun val elemF = x => Fix(list => List(Nil, Cons(x, list)))
    assert(elemF ==
      Decl(Many("x"),
        FixedPoint("list",
          Application("List", Many(
            TypeVar("Nil"),
            Application("Cons", Many(TypeVar("x"), TypeVar("list"))))))))
  }

  it should "parse datatypes mentioning known functors" in pending // Company example; mentions List

  it should "parse mutually recursive datatype families" in pending

  it should "parse mutually recursive datatypes mentioning known functors" in pending

}
