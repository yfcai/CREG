import org.scalatest._
import nominal.compiler.Parser

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

  it should "parse datatypes mentioning known functors" in pending // Company example; mentions List

  it should "parse mutually recursive datatype families" in pending

  it should "parse mutually recursive datatypes mentioning known functors" in pending

}
