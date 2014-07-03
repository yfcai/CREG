import org.scalatest._

class ParserSpec extends FlatSpec {
  import Parser.Tests._

  "Parser" should "parse records with or without fields" in {
    @record trait WithoutFields { SomeRecord }
    @record trait WithFields { SomeRecord(Field1, Field2, field3 = Field3, field4 = Field4, Field5) }
  }
}
