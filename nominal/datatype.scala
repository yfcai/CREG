package nominal
import scala.language.experimental.macros
import scala.reflect.macros.blackbox.Context
import scala.annotation.StaticAnnotation

import DatatypeRepresentation._

object datatype extends Parser with Preprocessor with DeclarationGenerator with SynonymGenerator {
  def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._

    if (annottees.size != 1)
      abortWithError(c)(annottees.head.tree.pos,
        "Bad use of @datatype. Usage example:\n\n  @datatype trait List[+A] {\n" +
          "    Nil\n    Cons(head = A, tail = List)\n  }\n.")

    val input = annottees.head.tree

    try {
      // parser parses DSL
      val parseTree: DataConstructor = parseOrAbort(c)(DataDeclP, input)

      // generate variants
      val forDeclarations: Iterator[Variant] = digestForDeclarationGenerator(c)(input, parseTree)
      val declarations: Iterator[Tree] = forDeclarations flatMap (variant => generateDeclaration(c)(variant))

      val synonymFood: SynonymGeneratorFood = digestForSynonymGenerator(c)(input, parseTree)
      val synonyms: Iterator[Tree] =
        (Iterator(generateSynonym(c)(synonymFood.dataSynonym._1, synonymFood.dataSynonym._2)) ++
          synonymFood.patternFunctor.map({ case (name, data) => generatePatternFunctor(c)(name, data) }).iterator)
      // preprocessor add Fix
      // declaration generator generates template classes
      // synonym generator generates synonyms

      // import language features needed for generated code
      val imports = Iterator(
        q"import _root_.scala.language.higherKinds",
        q"import _root_.scala.language.implicitConversions"
      )

      // TODO: append recursive polynomial functor instances etc to result
      val result = declarations ++ synonyms

      c.Expr(q"..${(imports ++ result).toSeq}")

    }
    catch {
      case PreprocessorException(message) =>
        abortWithError(c)(input.pos, message)
    }
  }
}

class datatype extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro datatype.impl
}
