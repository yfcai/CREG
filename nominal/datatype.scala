package nominal
import scala.language.experimental.macros
import scala.reflect.macros.blackbox.Context
import scala.annotation.StaticAnnotation

import DatatypeRepresentation._

object datatype extends Parser with Preprocessor with DeclarationGenerator {
  def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._

    val Seq(expr) = annottees
    val input = expr.tree

    // parser parses DSL
    val parseTree: DataConstructor = parseOrAbort(c)(DataDeclP, input)

    // generate variants
    val forDeclarations: Iterator[Variant] = digestForDeclarationGenerator(c)(input, parseTree)
    val declarations: Iterator[Tree] = forDeclarations flatMap (variant => generateDeclaration(c)(variant))

    // preprocessor add Fix
    // declaration generator generates template classes
    // synonym generator generates synonyms

    c.Expr(q"") // TODO: generate synonyms & functor instances too
  }
}

class datatype extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro datatype.impl
}