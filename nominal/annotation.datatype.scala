package nominal
package annotation

import scala.language.experimental.macros
import scala.reflect.macros.blackbox.Context
import scala.annotation.StaticAnnotation

import compiler._
import DatatypeRepresentation._

object datatype
extends Parser
   with Preprocessor
   with DeclarationGenerator
   with SynonymGenerator
   with TraversableGenerator
   with InterfaceHelperGenerator
{
  object Flag extends Enumeration {
    type Flag = Value
    val ImplicitConstructor = Value
  }

  def vanillaImpl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] =
    expandData(c)(annottees, Set())

  def expandData(c: Context)(annottees: Seq[c.Expr[Any]], options: Set[Flag.Flag]): c.Expr[Any] = {
    import c.universe._

    val (input, companion) = extractInput(c)(annottees)

    try {
      // parser parses DSL
      val parseTree: DataConstructor = parseOrAbort(c)(DataDeclP, input)

      // generate variants
      val forDeclarations: Iterator[Variant] = digestForDeclarationGenerator(c)(input, parseTree)
      val declarations: Iterator[Tree] = forDeclarations flatMap (variant => generateDeclaration(c)(variant))

      val synonymFood: SynonymGeneratorFood = digestForSynonymGenerator(c)(input, parseTree)
      val synonyms: Iterator[Tree] =
        (Iterator(generateSynonym(c)(synonymFood.dataSynonym._1, synonymFood.dataSynonym._2)) ++
          synonymFood.patternFunctor.map({ case (name, data) => generatePatternFunctorSynonym(c)(name, data) }).iterator)
      // preprocessor add Fix
      // declaration generator generates template classes
      // synonym generator generates synonyms

      // import language features needed for generated code
      val imports = scalaLanguageFeatureImports(c).iterator

      // companion object
      val updatedCompanion: c.Tree = injectIntoObject(c)(companion, Seq.empty) // nothing to inject for now

      var result = imports ++ declarations ++ synonyms ++ Some(updatedCompanion)

      if (options(this.Flag.ImplicitConstructor))
        result = result ++ generateAutoroll(c)(synonymFood)

      c.Expr(q"..${result.toSeq}")

    }
    catch {
      case PreprocessorException(message) =>
        abortWithError(c)(input.pos, message)
    }
  }

  /** @return (input-syntax-tree, companion-object)
    *
    * annoying operation; duplicates parser...
    */
  def extractInput(c: Context)(annottees: Seq[c.Expr[Any]]): (c.Tree, c.Tree) = {
    import c.universe._
    def giveUp: Nothing =
      abortWithError(c)(annottees.head.tree.pos,
        "Bad use of @datatype. Usage example:\n\n  @datatype trait List[+A] {\n" +
          "    Nil\n    Cons(head = A, tail = List)\n  }\n.")

    annottees.size match {
      case 0 => giveUp
      case n if n > 2 => giveUp

      case 1 =>
        val input = annottees.head.tree
        getNameOfTrait(c)(input).fold[(c.Tree, c.Tree)](giveUp)(name => (input, q"object ${TermName(name)}"))

      case 2 =>
        val (fst, snd) = (annottees.head.tree, annottees.last.tree)
        (getNameOfTrait(c)(fst), getNameOfTrait(c)(snd)) match {
          case (Some(_), None) => (fst, snd)
          case (None, Some(_)) => (snd, fst)
          case _ => giveUp
        }
    }
  }

  def getNameOfTrait(c: Context)(tree: c.Tree): Option[String] = {
    import c.universe._
    tree match {
      case q"trait $name [..$params]" => Some(name.toString)
      case q"trait $name [..$params] {}" => Some(name.toString)
      case q"trait $name [..$params] { ..$body }" => Some(name.toString)
      case _ => None
    }
  }

  def injectIntoObject(c: Context)(obj: c.Tree, newDecls: Seq[c.Tree]): c.Tree = {
    import c.universe._
    obj match {
      case q"..$attributes object $objectName extends ..$superClasses { ..$existingDecls }" =>
        // hack to put attributes back in the object
        q"object $objectName extends ..$superClasses { ..${newDecls ++ existingDecls} }" match {
          case ModuleDef(_, a, b) => ModuleDef(attributes, a, b)
        }

      case _ =>
        abortWithError(c)(obj.pos, "malformed companion object")
    }
  }
}

class datatype extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro datatype.vanillaImpl
}
