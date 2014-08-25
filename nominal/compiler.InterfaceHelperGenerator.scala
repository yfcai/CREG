/** Generate various interface improvement helpers for datatype declarations */

package nominal
package compiler

import scala.reflect.macros.blackbox.Context
import DatatypeRepresentation._

trait InterfaceHelperGenerator extends TraversableGenerator with Preprocessor {
  /** Given
    *
    *   @datatype trait Term {
    *     Void
    *     Var(name = String)
    *     Abs(param = String, body = Term)
    *     App(operator = Term, operand = Term)
    *   }
    *
    * generate
    *
    *   implicit def autoroll$macro$1997[Ab0 <% Term, Ap0 <% Term, Ap1 <% Term](
    *     t: TermT[Void, Var[String], Abs[String, Ab0], App[Ap0, Ap1]]
    *   ): Term = {
    *     @functor val rollF = (Ab0, Ap0, Ap1) => TermT[Void, Var[String], Abs[String, Ab0], App[Ap0, Ap1]]
    *     Roll[TermF](rollF(t) map (x => x: Term, x => x: Term, x => x: Term))
    *   }
    */
  def generateAutoroll(c: Context)(food: SynonymGeneratorFood): Option[c.Tree] = {
    import c.universe._
    food.patternFunctor match {
      // if there is no pattern functor,
      // then the datatype is not recursive and we don't have to autoroll.
      case None =>
        None

      case Some((patternFunctorName, patternFunctor)) =>
        Some(doGenerateAutoroll(c)(patternFunctorName, patternFunctor))
    }
  }

  def doGenerateAutoroll(c: Context)(patternFunctorName: Name, genericData: DataConstructor): c.Tree = {
    import c.universe._
    val DataConstructor(genericParams, FixedPoint(name, body)) = genericData

    val genericTypeNames = genericParams map (x => TypeName(x.name))

    val fixedType =
      if (genericParams.isEmpty)
        tq"${TypeName(name)}"
      else
        tq"${TypeName(name)}[..$genericTypeNames]"

    val arg = TermName(c freshName "t")

    // create a DataConstructor taking types to each of the recursive positions
    // call it the multi pattern functor
    val multiPatternFunctor = diversifyPatternFunctor(c)(name, body)

    // view bounds do not exist...
    val typeParams = mkTypeDefs(c)((genericParams ++ multiPatternFunctor.params) map (_.toInvariant))

    // TermT[Void, Var[String], Abs[String, Ab0], App[Ap0, Ap1]]
    val argType = meaning(c)(multiPatternFunctor.body)

    // x => x: Term, x => x: Term, ...
    val implicitCalls = multiPatternFunctor.params map (_ => q"(x => x: $fixedType)")

    val autoroll = TermName(c freshName "autoroll")

    val evidences = multiPatternFunctor.params map { param =>
      q"val ${TermName(param.name)} : (${TypeName(param.name)} => $fixedType)"
    }

    // ({ type λ[+X] = TermF[X] })#λ
    val patternFunctor = {
      val f = TypeName(patternFunctorName)
      val inner = TypeName(c freshName "inner")
      val x = TypeName(c freshName "X")
      val typeArgs = genericTypeNames :+ x
      tq"({ type $inner[+$x] = $f[..$typeArgs] })#$inner"
    }

    // the traversable functor about each and every recursive position
    val rollF = generateTraversable(c)(multiPatternFunctor)
    val autorollBody = q"${getRoll(c)}[$patternFunctor]($rollF($arg) map (..$implicitCalls))"

    q"implicit def $autoroll[..$typeParams]($arg: $argType)(implicit ..$evidences): $fixedType = $autorollBody"
  }

  /** create a DataConstructor mapping parameters to each occurrence of
    * `name` in `body`
    */
  def diversifyPatternFunctor(c: Context)(name: Name, body: Datatype): DataConstructor = {
    val occurrences = countOccurrences(name, body)
    val params: Many[Param] = (1 to occurrences).map(_ => Param covariant (c freshName name))(collection.breakOut)
    val iterator = params.iterator

    def renameRecursively(data: Datatype): Datatype = data match {
      case TypeVar(x)             if x == name => TypeVar(iterator.next.name)
      case fix @ FixedPoint(y, _) if y == name => fix
      case other                               => other gmapT renameRecursively
    }

    DataConstructor(params, renameRecursively(body))
  }

  def countOccurrences(name: Name, body: Datatype): Int = body match {
    case TypeVar(x) =>
      if (x == name) 1 else 0

    case FixedPoint(y, body) =>
      if (y == name) 0 else countOccurrences(name, body)

    case Intersect(_, _) | Reader(_, _) | Record(_, _) | Variant(_, _) =>
      body.children.map(child => countOccurrences(name, child)).foldLeft(0)(_ + _)
  }
}
