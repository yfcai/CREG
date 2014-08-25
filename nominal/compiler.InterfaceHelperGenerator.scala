/** Generate various interface improvement helpers for datatype declarations */

package nominal
package compiler

import scala.reflect.macros.blackbox.Context
import DatatypeRepresentation._

trait InterfaceHelperGenerator extends TraversableGenerator with Preprocessor {
  /** Given:
    *
    *   @datatype trait Term {
    *     Void
    *     Var(name = String)
    *     Abs(param = String, body = Term)
    *     App(operator = Term, operand = Term)
    *   }
    *
    * Generate:
    *
    *   implicit def autorollVoid(t: Void): Term = Roll[TermF](t)
    *   implicit def autorollVar(t: Var[String]): Term = Roll[TermF](Var(t.name))
    *   implicit def autorollAbs[T <% Term](t: Abs[String, T]): Term = Roll[TermF](Abs(t.param, t.body))
    *   implicit def autorollApp[S <% Term, T <% Term](t: App[S, T]): Term = Roll[TermF](App(t.operator, t.operand))
    */
  def generateAutoroll(c: Context)(food: SynonymGeneratorFood): Many[c.Tree] = {
    import c.universe._
    food.patternFunctor match {
      // if there is no pattern functor,
      // then the datatype is not recursive and we don't have to autoroll.
      case None =>
        Many.empty

      case Some((patternFunctorName, patternFunctor)) =>
        autorollAllRecords(c)(patternFunctorName, patternFunctor)
    }
  }

  /** Generate special implicit conversions for case objects
    * (resolution can't find them if the datatype is generic)
    *
    *   implicit def rollVoid$macro$1997(t: Void): Term = Roll[TermF](t)
    */
  def autorollAllRecords(c: Context)(patternFunctorName: Name, genericData: DataConstructor): Many[c.Tree] = {
    import c.universe._
    genericData match {
      case DataConstructor(genericParams,
             FixedPoint(name, Variant(header, nominals))) =>
        val records = nominals.asInstanceOf[Many[Record]]
        records map {
          case record @ Record(recordName, fields) =>
            val genericTypeNames = genericParams map (x => TypeName(x.name))

            val fixedType =
              if (genericParams.isEmpty)
                tq"${TypeName(name)}"
              else
                tq"${TypeName(name)}[..$genericTypeNames]"

            val arg = TermName(c freshName "t")

            // create a DataConstructor taking types to each of the recursive positions
            // call it the multi pattern functor
            val multiPatternFunctor = diversifyPatternFunctor(c)(name, record)
            val recursivePositions = multiPatternFunctor.params

            // view bounds do not exist...
            val typeParams = mkTypeDefs(c)((genericParams ++ recursivePositions) map (_.toInvariant))

            // TermT[Void, Var[String], Abs[String, Ab0], App[Ap0, Ap1]]
            val argType = meaning(c)(multiPatternFunctor.body)

            // x => x: Term, x => x: Term, ...
            val implicitCalls = recursivePositions map (_ => q"(x => x: $fixedType)")

            val autoroll = TermName(c freshName "autoroll" + recordName)

            val evidences = recursivePositions map { param =>
              q"val ${TermName(param.name)} : (${TypeName(param.name)} => $fixedType)"
            }

            // ({ type λ[+X] = TermF[X] })#λ
            val patternFunctor = mkInnerPatternFunctor(c)(patternFunctorName, genericParams)

            val autorollBody =
              if (fields.isEmpty)
                q"${getRoll(c)}[$patternFunctor]($arg)"
              else {
                val recordTerm = TermName(recordName)
                val newFields = fields.map {
                  case Field(fieldName, fieldType) =>
                    q"$arg.${TermName(fieldName)}"
                }
                q"${getRoll(c)}[$patternFunctor]($recordTerm(..$newFields))"
              }

            q"implicit def $autoroll[..$typeParams]($arg: $argType)(implicit ..$evidences): $fixedType = $autorollBody"
        }

      case _ =>
        Many.empty
    }
  }

  // ({ type λ[+X] = TermF[X] })#λ
  def mkInnerPatternFunctor(c: Context)(patternFunctorName: Name, genericParams: Many[Param]): c.Tree = {
    import c.universe._
    val f = TypeName(patternFunctorName)
    val inner = TypeName(c freshName "inner")
    val x = TypeName(c freshName "X")
    val typeArgs = genericParams.map(x => TypeName(x.name)) :+ x
    tq"({ type $inner[+$x] = $f[..$typeArgs] })#$inner"
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
