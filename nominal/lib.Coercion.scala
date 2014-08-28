/** Type coercion:
  *
  * - auto-roll at top level
  * - auto-roll at arbitrary level
  * - auto-cast (pending: need subtyping for datatypes with structural fixed points)
  * - interleaving auto-roll and auto-cast at arbitrary depth (probably really hard)
  */

package nominal
package lib

import scala.language.higherKinds
import scala.language.implicitConversions
import scala.language.experimental.macros

import scala.reflect.macros.blackbox.Context

import compiler._
import DatatypeRepresentation._

trait Coercion {
  // sadly, making `coerce` implicit does not alleviate the burden of writing it in client code.
  // scalac has problem finding the implicit witness.
  //
  // generating `collection.breakOut`-style code does not work either:
  // `coerceImpl` gets called with `Expected = Nothing`.
  def coerce[S, T](arg: S)(implicit witness: Fix.TypeWitness[T]): T = macro Coercion.coerceImpl[S, T]

  /** macro for testing purpose
    * @param info where the info should be written to
    */
  def coerceContextInfo[S, T]
    (arg: S, info: collection.mutable.Map[String, String])
    (implicit witness: Fix.TypeWitness[T]): T = macro Coercion.infoImpl[S, T]
}

object Coercion extends UniverseConstruction {
  import Fix.TypeWitness

  def infoImpl[Actual, Expected]
    (c: Context)
    (arg: c.Tree, info: c.Tree)
    (witness: c.Tree)
    (implicit actualTag: c.WeakTypeTag[Actual], expectedTag: c.WeakTypeTag[Expected]):
      c.Tree =
    {
      import c.universe._
      val (actualType, expectedType) = (actualTag.tpe, expectedTag.tpe)
      q"""{
        $info += ("actual" -> ${actualType.toString}) += ("expected" -> ${expectedType.toString})
        null.asInstanceOf[$expectedType]
      }"""
    }


  def coerceImpl[Actual, Expected]
    (c: Context)
    (arg: c.Tree)
    (witness: c.Tree)
    (implicit actualTag: c.WeakTypeTag[Actual], expectedTag: c.WeakTypeTag[Expected]):
      c.Tree = try {
    import c.universe._

    val argName = TermName(c freshName "coerced")
    val result = performCoercion(c)(q"$argName", actualTag.tpe, expectedTag.tpe)

    q"""{
      val $argName = $arg
      $result
    }"""
  }
  catch {
    case e: Throwable =>
      if (
        false && // disable stack trace printing
        ! isNothingType(expectedTag.tpe)
      ) {
        println(e.getMessage)
        println(e.printStackTrace)
        println
      }
      throw e
  }

  def performCoercion(c: Context)(arg: c.Tree, actualType: c.Type, expectedType: c.Type): c.Tree = {
    import c.universe._
    val actual = representOnce(c)(actualType)
    val expected = representOnce(c)(expectedType)
    (actual, expected) match {

      // actual & expected has compatible runtime type. do a cast.
      // question: can `adjust` subsume this?
      case _ if compatibleRuntimeTypes(c)(actualType, expectedType) =>
        q"$arg.asInstanceOf[$expectedType]"

      // from non-fixed to fixed: auto-roll at top level
      // record case replaced by auto-rolling at all levels (record-only for now)
      case (actual @ Variant(_, _), expected @ FixedPoint(_, _))
          if isScalaSubtype(c)(scalaType(c)(actual), scalaType(c)(expected.unrollOnce)) =>
        val tq"$fix[$functor]" = meaning(c)(expected)
        q"${getRoll(c)}[$functor]($arg)"

      // from fixed to non-fixed: auto-unroll at top level
      case (actual @ FixedPoint(_, _), expected)
          if isScalaSubtype(c)(scalaType(c)(actual.unrollOnce), scalaType(c)(expected)) =>
        q"$arg.unroll"

      case (actual, expected) => adjust(c)(arg, actualType, expectedType) match {
        case TypeError =>
          if (! isNothingType(expectedType))
            c.echo(arg.pos, s"ERROR: cannot coerce $actualType to $expectedType")
          abortWithError(c)(
            c.enclosingPosition,
            s"type error during coercion, see above.")

        case NoChange =>
          arg

        case Adjusted(code) =>
          code
      }
    }
  }

  def isNothingType(tpe: Context#Type): Boolean =
    tpe.typeSymbol.fullName == "scala.Nothing"

  def compatibleRuntimeTypes(c: Context)(actual: c.Type, expected: c.Type): Boolean =
    isSubDatatype(c)(Set.empty, actual, expected).nonEmpty

  // somewhere between subtyping of equi- and iso-recursive types
  // based on Pierce §21.9 figure 21-4 on page 305
  def isSubDatatype(c: Context)(
    assumptions: Set[(Datatype, Datatype)],
    subtype: c.Type,
    supertype: c.Type
  ): Option[Set[(Datatype, Datatype)]] =
    if (isScalaSubtype(c)(subtype, supertype))
      Some(assumptions)
    else {
      type Result = Option[Set[(Datatype, Datatype)]]
      val (subRep, superRep) = (representOnce(c)(subtype), representOnce(c)(supertype))

      val canons = (subRep.canonize, superRep.canonize)
      if (assumptions(canons))
        Some(assumptions)
      else {
        val newAssumptions = assumptions + canons

        //DEBUG
        if (newAssumptions.size > 100){
          println(s"\nBAD NEWS: GOT 100 ASSUMPTIONS\n")
          println(subtype)
          println
          println(supertype)
          println
          return None
        }

        (subRep, superRep) match {
          case (Variant(subhead, subcases), Variant(superhead, supercases))
              if subhead == superhead && subcases.length == supercases.length =>
            subcases.zip(supercases).foldLeft[Result](Some(newAssumptions)) {
              case (Some(assumption), (subcase @ Record(_, _), supercase @ Record(_, _))) =>
                isSubDatatype(c)(assumption, scalaType(c)(subcase), scalaType(c)(supercase))

              case (None, _) =>
                None

              case _ =>
                sys error s"500 internal error during subtyping. expect sums of records, got:\n  $subtype\n  $supertype"
            }

          case (Record(subname, subfields), Record(supername, superfields))
              if subname == supername && subfields.map(_.name) == superfields.map(_.name) =>
            subtype.typeArgs.zip(supertype.typeArgs).foldLeft[Result](Some(newAssumptions)) {
              case (Some(assumption), (subchild, superchild)) =>
                isSubDatatype(c)(assumption, subchild, superchild)

              case (None, _) =>
                None
            }

          case (subfix @ FixedPoint(_, _), superfix @ FixedPoint(_, _)) =>
            isSubDatatype(c)(
              newAssumptions,
              scalaType(c)(subfix.unrollOnce),
              scalaType(c)(superfix.unrollOnce))

          case _ =>
            None
        }
      }
    }

  def isScalaSubtype(c: Context)(subtype: c.Type, supertype: c.Type): Boolean = {
    import c.universe._
    c.inferImplicitValue(treeToType(c)(tq"$subtype <:< $supertype")) match {
      case q"" => false
      case _ => true
    }
  }

  sealed trait Adjustment[+T]
  case object TypeError extends Adjustment[Nothing]
  case object NoChange extends Adjustment[Nothing]
  case class Adjusted[T](code: T) extends Adjustment[T]

  def adjust(c: Context)(arg: c.Tree, actual: c.Type, expected: c.Type): Adjustment[c.Tree] = {
    import c.universe._
    if (isScalaSubtype(c)(actual, expected))
      NoChange
    else {
      val (actualRep, expectedRep) = (representOnce(c)(actual), representOnce(c)(expected))
      (actualRep, expectedRep) match {
        // record to fixed point
        case (actualRecord @ Record(_, _), fixed @ FixedPoint(fixedName, Variant(header, records))) =>
          records.find(_.name == actualRecord.name) match {
            case Some(expectedRecord0 @ Record(_, _)) =>
              val expectedRecord = (expectedRecord0 subst (fixedName, fixed)).asInstanceOf[Record]
              val tq"$fix[$functor]" = meaning(c)(expectedRep)
              adjustRecordBody(c)(arg, actualRecord, expectedRecord) match {
                case Some(body) => Adjusted(q"${getRoll(c)}[$functor]($body)")
                case None => TypeError
              }

            // no record of identical name found
            case _ => TypeError
          }

        // variant to fixed point, fixed point to variant, etc
        case _ =>
          TypeError
      }
    }
  }

  def adjustRecordBody(c: Context)(arg: c.Tree, actual: Record, expected: Record): Option[c.Tree] = {
    import c.universe._
    if (
      actual.name != expected.name ||
      actual.fields.map(_.name) != expected.fields.map(_.name)
    )
      None
    else if (actual.fields.isEmpty)
      Some(arg)
    else {
      val subAdjustments = actual.fields.zip(expected.fields).foldRight[Option[List[c.Tree]]](Some(Nil)) {
        case (_, None) =>
          None

        case ((Field(fieldName, fieldRep), Field(_, expectedFieldRep)), Some(otherCode)) =>
          val projectedArg = q"$arg.${TermName(fieldName)}"
          val (fieldType, expectedFieldType) = (scalaType(c)(fieldRep), scalaType(c)(expectedFieldRep))
          adjust(c)(projectedArg, fieldType, expectedFieldType) match {
            case TypeError =>
              None

            case NoChange =>
              Some(otherCode)

            case Adjusted(code) =>
              Some(q"${TermName(fieldName)} = $code" :: otherCode)
          }
      }
      subAdjustments match {
        case None =>
          None

        case Some(adjustments) if adjustments.isEmpty =>
          Some(arg)

        case Some(adjustments) if adjustments.nonEmpty =>
          Some(q"$arg.copy(..$adjustments)")
      }
    }
  }
}
