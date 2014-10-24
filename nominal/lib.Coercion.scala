/** Type coercion:
  *
  * - auto-roll at top level
  * - auto-roll at arbitrary level
  * - auto-cast
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

object Coercion extends UniverseConstruction with util.Traverse {
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

    // gotta dealias at every turn (dealiasing isn't recursive)
    val result = performCoercion(c)(q"$argName", actualTag.tpe.dealias, expectedTag.tpe.dealias)

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

      // from fixed to non-fixed: auto-unroll at top level
      case (actual @ FixedPoint(_, _), expected)
          if isScalaSubtype(c)(scalaType(c)(actual.unroll), scalaType(c)(expected)) =>
        q"$arg.unroll"

      case (actual, expected) => adjust(c)(arg, actualType, expectedType) match {
        case TypeError =>
          if (! isNothingType(expectedType))
            c.echo(arg.pos, s"ERROR: cannot coerce $actualType to $expectedType")
          abortWithError(c)(
            c.enclosingPosition,
            s"coercing $actualType to `Nothing`.\n" +
              "either there's a type error or the context has to little information.")

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

            // dealias type arguments (dealiasing isn't done recursively)
            val (subdealiased, superdealiased) = (subtype.dealias, supertype.dealias)

            subdealiased.typeArgs.zip(superdealiased.typeArgs).foldLeft[Result](Some(newAssumptions)) {
              case (Some(assumption), (subchild, superchild)) =>
                isSubDatatype(c)(assumption, subchild, superchild)

              case (None, _) =>
                None
            }

          case (subfix @ FixedPoint(_, _), superfix @ FixedPoint(_, _)) =>
            isSubDatatype(c)(
              newAssumptions,
              scalaType(c)(subfix.unroll),
              scalaType(c)(superfix.unroll))

          case _ =>
            None
        }
      }
    }

  def isScalaSubtype(c: Context)(subtype: c.Type, supertype: c.Type): Boolean = {
    import c.universe._
    inferImplicitValue(c)(tq"$subtype <:< $supertype").nonEmpty
  }

  sealed trait Adjustment[+T] { def map[U](f: T => U): Adjustment[U] }
  case object TypeError extends Adjustment[Nothing] { def map[U](f: Nothing => U): Adjustment[U] = this }
  case object NoChange extends Adjustment[Nothing] { def map[U](f: Nothing => U): Adjustment[U] = this }
  case class Adjusted[T](code: T) extends Adjustment[T] { def map[U](f: T => U): Adjustment[U] = Adjusted(f(code)) }

  /** Transitive closure of the following graph:
    *
    *   ACTUAL        EXPECTED
    *
    *   record   =>   record
    *     ^             |
    *     |             v
    *   variant       variant
    *     ^             |
    *     |             v
    *   fixed         fixed
    *
    */
  def adjust(c: Context)(arg: c.Tree, actual: c.Type, expected: c.Type): Adjustment[c.Tree] =
    adjustTrivially(c)(arg, actual, expected).getOrElse {
      val (actualRep, expectedRep) = (representOnce(c)(actual), representOnce(c)(expected))
        (actualRep, expectedRep) match {
        case (record: Record, expectedRecord: Record) =>
          recordToRecord(c)(arg, record, expectedRecord)

        case (record: Record, variant: Variant) =>
          recordToVariant(c)(arg, record, variant)

        case (record: Record, fixed: FixedPoint) =>
          recordToFixedPoint(c)(arg, record, fixed)

        case (variant: Variant, expectedVariant: Variant) =>
          variantToVariant(c)(arg, variant, expectedVariant)

        case (variant: Variant, fixed: FixedPoint) =>
          variantToFixedPoint(c)(arg, variant, fixed)

        // variant to fixed point, fixed point to variant, etc
        case _ =>
          TypeError
      }
    }

  // either no change, or call an implicit
  def adjustTrivially(c: Context)(arg: c.Tree, actual: c.Type, expected: c.Type): Option[Adjustment[c.Tree]] = {
    import c.universe._
    if (isScalaSubtype(c)(actual, expected))
      Some(NoChange)
    else {
      c.inferImplicitView(arg, actual, expected) match {
        case q"" => None
        case view => Some(Adjusted(q"$view($arg)"))
      }
    }
  }

  /** variant => fixed = variant => variant -> fixed */
  def variantToFixedPoint(c: Context)(arg: c.Tree, variant: Variant, fixed: FixedPoint): Adjustment[c.Tree] =
    variantToVariant(c)(arg, variant, fixed.unroll.asInstanceOf[Variant]) map rollWith(c)(fixed)

  /** variant => variant = variant -> record => variant */
  def variantToVariant(c: Context)(arg: c.Tree, actual: Variant, expected: Variant): Adjustment[c.Tree] =
    if (actual.name == expected.name) {
      import c.universe._

      val adjustedRecords: List[CaseDef] =
        actual.cases.asInstanceOf[Many[Record]].map({
          record => recordCaseDef(c)(record) {
            case (recordName, fieldNames) =>
              val newArg = q"$recordName"
              recordToVariant(c)(newArg, record, expected) match {
                case TypeError => return TypeError
                case Adjusted(code) => code
                case NoChange => newArg
              }
          }
        })(collection.breakOut)

      Adjusted(Match(arg, adjustedRecords))
    }
    else
      TypeError

  /** record => variant = record => record -> variant */
  def recordToVariant(c: Context)(arg: c.Tree, record: Record, variant: Variant): Adjustment[c.Tree] =
    variant.cases.find(_.name == record.name) match {
      case Some(expectedRecord @ Record(_, _)) =>
        // `recordToRecord` will test that actual and expected record fields match
        recordToRecord(c)(arg, record, expectedRecord)

      case _ => TypeError
    }

  /** record => fixed */
  def recordToFixedPoint(c: Context)(arg: c.Tree, record: Record, fixed: FixedPoint): Adjustment[c.Tree] =
    fixed.body match {
      case _: Variant =>
        recordToVariant(c)(arg, record, fixed.unroll.asInstanceOf[Variant]) map rollWith(c)(fixed)

      case _: Record =>
        recordToRecord(c)(arg, record, fixed.unroll.asInstanceOf[Record]) map rollWith(c)(fixed)

      case _ =>
        sys error s"\nCannot convert.\n\nActual datatype:\n$record\n\Expected datatype:\n$fixed\n\nCode:\n$arg\n"
    }

  def rollWith(c: Context)(fixed: FixedPoint): c.Tree => c.Tree = {
    import c.universe._
    val tq"$fix[$functor]" = meaning(c)(fixed)
    body => q"${getRoll(c)}[$functor]($body)"
  }

  /** record => record: primitive gulf-crossing recursion-invoking arrow */
  def recordToRecord(c: Context)(arg: c.Tree, actual: Record, expected: Record): Adjustment[c.Tree] = {
    import c.universe._
    if (
      actual.name != expected.name ||
      actual.fields.map(_.name) != expected.fields.map(_.name)
    )
      TypeError
    else if (actual.fields.isEmpty)
      Adjusted(arg)
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
          TypeError

        case Some(adjustments) if adjustments.isEmpty =>
          Adjusted(arg)

        case Some(adjustments) if adjustments.nonEmpty =>
          Adjusted(q"$arg.copy(..$adjustments)")
      }
    }
  }
}
