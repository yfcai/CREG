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
import scala.reflect.macros.whitebox.{ Context => WhiteContext }

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
      c.Tree = {
    performCoercion(c)(arg, actualTag.tpe, expectedTag.tpe)
  }

  def performCoercion(c: Context)(arg: c.Tree, actualType: c.Type, expectedType: c.Type): c.Tree = {
    import c.universe._
    val actual = representOnce(c)(actualType)
    val expected = representOnce(c)(expectedType)
    (actual, expected) match {
      // actual & expected has compatible runtime type. do a cast.
      case _ if compatibleRuntimeTypes(c)(actualType, expectedType) =>
        q"$arg.asInstanceOf[$expectedType]"

      case (FixedPoint(_, _), FixedPoint(_, _)) =>
        sys error s"TODO: coercion between fixed points\nfrom: $actual\n..to: $expected"

      // from non-fixed to fixed: auto-roll at top level
      case (actual, expected @ FixedPoint(_, _))
          if isScalaSubtype(c)(scalaType(c)(actual), scalaType(c)(expected.unrollOnce)) =>
        val tq"$fix[$functor]" = meaning(c)(expected)
        q"${getRoll(c)}[$functor]($arg)"

      // from fixed to non-fixed: auto-unroll at top level
      case (actual @ FixedPoint(_, _), expected)
          if isScalaSubtype(c)(scalaType(c)(actual.unrollOnce), scalaType(c)(expected)) =>
        q"$arg.unroll"

      // otherwise it's unsound.
      // somehow the first error message gets eaten and we're left with something about Nothing.
      case _ =>
        abortWithError(c)(
          c.enclosingPosition,
          s"cannot coerce $actualType to $expectedType")
    }
  }

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
          sys error "reached 300 assumptions"
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
}
