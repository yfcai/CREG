/** Type coersion:
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

trait Coersion {
  // sadly, making `coerce` implicit does not alleviate the burden of writing it in client code.
  // scalac has problem finding the implicit witness.
  //
  // generating `collection.breakOut`-style code does not work either:
  // `coerceImpl` gets called with `Expected = Nothing`.
  def coerce[S, T](arg: S)(implicit witness: Fix.TypeWitness[T]): T = macro Coersion.coerceImpl[S, T]

  /** macro for testing purpose
    * @param info where the info should be written to
    */
  def coerceContextInfo[S, T]
    (arg: S, info: collection.mutable.Map[String, String])
    (implicit witness: Fix.TypeWitness[T]): T = macro Coersion.infoImpl[S, T]
}

object Coersion extends UniverseConstruction {
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
      c.Tree =
  {
    import c.universe._
    val (actualType, expectedType) = (actualTag.tpe, expectedTag.tpe)

    //DEBUG
    println(s"\ncoercing $arg from $actualType to $expectedType\n")

    q"null.asInstanceOf[$expectedType]" // stub
  }
}
