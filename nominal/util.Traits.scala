/** Extract bits and pieces from a trait declaration */

package nominal
package util

import scala.reflect.macros.blackbox.Context
import compiler.DatatypeRepresentation.Many

trait Traits {
  def getNameParamsSupers(c: Context)(tree: c.Tree):
      Option[(c.TypeName, List[c.universe.TypeDef], List[c.Tree])] = {
    import c.universe._
    tree match {
      case q"trait $name [..$params] extends ..$supers" => Some((name, params, supers))
      case q"trait $name [..$params] extends ..$supers {}" => Some((name, params, supers))
      case q"trait $name [..$params] extends ..$supers { ..$body }" => Some((name, params, supers))
      case _ => None
    }
  }

  def getSupersOfTrait(c: Context)(tree: c.Tree): List[c.Tree] =
    getNameParamsSupers(c)(tree).get._3

  def getNameOfTrait(c: Context)(tree: c.Tree): Option[String] =
    getNameParamsSupers(c)(tree) map (_._1.toString)

  def getFullNameOfTrait(c: Context)(tree: c.Tree): Option[String] = {
    import c.universe._

    def mkName(name: c.TypeName, params: List[c.universe.TypeDef]): String = {
      //
      val paramNames = params map {
        case TypeDef(modifiers, typeName, typeParams, rhs) =>
          typeName.toString
      }

      if (paramNames.isEmpty)
        name.toString
      else
        s"$name[${paramNames mkString ", "}]"
    }

    getNameParamsSupers(c)(tree) map {
      case (name, params, supers) =>
        mkName(name, params)
    }
  }
}
