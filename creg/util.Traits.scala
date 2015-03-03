/** Extract bits and pieces from a trait declaration */

package creg
package util

import scala.reflect.macros.blackbox.Context
import compiler.DatatypeRepresentation.{Many, Name}

trait Traits {
  def nameParamsSupersMembers(c: Context)(tree: c.Tree):
      Option[(c.TypeName, List[c.universe.TypeDef], List[c.Tree], List[c.Tree])] = {
    import c.universe._
    tree match {
      case q"trait $name [..$params] extends ..$supers" =>
        Some((name, params, supers, List.empty))

      case q"trait $name [..$params] extends ..$supers {}" =>
        Some((name, params, supers, List.empty))

      case q"trait $name [..$params] extends ..$supers { ..$members }" =>
        Some((name, params, supers, members))

      case _ =>
        None
    }
  }

  def getSupersOfTrait(c: Context)(tree: c.Tree): List[c.Tree] =
    nameParamsSupersMembers(c)(tree).get._3

  def getNameOfTrait(c: Context)(tree: c.Tree): Option[String] =
    nameParamsSupersMembers(c)(tree) map (_._1.toString)

  def getFullNameOfTrait(c: Context)(tree: c.Tree): Option[String] = {
    import c.universe._

    def mkName(name: c.TypeName, params: List[c.universe.TypeDef]): String = {
      //
      val paramNames = getNamesOfTypeDefs(c)(params)

      if (paramNames.isEmpty)
        name.toString
      else
        s"$name[${paramNames mkString ", "}]"
    }

    nameParamsSupersMembers(c)(tree) map {
      case (name, params, supers, members) =>
        mkName(name, params)
    }
  }

  def getNamesOfTypeDefs(c: Context)(typeDefs: List[c.universe.TypeDef]): Many[Name] = {
    import c.universe._
    typeDefs.map({
      case TypeDef(mods, typeName, typeParams, rhs) =>
        typeName.toString
    })(collection.breakOut)
  }
}
