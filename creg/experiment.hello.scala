package creg
package experiment

import scala.reflect.macros.blackbox.Context
import scala.language.experimental.macros
import scala.annotation.StaticAnnotation

// hello-world annotation macro, taken from somewhere on the internet

object hello {
  def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._
    import Flag._
    val result = {
      annottees.map(_.tree).toList match {
        case q"object $name extends ..$parents { ..$body }" :: Nil =>

          val realParents = tq"A with B with C" match {
            case CompoundTypeTree(Template(parents, selfType, stuff)) =>
              parents
          }

          q"""
            sealed trait A
            sealed trait B
            sealed trait C
            object $name extends ..$realParents {
              def hello: ${typeOf[String]} = "Goodbye cruel world!"
              ..$body
            }
          """
      }
    }
    c.Expr[Any](result)
  }
}

class hello extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro hello.impl
}
