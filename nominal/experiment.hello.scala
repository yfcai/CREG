package nominal
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
          q"""
            object $name extends ..$parents {
              def hello: ${typeOf[String]} = "Goodbye cruel world!"
              ..$body
            }
          """
      }
    }

    val w = q"class Dummy { def method[A]: List[A] = ??? }; new Dummy"
    val x = c.typecheck(w).tpe.member(TermName("method")).typeSignature.finalResultType
    println
    println(x)
    println
    println(showRaw(x))
    println

    c.Expr[Any](result)
  }
}

class hello extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro hello.impl
}
