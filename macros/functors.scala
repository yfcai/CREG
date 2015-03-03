/** Public interface of creg functors */

package creg
package functors

import scala.language.experimental.macros
import scala.annotation.StaticAnnotation

class struct extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro annotation.struct.impl
}

class data extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro annotation.data.expandData
}

class functor extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro annotation.functor.impl
}

class synonym extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro annotation.synonym.impl
}

object coerce {
  def apply[S, T](arg: S)(implicit tagT: lib.Fix.TypeWitness[T]): T =
    macro lib.Coercion.coerceImpl[S, T]
}