/** Public interface of nominal functors */

package nominal
package functors

import scala.language.experimental.macros
import scala.annotation.StaticAnnotation

// TODO: rename this to @data
class data extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro annotation.data.expandData
}

class functor extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro annotation.functor.impl
}

object coerce {
  def apply[S, T](arg: S)(implicit witness: lib.Fix.TypeWitness[T]): T =
    macro lib.Coercion.coerceImpl[S, T]
}
