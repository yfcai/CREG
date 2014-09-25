/** Public interface of nominal functors */

package nominal
package functors

import scala.language.experimental.macros
import scala.annotation.StaticAnnotation

class datatype extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro annotation.datatype.expandData
}

class functor extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro annotation.functor.defaultImpl
}

class functorNoUnroll extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro annotation.functor.implNoUnroll
}

object coerce {
  def apply[S, T](arg: S)(implicit witness: lib.Fix.TypeWitness[T]): T =
    macro lib.Coercion.coerceImpl[S, T]
}
