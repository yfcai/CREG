/** Public interface of nominal functors */

package nominal
package functors

import scala.language.experimental.macros
import scala.annotation.StaticAnnotation

class datatype extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro annotation.datatype.vanillaImpl
}

class functor extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro annotation.functor.impl
}
