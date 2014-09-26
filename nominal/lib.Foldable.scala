package nominal
package lib

import language.higherKinds

class Foldable[F[+_]](F: Traversable.EndofunctorOf[F], term: Fix[F]) {
  def fold[T](f: F.Map[T] => T): T = {
    object cata extends (Fix[F] => T) {
      def apply(x: Fix[F]): T = f(F(x.unroll) map this)
    }
    cata(term)
  }
}
