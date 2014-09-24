package nominal
package lib

import language.higherKinds

class Foldable[F[+_]](term: Fix[F], F: Traversable { type Map[+X] = F[X] }) {
  def fold[T](f: F.Map[T] => T): T = {
    object cata extends (Fix[F] => T) {
      def apply(x: Fix[F]): T = f(F(x.unroll) map this)
    }
    cata(term)
  }
}
