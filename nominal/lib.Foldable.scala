package nominal
package lib

import language.higherKinds

class Foldable[F[+_]](term: Fix[F])(implicit functor: Traversable.Endofunctor[F]) {
  def fold[T](f: F[T] => T): T = f(functor(term.unroll) map (x => new Foldable(x) fold f))
}
