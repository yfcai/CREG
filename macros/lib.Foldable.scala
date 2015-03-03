package creg
package lib

import language.higherKinds

// constructor can't be path-dependent. this won't work:
//
//   class Foldable(F: TraversableBounded.Endofunctor)(t: Fix[F.Map]) { ... }
//
// implicit argument gives us at least the option not to write
//
//   new Foldable[TermF](t)(termF)
//
class Foldable[F[+_]](term: Fix[F])(implicit F: Traversable { type Map[+A] = F[A] }) {
  def fold[T](f: F[T] => T): T = {
    object cata extends (Fix[F] => T) {
      def apply(x: Fix[F]): T = f(F(x.unroll) map this)
    }
    cata(term)
  }
}
