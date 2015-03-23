package creg
package lib
package foldable

import language.higherKinds

trait Index {
  type Foldable[F[+_]] = foldable.Foldable[F]
}

// constructor can't be path-dependent. this won't work:
//
//   class Foldable(F: TraversableBounded.Endofunctor)(t: fix.Fix[F.Map]) { ... }
//
// implicit argument gives us at least the option not to write
//
//   new Foldable[TermF](t)(termF)
//
class Foldable[F[+_]](term: fix.Fix[F])(implicit F: traversable.Traversable { type Map[+A] = F[A] }) {
  def fold[T](f: F[T] => T): T = {
    object cata extends (fix.Fix[F] => T) {
      def apply(x: fix.Fix[F]): T = f(F(x.unroll) map this)
    }
    cata(term)
  }
}
