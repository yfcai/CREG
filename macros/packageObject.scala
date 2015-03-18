// bring Functor, Functor1, Functor2, etc. into top-level scope
// has to be package object; otherwise trait Functor and macro functor
// override each other on a case-insensitive file system.

import creg.lib._

package object creg
    extends fix.Index
    with functor.Index
    with foldable.Index
    with applicative.Index
    with traversable.Index
