// bring Functor, Functor1, Functor2, etc. into top-level scope
// has to be package object; otherwise trait Functor and macro functor
// override each other on a case-insensitive file system.
package object creg extends functors.Functors
