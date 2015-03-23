import creg.lib._

/** Macros to generate regular functors; interfaces for
  * applicative, monadic and traversable functors.
  *
  * ==Usage Example==
  *
  * The macro [[data @data]] generates datatypes.
  * The syntax is similar to datatype declarations in Haskell
  * with record constructors and explicit recursion.
  * {{{
  * @data def List[A] =
  *   Fix(list =>
  *     ListT {
  *       Nil
  *       Cons(head = A, tail = list)
  *     }
  *   )
  *
  * // In Haskell:
  * //
  * // data List a = Nil
  * //             | Cons { head :: a, tail :: List a }
  * }}}
  *
  * The macro [[coerce]] is used to define datatype literals.
  * Type annotation is mandatory for the result type of [[coerce]].
  * {{{
  * val xs: List[Int] = coerce { Cons(1, Cons(2, Cons(3, Cons(4, Nil)))) }
  * }}}
  *
  * The macro [[functor @functor]] generates regular functors
  * with the interface of
  * [[creg.lib.traversable.Traversable Traversable]] functors.
  * The syntax is identical to the declaration of datatypes.
  * {{{
  * @functor def elemF[A] =
  *   Fix(list => ListT { Nil ; Cons(head = A, tail = list) })
  *
  * // In Haskell:
  * //
  * // instance Functor List where
  * //   fmap f Nil         = Nil
  * //   fmap f (Cons x xs) = Cons (f x) (fmap f xs)
  *
  * // instance Traversable List where
  * //   traverse f Nil         = pure Nil
  * //   traverse f (Cons x xs) = Cons <$> f x <*> traverse f xs
  * }}}
  *
  * Functors can be applied to datatype values to view them
  * as containers.
  * {{{
  * elemF(xs) map (_ + 1) // the list 2, 3, 4, 5
  *
  * elemF(xs) reduce (0, _ + _) // 10
  * }}}
  */
package object creg
    extends applicative.Index
    with fix.Index
    with foldable.Index
    with functor.Index
    with monad.Index
    with traversable.Index
