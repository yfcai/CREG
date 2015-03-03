/** Standard Scala collections as traversable functors
  *
  * Which package is appropriate for this object?
  */

import creg.lib._

object BuiltInFunctors {
  // Open problem: How to interact with Scala collection library without code duplication?

  object seqF extends Traversable {
    type Map[+X] = Seq[X]
    def traverse[A, B](G: Applicative)(f: A => G.Map[B]): Map[A] => G.Map[Map[B]] = xs => {
      val mbs: Seq[G.Map[B]] = xs map f
      val nil: G.Map[Map[B]] = G pure Seq.empty
      val prepend: G.Map[B => Map[B] => Map[B]] = G pure (x => xs => x +: xs)
      mbs.foldRight(nil) { case (mb, acc) => G.call(G.call(prepend, mb), acc) }
    }
  }

  object elemF extends Traversable {
    type Map[+X] = List[X]
    def traverse[A, B](G: Applicative)(f: A => G.Map[B]): Map[A] => G.Map[Map[B]] = xs => {
      val mbs: List[G.Map[B]] = xs map f
      val nil: G.Map[Map[B]] = G pure Nil
      val prepend: G.Map[B => Map[B] => Map[B]] = G pure (x => xs => x :: xs)
      mbs.foldRight(nil) { case (mb, acc) => G.call(G.call(prepend, mb), acc) }
    }
  }
}
