// Strange traverse in §5.5 of Gibbons & Oliveira's "essence of
// the iterator pattern"
//
// StrangeTraverse.traverse is strange: it duplicates elements.
// It violates the "linearity law" in Jaskelioff & O'Conner's
// "representation of higher order functionals". Thus this
// traverse is ill-formed and does not correspond to any finitary
// container.
//
//

package creg.example

import creg._
import Monad.State._

object StrangeTraverse extends Traversable {
  type Map[+A] = A

  def traverse[A, B](G: Applicative)(f: A => G.Map[B]): A => G.Map[B] =
    x => {
      import G._
      call(call(
        pure[B => B => B](x => y => x),
        f(x)),
        f(x))
    }

  type State[S, A] = S => (A, S)
  type State2[S, A] = State[S, State[S, A]]

  def state2[S]: Applicative { type Map[+A] = State2[S, A] } =
    stateMonad[S] compose stateMonad[S]

  def f: Int => State[List[Int], Int] = x => xs => (x, xs :+ x)

  def runState2(m: State2[List[Int], Int]): (List[Int], List[Int]) =
    m(Nil) match { case (n, s) => (s, n(Nil)._2) }

  def lhs: State2[List[Int], Int] =
    apply(0).traverse(state2[List[Int]])(
      x => stateMonad[List[Int]].fmap(f)(f(x))
    )

  def rhs: State2[List[Int], Int] =
    stateMonad[List[Int]].fmap[Int, State[List[Int], Int]](
      f
    )(apply(0).traverse(stateMonad[List[Int]])(f))

  def run(): Unit = {
    println( "Testing linearity law:")
    println( "For all f : a -> F b and g : b -> G c,")
    println( "  trav (F g . f) == F (trav g) . trav f\n")
    println( "Choose F = G = stateMonad[List[Int]],")
    println( "       f = g = x => xs => (x, xs :+ x)\n")
    println( "Choose the traversable functor to be identity with")
    println( "       trav f x = const <$> f x <*> f x\n")
    val l = runState2(lhs)
    val r = runState2(rhs)
    println(s"Then states of LHS are: $l and")
    println(s"     states of RHS are: $r.\n")
    if (l != r)
      println("Linearity law is broken.")
    else
      println("Linearity law continues to hold.")
  }
}
