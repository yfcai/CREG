/** Case study of foldM:
  * abstracting effectful recursive operations
  *
  * Result of coffee room discussion on 27.01.2015.
  * Participants: Jona, Paolo, Tillmann, Cai
  */

import nominal.functors._
import nominal.lib._
import nominal.lib.Applicative._
import nominal.lib.Traversable.Endofunctor

object FoldM {
  def foldM[A](F: Endofunctor)(M: Monad)(algM: F.Map[A] => M.Map[A]):
      Fix[F.Map] => M.Map[A] =
    t => M.bind(
      F(t.unroll).traverse(M)( foldM(F)(M)(algM) ),
      algM
    )

  import Scrap.{List, Nil, Cons}
  import Compos2._

  @data def Tree[A] = Fix(tree => TreeT {
    Leaf(get = A)
    Branch(left = tree, right = tree)
  })

  def treeF[A] = {
    @functor def fun[T] = TreeT {
      Leaf(get = A)
      Branch(left = T, right = T)
    }
    fun
  }

  type State[S, +A] = S => (A, S)

  import Compos2._ // for state monad methods

  def uniqM[A]: Tree[A] => State[Int, Tree[Int]] =
    foldM[Tree[Int]](treeF[A])(stateMonad[Int]) {
      case Leaf(x) =>
        for {
          n <- readState
          _ <- writeState(n + 1)
        }
        yield coerce { Leaf(n) }

      // not `case t => pure(coerce(t))` because Scala lacks
      // type refinement/flow-sensitive typing
      case Branch(left, right) =>
        stateMonad pure (coerce { Branch(left, right) })
    }

  // replace leaves by 0, 1, 2, ...
  def uniq[A]: Tree[A] => Tree[Int] =
    t => evalState(uniqM(t), 0)

  def run() {
    val t: Tree[String] = coerce {
      Branch(
        Branch(
          Leaf("hello"),
          Leaf("world")),
        Branch(
          Leaf("goodbye"),
          Branch(
            Leaf("cruel"),
            Leaf("world"))))
    }

    println(s"t =\n$t\n")

    val u = uniq(t)

    println(s"uniq(t) =\n$u\n")
  }
}
