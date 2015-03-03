/** Case study of foldM:
  * abstracting effectful recursive operations
  *
  * Result of coffee room discussion on 27.01.2015.
  * Participants: Jona, Paolo, Tillmann, Cai
  */

import creg.functors._
import creg.lib._
import creg.lib.Applicative._

object FoldM {
  def foldM[A](F: Traversable)(M: Monad)(algM: F.Map[A] => M.Map[A]):
      Fix[F.Map] => M.Map[A] =
    t => M.bind(
      F(t.unroll).traverse(M)( foldM(F)(M)(algM) ),
      algM
    )

  import Scrap.{List, Nil, Cons}
  import Monad.State._

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

  // Given a state monad,
  // produce `uniq` method to replace leaves by unique integers
  trait Uniq {
    implicit def stateMonad[S]: Monad { type Map[+A] = State[S, A] }

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
        case branch @ Branch(_, _) =>
          stateMonad pure (coerce { branch })
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

  // baseline state monad without specifying traversal order
  trait StateMonad[S] extends Monad {
    type Map[+A] = State[S, A]
    def pure[A](x: A): Map[A] = s => (x, s)
    def bind[A, B](m: Map[A], f: A => Map[B]): Map[B] =
      s0 => m(s0) match { case (a, s1) => f(a)(s1) }
    def join[A](x: Map[Map[A]]): Map[A] =
      bind(x, (y: Map[A]) => y)
  }

  // monad for passing state from left to right
  class ForwardStateMonad[S] extends StateMonad[S] {
    def call[A, B](mf: Map[A => B], mx: Map[A]): Map[B] =
      bind(mf, (f: A => B) => bind(mx, (x: A) => pure(f(x))))
  }

  // monad for passing state from right to left
  class BackwardStateMonad[S] extends StateMonad[S] {
    def call[A, B](mf: Map[A => B], mx: Map[A]): Map[B] =
      bind(mx, (x: A) => bind(mf, (f: A => B) => pure(f(x))))
  }

  val forward  = new Uniq { def stateMonad[S] = new ForwardStateMonad  }
  val backward = new Uniq { def stateMonad[S] = new BackwardStateMonad }

  // run Uniq forward and backward

  def run() {
    println("\nRunning forward:\n")
    forward.run()
    println("\nRunning backward:\n")
    backward.run()
  }
  /*
  CONSOLE OUTPUT
  scala> FoldM.run

  Running forward:

  t =
  Roll(Branch(Roll(Branch(Roll(Leaf(hello)),Roll(Leaf(world)))),Roll(Branch(Roll(Leaf(goodbye)),Roll(Branch(Roll(Leaf(cruel)),Roll(Leaf(world))))))))

  uniq(t) =
  Roll(Branch(Roll(Branch(Roll(Leaf(0)),Roll(Leaf(1)))),Roll(Branch(Roll(Leaf(2)),Roll(Branch(Roll(Leaf(3)),Roll(Leaf(4))))))))


  Running backward:

  t =
  Roll(Branch(Roll(Branch(Roll(Leaf(hello)),Roll(Leaf(world)))),Roll(Branch(Roll(Leaf(goodbye)),Roll(Branch(Roll(Leaf(cruel)),Roll(Leaf(world))))))))

  uniq(t) =
  Roll(Branch(Roll(Branch(Roll(Leaf(4)),Roll(Leaf(3)))),Roll(Branch(Roll(Leaf(2)),Roll(Branch(Roll(Leaf(1)),Roll(Leaf(0))))))))
   */
}
