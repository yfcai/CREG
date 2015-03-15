/** Experiment to see whether subcategory constraints can be removed
  *
  * Conclusion:
  * Have to give up field names for removal of subcategory constraints.
  * Doing it with standard case classes result in type-unsoundness.
  */

package creg.example

import creg.functors._
import creg.lib._

object NoSubcategoryConstraints {
  @data def Term = Fix(T => TermT {
    Lit(n = Int)
    Var(x = String)
    Abs(x = String, t = T)
    App(s = T, t = T)
  })

  val termT: Traversable4 { type Map[+A, +B, +C, +D] = TermT[A, B, C, D] } =
    new Traversable4 {
      type Map[+A, +B, +C, +D] = TermT[A, B, C, D]

      def traverse[A, B, W, X, C, D, Y, Z]
        (G: Applicative)
        (f: A => G.Map[C], g: B => G.Map[D], h: W => G.Map[Y], k: X => G.Map[Z]):
          Map[A, B, W, X] => G.Map[Map[C, D, Y, Z]] =
      {
        def cast[A](x: A) = x.asInstanceOf[G.Map[Map[C, D, Y, Z]]]

        _ match {
          case n @ Lit(_)    => cast(f(n))
          case x @ Var(_)    => cast(g(x))
          case l @ Abs(_, _) => cast(h(l))
          case a @ App(_, _) => cast(k(a))
        }
      }
    }

  // The type TermT[Int, Int, Int, Int] is uninhabited.
  // However, the following method typechecks and will
  // produce runtime type error.

  def crashMe: TermT[Int, Int, Int, Int] =
    termT(Lit(42)).traverse[
      Int, Int, Int, Int
    ](Applicative.Identity)(
      _ => 42, _ => 42, _ => 42, _ => 42
    )
}
