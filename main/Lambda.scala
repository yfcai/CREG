import nominal.functors._
import nominal.lib._

/** Lambda calculus example in paper */

object Lambda {
  @data def Term = Fix(term => TermT {
    Lit(n = Int)
    Var(x = String)
    Abs(x = String, t = term)
    App(t1 = term, t2 = term)
  })

  // prepend underscore

  @functor def nameF[s] = Fix(term => TermT {
    Lit(n = Int)
    Var(x = s)
    Abs(x = s, t = term)
    App(t1 = term, t2 = term)
  })

  val rename: Term => Term = nameF.fmap("_" ++ _)

  // count names

  val names: Term => Int = nameF.mapReduce[String, Int](_ => 1)(0, _ + _)

  // count literals

  @functor def litF[n] = Fix(term => TermT {
    Lit(n = n)
    Var(x = String)
    Abs(x = String, t = term)
    App(t1 = term, t2 = term)
  })

  val literals: Term => Int = litF.mapReduce[Int, Int](_ => 1)(0, _ + _)
}
