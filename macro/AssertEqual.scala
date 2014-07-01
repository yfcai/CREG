import scala.reflect.macros.blackbox.Context

import DatatypeRepresentation.Many

trait AssertEqual {
  def assertEqualBlock(c: Context)(expected: c.Tree, actual: Many[c.Tree]): c.Expr[Any] = {
    import c.universe._
    if (actual.size == 1)
      assertEqual(c)(expected, actual.head)
    else
      assertEqual(c)(expected, q"..$actual")
  }

  def assertEqual(c: Context)(expected: c.Tree, actual: c.Tree): c.Expr[Any] = {
    import c.universe._
    // assert(actual.duplicate != actual) // this is actually true!
    // resorting to string comparison.
    // doesn't seem to have anything better.
    val eRaw = showRaw(expected)
    val aRaw = showRaw(actual)
    if (eRaw != aRaw) {
      System.err println s"\nExpected:\n$expected\nActual:\n$actual\n\nExpected:\n$eRaw\n\nActual:\n$aRaw\n"
      sys error "got error"
    }
    else
      c.Expr(actual)
  }
}

