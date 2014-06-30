import scala.reflect.macros.blackbox.Context

trait AssertEqual {
  def assertEqual(c: Context)(expected: c.Tree, actual: c.Tree): c.Expr[Any] = {
    import c.universe._
    // assert(actual.duplicate != actual) // this is actually true!
    // resorting to string comparison.
    // doesn't seem to have anything better.
    val eRaw = showRaw(expected)
    val aRaw = showRaw(actual)
    if (eRaw != aRaw) {
      System.err println s"\nExpected:\n$eRaw\n\nActual:\n$aRaw\n"
      sys error "got error"
    }
    else
      c.Expr(actual)
  }
}

