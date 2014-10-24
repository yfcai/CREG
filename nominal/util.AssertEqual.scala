package nominal
package util

import scala.reflect.macros.blackbox.Context

import compiler.DatatypeRepresentation.Many

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
      System.err println s"\nExpected:\n$expected\n\nActual:\n$actual\n\nExpected:\n$eRaw\n\nActual:\n$aRaw\n"
      throw new java.lang.AssertionError
    }
    else
      c.Expr(actual)
  }

  def assertHasPrefixBlock(c: Context)(expected: c.Tree, actual: Many[c.Tree]): c.Expr[Any] = {
    import c.universe._
    if (actual.size == 1)
      assertHasPrefix(c)(q"{$expected}", q"{${actual.head}}")
    else
      assertHasPrefix(c)(expected, q"..$actual")
  }

  def assertHasPrefix(c: Context)(expected: c.Tree, actual: c.Tree): c.Expr[Any] = {
    import c.universe._
    // assert(actual.duplicate != actual) // this is actually true!
    // resorting to string comparison.
    // doesn't seem to have anything better.
    val expectedList = expected match { case Block(list, _) => list }
    val actualList = actual match { case Block(list, _) => list }
    val eRaw = showRaw(expectedList)
    val aRaw = showRaw(actualList)
    if (aRaw.length < eRaw.length) {
      System.err println s"actual is shorter than expected\n" +
        s"got actual:\n$actual\n\nand expected:\n$expected\n"
      throw new java.lang.AssertionError
    }
    else {
      // get rid of last char (comma vs. closing bracket)
      val aref = aRaw.substring(0, eRaw.length - 1)
      val eref = eRaw.substring(0, eRaw.length - 1)
      if (eref != aref) {
        System.err println s"\nExpected:\n$expected\n\nActual:\n$actual\n\nExpected:\n$eref\n\nActual:\n$aref\n"
        throw new java.lang.AssertionError
      }
      else
        c.Expr(actual)
    }
  }

  def assertEqualObjects(expected: Any, actual: Any): Unit = {
    if (expected != actual) {
      System.err println s"\nExpected:\n$expected\n\nActual:\n$actual\n"
      throw new java.lang.AssertionError
    }
  }
}

