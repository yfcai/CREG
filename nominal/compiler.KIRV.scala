/** The KIRV framework: Constant, Identity, Record, Variant */

package nominal
package compiler

import scala.reflect.macros.blackbox.Context

import Functor._

trait KIRV extends util.Traverse {
  /** n-nary traversable functor mapping everything to tau */
  def constF(c: Context, n: Int)(tau: Code): c.Tree = {
    import c.universe._
    newTraversableN(c, n)(_ => tq"${TypeName(tau)}") {
      case (applicative, fs, as, bs) =>
        etaExpand(c)(q"$applicative.pure")
    }
  }

  /** n-nary traversable functor returning its i-th argument */
  def projectF(c: Context, n: Int)(i: Int): c.Tree = {
    import c.universe._
    newTraversableN(c, n)(params => tq"${params(i)}") {
      case (applicative, fs, as, bs) =>
        q"${fs(i)}"
    }
  }

  /** composing functors in a record, each functor on a field */
  def compositeF(c: Context, n: Int)(record: c.Tree, fieldFs: Many[c.Tree]): c.Tree = {
    import c.universe._
    val names = fieldFs map (_ => TermName(c freshName "F"))
    val recordName = TermName(c freshName "rcd")
    val rcdDef = q"val $recordName = $record"
    val valDefs = ((names zip fieldFs) map { case (name, functor) => q"val $name = $functor" })
    newTraversableWith(c, n)(
      rcdDef +: valDefs,
      as => composeFunctorMaps(c)(recordName, names, as)
    ) {
      case (applicative, fs, as, bs) =>
        val travParams =
          ( names.map(f => tq"${getFunctorMapOnObjects(c)(f)}[..$as]") ++
            names.map(f => tq"${getFunctorMapOnObjects(c)(f)}[..$bs]") )
        val traversals = names map (f => q"$f.traverse($applicative)(..$fs)")
        q"$recordName.traverse[..$travParams]($applicative)(..$traversals)"
    }
  }
}

object KIRV extends KIRV {
  // macros for tests
  import scala.language.experimental.macros
  import scala.annotation.StaticAnnotation
  import scala.reflect.macros.whitebox.{ Context => WhiteContext }

  def const[A](n: Int): Any = macro constImpl[A]
  def constImpl[A: c.WeakTypeTag](c: WhiteContext)(n: c.Expr[Int]): c.Expr[Any] = {
    import c.universe._
    val tpe = implicitly[WeakTypeTag[A]].tpe
    val name = c.freshName
    val typeName = TypeName(name)
    val functor = constF(c, c eval n)(name)
    c.Expr(q"{ type $typeName = $tpe ; $functor }")
  }

  def proj(i: Int, n: Int): Any = macro projImpl
  def projImpl(c: WhiteContext)(i: c.Expr[Int], n: c.Expr[Int]): c.Expr[Any] =
    c.Expr(projectF(c, c eval n)(c eval i))

  def composite(record: Any, n: Int)(fields: Any*): Any = macro compositeImpl
  def compositeImpl(c: WhiteContext)(record: c.Tree, n: c.Tree)(fields: c.Tree*): c.Tree =
    compositeF(c, c eval c.Expr[Int](n))(record, fields)
}
