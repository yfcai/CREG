/** The KIRV framework: Constant, Identity, Record, Variant */

package nominal
package compiler

import scala.reflect.macros.blackbox.Context

import Functor._

trait KIRV extends util.Traverse with util.AbortWithError {
  // specification of whether something is a projection or not
  abstract class KIRV[Tree] { def get: Tree }
  // projections choose an argument as the result
  case class Project[Tree](i: Int, n: Int, get: Tree) extends KIRV[Tree]
  // nestings put types under a constant heading
  case class Nest[Tree](get: Tree) extends KIRV[Tree]

  /** n-nary traversable functor mapping everything to tau */
  def constF(c: Context, n: Int)(tau: Code): c.Tree = {
    import c.universe._
    newTraversableEndofunctor(c, n)(_ => tq"${TypeName(tau)}") {
      case (applicative, fs, as, bs) =>
        etaExpand(c)(q"$applicative.pure")
    }
  }

  def constK(c: Context, n: Int)(tau: Code): KIRV[c.Tree] = Nest(constF(c, n)(tau))

  /** n-nary traversable functor returning its i-th argument */
  def projectF(c: Context, i: Int, n: Int): c.Tree = {
    import c.universe._
    newTraversableEndofunctor(c, n)(params => tq"${params(i)}") {
      case (applicative, fs, as, bs) =>
        q"${fs(i)}"
    }
  }

  def projectK(c: Context, i: Int, n: Int): KIRV[c.Tree] = Project(i, n, projectF(c, i, n))

  /** composing functors in a record, each functor on a field */
  def compositeF(c: Context, n: Int)(record: c.Tree, fieldFs: Many[c.Tree]): c.Tree = {
    import c.universe._
    val names = fieldFs map (_ => TermName(c freshName "F"))
    val recordName = TermName(c freshName "rcd")
    val rcdDef = q"val $recordName = $record"
    val valDefs = ((names zip fieldFs) map { case (name, functor) => q"val $name = $functor" })

    newTraversableEndofunctorWith(c, n)(
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

  /** composing functors with projections in mind */
  def compositeK(c: Context, n: Int)(parent: c.Tree, children: Many[KIRV[c.Tree]]): KIRV[c.Tree] = {
    import c.universe._

    val parentName = TermName(c freshName "parent")
    val parentDef  = q"val $parentName = $parent"

    val childNames = children map (_ => TermName(c freshName "child"))
    val childDefs  = (childNames zip children) map { case (name, child) => q"val $name = ${child.get}" }

    // figure out categorical bounds
    val cats = multiplexSubcatBounds(c, n)(parentName, children)

    ??? // TODO
  }

  def multiplexSubcatBounds(c: Context, n: Int)(parentName: c.TermName, children: Many[KIRV[c.Tree]]): Many[c.Tree] =
    (0 until n) map {
      case i =>
        import c.universe._

        // type is `Set` so that duplicate bounds are removed automatically
        val bounds: Set[Int] = children.zipWithIndex.flatMap({
          case (Project(j, n, _), k) if i == j => Some(k)
          case _                          => None
        })(collection.breakOut)

        // inconsistent bounds (a variant never have repeated records; records w/ distinct names are distinct)
        if (bounds.size > 1)
          abortWithError(c)(EmptyTree.pos,
            s"conflicting subcategorical bounds:\n\n${bounds mkString "\n"}\n")

        // no bound
        else if (bounds.size < 1)
          getAnyType(c)

        // one bound; time to multiplex
        else
          getFunctorCat(c, bounds.head, n)(parentName)
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
    c.Expr(projectF(c, c eval i, c eval n))

  def composite(record: Any, n: Int)(fields: Any*): Any = macro compositeImpl
  def compositeImpl(c: WhiteContext)(record: c.Tree, n: c.Tree)(fields: c.Tree*): c.Tree =
    compositeF(c, c eval c.Expr[Int](n))(record, fields)
}
