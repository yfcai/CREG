/** The KIRV framework: Constant, Identity, Record, Variant */

package nominal
package compiler

import scala.reflect.macros.blackbox.Context

import Functor._

trait KIRV extends util.Traverse with util.AbortWithError {
  // specification of whether something is a projection or not
  abstract class KIRV[Tree] { def get: Tree }
  // projections choose an argument as the result
  case class Proj[Tree](i: Int, n: Int, get: Tree) extends KIRV[Tree]
  // nestings put types under a constant heading
  case class Nest[Tree](get: Tree) extends KIRV[Tree]

  /** n-nary traversable functor mapping everything to tau */
  def constK(c: Context, n: Int)(tau: Code): KIRV[c.Tree] = Nest {
    import c.universe._
    newTraversableEndofunctor(c, n)(_ => tq"${TypeName(tau)}") {
      case (applicative, fs, as, bs) =>
        etaExpand(c)(q"$applicative.pure")
    }
  }

  /** n-nary traversable functor returning its i-th argument */
  def projectK(c: Context, i: Int, n: Int): KIRV[c.Tree] = Proj(i, n, {
    import c.universe._
    newTraversableEndofunctor(c, n)(params => tq"${params(i)}") {
      case (applicative, fs, as, bs) =>
        q"${fs(i)}"
    }
  })

  def multiplexSubcatBounds(c: Context, n: Int)(parentName: c.TermName, children: Many[KIRV[c.Tree]]):
      Many[c.Tree] =
    (0 until n) map {
      case i =>
        import c.universe._

        // type is `Set` so that duplicate bounds are removed automatically
        val bounds: Set[Int] = children.zipWithIndex.flatMap({
          case (Proj(j, n, _), k) if i == j => Some(k)
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

  /** composing functors in a record, each functor on a field */
  def compositeK(c: Context, n: Int)(parent: c.Tree, children: Many[KIRV[c.Tree]]): KIRV[c.Tree] = {
    import c.universe._

    val parentName = TermName(c freshName "parent")
    val parentDef  = q"val $parentName = $parent"

    val childNames = children map (_ => TermName(c freshName "child"))
    val childDefs  = (childNames zip children) map { case (name, child) => q"val $name = ${child.get}" }

    // subcategory bounds
    val cats = multiplexSubcatBounds(c, n)(parentName, children)

    // all the val defs
    val valDefs = parentDef +: childDefs

    // RHS of the mapping on objects
    val mapping: Many[TypeName] => c.Tree =
      params => composeFunctorMaps(c)(parentName, childNames, params)

    Nest(newBoundedTraversableWith(c, n)(cats, parentDef +: childDefs, mapping) {
      case (applicative, fs, as, bs) =>
        val travParams =
          ( childNames.map(f => tq"${getFunctorMapOnObjects(c)(f)}[..$as]") ++
            childNames.map(f => tq"${getFunctorMapOnObjects(c)(f)}[..$bs]") )
        val traversals = childNames map (f => q"$f.traverse($applicative)(..$fs)")
        q"$parentName.traverse[..$travParams]($applicative)(..$traversals)"
    })
  }

  def fixK(c: Context, n: Int)(functorKIRV: KIRV[c.Tree]): KIRV[c.Tree] = {
    import c.universe._

    val functorObj = functorKIRV.get
    val functor    = TermName(c freshName "fun")
    val functorDef = q"val $functor = $functorObj"

    val m = n + 1

    // POSSIBLE FUTURE VERIFICATION FOR ERROR MESSAGE IMPROVEMENT
    // 1. assert `functor` is an m-nary functor
    // 2. assert `functor.Cat1` is equal to `Any`

    // subcategory bounds are inherited from `functor`
    // `getFunctorCat` creates functor.Cat2 when i == 1,
    // thus we skip the bound `functor.Cat1`.
    val cats: Many[c.Tree] = (1 to n).map { i => getFunctorCat(c, i, m)(functor) }

    // create mapping on objects
    val lambda = TypeName(c freshName "lambda")
    val patternF: Many[TypeName] => c.Tree = params => {
      val x = TypeName(c freshName "x")
      val xdef = mkCovariantTypeDef(c)(x)
      val rhs = tq"${getFunctorMapOnObjects(c)(functor)}[..${x +: params}]"
      tq"({ type $lambda[$xdef] = $rhs })#$lambda"
    }
    val mapping: Many[TypeName] => c.Tree =
      params => tq"${getFix(c)}[${patternF(params)}]"

    Nest(newBoundedTraversableWith(c, n)(cats, Many(functorDef), mapping) {
      case (applicative, fs, as, bs) =>
        val x        = TermName(c freshName "x")
        val loop     = TermName(c freshName "loop")
        val mMap     = getMapOnObjects(c)
        val gMap     = getFunctorMapOnObjects(c)(applicative)
        val MA       = tq"$mMap[..$as]"
        val MB       = tq"$mMap[..$bs]"
        val GMB      = tq"$gMap[$MB]"
        val mbs      = MB +: bs.map(tau => tq"$tau")
        val unrolled = tq"${getFunctorMapOnObjects(c)(functor)}[..$mbs]"
        val pfbs     = patternF(bs)
        val rolled   = tq"${getFix(c)}[$pfbs]"
        val pureBody = etaExpand(c)(q"${getRoll(c)}[$pfbs]")
        val pureRoll = q"${getPure(c)(applicative)}[$unrolled => $rolled]($pureBody)"
        val args     = q"this" +: fs.map(f => q"$f")
        val body     = q"$functor.traverse($applicative)(..$args)($x.unroll)"
        val loopBody = mkCallTree(c)(applicative, Many(pureRoll, body))
        q"""
          object $loop extends ($MA => $GMB) {
            def apply($x : $MA): $GMB = $loopBody
          }

          $loop
        """
    })
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
    val functor = constK(c, c eval n)(name).get
    c.Expr(q"{ type $typeName = $tpe ; $functor }")
  }

  def proj(i: Int, n: Int): Any = macro projImpl
  def projImpl(c: WhiteContext)(i: c.Expr[Int], n: c.Expr[Int]): c.Expr[Any] =
    c.Expr(projectK(c, c eval i, c eval n).get)

  def composite(record: Any, n: Int)(fields: Any*)(areProj: Int*): Any = macro compositeImpl
  def compositeImpl(c: WhiteContext)(record: c.Tree, n: c.Tree)(fields: c.Tree*)(areProj: c.Tree*):
      c.Tree = {
    val nVal = c eval c.Expr[Int](n)
    val areProjEvaluated = areProj map (m => c eval c.Expr[Int](m))
    val children = fields.zip(areProjEvaluated) map {
      case (field, i) if i >= 0 & i < nVal =>
        Proj(i, nVal, field)
      case (field, i) =>
        Nest(field)
    }
    compositeK(c, nVal)(record, children).get
  }

  def fix(functor: Any, n: Int): Any = macro fixImpl
  def fixImpl(c: WhiteContext)(functor: c.Tree, n: c.Tree): c.Tree =
    fixK(c, c eval c.Expr[Int](n))(Nest(functor)).get
}
