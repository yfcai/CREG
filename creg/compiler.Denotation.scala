/** The denotational semantics of functor representations
  *
  *
  * decl := params => body
  * 
  * params := typevar
  *         | (typevar, typevar, ..., typevar)
  * 
  * body := typevar
  *       | Fix(typevar => body)
  *       | scala-functor(body, body, ..., body)
  *       | scala-constant
  *
  *
  * ⟦ params => body ⟧ = ⟦ body ⟧ params
  * 
  * ⟦ typevar ⟧ params = projection-functor(i, n)
  *   where
  *     i = lookup typevar params
  *     n = length params
  * 
  * ⟦ Fix(x => body) ⟧ params = λ ..args. μ xArg. (⟦ body ⟧ (x +: params) ..(xArg +: args))
  *   where
  *     assert(length args == length params)
  * 
  * ⟦ scala-functor(bodies: _*) ⟧ params =
  *   λ args. scala-functor(bodies map (body => ⟦ body ⟧ params args))
  *     where
  *       assert(length args == length params)
  * 
  * ⟦ scala-constant ⟧ params = n-nary-constant-functor n scala-constant
  *   where
  *     n = length params
  */

package creg
package compiler

import scala.reflect.macros.blackbox.Context
import DatatypeRepresentation._

private[creg]
trait Denotation extends UniverseConstruction with util.Traverse {
  private[this] type Env = Many[Name]

  /* @param bounded if true , always generate TraversableBoundedN
   *                if false, always generate TraversableN <: Functor
   */
  def evalFunctor(c: Context)(functor: DataConstructor, bounded: Boolean):
      c.Tree =
    evalData(c)(functor.body, bounded)(functor.params.map(_.name))

  def evalData(c: Context)(data: Datatype, bounded: Boolean):
      Env => c.Tree = data match {
    case typeVar: TypeVar =>
      evalTypeVar(c)(typeVar, bounded)

    case typeConst: TypeConst =>
      evalTypeConst(c)(typeConst, bounded)

    case fixedpoint: FixedPoint =>
      evalFixedPoint(c)(fixedpoint, bounded)

    case record: Record =>
      evalRecord(c)(record, bounded)

    case variant: Variant =>
      evalVariant(c)(variant, bounded)

    case functorApp: FunctorApplication =>
      evalFunctorApplication(c)(functorApp, bounded)

    case LetBinding(lhs, rhs) =>
      evalData(c)(rhs, bounded)
  }

  def evalTypeVar(c: Context)(typeVar: TypeVar, bounded: Boolean):
      Env => c.Tree = env => {
    import c.universe._
    val x = typeVar.name
    val n = env.length
    val i = env indexOf x
    require(i >= 0)
    evalProj(c, i, n)
  }

  def evalTypeConst(c: Context)(typeConst: TypeConst, bounded: Boolean):
      Env => c.Tree = env => {
    import c.universe._
    val x = typeConst.code
    val n = env.length
    val i = env indexOf x
    require(i < 0)
    evalConst(c, x, n)
  }

  /** n-nary traversable functor mapping everything to tau */
  def evalConst(c: Context, x: Name, n: Int): c.Tree = {
    import c.universe._
    newTraversableEndofunctor(c, n)(_ => tq"${TypeName(x)}") {
      case (applicative, fs, as, bs) =>
        etaExpand(c)(q"$applicative.pure")
    }
  }

  /** n-nary traversable functor returning its i-th argument */
  def evalProj(c: Context, i: Int, n: Int): c.Tree = {
    import c.universe._
    newTraversableEndofunctor(c, n)(params => tq"${params(i)}") {
      case (applicative, fs, as, bs) =>
        q"${fs(i)}"
    }
  }

  /** applying an unknown functor */
  def evalFunctorApplication(c: Context)(
    functorApp: FunctorApplication, bounded: Boolean):
      Env => c.Tree = {
    import c.universe._

    val functorCode = c parse functorApp.functor.code
    val n = functorApp.functorArity
    evalComposite(c)("functor", functorApp, functorCode, bounded)

    /* Use implicits so as to interoperate with built-in functors
     * (Seems unnecessary)

    // `functor` is not a type; it is a type constructor
    // here betting on Scalac's parser not doing enough type checking
    // to figure that out & throw tantrums
    val functor = meaning(c)(functorApp.functor)
    val n = functorApp.functorArity
    val functorCode = getImplicitly(c)(tq"${getTraversableEndofunctorOf(c, n)}[$functor]")
    evalComposite(c)("functor", functorApp, functorCode)
     */
  }

  def evalRecord(c: Context)(record: Record, bounded: Boolean):
      Env => c.Tree = {
    import c.universe._
    evalComposite(c)(record.name, record, q"${TermName(record.name)}", bounded)
  }

  def evalVariant(c: Context)(variant: Variant, bounded: Boolean):
      Env => c.Tree = {
    import c.universe._
    evalComposite(c)(variant.name, variant, q"${TermName(variant.name)}", bounded)
  }

  def evalComposite(c: Context)(
    parentName: Name, parentData: Datatype, parentCode: c.Tree,
    bounded: Boolean):
      Env => c.Tree = env => {
    import c.universe._

    val parent = TermName(c freshName parentName)

    // help Scalac typecheck things
    val parentSelfType = parentCode match {
      case ident @ Ident(_) => tq"$ident.type"
      case _ => TypeTree()
    }

    val parentDef = q"val $parent: $parentSelfType = $parentCode"

    val namedSubfunctors = parentData.children.toSeq.zipWithIndex.map {
      case (data, i) =>
        (TermName(c freshName s"_$i"), evalData(c)(data, bounded)(env))
    }

    val subfunctorDefs = namedSubfunctors.map {
      case (x, xdef) => q"val $x = $xdef"
    }

    val dfns = parentDef +: subfunctorDefs

    val typeMap = (as: Many[TypeName]) => {
      meaning(c)(parentData rename {
        Map((env zip (as.map(_.toString))): _*)
      })
    }

    val body:
        (TermName, Many[TermName], Many[TypeName], Many[TypeName]) => c.Tree =
    {
      case (applicative, fs, as, bs) =>
        val names = namedSubfunctors.map(_._1)
        val travParams =
          ( names.map(f => tq"${getFunctorMapOnObjects(c)(f)}[..$as]") ++
            names.map(f => tq"${getFunctorMapOnObjects(c)(f)}[..$bs]") )
        val traversals = names map (f => q"$f.traverse($applicative)(..$fs)")
        q"$parent.traverse[..$travParams]($applicative)(..$traversals)"
    }

    if (bounded) {
      // construct dummy functor application as far as bounds are concerned
      val bounds = getBounds(c)(parentData, env)
      val cats = boundsToCats(c)(bounds)
      newTraversableBoundedWith(c, env.length)(cats, dfns, typeMap)(body)
    }
    else
      newTraversableEndofunctorWith(c, env.length)(dfns, typeMap)(body)

  }

  def evalFixedPoint(c: Context)(fixedpoint: FixedPoint, bounded: Boolean):
      Env => c.Tree = env => {
    import c.universe._
    val FixedPoint(x, body) = fixedpoint
    val bodyEnv  = x +: env
    val bodyCode = evalData(c)(body, bounded)(bodyEnv)
    val bodyName = TermName(c freshName "body")
    val bodyDef  = q"val $bodyName = $bodyCode"

    // create mapping on objects
    val lambda = TypeName(c freshName "lambda")
    val patternF: Many[TypeName] => c.Tree = params => {
      val x = TypeName(c freshName "x")
      val xdef = mkCovariantTypeDef(c)(x)
      val mangle = Map(bodyEnv zip ((x +: params).map(_.toString)): _*)
      val rhs = meaning(c)(body rename mangle)
      tq"({ type $lambda[$xdef] = $rhs })#$lambda"
    }

    val dfns = Many(bodyDef)

    val mapping: Many[TypeName] => c.Tree =
      params => tq"${getFix(c)}[${patternF(params)}]"

    val bodyImpl:
        (TermName, Many[TermName], Many[TypeName], Many[TypeName]) => c.Tree =
    {
      case (applicative, fs, as, bs) =>
        val x        = TermName(c freshName "x")
        val loop     = TermName(c freshName "loop")
        val mMap     = getMapOnObjects(c)
        val gMap     = getFunctorMapOnObjects(c)(applicative)
        val MA       = tq"$mMap[..$as]"
        val MB       = tq"$mMap[..$bs]"
        val GMB      = tq"$gMap[$MB]"
        val mbs      = MB +: bs.map(tau => tq"$tau")
        val unrolled = tq"${getFunctorMapOnObjects(c)(bodyName)}[..$mbs]"
        val pfbs     = patternF(bs)
        val rolled   = tq"${getFix(c)}[$pfbs]"
        val pureBody = etaExpand(c)(q"${getRoll(c)}[$pfbs]")
        val pureRoll = q"${getPure(c)(applicative)}[$unrolled => $rolled]($pureBody)"
        val args     = q"this" +: fs.map(f => q"$f")
        val body     = q"$bodyName.traverse($applicative)(..$args)($x.unroll)"
        val loopBody = mkCallTree(c)(applicative, Many(pureRoll, body))
        q"""
          object $loop extends ($MA => $GMB) {
            def apply($x : $MA): $GMB = $loopBody
          }

          $loop
        """
    }

    if (bounded) {
      val bodyBds  = getBounds(c)(fixedpoint, env)
      val cats = boundsToCats(c)(bodyBds)
      newTraversableBoundedWith(c, env.length)(cats, dfns, mapping)(bodyImpl)
    }
    else
      newTraversableEndofunctorWith(c, env.length)(dfns, mapping)(bodyImpl)
  }

  def boundsToCats(c: Context)(bounds: Many[Option[c.Tree]]): Many[c.Tree] =
    bounds map (_.getOrElse(getAnyType(c)))

  def getBounds(c: Context)(data: Datatype, env: Env): Many[Option[c.Tree]] =
    data match {
      // type constants produce no constraints
      case TypeConst(x) =>
        unconstrainedBounds(c)(env)

      // type vars produce no constraints
      case TypeVar(x) =>
        unconstrainedBounds(c)(env)

      // records just accumulate constraints generated by children
      case Record(r, fields) =>
        intersect(c, env.length)(fields map (field => getBounds(c)(field.get, env)))

      // to make things simple here,
      // we only support interspercing endofunctors for now
      case FunctorApplication(functor, args) =>
        val functorCode = c parse functor.code
        val argWithIndex = args.zipWithIndex
        val argBounds = intersect(c, env.length)(args map (arg => getBounds(c)(arg, env)))
        val projBounds = env map {
          case x =>
            val xSummands = argWithIndex flatMap {
              case (TypeVar(y), i) if x == y =>
                Some(getTreeCat(c, i)(functorCode))

              case _ =>
                None
            }
            intersectOnce(c)(xSummands)
        }

        intersect(c, env.length)(Many(argBounds, projBounds))

      // variants generate constraints on cases that are variables in env
      // in addition to accumulating bounds
      case Variant(v, cases) =>
        val caseBounds = intersect(c, env.length)(cases map (each => getBounds(c)(each, env)))
        val projBounds = env map {
          case x =>
            val xSummands = cases flatMap {
              case _ =>
                None
            }
            intersectOnce(c)(xSummands)
        }

        intersect(c, env.length)(Many(caseBounds, projBounds))

      // fixed points require `x` to be unconstrained
      case FixedPoint(x, body) =>
        val bodyBounds = getBounds(c)(body, x +: env)
        // require(bodyBounds.head.isEmpty) // `x` must be unconstrained, but we let scalac check that.
        bodyBounds.tail

      case LetBinding(lhs, rhs) =>
        getBounds(c)(rhs, env)
    }

  def unconstrainedBounds(c: Context)(env: Env): Many[Option[c.Tree]] =
    env map (_ => None)

  // can't abstract type of bounds due to path-dependency
  def intersect(c: Context, n: Int)(manyBounds: Many[Many[Option[c.Tree]]]):
      Many[Option[c.Tree]] =
    transpose(manyBounds, n) map (_ flatMap (x => x)) map (xs => intersectOnce(c)(xs))

  def intersectOnce(c: Context)(bounds: Many[c.Tree]): Option[c.Tree] =
    if (bounds.isEmpty)
      None
    else
      Some(bounds.reduce[c.Tree] {
        case (lhs, rhs) => import c.universe._ ; tq"$lhs with $rhs"
      })

  def transpose[T](matrix: Many[Many[T]], cols: Int): Many[Many[T]] =
    (0 until cols) map (i => matrix map (_(i)))
}
