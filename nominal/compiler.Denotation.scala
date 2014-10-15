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

package nominal
package compiler

import scala.reflect.macros.blackbox.Context
import DatatypeRepresentation._

trait Denotation extends UniverseConstruction with util.Traverse {
  private[this] type Env = Many[Name]

  def evalFunctor(c: Context)(functor: DataConstructor): c.Tree =
    evalData(c)(functor.body)(functor.params.map(_.name))

  def evalData(c: Context)(data: Datatype): Env => c.Tree = data match {
    case typeVar: TypeVar =>
      evalTypeVar(c)(typeVar)

    case fixedpoint: FixedPoint =>
      evalFixedPoint(c)(fixedpoint)

    case record: Record =>
      evalRecord(c)(record)

    case variant: Variant =>
      evalVariant(c)(variant)

    case RecordAssignment(record, x) =>
      evalTypeVar(c)(x)
  }

  def evalTypeVar(c: Context)(typeVar: TypeVar): Env => c.Tree = env => {
    import c.universe._
    val x = typeVar.name
    val n = env.length
    val i = env indexOf x
    if (i < 0)
      evalConst(c, x, n)
    else
      evalProj(c, i, n)
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

  def evalRecord(c: Context)(record: Record): Env => c.Tree = env => {
    import c.universe._
    val Record(name, fields) = record
    val termName = TermName(name) // assumed to be generated

    val namedSubfunctors = fields.map {
      case Field(fieldName, fieldBody) =>
        (TermName(c freshName fieldName), evalData(c)(fieldBody)(env))
    }

    val subfunctorDefs = namedSubfunctors.map {
      case (x, xdef) => q"val $x = $xdef"
    }

    val bounds = getBounds(c)(record, env)

    def mangle(as: Many[TypeName]) = Map((env zip (as.map(_.toString))): _*)

    newBoundedTraversableWith(c, env.length)(
      boundsToCats(c)(bounds),
      subfunctorDefs,
      as => meaning(c)(record rename mangle(as))
    ) {
      case (applicative, fs, as, bs) =>
        val names = namedSubfunctors.map(_._1)
        val travParams =
          ( names.map(f => tq"${getFunctorMapOnObjects(c)(f)}[..$as]") ++
            names.map(f => tq"${getFunctorMapOnObjects(c)(f)}[..$bs]") )
        val traversals = names map (f => q"$f.traverse($applicative)(..$fs)")
        q"$termName.traverse[..$travParams]($applicative)(..$traversals)"
    }
  }

  // almost the same as evalRecord. should refactor.
  def evalVariant(c: Context)(variant: Variant): Env => c.Tree = env => {
    import c.universe._
    val Variant(name, cases) = variant
    val termName = TermName(name) // assumed to be generated

    val namedSubfunctors = cases.map { variantCase =>
      (TermName(c freshName variantCase.name), evalData(c)(variantCase)(env))
    }

    val subfunctorDefs = namedSubfunctors.map {
      case (x, xdef) => q"val $x = $xdef"
    }

    val bounds = getBounds(c)(variant, env)

    def mangle(as: Many[TypeName]) = Map((env zip (as.map(_.toString))): _*)

    newBoundedTraversableWith(c, env.length)(
      boundsToCats(c)(bounds),
      subfunctorDefs,
      as => meaning(c)(variant rename mangle(as))
    ) {
      case (applicative, fs, as, bs) =>
        val names = namedSubfunctors.map(_._1)
        val travParams =
          ( names.map(f => tq"${getFunctorMapOnObjects(c)(f)}[..$as]") ++
            names.map(f => tq"${getFunctorMapOnObjects(c)(f)}[..$bs]") )
        val traversals = names map (f => q"$f.traverse($applicative)(..$fs)")
        q"$termName.traverse[..$travParams]($applicative)(..$traversals)"
    }
  }

  def evalFixedPoint(c: Context)(fixedpoint: FixedPoint): Env => c.Tree = env => {
    import c.universe._
    val FixedPoint(x, body) = fixedpoint
    val bodyEnv  = x +: env
    val bodyCode = evalData(c)(body)(bodyEnv)
    val bodyName = TermName(c freshName "body")
    val bodyDef  = q"val $bodyName = $bodyCode"
    val bodyBds  = getBounds(c)(fixedpoint, env)

    // create mapping on objects
    val lambda = TypeName(c freshName "lambda")
    val patternF: Many[TypeName] => c.Tree = params => {
      val x = TypeName(c freshName "x")
      val xdef = mkCovariantTypeDef(c)(x)
      val mangle = Map(bodyEnv zip ((x +: params).map(_.toString)): _*)
      val rhs = meaning(c)(body rename mangle)
      tq"({ type $lambda[$xdef] = $rhs })#$lambda"
    }

    val mapping: Many[TypeName] => c.Tree =
      params => tq"${getFix(c)}[${patternF(params)}]"

    newBoundedTraversableWith(c, env.length)(boundsToCats(c)(bodyBds), Many(bodyDef), mapping) {
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
  }

  def boundsToCats(c: Context)(bounds: Many[Option[c.Tree]]): Many[c.Tree] =
    bounds map (_.getOrElse(getAnyType(c)))

  def getBounds(c: Context)(data: Datatype, env: Env): Many[Option[c.Tree]] =
    data match {
      // type vars produce no constraints
      case TypeVar(x) =>
        unconstrainedBounds(c)(env)

      // records just accumulate constraints generated by children
      case Record(r, fields) =>
        intersect(c, env.length)(fields map (field => getBounds(c)(field.get, env)))

      // variants generate constraints on cases that are variables in env
      // in addition to accumulating bounds
      case Variant(v, cases) =>
        val caseBounds = intersect(c, env.length)(cases map (each => getBounds(c)(each, env)))
        val projBounds = env map {
          case x =>
            val xSummands = cases flatMap {
              case RecordAssignment(record, TypeVar(y)) if x == y =>
                Some(meaning(c)(record))

              case _ =>
                None
            }
            intersectOnce(c)(xSummands)
        }

        intersect(c, env.length)(Many(caseBounds, projBounds))

      // fixed points require `x` to be unconstrained
      case FixedPoint(x, body) =>
        val bodyBounds = getBounds(c)(body, x +: env)
        require(bodyBounds.head.isEmpty) // `x` must be unconstrained
        bodyBounds.tail

      case RecordAssignment(lhs, rhs) =>
        unconstrainedBounds(c)(env)
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
