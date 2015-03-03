package nominal
package compiler

import scala.reflect.macros.blackbox.Context
import scala.reflect.macros.TypecheckException

import DatatypeRepresentation._

trait UniverseConstruction extends util.AbortWithError with util.TupleIndex with util.Paths {

  // ====================== //
  // FROM DATATYPE TO SCALA //
  // ====================== //

  /** @param rep    our representation of a datatype
    * @return       scala's representation of a type
    */
  def meaning(c: Context)(rep: Datatype): c.Tree = {
    import c.universe._
    rep match {
      case TypeConst(tpe) =>
        val q"??? : $result" = c parse(s"??? : ($tpe)")
        result

      case TypeVar(tpe) =>
        val q"??? : $result" = c.parse(s"??? : ($tpe)")
        result

      case Record(name, fields) =>
        tq"${TypeName(name)}[..${fields.map(field => meaning(c)(field.get))}]"

      case Variant(typeVar, records) =>
        tq"${meaning(c)(TypeVar(typeVar))}[..${records.map(record => meaning(c)(record))}]"

      case FixedPoint(paramName, body) =>
        // to take the fixed point, the data constructor must be unary
        val fix = getFix(c)
        val innerType = mkInnerType(c)
        val typeDef = covariantTypeDef(c)(paramName)

        tq"""
          $fix[({
            type $innerType[$typeDef] = ${meaning(c)(body)}
          })#$innerType]
        """

      case LetBinding(lhs, rhs) =>
        meaning(c)(rhs)

      case FunctorApplication(functor, args) =>
        val xs = args map (x => meaning(c)(x))
        tq"${getTreeMapOnObjects(c)(c parse functor.code)}[..$xs]"
    }
  }

  def noRecognition(data: Datatype): Nothing =
    sys error s"unrecognized datatype:\n\n    $data"

  /** @param rep datatype representation
    *
    * @return corresponding scala type with all type synonyms resolved
    */
  def scalaType(c: Context)(rep: Datatype): c.Type =
    treeToType(c)(meaning(c)(rep))

  def treeToType(c: Context)(typeTree: c.Tree): c.Type = {
    import c.universe._
    c.typecheck(q"??? : $typeTree").tpe.dealias
  }

  def mkInnerType(c: Context): c.TypeName = c.universe.TypeName(c freshName "innerType")

  /** @param name name of type parameter
    * @return covariant type parameter of that name
    */
  def covariantTypeParam(c: Context)(name: Name): c.Tree = {
    import c.universe._
    val q"type Dummy[$result]" = q"type Dummy[+${TypeName(name)}]"
    result
  }

  def covariantTypeParams(c: Context)(names: Many[Name]): Many[c.Tree] =
    names.map(name => covariantTypeParam(c)(name))

  // covariantTypeDef* are just like covariantTypeParam*, except outputting typedefs

  def covariantTypeDef(c: Context)(name: Name): c.universe.TypeDef = {
    import c.universe._
    val param = covariantTypeParam(c)(name)

    // strangely, macros can adapt TypeName arguments of a trait to TypeDefs,
    // but cannot adapt those of a type synonym.
    // hence the quote+unquote here.
    val traitIn = TypeName(c freshName "Trait")
    val q"trait $traitOut[$typeDef]" = q"trait $traitIn[$param]"
    typeDef
  }

  def covariantTypeDefs(c: Context)(names: Many[Name]): Many[c.universe.TypeDef] =
    names.map(name => covariantTypeDef(c)(name))

  def mkTypeDef(c: Context)(param: Param): c.universe.TypeDef = mkBoundedTypeDef(c)(param, Map.empty)

  // make a TypeDef according to variance
  def mkBoundedTypeDef(c: Context)(param: Param, bounds: Map[Name, Datatype]): c.universe.TypeDef = {
    import c.universe._
    val variance = param.variance.scalaSymbol
    val traitIn = TypeName(c freshName "Trait")
    if (bounds contains param.name) {
      val bound = meaning(c)(bounds(param.name))
      val q"class $traitOut[$typeDef] { ..$bodyOut }" = c.parse(s"class $traitIn[ $variance ${param.name} <: $bound ]")
      typeDef
    }
    else {
      val q"class $traitOut[$typeDef] { ..$bodyOut }" = c.parse(s"class $traitIn[ $variance ${param.name} ]")
      typeDef
    }
  }

  def mkTypeDefs(c: Context)(params: Many[Param]): Many[c.universe.TypeDef] = mkBoundedTypeDefs(c)(params, Map.empty)

  def mkBoundedTypeDefs(c: Context)(params: Many[Param], bounds: Map[Name, Datatype]): Many[c.universe.TypeDef] =
    params.map(param => mkBoundedTypeDef(c)(param, bounds))

  /* get implicit value of a reified type */
  def inferImplicitValue(c: Context)(typeTree: c.Tree): Option[c.Tree] = {
    import c.universe._
    c.inferImplicitValue(treeToType(c)(typeTree), true /*silent*/) match {
      case q"" =>
        None

      case tree =>
        Some(tree)
    }
  }



  // ====================== //
  // FROM SCALA TO DATATYPE //
  // ====================== //

  def reifyRegular(c: Context)(tpe: c.Type): Regular[c.Type] =
    reifyWithEnv(c)(tpe, tpe, Map.empty)

  //  precondition: `tpeOut` is valid type in c
  //                `env` contains only types valid in c
  //
  // postcondition: all types in return value are valid in c
  def reifyWithEnv(c: Context)
    ( tpe0: c.Type,
      tpeOut0: c.Type,
      env: Map[c.universe.Symbol, (String, c.Type)]): Regular[c.Type] =
  {
    val tpe = tpe0.dealias
    val tpeOut = tpeOut0.dealias

    // bound type variable
    if (tpe.typeArgs.isEmpty && env.contains(tpe.typeSymbol)) {
      val (myId, myTpe) = env(tpe.typeSymbol)
      RegularVar(myId, myTpe)
    }

    // fixed point
    else if (isFixedPointOfSomeFunctor(c)(tpe)) {
      val List(fun0)  = tpe.typeArgs
      val functor     = fun0.etaExpand
      val List(param) = functor.typeParams
      val myId        = freshID(c)
      val newEnv      = env.updated(param, (myId, tpeOut))

      val myBody      = functor.resultType
      val myBodyOut   = applyEnv(c)(myBody, newEnv)

      RegularFix(myId, tpeOut, reifyWithEnv(c)(myBody, myBodyOut, newEnv))
    }

    // possibly a functor application
    // do not try to look up the functor here
    else if (tpe.typeArgs.nonEmpty) {
      assert(tpe.typeArgs.size == tpeOut.typeArgs.size)

      RegularFun(freshID(c), tpeOut,
        tpe.typeArgs.zip(tpeOut.typeArgs).map {
          case (child, childOut) =>
            reifyWithEnv(c)(child, childOut, env)
        }
      )
    }

    // unrecognized base type
    else
      RegularVar(freshID(c), tpeOut)
  }

  // resolve pending substitutions
  def applyEnv(c: Context)(
    tpe: c.Type,
    env: Map[c.universe.Symbol, (String, c.Type)]): c.Type =
  {
    val (lhs, rhs) = env.view.map(p => (p._1, p._2._2)).toList.unzip
    tpe.substituteTypes(lhs, rhs)
  }

  def freshID(c: Context): String = c.freshName()

  // requires `tpe` be dealiased
  def isFixedPointOfSomeFunctor(c: Context)(tpe: c.Type): Boolean =
    getFixWithoutRoot == tpe.typeConstructor.typeSymbol.fullName
}

object UniverseConstruction {
  object Tests extends UniverseConstruction with Parsers with util.AssertEqual with util.Persist {
    import language.experimental.macros
    import scala.annotation.StaticAnnotation

    def isFix[T]: Boolean = macro isFixImpl[T]
    def isFixImpl[T](c: Context)(implicit tag: c.WeakTypeTag[T]): c.Tree = {
      import c.universe._

      val truth = isFixedPointOfSomeFunctor(c)(tag.tpe)

      if (truth)
        q"true"
      else
        q"false"
    }

    def reify[T]: DatatypeRepresentation.Datatype = macro reifyImpl[T]
    def reifyImpl[T](c: Context)(implicit tag: c.WeakTypeTag[T]): c.Tree = {
      val regular = reifyRegular(c)(tag.tpe).toDatatype.canonize
      persist(c)(regular)
    }

    def unrollFix[T]: String = macro unrollFixImpl[T]
    def unrollFixImpl[T](c: Context)(implicit tag: c.WeakTypeTag[T]): c.Tree = {
      val RegularFix(id, tpe, body) = reifyRegular(c)(tag.tpe)
      persist(c)(body.tpe.toString)
    }
  }
}
