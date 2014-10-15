package nominal
package util

import scala.reflect.macros.blackbox.Context

import compiler.DatatypeRepresentation.{Record, Many}

trait Traverse extends Paths {
  /** from record, create `case recordName @ Record(fieldNames @ _*) => body`
    * where body = mkBody(recordName, fieldNames)
    */
  def recordCaseDef(c: Context)(record: Record)(mkBody: (c.TermName, Many[c.TermName]) => c.Tree): c.universe.CaseDef = {
    import c.universe._
    val recordIdentName = TermName(record.name)
    val recordIdent = Ident(recordIdentName)
    val recordName = TermName(c freshName record.name.toLowerCase)
    val fieldNames = record.fields.map(field => TermName(c freshName field.name))
    val fieldBindings = fieldNames.map(name => Bind(name, Ident(termNames.WILDCARD)))
    if (fieldNames.isEmpty)
      cq"$recordIdent => ${mkBody(recordIdentName, fieldNames)}"
    else
      cq"$recordName @ $recordIdent(..$fieldBindings) => ${mkBody(recordName, fieldNames)}"
  }

  /** @param mapping mapping type variables to result type
    *
    * @param body mapping (applicative, function names, input type params, output type params) to body of `traverse` method
    *
    * @return q"new TraversableN { def traverse[...](...) = body(...) }"
    */
  def newTraversableEndofunctor(c: Context, n: Int)
    (mapping: Many[c.TypeName] => c.Tree)
    (body: (c.TermName, Many[c.TermName], Many[c.TypeName], Many[c.TypeName]) => c.Tree):
      c.Tree =
    newTraversableEndofunctorWith(c, n)(Many.empty, mapping)(body)

  def newTraversableEndofunctorWith(c: Context, n: Int)
    (valDefs: Many[c.Tree], mapping: Many[c.TypeName] => c.Tree)
    (body: (c.TermName, Many[c.TermName], Many[c.TypeName], Many[c.TypeName]) => c.Tree):
      c.Tree =
    newTraversableTrait(c, n)(getTraversableEndofunctor(c, n), valDefs, mapping)(body)

  def newBoundedTraversableWith(c: Context, n: Int)
    (bounds: Many[c.Tree], valDefs: Many[c.Tree], mapping: Many[c.TypeName] => c.Tree)
    (body: (c.TermName, Many[c.TermName], Many[c.TypeName], Many[c.TypeName]) => c.Tree):
      c.Tree = {
    import c.universe._
    val cats = bounds.zipWithIndex.map {
      case (bound, i) =>
        q"type ${typeNameCat(c, i)} = $bound"
    }
    newTraversableTrait(c, n)(getBoundedTraversable(c, n), cats ++ valDefs, mapping)(body)
  }

  def newTraversableTrait(c: Context, n: Int)
    (theTrait: c.Tree, valDefs: Many[c.Tree], mapping: Many[c.TypeName] => c.Tree)
    (body: (c.TermName, Many[c.TermName], Many[c.TypeName], Many[c.TypeName]) => c.Tree): c.Tree =
  {
    import c.universe._
    q"""
      new $theTrait {
        ${mkTypeMap(c, n)(mapping)}
        ${mkDefTraverse(c, n)(body)}
        ..$valDefs
      }
    """
  }

  def mkTypeMap(c: Context, n: Int)(mapping: Many[c.TypeName] => c.Tree): c.Tree =
    if (n < 1) {
      import c.universe._
      q"type ${TypeName(mappingOnObjects)} = ${mapping(Many.empty)}"
    }
    else {
      import c.universe._
      val tA: Many[TypeName] = (1 to n).map(_ => TypeName(c freshName "A"))(collection.breakOut)
      q"type ${TypeName(mappingOnObjects)}[..${mkCovariantTypeDefs(c)(tA)}] = ${mapping(tA)}"
    }

  def mkDefTraverse(c: Context, n: Int)
    (body: (c.TermName, Many[c.TermName], Many[c.TypeName], Many[c.TypeName]) => c.Tree):
      c.Tree =
    if (n <= 0)
      c parse ""
    else {
      import c.universe._
      val tA: Many[TypeName] = (1 to n).map(_ => TypeName(c freshName "A"))(collection.breakOut)
      val tB: Many[TypeName] = (1 to n).map(_ => TypeName(c freshName "B"))(collection.breakOut)
      val fs: Many[TermName] = (1 to n).map(_ => TermName(c freshName "F"))(collection.breakOut)
      val G  = TermName(c freshName "G")
      val tG = getFunctorMapOnObjects(c)(G)
      val fTypes: Many[Tree] = (tA, tB).zipped.map { case (a, b) => tq"$a => $tG[$b]" }
      val explicitParams = mkValDefs(c)(fs, fTypes)
      val resultType = tq"${mkTraverseIn(c)(tA)} => ${mkTraverseOut(c)(G, tB)}"
      val theBody = body(G, fs, tA, tB)

      val cats = (0 until n).map(i => getThisCat(c, i))
      val tAB = mkInvariantTypeDefs(c)(tA ++ tB, cats ++ cats)

      q"""
      def traverse[..$tAB]($G : ${getApplicative(c)})(..$explicitParams): $resultType = $theBody
    """
    }

  def mkTraverseIn(c: Context)(as: Many[c.TypeName]): c.Tree = {
    import c.universe._
    tq"${getThisMapOnObjects(c)}[..$as]"
  }

  def mkTraverseOut(c: Context)(G: c.TermName, bs: Many[c.TypeName]): c.Tree = {
    import c.universe._
    val tG = getFunctorMapOnObjects(c)(G)
    tq"$tG[${getThisMapOnObjects(c)}[..$bs]]"
  }

  def composeFunctorMaps(c: Context)(parent: c.TermName, functors: Many[c.TermName], params: Many[c.TypeName]):
      c.Tree = {
    import c.universe._
    val insides = functors map { f => tq"${getFunctorMapOnObjects(c)(f)}[..$params]" }
    tq"${getFunctorMapOnObjects(c)(parent)}[..$insides]"
  }

  def mkCovariantTypeDef(c: Context)(param: c.TypeName): c.universe.TypeDef = {
    val defs = mkCovariantTypeDefs(c)(Many(param))
    assert(defs.length == 1)
    defs.head
  }

  def mkCovariantTypeDefs(c: Context)(params: Many[c.TypeName]): Many[c.universe.TypeDef] = {
    if (params.isEmpty)
      sys error "mkCovariantTypeDefs called with empty params"

    import c.universe._
    val traitIn = TypeName(c freshName "Trait")
    val q"class $traitOut[..$typeDef] { ..$bodyOut }" =
      c parse s"class $traitIn[" + (params map ("+" + _) mkString ", ") + "]"
    typeDef
  }

  def mkInvariantTypeDefs(c: Context)(params: Many[c.TypeName], bounds: Many[c.Tree]): Many[c.universe.TypeDef] = {
    import c.universe._
    val traitIn = TypeName(c freshName "Trait")

    val boundedParams = params zip bounds map {
      case (param, bound) => s"$param <: ${showCode(bound)}"
    }

    val q"class $traitOut[..$typeDef] { ..$bodyOut }" =
      c parse s"class $traitIn[" + (boundedParams mkString ", ") + "]"
    typeDef
  }

  def mkValDef(c: Context)(termName: c.TermName, tpe: c.Tree): c.universe.ValDef = {
    import c.universe._
    val methodIn = TermName(c freshName "method")
    val q"def $methodOut($valDef)" = q"def $methodIn($termName : $tpe)"
    valDef
  }

  def mkValDefs(c: Context)(names: Many[c.TermName], types: Many[c.Tree]): Many[c.universe.ValDef] =
    (names, types).zipped.map { case (name, tpe) => mkValDef(c)(name, tpe) }

  def mkCallTree(c: Context)(applicative: c.TermName, leaves: Many[c.Tree]): c.Tree = {
    import c.universe._
    leaves.reduceLeft[c.Tree]({
      case (callTree, nextArg) =>
        q"$applicative.call($callTree, $nextArg)"
    })
  }

  /** @param applicative the applicative to call `pure` on
    *
    * @param termName the name of the uncurried function
    *
    * @param typeName the name of the type constructor of the result type
    *
    * @param typeParams the arguments of the type constructor in the result type
    *                   they also serve as argument types btw
    */
  def mkPureCurriedFunction(c: Context)(
    applicative: c.TermName,
    termName: c.TermName,
    typeName: c.TypeName,
    typeParams: Many[c.TypeName]
  ): c.Tree = {
    import c.universe._

    val typeBody = tq"$typeName[..$typeParams]"
    val curriedType = typeParams.foldRight(typeBody) {
      case (param, body) =>
        tq"$param => $body"
    }

    val termParams = typeParams.map(_ => TermName(c freshName "x"))
    val termBody = q"$termName(..$termParams)"
    val curriedTerm = termParams.foldRight(termBody) {
      case (param, body) =>
        Function(List(mkValDef(c)(param, TypeTree())), body)
    }

    q"${getPure(c)(applicative)}[$curriedType]($curriedTerm)"
  }

  def etaExpand(c: Context)(expr: c.Tree): c.Tree = {
    import c.universe._
    val x = TermName(c freshName "x")
    Function(List(mkValDef(c)(x, TypeTree())), q"$expr($x)")
  }

  def mkIntersectionType(c: Context)(types: Many[c.Tree]): c.Tree = {
    import c.universe._
    if (types.isEmpty)
      getAnyType(c)
    else {
      val intersectionTypeCode = types map (x => s"(${showCode(x)})") mkString " with "
      val q"??? : $intersectionType" = c parse s"??? : ($intersectionTypeCode)"
      intersectionType
    }
  }
}
