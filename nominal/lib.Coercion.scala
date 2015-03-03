/** Type coercion a la TAPL (Pierce) §21.9 */

package nominal
package lib

import scala.language.higherKinds
import scala.language.implicitConversions
import scala.language.experimental.macros
import scala.collection.mutable.{HashMap => MMap, MultiMap, Set => MSet}
import scala.reflect.macros.blackbox.Context

import compiler._
import DatatypeRepresentation._

object Coercion extends UniverseConstruction with util.Traverse {
  import Fix.TypeWitness

  def coerceImpl[Actual, Expected]
    (c: Context)
    (arg: c.Tree)
    (tagT: c.Tree)
    (implicit
      actualTag: c.WeakTypeTag[Actual],
      expectedTag: c.WeakTypeTag[Expected]): c.Tree =

    try { performCoerce(c)(arg)(tagT)(actualTag, expectedTag) }
    catch {
      case e: Throwable =>
        if (
          false && // disable stack trace printing
            ! isNothingType(expectedTag.tpe)
        ) {
          println(e.getMessage)
          println(e.printStackTrace)
          println
        }
        throw e
    }

  def performCoerce[Actual, Expected]
    (c: Context)
    (arg: c.Tree)
    (tagT: c.Tree)
    (implicit
      actualTag: c.WeakTypeTag[Actual],
      expectedTag: c.WeakTypeTag[Expected]): c.Tree =
    {
      import c.universe._

      val actual   = reifyRegular(c)(actualTag.tpe)
      val expected = reifyRegular(c)(expectedTag.tpe)

      witness(c)(Map.empty, actual, expected) match {
        case None =>
          if (! isNothingType(expected.tpe))
            c.echo(arg.pos, s"ERROR: Coercion failed.\n" +
              s"    Actual = ${actual.tpe}\n" +
              s"  Expected = ${expected.tpe}\n")

          abortWithError(c)(
            c.enclosingPosition,
            s"Coercion failed. Either there's a type error,\n" +
              "or the context has too little information.")

        case Some((ctx0, dfs0, diffRep, graph)) =>
          val TheWitness = TermName(c freshName "TheWitness")
          val (ctx, dfs) = optimizeCoerce(c)(
            ctx0, dfs0, actual, expected,
            diffRep, graph
          )
          val f = ctx((actual.id, expected.id))

          q"""{
            object $TheWitness { ..$dfs }
            $TheWitness . $f($arg)
          }"""
      }
    }

  private[this] type Vertex        = (String, String)
  private[this] type Env[TermName] = Map[Vertex, TermName]
  private[this] type DiffRep       = Set[Vertex]
  private[this] type Graph         = Seq[(Vertex, Vertex)]

  /** Pierce's memoized version of of Amadio & Cardelli's subtyping algorithm
    * with extra book-keeping to compute witnesses
    * with extra book-keeping for optimization via safe typecasts
    *
    * @return Some((labels, defs, diff, graph))
    *   where
    *     labels = mapping source-target pairs to conversion method names
    *     defs   = mapping source-target pairs to method definitions
    *     diff   = set of source-target pairs corresponding to conversions
    *              that do not preserve runtime object representation
    *     graph  = dependency graph between source-target pairs
    *
    * reps & graph are necessary for optimization alone.
    */
  def witness(c: Context)(
    context: Map[(String, String), c.universe.TermName],
    source : Regular[c.Type],
    target : Regular[c.Type]):
      Option[(Env[c.TermName], Env[Env[c.TermName] => c.Tree], DiffRep, Graph)] =
  {
    import c.universe._
    type ReturnType = Option[(
      Env[TermName],
      Env[Env[TermName] => Tree],
      DiffRep,
      Graph
    )]

    // pre-computed: preserves representation only if all subcomputations does
    // to be determined later
    if (context.contains((source.id, target.id)))
      Some((context, Map.empty, Set.empty, Seq.empty))

    else {

      val f  = TermName(c.freshName("f"))
      val a0 = context.updated((source.id, target.id), f)

      def mkF(body: (TermName, Env[TermName]) => Tree): Env[TermName] => Tree = {
        val x = TermName(c freshName "x")
        env => q"def $f($x: ${source.tpe}): ${target.tpe} = ${body(x, env)}"
      }

      // source <: target: preserves representation
      if (isScalaSubtype(c)(source.tpe, target.tpe))
        Some((a0, Map((source.id, target.id) -> mkF((x, env) => q"$x")),
          Set.empty,
          Seq.empty
        ))

      else inferImplicitView(c)(source.tpe, target.tpe) match {
        // source <% target: does not preserve representation
        case Some(view) =>
          Some((a0, Map((source.id, target.id) -> mkF((x, env) => q"$view($x)")),
            Set(source.id -> target.id),
            Seq.empty
          ))

        case None =>

          (source, target) match {
            // simultaneous unroll: preserves representation
            case (
              src @ RegularFix(srcId, srcTpe, _),
              tgt @ RegularFix(tgtId, tgtTpe, _)) =>
              for {
                (a1, dfs, diffRep, graph) <- witness(c)(a0, src.unroll, tgt.unroll)
                newDfn = mkF { (x, env) =>
                  val f1 = env((src.body.id, tgt.body.id))
                  q"${getRoll(c)}[..${tgtTpe.typeArgs}]($f1($x.unroll))"
                }
              }
              yield (
                a1,
                dfs + ((srcId -> tgtId) -> newDfn),
                diffRep,
                ((srcId -> tgtId) -> (src.body.id -> tgt.body.id)) +: graph
              )

            // unroll target: does not preserve representation
            case (source @ RegularFix(id, srcTpe, _), _) =>
              for {
                (a1, dfs, diffRep, graph) <- witness(c)(a0, source.unroll, target)
                newDfn = mkF { (x, env) =>
                  val f1 = env((source.body.id, target.id))
                  q"$f1($x.unroll)"
                }
              } yield (a1, dfs + ((source.id, target.id) -> newDfn),
                diffRep + (source.id -> target.id),
                ((source.id -> target.id) -> (source.body.id -> target.id)) +: graph
              )

            // unroll source: does not preserve representation
            case (_, target @ RegularFix(id, tgtTpe, _)) =>
              for {
                (a1, dfs, diffRep, graph) <- witness(c)(a0, source, target.unroll)
                newDfn = mkF { (x, env) =>
                  val f1 = env((source.id, target.body.id))
                  q"${getRoll(c)}[..${tgtTpe.typeArgs}]($f1($x))"
                }
              }
              yield (a1, dfs + ((source.id, target.id) -> newDfn),
                diffRep + (source.id -> target.id),
                ((source.id -> target.id) -> (source.id -> target.body.id)) +: graph
              )

            // identical functor at top level: preserves representation
            case (
              RegularFun(srcId, srcTpe, srcArgs),
              RegularFun(tgtId, tgtTpe, tgtArgs))
                if equalTypeConstructor(c)(srcTpe, tgtTpe) =>

              val (cons, n) = getTypeConstructorArity(c)(srcTpe)

              // requires traversable for now
              // may switch to require functor instead later
              val travTrait = getBoundedTraversable(c, n)

              val typeMap = mkTypeMap(c, n) { types => tq"$cons[..$types]" }

              // either both are records, or both are variants,
              // or it is a built-in traversable.
              val maybeFunctor: Tree =
                if (isRecordOrVariantType(c)(srcTpe)){

                  // !!! HACK !!!
                  //
                  // Grab the companion object
                  // by printing the type constructor as if it's a term.
                  // `showCode` does not work. Have to call `toString`.
                  //
                  // Alternatively, may declare all companion objects implicit
                  // and risk polluting the implicit scope beyond recognition.
                  //
                  val typeString = tq"${srcTpe.typeConstructor}".toString
                  val companion = c parse typeString

                  companion
                }
                else
                  c.inferImplicitValue(
                    treeToType(c)(tq"$travTrait { $typeMap }"),
                    true, // return empty result, do not throw exception
                    true  // disable implicit macros during this search
                  )

              maybeFunctor match {
                case q"" => None
                case functor =>
                  assert(srcArgs.size == tgtArgs.size)

                  val args = srcArgs.zip(tgtArgs)

                  for {
                    (an, dfs, diffRep, graph) <- args.foldLeft[ReturnType](
                      Some((a0, Map.empty, Set.empty, Seq.empty))
                    ) {
                      case (maybe, (s_i, t_i)) =>
                        for {
                          (a_prev, dfs_prev, sr_prev, gr_prev) <- maybe
                          (a_i, dfs_i, sr_i, gr_i) <- witness(c)(a_prev, s_i, t_i)
                        }
                        yield (a_i, dfs_prev ++ dfs_i,
                          sr_prev ++ sr_i,
                          ((source.id -> target.id) -> (s_i.id -> t_i.id)) +:
                            (gr_i ++ gr_prev)
                        )
                    }

                    newDfs = mkF { (x, env) =>
                      val fs = args.map {
                        case (srcChild, tgtChild) =>
                          env((srcChild.id, tgtChild.id))
                      }
                      q"$functor[..${srcArgs.map(_.tpe)}]($x).map(..$fs)"
                    }
                  }
                  yield (an, dfs + ((source.id, target.id) -> newDfs),
                    diffRep,
                    graph
                  )
              }

            // converting records to variants: preserves representation
            case (_, RegularFun(tgtId, tgtTpe, tgtArgs))
                if isRecordOfVariant(c)(source.tpe, tgtTpe) =>

              val results = tgtArgs.flatMap { candidate =>
                for {
                  (ctx, dfs, diff, gr) <- witness(c)(a0, source, candidate)
                }
                yield (candidate, ctx, dfs,
                  diff,
                  ((source.id -> target.id) -> (source.id -> candidate.id)) +: gr
                )
              }

              // no match; bad coercion.
              if (results.isEmpty)
                None

              // multiple matches, fatal error.
              else if (results.tail.nonEmpty) {
                val fatalError =
                  s"""|
                      |
                      |FATAL COERCION ERROR
                      |More than one variant case matches actual record.
                      |
                      |    Actual = ${source.tpe}
                      |
                      |  Expected = $tgtTpe
                      |
                      |
                      |""".stripMargin
                System.err.println(fatalError)
                sys error fatalError
              }

              // unique match, is good.
              else {
                val (candidate, a1, dfs, diff, graph) = results.head
                Some((
                  a1,
                  dfs + ((source.id, target.id) -> mkF((x, env) => {
                    val f1 = env((source.id, candidate.id))
                    q"$f1($x)"
                  })),
                  diff,  // updated at candidate's
                  graph  // updated at candidate's
                ))
              }

            case _ =>
              None
          }
      }
    }
  }

  /** optimize away coercions with identical runtime representation */
  def optimizeCoerce(c: Context)(
    context : Env[c.TermName],
    dfs     : Env[Env[c.TermName] => c.Tree],
    source  : Regular[c.Type],
    target  : Regular[c.Type],
    diffRep : DiffRep,
    graph0  : Graph):
      (Env[c.TermName], List[c.Tree]) =
  {
    val (env, indexedDfs) = optimizeCoerceWithIndex(c)(
      context, dfs, source, target, diffRep, graph0
    )

    (env, indexedDfs.map(_._2))
  }

  /** @return (env, indexedDfs) where
    *   `env` maps vertices to name of corresponding conversion methods
    *   `indexedDfs` is a list of definitions indexed by name of method
    */
  def optimizeCoerceWithIndex(c: Context)(
    context : Env[c.TermName],
    dfs     : Env[Env[c.TermName] => c.Tree],
    source  : Regular[c.Type],
    target  : Regular[c.Type],
    diffRep : DiffRep,
    graph0  : Graph):
      (Env[c.TermName], List[(String, c.Tree)]) =
  {
    import c.universe._

    // represent graph by map from each predecessor to its set of successors
    val graph = mkMultiGraph(graph0)

    // the starting vertex (top-level conversion)
    val start = (source.id, target.id)

    // propagate nonpreservation of runtime representation exhaustively,
    // obtain all vertices corresponding to conversions that cannot
    // be safely replaced by typecasts
    //
    // algorithm is depth-first-search until result stops changing.
    // It should be possible to discover `diff` in one DFS in O(n log n) time
    // if we reverse the dependency graph and add links from mu-bindings
    // to all type variables bound by it.
    // we implement a slow O(n^2 log n) algorithm here because we're lazy.
    val diff  = applyExhaustively(diffRep)(propagateDiff(start, graph))

    // discover nearest representation-preserving descendants of `start`
    val casts = optimizedVertices(start, graph, diff)

    // convert regular types to maps
    val getTpe: PartialFunction[String, Type] =
      extractTpes(c)(source) orElse extractTpes(c)(target)

    // optimized context: cast as much as possible
    val ctxOpt: Env[TermName] = context ++ casts.map({
      v => (v, TermName(c.freshName("cast")))
    })

    val conversionMethods: List[(String, Tree)] = dfs.flatMap({
      case (v @ (src, tgt), dfn) =>
        if (casts(v)) {
          // generate a cast
          val f      = ctxOpt(v)
          val srcTpe = getTpe(src)
          val tgtTpe = getTpe(tgt)
          val x      = TermName(c freshName "x")
          List(
            ( f.toString,
              q"def $f($x : $srcTpe): $tgtTpe = $x.asInstanceOf[$tgtTpe]"
            ),

            // append method without cast based on old context
            (context(v).toString, dfn(context))
          )
        }
        else
          // generate a conversion
          List((ctxOpt(v).toString, dfn(ctxOpt)))
    })(collection.breakOut)

    (ctxOpt, conversionMethods)
  }

  /** convert a Graph into a MultiGraph, or graph based on multimap */
  type MultiGraph = MultiMap[Vertex, Vertex]
  def mkMultiGraph(graph: Graph): MultiGraph = {
    val mm = new MMap[Vertex, MSet[Vertex]] with MultiGraph
    graph.foreach { case (source, target) => mm.addBinding(source, target) }
    mm
  }

  def applyExhaustively[T](initial: T)(step: T => Option[T]): T =
    step(initial) match {
      case None       => initial
      case Some(next) => applyExhaustively(next)(step)
    }

  /** extract all types mentioned in a regular type */
  def extractTpes(c: Context)(tau: Regular[c.Type]): Map[String, c.Type] =
    tau match {
      case RegularVar(id, tpe) =>
        Map(id -> tpe)

      case RegularFun(id, tpe, args) =>
        Map(id -> tpe) ++ args.flatMap(sigma => extractTpes(c)(sigma))

      case RegularFix(id, tpe, body) =>
        Map(id -> tpe) ++ extractTpes(c)(body)
    }

  /** traverse graph once & discover vertices to convert to casts
    * those conversions without dependencies are not marked,
    * because their baseline implementation should be faster than
    * a typecast
    */
  def optimizedVertices(start: Vertex, graph: MultiGraph, diff: DiffRep):
      Set[Vertex] =
    abortiveDFS[Set[Vertex]](start, graph)(Set.empty) {
      // do not descend into representation-preserving conversions
      case (v, set) =>
        if (! diff(v)) {
          if (graph.withDefault(_ => MSet.empty[Vertex])(v).nonEmpty)
            // convert a traversal into a typecast
            Some(set + v)
          else
            // there's no traversal anyway, no need to generate cast
            Some(set)
        }
        else None
    } {
      // descend into non-representation-preserving conversions
      // to discover nearest representation-preserving descendants
      (v, set) => { assert(diff(v)) ; set }
    }

  /** traverse graph once & propagage difference in runtime representation */
  def propagateDiff(start: Vertex, graph: MultiGraph): DiffRep => Option[DiffRep] =
    diff => {
      val (newDiff, acc) = abortiveDFS[
        (Set[Vertex], List[Vertex])
      ](start, graph)((diff, Nil)) {
        // never abort the DFS because non-preserving conversion
        // may invoke preserving subconversions, which must be marked
        // according to whether its subsubconversions are preseving
        // or not.
        (_, _) => None
      } {
        // descend into dependencies.
        // if they are non-representation-preserving,
        // so is the conversion associated with `next`.
        case (v, (diff, acc)) =>
          if (
            diff(v) || graph.withDefault(
              _ => MSet.empty[Vertex]
            )(v).filter(diff).isEmpty
          )
            (diff, acc)
          else
            (diff + v, v :: acc)
      }
      if (acc.isEmpty)
        None
      else
        Some(newDiff)
    }

  /** depth-first-search with accumulator and possibility to not descend */
  def abortiveDFS[T](start: Vertex, graph: MultiGraph)
    (startingState: T)
    (abortWithRslt: (Vertex, T) => Option[T])
    (transition   : (Vertex, T) => T): T =
  {
    def search(next: Vertex): (T, Set[Vertex]) => (T, Set[Vertex]) =
      (state, visited) => {
        if (visited(next))
          (state, visited)
        else {
          val nextVisited = visited + next

          abortWithRslt(next, state) match {
            case Some(nextState) =>
              (nextState, nextVisited)

            case None =>
              val result =
                graph.withDefault(_ => MSet.empty[Vertex])(next).foldLeft[
                  (T, Set[Vertex])
                ]((state, nextVisited)) {
                  case ((state, visited), child) =>
                    search(child)(state, visited)
                }
              (transition(next, result._1), result._2)
          }
        }
      }

    search(start)(startingState, Set.empty)._1
  }


  // UTILITIES

  // subsumes subtyping
  def inferImplicitView(c: Context)(actual: c.Type, expected: c.Type):
      Option[c.Tree] =
  {
    import c.universe._
    // infer implicit view with macros disabled
    c.inferImplicitView(q"???", actual, expected, true, true) match {
      case q""  => None
      case view => Some(view)
    }
  }

  def getTypeConstructorArity(c: Context)(tpe: c.Type): (c.Type, Int) = {
    val cons = tpe.dealias.typeConstructor
    (cons, cons.typeParams.size)
  }

  def equalTypeConstructor(c: Context)(lhs: c.Type, rhs: c.Type): Boolean = {
    lhs.dealias.typeConstructor.typeSymbol ==
    rhs.dealias.typeConstructor.typeSymbol
  }

  // test of tpe is a record or a variant
  def isRecordOrVariantType(c: Context)(tpe: c.Type): Boolean =
    isScalaSubtype(c)(tpe, treeToType(c)(getRecordOrVariant(c)))

  def isRecordType(c: Context)(tpe: c.Type): Boolean =
    isScalaSubtype(c)(tpe, treeToType(c)(getRecord(c)))

  def isVariantType(c: Context)(tpe: c.Type): Boolean =
    isScalaSubtype(c)(tpe, treeToType(c)(getVariant(c))) && ! isRecordType(c)(tpe)

  // test if lhs0 is a record in the variant type rhs0
  def isRecordOfVariant(c: Context)(lhs0: c.Type, rhs0: c.Type): Boolean =
    isRecordType(c)(lhs0) && isVariantType(c)(rhs0)

  // dealias `tpe`, then apply its type constructor to Nothings
  def applyConstructorToNothing(c: Context)(tpe: c.Type): c.Type = {
    val nothing = treeToType(c)(getNothingType(c)) // can reuse?
    val cons = tpe.dealias.typeConstructor.etaExpand
    cons.resultType.substituteTypes(
      cons.typeParams,
      cons.typeParams map { _ => nothing })
  }


  def infoImpl[Actual, Expected]
    (c: Context)
    (arg: c.Tree, info: c.Tree)
    (witness: c.Tree)
    (implicit actualTag: c.WeakTypeTag[Actual], expectedTag: c.WeakTypeTag[Expected]):
      c.Tree =
    {
      import c.universe._
      val (actualType, expectedType) = (actualTag.tpe, expectedTag.tpe)
      q"""{
        $info += ("actual" -> ${actualType.toString}) += ("expected" -> ${expectedType.toString})
        null.asInstanceOf[$expectedType]
      }"""
    }

  def isNothingType(tpe: Context#Type): Boolean =
    tpe.typeSymbol.fullName == "scala.Nothing"

  def isScalaSubtype(c: Context)(subtype: c.Type, supertype: c.Type): Boolean = {
    import c.universe._
    inferImplicitValue(c)(tq"$subtype <:< $supertype").nonEmpty
  }


  // testing macros
  object Test {
    // test if there's a cast at top level or not
    def hasCast[S, T]: Boolean =
      macro hasCastImpl[S, T]

    def hasCastImpl[Actual, Expected](c: Context)(
      implicit
        actualTag: c.WeakTypeTag[Actual],
      expectedTag: c.WeakTypeTag[Expected]): c.Tree =
    {
      import c.universe._

      val actual   = reifyRegular(c)(actualTag.tpe)
      val expected = reifyRegular(c)(expectedTag.tpe)

      witness(c)(Map.empty, actual, expected) match {
        case None =>
          sys error "`hasCast` must be called on valid coercions"

        case Some((ctx0, dfs0, diffRep, graph)) =>

          val (ctx, dfs) = optimizeCoerceWithIndex(c)(
            ctx0, dfs0, actual, expected,
            diffRep, graph
          )

          val f = ctx((actual.id, expected.id)).toString

          dfs.find(_._1 == f) match {
            case Some((_, q"def $f($x : $src): $tgt = $y.asInstanceOf[$tgt2]")) =>
              q"true"

            case other =>
              q"false"
          }
      }
    }

    // Test macro sameRep[S, T] returns whether S, T has same runtime
    // representationl.
    def sameRep[S, T]: Boolean =
      macro sameRepImpl[S, T]

    def sameRepImpl[Actual, Expected](c: Context)(
      implicit
        actualTag: c.WeakTypeTag[Actual],
      expectedTag: c.WeakTypeTag[Expected]): c.Tree =
    {
      import c.universe._

      val source = reifyRegular(c)(actualTag.tpe)
      val target = reifyRegular(c)(expectedTag.tpe)

      witness(c)(Map.empty, source, target) match {
        case None =>
          q"false"
        case Some((ctx0, dfs0, diffRep, graph)) =>
          val hasSameRep = testRepresentationPreserving(
            (source.id, target.id), graph, diffRep
          )
          q"$hasSameRep"
      }
    }

    /** test if starting vertex corresponds to a different runtime rep.
      * CAUTION: not efficient; for testing only.
      */
    def testRepresentationPreserving(start: Vertex, graph0: Graph, diffRep: DiffRep):
        Boolean =
    {
      val graph = mkMultiGraph(graph0)
      val diff = applyExhaustively(diffRep)(propagateDiff(start, graph))
      ! diff(start)
    }
  }
}
