/** Type coercion a la TAPL (Pierce) §21.9 */

package nominal
package lib

import scala.language.higherKinds
import scala.language.implicitConversions
import scala.language.experimental.macros

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

        case Some((context, dfs)) =>
          val TheWitness = TermName(c freshName "TheWitness")
          val f = context((actual.id, expected.id))
          q"""{
            object $TheWitness { ..$dfs }
            $TheWitness . $f($arg)
          }"""
      }
    }

  // coercion algorithm
  def witness(c: Context)(
    context: Map[(String, String), c.universe.TermName],
    source : Regular[c.Type],
    target : Regular[c.Type]):
      Option[(Map[(String, String), c.universe.TermName], Seq[c.Tree])] =
  {
    import c.universe._

    // pre-computed
    if (context.contains((source.id, target.id)))
      Some((context, Seq.empty))

    else {

      val f  = TermName(c.freshName("f"))
      val a0 = context.updated((source.id, target.id), f)

      def mkF(body: TermName => Tree): Tree = {
        val x = TermName(c freshName "x")
        q"def $f($x: ${source.tpe}): ${target.tpe} = ${body(x)}"
      }

      // source <: target
      if (isScalaSubtype(c)(source.tpe, target.tpe))
        Some((a0, Seq(mkF { x => q"$x" })))

      else inferImplicitView(c)(source.tpe, target.tpe) match {
        // source <% target
        case Some(view) =>
          Some((a0, Seq(mkF { x => q"$view($x)" })))

        case None =>

          (source, target) match {
            case (source @ RegularFix(id, srcTpe, _), _) =>
              for {
                (a1, dfs) <- witness(c)(a0, source.unroll, target)
                f1 = a1((source.body.id, target.id))
                newDfn = mkF(x => q"$f1($x.unroll)")
              } yield (a1, newDfn +: dfs)

            case (_, target @ RegularFix(id, tgtTpe, _)) =>
              for {
                (a1, dfs) <- witness(c)(a0, source, target.unroll)
                f1 = a1((source.id, target.body.id))
                newDfn = mkF { x =>
                  q"${getRoll(c)}[..${tgtTpe.typeArgs}]($f1($x))"
                }
              }
              yield (a1, newDfn +: dfs)

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
                    (an, dfs) <- args.foldLeft[Option[
                      (Map[(String, String), c.universe.TermName], Seq[c.Tree])
                    ]]( Some((a0, Seq.empty)) ) {
                      case (maybe, (s_i, t_i)) =>
                        for {
                          (a_prev, dfs_prev) <- maybe
                          (a_i, dfs_i) <- witness(c)(a_prev, s_i, t_i)
                        }
                        yield (a_i, dfs_prev ++ dfs_i)
                    }

                    fs = args.map {
                      case (srcChild, tgtChild) =>
                        an((srcChild.id, tgtChild.id))
                    }

                    newDfs = mkF { x => q"$functor[..${srcArgs.map(_.tpe)}]($x).map(..$fs)" }
                  }
                  yield (an, newDfs +: dfs)
              }

            // converting records to variants
            case (_, RegularFun(tgtId, tgtTpe, tgtArgs))
                if isRecordOfVariant(c)(source.tpe, tgtTpe) =>

              val results = tgtArgs.flatMap { candidate =>
                for {
                  (ctx, dfs) <- witness(c)(a0, source, candidate)
                }
                yield (candidate, ctx, dfs)
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
                val (candidate, a1, dfs) = results.head
                val f1 = a1((source.id, candidate.id))
                Some((a1, mkF(x => q"$f1($x)") +: dfs))
              }

            case _ =>
              None
          }
      }
    }
  }

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
}
