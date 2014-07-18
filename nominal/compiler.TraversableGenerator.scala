package nominal
package compiler

/** Generate code for the pattern functor only
  * To test the waters before generating for arbitrary functors
  */

import scala.reflect.macros.blackbox.Context

import DatatypeRepresentation._

/** generate 'new Traversable { blah blah blah }'
  *
  * @param functor the functor whose traversable instance is to be generated
  * @param subcats @see generateSubcategories
  */
trait TraversableGenerator extends SynonymGenerator {

  // only generate 'new TraversableN { ... }'
  // leave the wrapping of generics to someone else
  def generateTraversable(c: Context)(functor: DataConstructor, subcats: Map[Name, Datatype]): c.Tree =
    newTraversable(c)(functor.arity, generateTraversableBody(c)(functor, subcats))

  def generateTraversableBody(c: Context)(functor: DataConstructor, subcats: Map[Name, Datatype]): Many[c.Tree] = {
    // type Cat1 = Any; type Cat2 = Abs[_, _]
    val subcategories = generateSubcategories(c)(functor, subcats)
    val mapSynonym = generateBoundedSynonym(c)(mappingOnObjects, functor, subcats)
    val defTraverse = generateDefTraverse(c)(functor, subcats)
    val imports = scalaLanguageFeatureImports(c)
    imports ++ subcategories :+ mapSynonym :+ defTraverse
  }

  def mappingOnObjects: String = "Map"

  def applicativeEndofunctor(c: Context)(f: c.TypeName): c.Tree = {
    import c.universe._
    val q"??? : $tpe" = q"??? : _root_.nominal.lib.Applicative.Endofunctor[$f]"
    tpe
  }

  def fullyQualifiedTraversableTrait: String = "_root_.nominal.lib.Traversable"

  def newTraversable(c: Context)(arity: Int, body: Many[c.Tree]): c.Tree = {
    import c.universe._
    require(arity >= 1 /* && arity <= max N such that TraversableN exists */)
    val q"new $traversableN" = c.parse(s"new $fullyQualifiedTraversableTrait${if (arity == 1) "" else arity.toString }")
    q"new $traversableN { ..$body }"
  }

  /** type Cat1 = Any; type Cat2 = Abs[_, _]
    *
    * @param subcats mapping each param name to the subcategory whose objects the param can be bound to
    *                if a mapping doesn't exist, then that param can bind to any scala type
    */
  def generateSubcategories(c: Context)(functor: DataConstructor, subcats: Map[Name, Datatype]): Many[c.Tree] = {
    import c.universe._
    functor.params.zipWithIndex.map {
      case (Param(name, _), i) =>
        val catName = if (functor.params.size == 1) "Cat" else s"Cat${i + 1}"
        if (subcats contains name)
          generateConcreteSynonym(c)(catName, subcats(name))
        else
          c parse s"type $catName = Any"
    }
  }

  /** def traverse[F[_]: IsApplicative, A <: Cat, B <: Cat](f: A => F[B], t0: Map[A]): F[Map[B]]
    */
  def generateDefTraverse(c: Context)(functor: DataConstructor, subcats: Map[Name, Datatype]): c.Tree = {
    import c.universe._
    // type parameters of .traverse
    val tF: TypeName = TypeName(c freshName "F")
    val tA: Many[TypeName] = functor.params.map(_ => TypeName(c freshName "A"))
    val tB: Many[TypeName] = functor.params.map(_ => TypeName(c freshName "B"))
    val q"trait Trait[$typeDefF]" = q"trait Trait[$tF[_]]"
    val unmangledTypeNames =
      Map((tA, functor.params).zipped.map({ case (a, p) => (a.toString, p.name) }): _*) ++
        (tB, functor.params).zipped.map({ case (b, p) => (b.toString, p.name) })
    val typeDefs: Many[TypeDef] =
      typeDefF +: mkBoundedTypeDefs(c)(
        (tA ++ tB) map (Param invariant _.toString),
        unmangledTypeNames flatMap {
          case (mangled, param) if subcats contains param => Some((mangled, subcats(param)))
          case _ => None
        })

    // functions A => F[B], C => F[D], etc.
    val functions: Many[TermName] = functor.params.map(param => TermName(c freshName "f"))
    val functionTypes: Many[Tree] = (tA, tB).zipped.map {
      case (a, b) =>
        val q"??? : $functionType" = q"??? : ($a => $tF[$b])"
        functionType
    }

    // mA: Map[A, C, ...]
    val mA: TermName = TermName(c freshName "mA")
    val mapping: TypeName = TypeName(mappingOnObjects)
    val q"??? : $mAType" = q"??? : $mapping[..$tA]"

    // F[Map[B, D, ...]]
    val q"??? : $resultType" = q"??? : $tF[$mapping[..$tB]]"

    // (f: A => F[B], g: C => F[D], ..., mA: Map[A, C, ...])
    val explicitParams = mkValDefs(c)(functions :+ mA, functionTypes :+ mAType)

    // applicative: Applicative.Endofunctor[F]
    val applicative: TermName = TermName(c freshName "applicative")
    val q"??? : $applicativeType" = q"??? : ${applicativeEndofunctor(c)(tF)}"

    // mapping type params to corresponding function calls
    val env: Map[DatatypeRepresentation.Name, Tree => Tree] =
      Map(
        (functor.params, functions).zipped.map {
          case (param, function) =>
            (param.name, (x: c.Tree) => q"$function($x)")
        } : _*)

    // recursive call to traverse
    val recursiveCall: Tree => Tree =
      x => q"traverse(..${functions.map(f => q"$f") :+ x})"

    val body: Tree = generateDefTraverseBody(c)(q"$mA", functor.body, env, applicative, recursiveCall)

    val result = q"def traverse[..$typeDefs](..$explicitParams)(implicit $applicative : $applicativeType): $resultType = $body"

    println(s"\n$result\n")

    result
  }

  def mkValDef(c: Context)(termName: c.TermName, tpe: c.Tree): c.universe.ValDef = {
    import c.universe._
    val methodIn = TermName(c freshName "method")
    val q"def $methodOut($valDef)" = q"def $methodIn($termName : $tpe)"
    valDef
  }

  def mkValDefs(c: Context)(names: Many[c.TermName], types: Many[c.Tree]): Many[c.universe.ValDef] =
    (names, types).zipped.map { case (name, tpe) => mkValDef(c)(name, tpe) }

  /** body of def traverse[...](...)(...)
    *
    * @param mA          name of Map[A..]
    * @param datatype    structure of Map[A..]
    * @param env         mapping names to functions: beware name capturing!
    * @param applicative the name of the Applicative.Endofunctor instance
    */
  def generateDefTraverseBody(c: Context)(
    mA: c.Tree, datatype: Datatype,
    env: Map[DatatypeRepresentation.Name, c.Tree => c.Tree],
    applicative: c.TermName,
    recursiveCall: c.Tree => c.Tree):
      c.Tree =
  {
    import c.universe._

    datatype match {
      case TypeVar(x) =>
        if (env contains x)
          q"${env(x)(mA)}"
        else {
          val tpe = meaning(c)(datatype)
          q"$applicative.pure[$tpe]($mA)"
        }

      case FixedPoint(x, body) =>
        val unrolled = q"$mA.unroll"
        val newEnv = env.updated(x, recursiveCall) // takes care of capture avoidance for free
        generateDefTraverseBody(c)(unrolled, body, newEnv, applicative, recursiveCall)

      case Variant(header, cases) =>
        if (cases.isEmpty)
          c parse s"""_root_.scala.sys error "instance of empty variant $header""""
        else {
          // for now, require subfields of variants be records
          // if they are not, then they should be reconstructed as records
          // with type reification.
          q"???"
        }

      case Record(name, fields) =>

        val testing = q"x match { case A => c }"
        println(s"\n$testing")
        println(showRaw(testing) + "\n")
        /*
         // empty record, case object variant case, named unit...
         x match {
           case A => c
         }
         Match(
           Ident(TermName("x")),
           List(
             CaseDef(Ident(TermName("A")), EmptyTree, Ident(TermName("c")))
           )
         )

         // records with fields
         x match {
           case A((b @ _)) => c
         }
         Match(
           Ident(TermName("x")),
           List(
             CaseDef(
               Apply(Ident(TermName("A")), List(Bind(TermName("b"), Ident(termNames.WILDCARD)))),
               EmptyTree,
               Ident(TermName("c"))
             )
           )
         )

         // catch-all match. less relevant.
         x match {
           case (y @ _) => z
         }
         Match(
           Ident(TermName("x")),
           List(
             CaseDef(Bind(TermName("y"), Ident(termNames.WILDCARD)), EmptyTree, Ident(TermName("z")))
           )
         )
         */

        // yay! CaseDef is a tree!
        CaseDef(Bind(TermName("y"), Ident(termNames.WILDCARD)), EmptyTree, Ident(TermName("z"))): Tree
        q"???" // still to do

      case Reader(domain, range) =>
        // by function composition, can build `domain => F[ σ(range) ]`.
        // want F[ σ(domain => range) ] = F[ domain => σ(range) ].
        // this looks as if it requries F to be more than applicative.
        ???

      case Intersect(lhs, rhs) =>
        // not sure what to do in this case
        ???
    }
  }

  def scalaLanguageFeatureImports(c: Context): Many[c.Tree] = {
    import c.universe._
    Many(
        q"import _root_.scala.language.higherKinds",
        q"import _root_.scala.language.implicitConversions")
  }
}

object TraversableGenerator {
  object Tests extends TraversableGenerator with util.AssertEqual with util.ExpectCompilerError {
    import scala.language.experimental.macros
    import scala.annotation.StaticAnnotation

    val ConstInt =
      DataConstructor(Many(Param covariant "X"), TypeVar("Int"))

    val Identity =
      DataConstructor(Many(Param covariant "X"), TypeVar("X"))

    val Product =
      DataConstructor(Many(Param covariant "X", Param covariant "Y"),
        Record("Tuple2", Many(Field("_1", TypeVar("X")), Field("_2", TypeVar("Y")))))


    // test generation of `type Cat = ...`
    class c123 extends StaticAnnotation { def macroTransform(annottees: Any*): Any = macro Impl.c123 }

    // failed attempt to assert that C2.Map[Boolean] does not conform to declared bounds
    // because c.typecheck does not detect this error
    def c2MapError: String = macro Impl.c2MapError

    object Impl {
      // constant functor on everything
      def c1(c: Context) = {
        import c.universe._
        q"""object C1 extends nominal.lib.Traversable {
          ..${generateTraversableBody(c)(ConstInt, Map.empty)}
        }"""
      }

      // identity functor on integers
      def c2(c: Context) = {
        import c.universe._
        q"""object C2 extends nominal.lib.Traversable {
          ..${generateTraversableBody(c)(Identity, Map("X" -> TypeVar("Int")))}
        }"""
      }

      // product functor with 2nd component limited to Either[Int, Boolean]
      def c3(c: Context) = {
        import c.universe._
        q"""object C3 extends nominal.lib.Traversable2 {
          ..${generateTraversableBody(c)(Product, Map("Y" -> TypeVar("Either[Int, Boolean]"))) }
        }"""
      }

      def c123(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
        import c.universe._
        c.Expr(q"..${c1(c) :: c2(c) :: c3(c) :: Nil}")
      }

      // must be called with a context where c123 is already expanded
      def c2MapError(c: Context): c.Expr[String] = {
        import c.universe._
        expectCompilerError(c)(q"??? : C2.Map[Boolean]")
      }
    }

  }
}
