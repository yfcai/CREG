package traversableGeneration

import java.io.{ File, FileWriter }

object Main {
  def main(args: Array[String]) {
    val Array(base, classOutput) = args take 2 map (new File(_))

    deleteIrrelevantFiles(base)

    /**
      */
    if (shouldGenerate(base))
      generateAndExport(base)
    else
      exportOnly(base)
  }

  val maxArity: Int = 22 // like Scala tuples

  val filesToGenerate: List[(String, (File, String) => Unit)] = List(
    ("Fix.scala"        , exportFix),
    ("Monad.scala"      , exportMonad),
    ("Functors.scala"   , exportFunctors),
    ("Applicative.scala", exportApplicative),
    ("Traversable.scala", exportTraversables),
    ("Foldable.scala"   , exportFoldable)
  )

  // regenerate files and export their paths
  def generateAndExport(base: File) = {
    Console.err.println(s"Generating sources:")
    filesToGenerate.foreach {
      case (filename, generator) => generator(base, filename)
    }
  }

  // export paths only, do not generate anything
  def exportOnly(base: File) = {
    Console.err.println(s"Keeping old sources:")
    filesToGenerate.foreach {
      case (filename, generator) => export(new File(base, filename).getCanonicalPath)
    }
  }

  // test whether some generated source is older than this file.
  // this hack combined with setting the generated dir as "unmanaged"
  // keeps `sbt` from frivolous recompilations and also from looping
  // on `~test`
  def shouldGenerate(base: File): Boolean = {
    val thisTimestamp       = new File(__FILE__).lastModified
    val generatedTimestamps = filesToGenerate.map {
      case (filename, generator) =>
        val file = new File(base, filename)
        if (file.exists) file.lastModified else -1
    }
    if (generatedTimestamps.isEmpty)
      false // no file to generate anyway
    else
      thisTimestamp >= generatedTimestamps.min
  }

  def deleteIrrelevantFiles(base: File) {
    if (base.exists) {
      val actual     = Set(base.list: _*)
      val expected   = Set(filesToGenerate.map(_._1): _*)
      val irrelevant = actual -- expected
      if (irrelevant.nonEmpty)
        Console.err.println(s"Deleting irrelevant files:")
      irrelevant.foreach { file =>
        Console.err.println("- " + file)
        new File(base, file).delete()
      }
    }
    else
      base.mkdirs()
  }

  def __FILE__ : String =
    new Throwable().getStackTrace().head.getFileName()

  // stdout is exported as paths
  def export(path: String): Unit =
    Console.out.println(path)

  // stderr is echoed as [info] in sbt console
  def info(message: String): Unit =
    Console.err.println(message)

  // generate fix/monad/applicative

  def exportFix(base: File, filename: String) =
    exportFunctorLike(base, filename, _ => fixSource)

  def exportMonad(base: File, filename: String) =
    exportFunctorLike(base, filename, _ => monadSource)

  def exportApplicative(base: File, filename: String) =
    exportFunctorLike(base, filename, _ => applicativeSource)

  def exportFoldable(base: File, filename: String) =
    exportFunctorLike(base, filename, _ => foldableSource)

  // generate Functor, Functor2, ...
  def exportFunctors(base: File, filename: String) =
    exportFunctorLike(base, filename, generateFunctors)

  // generate Traversable, Traversable2, ...
  def exportTraversables(base: File, filename: String) =
    exportFunctorLike(base, filename, generateTraversables)

  def exportFunctorLike(
    base: File, filename: String, generator: Int => String
  ) {
    val path = new File(base, filename).getCanonicalPath
    val file = new FileWriter(path)
    file.write(generator(22))
    file.close
    export(path)
  }

  def mkABC(alphabet: String): Int => String = {
    val n = alphabet.length
    new (Int => String) {
      def apply(i: Int): String =
        if (i < n)
          alphabet.substring(i, i + 1)
        else
          apply(i / n) + apply(i % n)
    }
  }

  val alphUpper   = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
  val alphLower   = alphUpper.toLowerCase
  val applicative = "_G" // must be disjoint from alphabets
  val mA          = "_m" // must be disjoint from alphabets


  val ABC = mkABC(alphUpper)
  val xyz = mkABC(alphLower)

  def generateFunctors(maxArity: Int): String = {
    val individualFunctors =
      Range.inclusive(1, maxArity).map(generateFunctorTrait).mkString("\n")

    val functorsIndex = generateFunctorsTableOfContents(maxArity)

    s"""|package creg
        |package lib
        |package functor
        |import language.higherKinds
        |
        |$functorsIndex
        |$individualFunctors
        |""".stripMargin
  }

  def generateFunctorsTableOfContents(maxArity: Int): String = {
    val synonyms =
      Range.inclusive(1, maxArity).map(generateFunctorSynonym).mkString("\n")

    s"""|trait Index {
        |$synonyms
        |}
        |""".stripMargin
  }

  def generateFunctorSynonym(n: Int): String = {
    val functor = mkFunctorLike("Functor", n)
    s"  type $functor = functor.$functor"
  }

  def generateTraversableSynonym(n: Int): String = {
    val traversable = mkFunctorLike("Traversable", n)
    s"  type $traversable = traversable.$traversable"
  }

  def generateTraversables(maxArity: Int): String = {
    val individualTraversables =
      Range.inclusive(1, maxArity).
        map(generateTraversableTraits).mkString("\n")

    val synonyms =
      Range.inclusive(1, maxArity).map(generateTraversableSynonym).mkString("\n")

    s"""|package creg
        |package lib
        |package traversable
        |
        |import language.higherKinds
        |
        |trait Index {
        |$synonyms
        |}
        |
        |$traversable0Source
        |$individualTraversables
        |""".stripMargin
  }

  def generateTraversableTraits(n: Int): String = {
    val functor = mkFunctorLike("functor.Functor", n)
    val endofun = mkFunctorLike("Traversable", n)
    val bounded = mkFunctorLike("TraversableBounded", n)
    s"""|trait $endofun extends $functor with $bounded {${extraSource(n, extraTraversableHeaderSource)}
        |  ${vacuousSubcategoryBounds(n)}
        |  type Map[${covariantParams(n)}]
        |${extraSource(n, extraEndofunctorMethodSource)}}
        |
        |trait $bounded {
        |  ${abstractSubcategoryBounds(n)}
        |  type Map[${boundedCovariantParams(n)}]
        |  type Range = Map[${(0 until n).map("Cat" + _).comma}]
        |  ${traverseDef(n)}
        |  ${traverseFmapDef(n)} = ${traverseFmapImpl(n)}
        |  ${viewDef(n)}
        |  ${extraSource(n, extraTraversableMethodSource)}
        |  ${viewClass(n, bounded)}
        |}
        |""".stripMargin
  }

  /** @param n arity of the functor trait */
  def generateFunctorTrait(n: Int): String = {
    val traitName = mkFunctorLike("Functor", n)
    s"""|trait $traitName {
        |  type Map[${covariantParams(n)}]
        |  ${fmapDef(n)}
        |}
        |""".stripMargin
  }

  def extraSource(n: Int, body: String): String =
    if (n == 1) body else ""

  def fmapDef(n: Int): String =
    s"def fmap[${fmapParams(n)}](${fmapArgs(n)}): ${fmapResult(n)}"

  def traverseFmapDef(n: Int): String =
    s"def fmap[${traverseParams(n)}](${fmapArgs(n)}): ${fmapResult(n)}"

  def traverseFmapImpl(n: Int): String =
    s"traverse[${fmapParams(n)}](applicative.Applicative.Identity)(${mkIdentifiers(n).comma})"

  def traverseDef(n: Int): String =
    s"def traverse[${traverseParams(n)}]($applicative : applicative.Applicative)" +
  s"(${traverseArgs(n)}): ${traverseResult(n)}"

  def viewDef(n: Int): String = {
    val params = mkTraverseParams(n)._1.comma
    val args   = mkUnzippedParams(n)._1.comma
    s"def apply[$params]($mA : ${traverseDomain(n)}): View[$args] = new View($mA)"
  }

  def functorViewClass(n: Int, functor: String): String = {
    ???
  }

  def viewClass(n: Int, bounded: String): String = {
    val (fromRaw, toRaw) = mkTraverseParams(n)
    val (from, to)       = (fromRaw.comma, toRaw.comma)
    val baseMap          = traverseDomain(n)
    val fs               = mkIdentifiers(n).comma
    s"""|class View[$from]($mA : ${traverseDomain(n)}) {
        |    def traverse[$to]($applicative : applicative.Applicative)(${traverseArgs(n)}):
        |        ${traverseCodomain(n)} =
        |      $bounded.this.traverse($applicative)($fs)($mA)
        |    def map[$to](${fmapArgs(n)}): ${fmapCodomain(n)} =
        |      $bounded.this.fmap($fs)($mA)
        |  ${extraSource(n, extraTraversableViewSource)}}""".stripMargin
  }

  def lessCat(i: Int): String = s" <: Cat$i"

  def mkCats(n: Int): Seq[String] =
    (0 until n).map("type Cat" + _)

  def abstractSubcategoryBounds(n: Int): String =
    mkCats(n).semicolon

  def vacuousSubcategoryBounds(n: Int): String =
    mkCats(n).map(_ + " = Any").semicolon

  def mkFunctorLike(base: String, arity: Int): String =
    if (arity == 1) base else base + arity

  def unfold[T](n: Int)(coalgebra: Int => T): List[T] = {
    def loop(i: Int): List[T] =
      if (i >= n)
        Nil
      else
        coalgebra(i) :: loop(i + 1)
    loop(0)
  }

  implicit class Commatize(xs: Seq[String]) {
    def comma     = xs mkString ","
    def semicolon = xs mkString ";"
  }

  def mkIdentifiers(n: Int): List[String] =
    unfold(n)(xyz)

  def mkParams(n: Int): List[String] =
    unfold(n)(ABC)

  def mkDoubleParams(n: Int): List[(String, String)] =
    unfold(n)(i => (ABC(2 * i), ABC(2 * i + 1)))

  def mkUnzippedParams(n: Int): (List[String], List[String]) =
    mkDoubleParams(n).unzip

  def covariantParams(n: Int): String = mkParams(n).map("+" + _).comma

  def boundedCovariantParams(n: Int): String =
    mkParams(n).zipWithIndex.map({
      case (param, i) => "+" + param + lessCat(i)
    }).comma

  def fmapParams(n: Int): String = {
    val (fromParams, toParams) = mkUnzippedParams(n)
      (fromParams ++ toParams).comma
  }

  def mkTraverseParams(n: Int): (List[String], List[String]) = {
    val cats = mkDoubleParams(n).zipWithIndex.map {
      case ((p1, p2), i) =>
        val cat = lessCat(i)
        (p1 + cat, p2 + cat)
    }
    cats.unzip
  }

  def traverseParams(n: Int): String = {
    val (fromParams, toParams) = mkTraverseParams(n)
      (fromParams ++ toParams).comma
  }

  def fmapCodomain(n: Int): String =
    s"Map[${mkUnzippedParams(n)._2.comma}]"

  def fmapResult(n: Int): String = {
    val (fromArgs, toArgs) = mkUnzippedParams(n)
    s"Map[${fromArgs.comma}] => Map[${toArgs.comma}]"
  }

  def traverseDomain(n: Int): String =
    s"Map[${mkUnzippedParams(n)._1.comma}]"

  def traverseCodomain(n: Int): String =
    s"$applicative.Map[Map[${mkUnzippedParams(n)._2.comma}]]"

  def traverseResult(n: Int): String =
    s"${traverseDomain(n)} => ${traverseCodomain(n)}"

  def fmapArgs(n: Int): String =
    mkArgs(n, _ + " => " + _)

  def traverseArgs(n: Int): String =
    mkArgs(n, _ + s" => $applicative.Map[" + _ + "]")

  def mkArgs(n: Int, mkTpe: (String, String) => String): String = {
    mkIdentifiers(n).zip(mkDoubleParams(n)).map({
      case (f, (domain, range)) => s"$f : ${mkTpe(domain, range)}"
    }).comma
  }

  def fixSource: String =
    """|package creg
       |package lib
       |package fix
       |
       |import language.higherKinds
       |
       |trait Index {
       |  type Fix[+F[+_]] = fix.Fix[F]
       |  val  Fix : fix.Fix.type  = fix.Fix
       |  val  Roll: fix.Roll.type = fix.Roll
       |}
       |
       |// much as I would like to make `Fix` path-dependent
       |// on some functor, we need the type param `F` for
       |// coercion. If there are too many levels of nested
       |// path-dependent types then scalac will gice up and
       |// refuese to tell us anything.
       |sealed trait Fix[+F[+_]] { def unroll: F[Fix[F]] }
       |
       |sealed case class Roll[+F[+_]](unroll: F[Fix[F]]) extends Fix[F]
       |
       |object Fix {
       |  // dummy class to help scalac figure out the expected result type
       |  // of an implicit conversion. it is less straightforward than
       |  // expected. here we use the collection.breakOut + CanBuildFrom
       |  // pattern.
       |  //
       |  // covariance of type parameter is not option.
       |  class TypeWitness[+T]
       |  object TypeWitness extends TypeWitness[Nothing] {
       |    implicit def get[T]: TypeWitness[T] = this
       |  }
       |
       |  // marker of variants and records
       |  // beware: because records extends variants, they will
       |  // be marked as variants, too.
       |  //
       |  // if x is a subtype of both Record and Variant, then it is a record
       |  // if x is a subtype of Variant, then it is a variant
       |  // if x is a subtype of neither, then it is not a datatype
       |  trait RecordOrVariant
       |  trait Variant extends RecordOrVariant
       |  trait Record  extends RecordOrVariant
       |}
       |""".stripMargin

  def applicativeSource: String =
    """|package creg
       |package lib
       |package applicative
       |
       |trait Index {
       |  type Applicative = applicative.Applicative
       |  val  Applicative: applicative.Applicative.type = applicative.Applicative
       |}
       |
       |import language.higherKinds
       |
       |trait Applicative extends functor.Functor { self =>
       |  // Applicative functors are only defined on the entire Scala category.
       |  // It's hard to define applicative functors on subcategories because
       |  // a subcategory may not have exponentials (used in `call`).
       |  type Map[+X]
       |  def pure[A](x: A): Map[A]
       |  def call[A, B](f: Map[A => B], x: Map[A]): Map[B]
       |
       |  def fmap[A, B](f: A => B): Map[A] => Map[B] = x => call(pure(f), x)
       |
       |  def roll[F[+_]](x: Map[F[fix.Fix[F]]]): Map[fix.Fix[F]] =
       |    call(
       |      pure[F[fix.Fix[F]] => fix.Fix[F]](y => fix.Roll(y)),
       |      x)
       |
       |  def compose(that: Applicative):
       |      Applicative { type Map[+X] = self.Map[that.Map[X]] } =
       |    new Applicative {
       |      type Map[+X] = self.Map[that.Map[X]]
       |
       |      def pure[A](x: A): Map[A] = self.pure(that.pure(x))
       |
       |      def call[A, B](f: Map[A => B], x: Map[A]): Map[B] =
       |        self.call(self.call(
       |          self pure {
       |            (f: that.Map[A => B]) => (x: that.Map[A]) => that.call(f, x)
       |          },
       |          f),
       |          x)
       |    }
       |}
       |
       |// specific applicative functors
       |// beware SI-2089
       |object Applicative {
       |  type Of[F[+_]] = Applicative { type Map[+X] = F[X] }
       |
       |  // identity applicative functor
       |  type Identity[+X] = X
       |
       |  implicit object Identity extends Applicative {
       |    type Map[+X] = Identity[X]
       |    def pure[A](x: A): A = x
       |    def call[A, B](f: A => B, x: A): B = f(x)
       |  }
       |
       |  // constant applicative functor
       |  type Const[A] = { type λ[+X] = A }
       |
       |  def Const[A](default: A, combine: (A, A) => A): Applicative { type Map[+X] = A } =
       |    new Applicative {
       |      type Map[+X] = A
       |      def pure[X](x: X): A = default
       |      def call[X, Y](f: A, x: A): A = combine(f, x)
       |    }
       |
       |  def FreeMonoid[A]: Applicative { type Map[+X] = List[A] } =
       |    Const[List[A]](Nil, _ ++ _)
       |
       |  def Maybe[A]: Applicative { type Map[+X] = Option[X] } =
       |    new Applicative {
       |      type Map[+A] = Option[A]
       |      def pure[A](x: A): Option[A] = Some(x)
       |      def call[A, B](f: Option[A => B], x: Option[A]): Option[B] = (f, x) match {
       |        case (Some(f), Some(x)) => Some(f(x))
       |        case _ => None
       |      }
       |    }
       |}
       |""".stripMargin

  def monadSource: String =
    """|package creg
       |
       |import lib._
       |
       |import language.higherKinds
       |
       |object Monad {
       |  object State {
       |    type State[S, +A] = S => (A, S)
       |
       |    private[this] // necessary to make inner type λ covariant
       |    type CurriedState[S] = {
       |      type λ[+A] = State[S, A]
       |    }
       |
       |    implicit def stateMonad[S] = new MonadWithBind {
       |      type Map[+A] = CurriedState[S]#λ[A]
       |      def pure[A](x: A): Map[A] = s => (x, s)
       |      def bind[A, B](m: Map[A], f: A => Map[B]): Map[B] =
       |        s0 => m(s0) match { case (a, s1) => f(a)(s1) }
       |    }
       |
       |    implicit class CurriedStateMonadView[A, S](x: CurriedState[S]#λ[A])
       |        extends Monad.View[CurriedState[S]#λ, A](x)
       |
       |    def readState [S]: State[S, S]                 = s => (s, s)
       |    def writeState[S](s: S): State[S, Unit]        = _ => ((), s)
       |    def evalState [S, A](sm: State[S, A], s: S): A = sm(s)._1
       |  }
       |
       |  // for-comprehension support for monads
       |  class View[M[+_]: Monad.ic, A](x: M[A]) {
       |    val monad = implicitly[Monad.ic[M]]
       |    import monad._
       |    def flatMap[B](f: A => M[B]): M[B] = bind(x, f)
       |    def map[B](f: A => B): M[B] = bind(x, pure[B] _ compose f)
       |  }
       |
       |  // e. g.,  Monad.ic[Identity]   where   type Identity[+A] = A
       |  type ic[M[+_]] = Monad { type Map[+X] = M[X] }
       |}
       |
       |trait Monad extends applicative.Applicative {
       |  type Map[+X]
       |
       |  // inherited from applicative
       |  def pure[A](x: A): Map[A]
       |  def call[A, B](f: Map[A => B], x: Map[A]): Map[B]
       |
       |  // idiosyncratic to monad
       |  def join[A](x: Map[Map[A]]): Map[A]
       |  def bind[A, B](m: Map[A], f: A => Map[B]): Map[B]
       |}
       |
       |trait MonadWithBind extends Monad {
       |  def pure[A](x: A): Map[A]
       |  def bind[A, B](m: Map[A], f: A => Map[B]): Map[B]
       |
       |  def call[A, B](f: Map[A => B], x: Map[A]): Map[B] =
       |    bind(f, (f: A => B) => bind(x, (x: A) => pure(f(x))))
       |
       |  def join[A](x: Map[Map[A]]): Map[A] =
       |    bind(x, (y: Map[A]) => y)
       |}
       |""".stripMargin

  def traversable0Source: String =
    """|trait Traversable0 {
       |  type Map >: this.type
       |  type Range = Map
       |  def traverse(G: applicative.Applicative)(): Map => G.Map[Map] = G pure _
       |}
       |""".stripMargin

  def extraTraversableHeaderSource: String =
    "  thisFunctor =>"

  def extraEndofunctorMethodSource: String =
    """|
       |  def compose(that: Traversable) =
       |    new Traversable {
       |      type Map[+A] = thisFunctor.Map[that.Map[A]]
       |      def traverse[A, B](G: applicative.Applicative)(f: A => G.Map[B]):
       |          this.Map[A] => G.Map[this.Map[B]] =
       |        thisFunctor.traverse[that.Map[A], that.Map[B]](G)(that.traverse(G)(f))
       |    }
       |""".stripMargin

  def extraTraversableMethodSource: String =
    """|def mapReduce[A <: Cat0, B <: Cat0](f: A => B)(
       |    default: B, combine: (B, B) => B):
       |      Map[A] => B =
       |    traverse[A, B](applicative.Applicative.Const(default, combine))(f)
       |
       |  def crush[A <: Cat0](z: A, op: (A, A) => A): Map[A] => A = mapReduce(identity[A])(z, op)
       |
       |  def toList[A <: Cat0]: Map[A] => List[A] =
       |    traverse(applicative.Applicative.FreeMonoid[A])((x: A) => List(x))
       |
       |  def fromList[A <: Cat0](children: List[A]): Map[A] => Map[A] =
       |    t => {
       |      import Monad.State._
       |      evalState(
       |        traverse(stateMonad[List[A]])({
       |          (oldChild: A) => for {
       |            children <- readState
       |            _        <- writeState(children.tail)
       |          }
       |          yield children.head
       |        })(t),
       |        children
       |      )
       |    }
       |""".stripMargin

  def extraTraversableViewSource: String =
    """|    // McBride & Paterson's reduce
       |    def reduce(monoidId: A, monoidOp: (A, A) => A): A =
       |      mapReduce(identity)(monoidId, monoidOp)
       |
       |    def mapReduce[B <: Cat0](f: A => B)(monoidId: B, monoidOp: (B, B) => B): B =
       |      traverse(applicative.Applicative.Const(monoidId, monoidOp))(f)""".stripMargin

  // TODO: repackage
  def foldableSource: String =
    """|package creg
       |package lib
       |package foldable
       |
       |import language.higherKinds
       |
       |trait Index {
       |  type Foldable[F[+_]] = foldable.Foldable[F]
       |}
       |
       |// constructor can't be path-dependent. this won't work:
       |//
       |//   class Foldable(F: TraversableBounded.Endofunctor)(t: fix.Fix[F.Map]) { ... }
       |//
       |// implicit argument gives us at least the option not to write
       |//
       |//   new Foldable[TermF](t)(termF)
       |//
       |class Foldable[F[+_]](term: fix.Fix[F])(implicit F: traversable.Traversable { type Map[+A] = F[A] }) {
       |  def fold[T](f: F[T] => T): T = {
       |    object cata extends (fix.Fix[F] => T) {
       |      def apply(x: fix.Fix[F]): T = f(F(x.unroll) map this)
       |    }
       |    cata(term)
       |  }
       |}
       |""".stripMargin
}
