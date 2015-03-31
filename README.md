# CREG

First-**C**lass **Reg**ular Functors

by [Yufei Cai et al.][project]


#### Installation

1. Download and install [simple-build-tool][sbt].

2. Create a project directory with the following `build.sbt`:

    ```scala
    scalaVersion := "2.11.3"

    resolvers ++= Seq(
      Resolver.sonatypeRepo("releases"),
      Resolver.sonatypeRepo("snapshots")
    )

    libraryDependencies ++= Seq(
      "com.github.yfcai" %% "creg" % "0.1.2",
      compilerPlugin("org.scalamacros" % "paradise_2.11.3" % "2.1.0-M5")
    )
    ```


#### Usage example

Suppose there is a correct `build.sbt` in the current directory.

```scala
[demo]$ sbt
[info] Loading global plugins from $HOME/.sbt/0.13/plugins
[info] Set current project to demo (in build file:$HOME/demo/)
> console
[info] Updating {file:$HOME/demo/}demo...
[info] Resolving jline#jline;2.12 ...
[info] downloading https://oss.sonatype.org/content/repositories/releases/com/github/yfcai/creg_2.11/0.1.2/creg_2.11-0.1.2.jar ...
[info] 	[SUCCESSFUL ] com.github.yfcai#creg_2.11;0.1.2!creg_2.11.jar (1548ms)
[info] Done updating.
[info] Starting scala interpreter...
[info]
Welcome to Scala version 2.11.3 (Java HotSpot(TM) 64-Bit Server VM, Java 1.7.0_71).
Type in expressions to have them evaluated.
Type :help for more information.

scala> import creg._
import creg._

scala> @data def List[A] = Fix(L => ListT { Nil ; Cons(head = A, tail = L) })
import _root_.scala.language.higherKinds
import _root_.scala.language.implicitConversions
defined trait ListT
defined trait Nil
defined object Nil
defined class Cons
defined object Cons
defined object ListT
defined type alias List
defined type alias ListF

scala> val xs: List[Int] = coerce { Cons(1, Cons(2, Cons(3, Cons(4, Nil)))) }
xs: List[Int] = Roll(Cons(1,Roll(Cons(2,Roll(Cons(3,Roll(Cons(4,Roll(Nil)))))))))

scala> @functor def elemF[A] = Fix(L => ListT { Nil ; Cons(head = A, tail = L) })
elemF: creg.lib.traversable.Traversable{...}


scala> elemF(xs) map (_ * 2)
res0: elemF.Map[Int] = Roll(Cons(2,Roll(Cons(4,Roll(Cons(6,Roll(Cons(8,Roll(Nil)))))))))

scala> elemF(xs) reduce (0, _ + _)
res1: Int = 10
```


#### Documentation

The [documentation][doc] is a work in progress.


#### Navigation

There are various interesting usage [examples][main].
[Banana][banana] is a good starting point for innocent people,
and [Tyranny][tyranny] is a good starting point for those who have
access to our unpublished super secret manuscript.

The interfaces [Functor][functor], [Applicative][appl],
[Traversable][trav] and [Fix][fix] are generated. They can be
found in the folder for [managed source files][managed].

#### Plan

3. Document [examples][main] better.

4. Document [implementation][macros] better.

5. Improve error messages.


[doc]:      http://yfcai.github.io/CREG/macros/target/scala-2.11/api/index.html#creg.package
[sbt]:      http://www.scala-sbt.org/
[tyranny]:  example/TyrannyOfTheDominantFunctor.scala
[main]:     example/
[project]:  http://ps.informatik.uni-tuebingen.de/research/functors/
[appl]:     generator/target/scala-2.11/src_managed/test/Applicative.scala
[banana]:   example/Banana.scala
[fix]:      generator/target/scala-2.11/src_managed/test/Fix.scala
[functor]:  generator/target/scala-2.11/src_managed/test/Functors.scala
[macros]:   macros
[managed]:  generator/target/scala-2.11/src_managed/test
[trav]:     generator/target/scala-2.11/src_managed/test/Traversable.scala
