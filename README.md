# CREG

First-**C**lass **Reg**ular Functors

by [Yufei Cai et al.][project]


#### Installation

1. Download and install [simple-build-tool][sbt].
2. Run `sbt` here. Make sure the computer is connected to the internet.
3. Type `compile` into the console to build everything.
   It will take 2--5 minutes the first time around.
4. Type `run` into the console to execute [main class][tyranny].
5. Type `test` into the console to screen for errors.


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

2. Upload a jar to some binary distribution service so that
   installation would not traumatize innocent people.

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
