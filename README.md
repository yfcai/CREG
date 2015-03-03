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


#### Navigation

There are various interesting usage examples in the [main folder][main].
[Banana][banana] is a good starting point for innocent people,
and [Tyranny][tyranny] is a good starting point for those who have
access to our unpublished super secret manuscript.

#### Plan

1. Create package object `creg.package` so that users can import
   everything in one go.

2. Upload a jar to some binary distribution service so that
   installation would not traumatize innocent people.

3. Document examples in [main][main] better.

4. Document [implementation][macros] better.

5. Improve error messages.


[sbt]:      http://www.scala-sbt.org/
[tyranny]:  main/TyrannyOfTheDominantFunctor.scala
[main]:     main/
[project]:  http://ps.informatik.uni-tuebingen.de/research/functors/
[banana]:   main/Banana.scala
[macros]:   macros
