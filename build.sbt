val sversion = "2.11.1"

resolvers ++= List("releases").map(Resolver.sonatypeRepo)


// creg macro

lazy val creg = project in file("creg") settings (
  scalaVersion := sversion,
  scalacOptions := Seq("-deprecation", "-feature", "-unchecked", "-Xlint"),
  libraryDependencies ++= List(
    "commons-codec" % "commons-codec" % "1.9",
    "org.scala-lang" % "scala-reflect" % sversion,
    "org.scala-lang" % "scala-compiler" % sversion, // for scala.tools.reflect.ToolBoxError
    compilerPlugin("org.scalamacros" % s"paradise_$sversion" % "2.0.0") // caution: must be a compilerPlugin!
  )
)


// tests

lazy val test = project in file(".") dependsOn creg settings (
  fork := true, // otherwise cannot deserialize
  scalaVersion := sversion,
  scalaSource in Compile := new File(baseDirectory.value, "main"),
  scalaSource in Test := new File(baseDirectory.value, "test"),
  autoCompilerPlugins := true,
  scalacOptions := Seq("-deprecation", "-feature", "-unchecked", "-Xlint"),
  libraryDependencies ++= List(
    "commons-codec" % "commons-codec" % "1.9",
    "org.scalatest" % "scalatest_2.11" % "2.1.4",
    "org.scala-lang" % "scala-compiler" % sversion, // for scala.tools.reflect.ToolBoxError
    compilerPlugin("org.scalamacros" % s"paradise_$sversion" % "2.0.0") // caution: must be a compilerPlugin!
  )
)
