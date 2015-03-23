val sversion = "2.11.1"

val options = Seq("-deprecation", "-feature", "-unchecked", "-Xlint")

resolvers ++= List("releases").map(Resolver.sonatypeRepo)


// generate Traversable, Traversable2, Traversable3, etc

lazy val generator =
  project in file("generator") settings (
  Seq(
    scalaVersion := sversion,
    scalacOptions := options,
    sourceManaged in Compile := new java.io.File("/var/tmp")
  ) ++ generationSettings: _*
)

// creg macros

val hardcodedGeneratedSourceDirectory: String =
  "../traversableGeneration/target/scala-2.11/src_managed/test"

lazy val macros = (project in file("macros")).dependsOn(
  generator % "compile->test"
).settings(
  //managedSourceDirectories in Compile <++=
  //  generator.configurations.find(_.name == "")
  scalaVersion := sversion,
  scalacOptions := options,
  libraryDependencies ++= List(
    "commons-codec" % "commons-codec" % "1.9",
    "org.scala-lang" % "scala-reflect" % sversion,
    //
    // for scala.tools.reflect.ToolBoxError
    "org.scala-lang" % "scala-compiler" % sversion,
    //
    // caution: must be a compilerPlugin!
    compilerPlugin("org.scalamacros" % s"paradise_$sversion" % "2.0.0") 
  ),
  //
  // directory of generated source.
  // anything better than this hard-coded path?
  unmanagedSourceDirectories in Compile <+= baseDirectory {
    _ / hardcodedGeneratedSourceDirectory
  }
)


// tests

lazy val test = project in file(".") dependsOn macros settings (
  fork := true, // otherwise cannot deserialize
  scalaVersion := sversion,
  scalaSource in Compile := new File(baseDirectory.value, "example"),
  scalaSource in Test := new File(baseDirectory.value, "test"),
  autoCompilerPlugins := true,
  scalacOptions := options,
  libraryDependencies ++= List(
    "commons-codec" % "commons-codec" % "1.9",
    "org.scalatest" % "scalatest_2.11" % "2.1.4",
    "org.scala-lang" % "scala-compiler" % sversion, // for scala.tools.reflect.ToolBoxError
    compilerPlugin("org.scalamacros" % s"paradise_$sversion" % "2.0.0") // caution: must be a compilerPlugin!
  )
)
