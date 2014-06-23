val sversion = "2.11.1"

resolvers ++= List("releases").map(Resolver.sonatypeRepo)


// macro

lazy val macro = project in file("macro") settings (
  scalaVersion := sversion,
  scalacOptions := Seq("-deprecation", "-feature", "-unchecked", "-Xlint"),
  libraryDependencies ++= List(
    "org.scala-lang" % "scala-reflect" % sversion,
    //"org.scala-lang" % "scala-compiler" % sversion, // uncomment this for scala.tools.reflect.ToolBox
    compilerPlugin("org.scalamacros" % s"paradise_$sversion" % "2.0.0") // caution: must be a compilerPlugin!
  )
)


// root

lazy val root = project in file(".") dependsOn macro settings (
  scalaVersion := sversion,
  scalaSource in Compile := new File(baseDirectory.value, "empty"),
  scalaSource in Test := new File(baseDirectory.value, "test"),
  autoCompilerPlugins := true,
  scalacOptions := Seq("-deprecation", "-feature", "-unchecked", "-Xlint"),
  libraryDependencies ++= List(
    "org.scalatest" % "scalatest_2.11" % "2.1.4",
    compilerPlugin("org.scalamacros" % s"paradise_$sversion" % "2.0.0") // caution: must be a compilerPlugin!
  )
)
