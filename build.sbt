import SonatypeKeys._

val cregVersion = "0.1.2"

val sversion = "2.11.3"

val options = Seq("-deprecation", "-feature", "-unchecked",
  "-Xlint", "-Xlint:-type-parameter-shadow")

resolvers ++= List("releases").map(Resolver.sonatypeRepo)


// creg macros

val paradise = /* "paradise" */ s"paradise_$sversion"

val paradiseVersion = "2.1.0-M5"

// relevant for documentation generation
val hardcodedGeneratedSourceDirectory: String = "lib"

lazy val creg = project in file("creg") settings(Seq(
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
    compilerPlugin("org.scalamacros" % paradise % paradiseVersion)
  ),
  //
  // directory of generated source.
  // anything better than this hard-coded path?
  // (only noticeable in documentation generation;
  // compiles fine also without this line.)
  unmanagedSourceDirectories in Compile <+= baseDirectory {
    _ / hardcodedGeneratedSourceDirectory
  },
  //
  // publish this project
  publishArtifact in Compile := true,
  publishArtifact in Test := false,
  publishTo := {
    val nexus = "https://oss.sonatype.org/"
    if (isSnapshot.value)
      Some("snapshots" at nexus + "content/repositories/snapshots")
    else
      Some("releases"  at nexus + "service/local/staging/deploy/maven2")
  },
  organization := "com.github.yfcai",
  version := cregVersion,
  publishMavenStyle := true,
  pomIncludeRepository := { _ => false },
  pomExtra := {
    <url>http://ps.informatik.uni-tuebingen.de/research/functors/</url>
        <licenses>
    <license>
    <name>MIT License</name>
    <url>http://www.opensource.org/licenses/mit-license.php</url>
        </license>
    </licenses>
    <scm>
    <connection>scm:git:github.com/yfcai/CREG.git</connection>
    <developerConnection>scm:git:git@github.com:yfcai/CREG.git</developerConnection>
    <url>git@github.com/yfcai/CREG/</url>
    </scm>
    <developers>
    <developer>
    <name>Yufei Cai</name>
    <email>yufei.cai@uni-tuebingen.de</email>
    <organization>Lehrstuhl Programmiersprachen und Softwaretechnik,
    Karl Eberhards Universitaet Tuebingen</organization>
    <organizationUrl>http://ps.informatik.uni-tuebingen.de/</organizationUrl>
        </developer>
    </developers>
  }
) ++ sonatypeSettings : _*)


// tests

lazy val test = project in file(".") dependsOn creg settings (
  fork := true, // otherwise cannot deserialize
  scalaVersion := sversion,
  scalaSource in Compile := new File(baseDirectory.value, "example"),
  scalaSource in Test := new File(baseDirectory.value, "test"),
  autoCompilerPlugins := true,
  scalacOptions := options,
  publishArtifact := false,
  libraryDependencies ++= List(
    "commons-codec" % "commons-codec" % "1.9",
    "org.scalatest" % "scalatest_2.11" % "2.1.4",
    compilerPlugin("org.scalamacros" % paradise % paradiseVersion) // caution: must be a compilerPlugin!
  )
)
