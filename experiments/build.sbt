val sversion = "2.11.0"

scalaVersion := sversion

scalacOptions := Seq("-deprecation", "-feature", "-unchecked", "-Xlint")

libraryDependencies += "org.scala-lang" % "scala-reflect" % sversion
