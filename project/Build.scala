// cargo code from:
// https://github.com/inc-lc/ilc-scala/blob/f0e2e84a0e9e97555c3c39f96d4c559c25011a0a/project/Build.scala

import sbt._
import Keys._
import sbt.Defaults._
import scala.language.postfixOps

object BuildUnit extends Build {
  val __FILE__ : String = new Throwable().getStackTrace.head.getFileName

  // hard-coded destination folder
  val cregLib: File = new File(__FILE__, "../creg/lib")

  // run the code generator
  creg.generator.Generator.run(cregLib)
}
