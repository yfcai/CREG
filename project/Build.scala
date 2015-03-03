// cargo code from:
// https://github.com/inc-lc/ilc-scala/blob/f0e2e84a0e9e97555c3c39f96d4c559c25011a0a/project/Build.scala

import sbt._
import Keys._
import sbt.Defaults._
import scala.language.postfixOps

object BuildUnit extends Build {
  //Remove remaining files in target directory.
  def descendants(p: PathFinder) = p * AllPassFilter ***

  private val generatorMainClass = "traversableGeneration.Main"

  val triggerStage = Test
  val compileStage = Compile

  private[this]
  val generatingExamplesInto: String =
    "Generating n-nary functor traits into:"

  //Exposed to build.sbt
  //
  // caveat: can't use .taskValue (exposed in sbt 0.13.6)
  // because this project triggers NullPointerException in
  // sbt 0.13.6
  //
  val generationSettings = Seq(
    // code to generate examples at stage `test`
    // usage described in ./src/main/scala/Examples.scala
    sourceGenerators in triggerStage <+=
      (sourceManaged in triggerStage,
        classDirectory in compileStage,
        fullClasspath in compileStage,
        thisProject in compileStage,
        taskTemporaryDirectory in compileStage,
        scalaInstance in compileStage,
        baseDirectory in compileStage,
        javaOptions in compileStage,
        outputStrategy in compileStage,
        javaHome in compileStage,
        connectInput in compileStage
          in compileStage) map {
        (genSrcDir, classDir, lib,
          tp, tmp, si, base, options, strategy, javaHomeDir, connectIn
        ) =>
        consoleLogger.info(generatingExamplesInto)
        consoleLogger.info(genSrcDir.toString)
        val genFiles = generateExamples(new ExamplesRunner(
          tp.id,
          lib.files,
          generatorMainClass,
          Seq(genSrcDir, classDir) map (_.getCanonicalPath),
          ForkOptions(
            bootJars = si.jars,
            javaHome = javaHomeDir,
            connectInput = connectIn,
            outputStrategy = strategy,
            runJVMOptions = options,
            workingDirectory = Some(base))))

        genFiles
      }
  )

  // Generate .class files from ilc.Examples during test:compile
  //
  // Architecture:
  //
  // 1. compile ilc.Examples
  // 2. execute ilc.Examples.main, giving the base dir as argument
  // 3. read stdout of ilc.Examples.main fork, convert lines to a list of dirs
  // 4. return those dirs as files
  //
  def generateExamples(generator: ExamplesRunner): Seq[File] =
  {
    generator.start().map(path => {
      val file = new File(path)
      consoleLogger.info("- " ++ file.getName)
      file
    })
  }

  val consoleLogger = ConsoleLogger()

  // Adapted from:
  // http://stackoverflow.com/a/10286201
  class ExamplesRunner(
    subproject: String,
    classpath: Seq[File],
    generatorMainClass: String,
    args: Seq[String],
    config: ForkOptions)
  extends sbt.ScalaRun
  {
    def start(): Seq[String] = {
      val acc = new Accumulogger
      run(generatorMainClass, classpath, args, acc) match {
        case Some(error) =>
          sys.error("found some error: " ++ error)

        case None =>
          ()
      }
      acc.lines
    }

    override def run(mainClass: String, classpath: Seq[File],
      options: Seq[String], log: Logger): Option[String] =
    {
      val javaOptions = classpathOption(classpath)

      val strategy = config.outputStrategy getOrElse LoggedOutput(log)
      val updConfig = config copy (runJVMOptions = config.runJVMOptions ++
        javaOptions, envVars = Map.empty, outputStrategy = Some(strategy))
      val process =  Fork.java.fork(updConfig, mainClass :: options.toList)
      def cancel() = {
        log.warn("Run canceled.")
        process.destroy()
        1
      }
      val exitCode =
        try process.exitValue()
        catch { case e: InterruptedException => cancel() }
      processExitCode(exitCode, "runner")
    }
    private def classpathOption(classpath: Seq[File]) =
      "-classpath" :: Path.makeString(classpath) :: Nil
    private def processExitCode(exitCode: Int, label: String) = {
      if(exitCode == 0) None
      else Some("Nonzero exit code returned from " +
        label + ": " + exitCode)
    }
  }

  // accumulator+logger
  class Accumulogger extends Logger {
    protected[this] var accumulator: List[String] = Nil

    def log(level: Level.Value, message: => String): Unit = level match {
      // we echo warnings
      case Level.Warn =>
        consoleLogger.warn(message)

      // we echo things printed to stderr as info
      case Level.Error =>
        consoleLogger.info(message)

      case _ =>
        accumulator = message :: accumulator
    }

    def lines: List[String] = accumulator.reverse

    // fill interface with dummy methods, hope they don't get called
    // in order that Accumulogger be concrete
    def success(goodJob: => String): Unit = sys error goodJob
    def trace(t: => Throwable): Unit = sys error t.toString
  }
}
