/*
 * Copyright 2023 Magnus Madsen, 2024 Jakob Schneider Villumsen
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package ca.uwaterloo.flix.tools

import ca.uwaterloo.flix.api.{Flix, PhaseTime}
import ca.uwaterloo.flix.language.ast.shared.SecurityContext
import ca.uwaterloo.flix.language.ast.Symbol
import ca.uwaterloo.flix.language.phase.unification.zhegalkin.ZhegalkinCache
import ca.uwaterloo.flix.runtime.CompilationResult
import ca.uwaterloo.flix.util.StatUtils.{average, median}
import ca.uwaterloo.flix.util.collection.ListMap
import ca.uwaterloo.flix.util.{FileOps, LibLevel, Options}
import org.json4s.JsonAST
import org.json4s.JsonDSL.*

import java.nio.file.attribute.BasicFileAttributes
import java.nio.file.{FileVisitResult, Files, Path, SimpleFileVisitor}
import java.util.zip.{ZipEntry, ZipOutputStream}
import java.util.{Calendar, GregorianCalendar}
import scala.collection.mutable
import scala.util.{Failure, Success, Using}

object BenchmarkInliner {

  sealed trait Suite {
    override def toString: String = this match {
      case Suite.Micro => "micro"
      case Suite.Medium => "medium"
      case Suite.Macro => "macro"
      case Suite.All => "all"
    }
  }

  object Suite {

    case object Micro extends Suite

    case object Medium extends Suite

    case object Macro extends Suite

    case object All extends Suite

  }

  private val RunningTimeWarmupTime: Int = 10

  private val RunningTimeBenchmarkTime: Int = 10

  private val CompilationWarmupTime: Int = 10

  private val CompilationBenchmarkTime: Int = 10

  private val NumberOfRuns: Int = 100_000

  /**
    * Set this to `true` for additional details during benchmarking.
    */
  private val Verbose: Boolean = true

  /**
    * A set of benchmarks that are small and quick to run which are specifically targeted by the optimizer.
    */
  private val MicroBenchmarks: Map[String, String] = Map(
    "List.filter" -> listFilter,
    "List.foldLeft" -> listFoldLeft,
    "List.foldRight" -> listFoldRight,
    "List.map" -> listMap,
    "List.length" -> listLength,
    "List.reverse" -> listReverse,
    "List.filterMap" -> listFilterMap,
    "Map.filter" -> mapFilter,
    "Map.foldLeft" -> mapFoldLeft,
    "Map.foldRight" -> mapFoldRight,
    "Set.filter" -> libSetFilter,
    "Set.foldLeft" -> libSetFoldLeft,
    "Set.foldRight" -> libSetFoldRight,
    "Map10k" -> map10K,
    "FilterMap10k" -> filterMap10K,
    "Map10kOptimized" -> map10KOptimized,
    "FilterMap10kOptimized" -> filterMap10KOptimized,
  )

  /**
    * A set of benchmarks that are not targeted directly by the optimizer
    * but remain small programs.
    */
  private val MediumBenchmarks: Map[String, String] = Map(
    "MutualRecursion" -> mutualRecursion,
    "ImperativeForLoops" -> imperativeForLoops,
    "InternalMutability" -> internalMutability,
    "Introduction" -> introduction,
    "ConnectGraph" -> connectGraph,
    "DeliveryDate" -> deliveryDate,
    "RailRoadNetwork" -> railRoadNetwork,
    "TopSort" -> topSort,
    "TwoSat" -> twoSat,
  )

  /**
    * A set of benchmarks that are full programs or libraries or expensive functions.
    */
  private val MacroBenchmarks: Map[String, String] = Map(
    "ANSITerminal" -> ansiTerminal,
    "FordFulkerson" -> fordFulkerson,
    "FlixJson" -> flixJson,
    "FloydWarshall" -> floydWarshall,
    "IDE" -> ide,
    "IFDS" -> ifds,
    "Interpreter" -> interpreter,
    "ListSet" -> listSet,
    "Palindrome" -> palindrome,
    "Parsers" -> parsers,
    "Sequence" -> sequence,
    "SingleSourceShortestDistance" -> singleSourceShortestDistance,
    "SingleSourceShortestPaths" -> singleSourceShortestPaths,
    "SingleSourceShortestPathsArbitrary" -> singleSourceShortestPathsArbitrary,
    "Stratifier" -> stratifier,
    "Talpin1992" -> talpin1992,
    "TuringMachine" -> turingMachine,
  )

  private def baseDir: Path = Path.of("./build/").normalize()

  private def classDir: Path = baseDir.resolve("class/").normalize()

  private def classDirFor(path: String): Path = classDir.resolve(path).normalize()

  private def jarDir: Path = baseDir.resolve("jar/").normalize()

  private def jarDirFor(path: String): Path = jarDir.resolve(path).normalize()

  private def benchOutputPath: Path = baseDir.resolve("perf/").normalize()

  private def scriptOutputPath: Path = baseDir.resolve("scripts/").normalize()

  private def benchmarkScriptPath: Path = scriptOutputPath.resolve("benchmark.sh").normalize()

  private def benchmarkCompilerScriptPath: Path = scriptOutputPath.resolve("benchmark-compiler.sh").normalize()

  private def runScriptPath: Path = scriptOutputPath.resolve("all.sh").normalize()

  private def pythonPath: Path = scriptOutputPath.resolve("plots.py").normalize()

  def generateSetup(opts: Options, suite: Suite, asprofPath: Option[String]): Unit = {
    println("Generating setup...")

    val programs = programsFromSuite(suite)

    println("Building jars...")
    writeJars(programs, opts, asprofPath)
    FileOps.writeString(runScriptPath, mkRunScript(programs.size))
    FileOps.writeString(benchmarkCompilerScriptPath, mkCompilerScript(suite))
    FileOps.writeString(pythonPath, Python)
    Files.createDirectories(benchOutputPath)
    println(s"Please run $runScriptPath")
  }

  private def mkRunScript(programCount: Int): String = {
    val compilerEstimate = estimateTimeMinutes(programCount, CompilationWarmupTime, CompilationBenchmarkTime)
    val flixEstimate = estimateTimeMinutes(programCount, RunningTimeWarmupTime, RunningTimeBenchmarkTime)
    val totalEstimate = compilerEstimate + flixEstimate
    s"""#!/bin/bash
       |
       |echo "Compiler benchmark time estimate: $compilerEstimate minutes"
       |echo "Flix benchmark time estimate: $flixEstimate minutes"
       |echo "Total time estimate: $totalEstimate minutes"
       |
       |echo "Benchmarking Compiler..."
       |bash $benchmarkCompilerScriptPath
       |
       |echo "Benchmarking programs..."
       |bash $benchmarkScriptPath
       |
       |echo "Zipping output"
       |zip -r build.zip $benchOutputPath
       |
       |echo "Done"
       |
       |""".stripMargin
  }

  def runCompilerBenchmark(opts: Options, suite: Suite): Unit = {
    val programs = programsFromSuite(suite)
    val outFileName = outFileFromSuite(suite)

    println("Benchmarking compilation...")
    val t0 = System.nanoTime()
    val benchmarks = runBenchmarking(programs, opts)
    val filePath = benchOutputPath.resolve(outFileName).normalize()
    FileOps.writeJSON(filePath, benchmarks)

    println(s"Done. Results written to '$filePath'")

    val tDelta = System.nanoTime() - t0
    val seconds = nanosToMinutes(tDelta)
    println(s"Took $seconds minutes total")
  }

  private def outFileFromSuite(suite: Suite): String = {
    s"$suite.json"
  }

  private def programsFromSuite(suite: Suite): Map[String, String] = {
    suite match {
      case Suite.Micro => MicroBenchmarks
      case Suite.Medium => MediumBenchmarks
      case Suite.Macro => MacroBenchmarks
      case Suite.All => MicroBenchmarks ++ MediumBenchmarks ++ MacroBenchmarks
    }
  }

  private def debug(s: String): Unit = {
    if (Verbose) {
      println(s)
    }
  }

  private def writeJars(programs: Map[String, String], opts: Options, asprofPath: Option[String]): Unit = {
    val configs = mkConfigurations(opts.copy(loadClassFiles = false))
      .flatMap(o => programs.map { case (name, prog) => (o, name, prog) })
    configs.foreach(buildAndWriteJar)
    val snippets = configs.map {
      case (o, name, _) => mkScriptSnippet(BenchmarkFile(name, o), asprofPath)
    }
    val script = mkScript(snippets)
    FileOps.writeString(benchmarkScriptPath, script)
  }

  private def buildAndWriteJar(config: (Options, String, String)): Unit = {
    val (opts, name, prog) = config

    // Build
    implicit val sctx: SecurityContext = SecurityContext.AllPermissions
    val file = BenchmarkFile(name, opts)
    val baseline = BenchmarkFile.BaselineFile(file)
    Files.createDirectories(file.BuildDir)
    val flix = new Flix().setOptions(opts.copy(output = Some(file.BuildDir)))
    flix.addSourceCode(name, prog)
    flix.addSourceCode("mainProg", mainProg(baseline.toString))
    flix.addSourceCode("blackHole", blackhole)
    flix.compile().unsafeGet

    // Jar
    Files.createDirectories(jarDir)
    val classFiles =
      FromBootstrap.getAllFiles(file.ClassFilesDir)
        .map { path =>
          (path, FromBootstrap.convertPathToRelativeFileName(file.ClassFilesDir, path))
        }.sortBy(snd)


    Using(new ZipOutputStream(Files.newOutputStream(file.JarFilePath))) { zip =>
      val (manifestName, manifestContent) = FromBootstrap.manifest
      FromBootstrap.addToZip(zip, manifestName, manifestContent.getBytes)

      for ((buildFile, fileNameWithSlashes) <- classFiles) {
        FromBootstrap.addToZip(zip, fileNameWithSlashes, buildFile)
      }
    } match {
      case Success(_) =>
      case Failure(e) => throw e
    }
  }

  private case class BenchmarkFile(private val name: String, private val opts: Options) {
    private val FileName: String = {
      val suffix = if (opts.xnooptimizer) "disabled" else "enabled"
      s"${name}_$suffix"
    }
    private val JarName: String = s"$FileName.jar"
    val BuildDir: Path = classDirFor(s"$FileName/")
    val ClassFilesDir: Path = BuildDir.resolve("class/").normalize()
    val JarFilePath: Path = jarDirFor(JarName)
    val OutputFile: Path = benchOutputPath.resolve(s"$FileName.json").normalize()
    val ProfilingOutFile: Path = benchOutputPath.resolve(s"$FileName-profile.txt").normalize()
  }

  private object BenchmarkFile {
    def BaselineFile(file: BenchmarkFile): Path = {
      val baseOpts = file.opts.copy(xnooptimizer = true)
      BenchmarkFile(file.name, baseOpts).OutputFile
    }
  }

  private def mkScriptSnippet(file: BenchmarkFile, asprofPath: Option[String]): String = {
    s"""rm -f ${file.OutputFile}
       |echo "Benchmarking ${file.JarFilePath}"
       |java ${asprofPath.map(p => s"-agentpath:$p=start,fmt=collapsed,event=alloc,file=${file.ProfilingOutFile}").getOrElse("")} -jar ${file.JarFilePath} >> ${file.OutputFile}
       |""".stripMargin
  }

  private def mkScript(snippets: List[String]): String = {
    s"""#!/bin/bash
       |
       |${snippets.mkString("\n")}
       |
       |""".stripMargin
  }

  private def mkCompilerScript(suite: Suite): String = {
    s"""#!/bin/bash
       |
       |java -jar flix.jar benchmark-inliner-compiler --suite $suite
       |
       |""".stripMargin
  }

  private def fst[A, B](x: (A, B)): A = x._1

  private def snd[A, B](x: (A, B)): B = x._2

  private def estimateTimeMinutes(programsCount: Int, warmupTime: Int, benchmarkTime: Int): Int = {
    val timeCalc = (time: Int) => time * programsCount * 2
    timeCalc(warmupTime) + timeCalc(benchmarkTime)
  }

  private def programSuiteFromProgram(progName: String): String = {
    if (MicroBenchmarks.contains(progName))
      "micro"
    else if (MediumBenchmarks.contains(progName))
      "medium"
    else
      "macro"
  }

  private def runBenchmarking(programs: Map[String, String], opts: Options): JsonAST.JObject = {
    val totalTime = estimateTimeMinutes(programs.size, CompilationWarmupTime, CompilationBenchmarkTime)
    debug(s"Programs        : ${programs.size}")
    debug(s"Warmup          : $CompilationWarmupTime minutes")
    debug(s"Bench           : $CompilationBenchmarkTime minutes")
    debug(s"Total (Compiler): $totalTime minutes")

    val runConfigs = mkConfigurations(opts).flatMap(o => programs.map { case (name, prog) => (o, name, prog) })
    val programExperiments = benchmarkWithIndividualMaxTime(runConfigs, minutesToNanos(CompilationWarmupTime), minutesToNanos(CompilationBenchmarkTime))

    val compilationTimeStats = programExperiments.m.map {
      case (name, runs) => name -> stats(runs.map(_.compilationTime))
    }

    // Timestamp (in seconds) when the experiment was run
    val timestamp = nanosToSeconds(System.nanoTime())

    ("timestamp" -> timestamp) ~
      ("programs" -> {
        programExperiments.m.map {
          case (name, runs) =>
            ("programName" -> name) ~ {
              ("summary" -> {
                "compilationTime" -> {
                  val stats = compilationTimeStats.apply(name)
                  ("best" -> stats.min) ~
                    ("worst" -> stats.max) ~
                    ("average" -> stats.average) ~
                    ("median" -> stats.median)
                }
              }) ~ ("suite" -> programSuiteFromProgram(name)) ~
                ("results" -> runs.map(_.toJson))
            }
        }
      })
  }

  /**
    * Represents a run of a single program.
    *
    * @param name            The name of the program
    * @param lines           The number of lines of source code in the program
    * @param compilationTime The median time taken to compile the program
    * @param phases          The median running time of each compilation phase
    * @param codeSize        The number of bytes of the compiled program
    */
  private case class Run(name: String, lines: Int, compilationTime: Long, phases: List[(String, Long)], codeSize: Int) {
    def toJson: JsonAST.JObject = {
      ("lines" -> lines) ~
        ("compilationTime" -> compilationTime) ~
        ("phases" -> phases) ~
        ("codeSize" -> codeSize)
    }
  }

  private case class Stats[T](min: T, max: T, average: Double, median: Double)

  private def stats[T](xs: Seq[T])(implicit numeric: Numeric[T]): Stats[T] = {
    Stats(xs.min, xs.max, average(xs), median(xs))
  }

  private def mkConfigurations(opts: Options): List[Options] = {
    val o0 = opts.copy(xnooptimizer = true, lib = LibLevel.All, progress = false, incremental = false)
    val o1 = o0.copy(xnooptimizer = false)
    o0 :: o1 :: Nil
  }

  private def benchmarkWithIndividualMaxTime(runConfigs: List[(Options, String, String)], maxWarmupNanos: Long, maxNanos: Long): ListMap[String, Run] = {
    implicit val sctx: SecurityContext = SecurityContext.AllPermissions
    val runs = scala.collection.mutable.ListBuffer.empty[Run]
    for ((config, name, prog) <- runConfigs) {
      debug(s"Benchmarking $name with optimizer ${if (config.xnooptimizer) "disabled" else "enabled"}")
      debug(s"Warming up for ${nanosToMinutes(maxWarmupNanos)} minutes...")

      val t0Compiler = System.nanoTime()
      val _ = benchmarkCompilationWithMaxTime(config, name, prog, maxWarmupNanos)
      val (compilationTimings, result) = benchmarkCompilationWithMaxTime(config, name, prog, maxNanos)
      val tDeltaCompiler = System.nanoTime() - t0Compiler

      debug(s"Took ${nanosToMinutes(tDeltaCompiler)} minutes total")

      runs += collectRun(name, compilationTimings, result.get)
    }
    ListMap.from(runs.map(r => (r.name, r)))
  }

  private def benchmarkCompilationWithMaxTime(o: Options, name: String, prog: String, maxNanos: Long)(implicit sctx: SecurityContext): (Seq[(Long, List[(String, Long)])], Option[CompilationResult]) = {
    val compilationTimings = scala.collection.mutable.ListBuffer.empty[(Long, List[(String, Long)])]
    var usedTime = 0L
    var result: Option[CompilationResult] = None
    val mainProgEmpty = mainProg("")
    while (usedTime < maxNanos) {
      val t0 = System.nanoTime()
      val flix = new Flix().setOptions(o)
      ZhegalkinCache.clearCaches()
      flix.addSourceCode(s"$name", prog)
      flix.addSourceCode("mainProg", mainProgEmpty)
      flix.addSourceCode("blackHole", blackhole)
      val compilationResult = flix.compile().unsafeGet
      val phaseTimes = flix.phaseTimers.map { case PhaseTime(phase, time) => phase -> time }.toList
      val timing = (compilationResult.totalTime, phaseTimes)
      compilationTimings += timing
      usedTime += (System.nanoTime() - t0)
      result = Some(compilationResult)
    }
    (compilationTimings.toSeq, result)
  }

  private def collectRun(name: String, compilationTimings: Seq[(Long, List[(String, Long)])], result: CompilationResult): Run = {
    val lines = result.getTotalLines
    val compilationTime = median(compilationTimings.map(fst)).toLong
    val phaseTimings = compilationTimings.flatMap(snd).foldLeft(Map.empty[String, Seq[Long]]) {
      case (acc, (phase, time)) => acc.get(phase) match {
        case Some(timings) => acc + (phase -> timings.appended(time))
        case None => acc + (phase -> Seq(time))
      }
    }.map { case (phase, timings) => phase -> median(timings).toLong }.toList
    val codeSize = result.codeSize

    Run(name, lines, compilationTime, phaseTimings, codeSize)
  }


  private def minutesToNanos(minutes: Long): Long = {
    secondsToNanos(minutes * 60)
  }

  private def secondsToNanos(seconds: Long): Long = {
    seconds * 1_000_000_000
  }

  private def nanosToSeconds(nanos: Long): Long = {
    nanos / 1_000_000_000
  }

  private def nanosToMinutes(nanos: Long): Long = {
    nanosToSeconds(nanos) / 60
  }

  private object FromBootstrap {

    private val ENOUGH_OLD_CONSTANT_TIME: Long = new GregorianCalendar(2014, Calendar.JUNE, 27, 0, 0, 0).getTimeInMillis

    /**
      * @param root the root directory to compute a relative path from the given path
      * @param path the path to be converted to a relative path based on the given root directory
      * @return relative file name separated by slashes, like `path/to/file.ext`
      */
    def convertPathToRelativeFileName(root: Path, path: Path): String =
      root.relativize(path).toString.replace('\\', '/')


    private class FileVisitor extends SimpleFileVisitor[Path] {
      val result: mutable.ListBuffer[Path] = mutable.ListBuffer.empty

      override def visitFile(file: Path, attrs: BasicFileAttributes): FileVisitResult = {
        result += file
        FileVisitResult.CONTINUE
      }
    }

    /**
      * Returns all files in the given path `p`.
      */
    def getAllFiles(p: Path): List[Path] = {
      if (Files.isReadable(p) && Files.isDirectory(p)) {
        val visitor = new FileVisitor
        Files.walkFileTree(p, visitor)
        visitor.result.toList
      } else {
        Nil
      }
    }

    /**
      * Adds an entry to the given zip file.
      */
    def addToZip(zip: ZipOutputStream, name: String, p: Path): Unit = {
      if (Files.exists(p)) {
        addToZip(zip, name, Files.readAllBytes(p))
      }
    }

    /**
      * Adds an entry to the given zip file.
      */
    def addToZip(zip: ZipOutputStream, name: String, d: Array[Byte]): Unit = {
      val entry = new ZipEntry(name)
      entry.setTime(ENOUGH_OLD_CONSTANT_TIME)
      zip.putNextEntry(entry)
      zip.write(d)
      zip.closeEntry()
    }

    def manifest: (String, String) = {
      ("META-INF/MANIFEST.MF",
        """Manifest-Version: 1.0
          |Main-Class: Main
          |""".stripMargin)
    }
  }

  private def blackhole: String = {
    """
      |pub def blackhole(t: a): Unit \ IO =
      |    Ref.fresh(Static, t); ()
      |""".stripMargin
  }

  private def mainProg(baselineFilePath: String): String = {
    s"""
       |import java.lang.System
       |pub def main(): Unit \\ IO = run {
       |    //
       |    // Constants
       |    //
       |    let warmupTime = ${RunningTimeWarmupTime}i64;
       |    let benchTime  = ${RunningTimeBenchmarkTime}i64;
       |    let runs       = $NumberOfRuns;
       |
       |    //
       |    // Benchmarking functions
       |    //
       |    def doSampling(usedNanos, maxNanos, usedRuns) = {
       |        if (usedNanos < maxNanos and usedRuns < runs) {
       |            let t0 = System.nanoTime();
       |            runBenchmark();
       |            let tDelta = System.nanoTime() - t0;
       |            doSampling(usedNanos + tDelta, maxNanos, usedRuns + 1)
       |        } else {
       |            usedNanos
       |        }
       |    };
       |
       |    def bench(usedNanos, maxNanos, samples) = {
       |        if (usedNanos < maxNanos) {
       |            let sample = doSampling(usedNanos, maxNanos, 0) - usedNanos;
       |            bench(usedNanos + sample, maxNanos, sample :: samples)
       |        } else {
       |            List.reverse(samples)
       |        }
       |    };
       |
       |    let totalTime = warmupTime + benchTime;
       |    Console.eprintln("Expected total time: $${totalTime}");
       |
       |    Console.eprintln("Benchmarking for $${benchTime} minutes, running $${runs} times for each sample");
       |
       |    Console.eprintln("Warming up for $${warmupTime} minutes");
       |
       |    discard bench(0i64, minutesToNanos(warmupTime), List.empty());
       |    let samples = bench(0i64, minutesToNanos(benchTime), List.empty());
       |    let json = toJSONMain(samples);
       |
       |    Console.println(ToString.toString(json));
       |    Console.eprintln("Done")
       |
       |} with Console.runWithIO
       |
       |pub def minutesToNanos(minutes: Int64): Int64 = {
       |    secondsToNanos(minutes * 60i64)
       |}
       |
       |pub def secondsToNanos(seconds: Int64): Int64 = {
       |    seconds * 1_000_000_000i64
       |}
       |
       |pub def nanosToSeconds(nanos: Int64): Int64 = {
       |    nanos / 1_000_000_000i64
       |}
       |
       |
       |def toJSONMain(samples: List[Int64]): JSONMain = {
       |    JSONMain.Obj(
       |        List#{
       |            ("baseline",
       |                JSONMainJVal.JSONMainLit(JSONMainLit.Str("$baselineFilePath"))
       |            ),
       |            ("samples",
       |                JSONMainJVal.Arr(List.toVector(samples) |> Vector.map(n -> JSONMainJVal.JSONMainLit(JSONMainLit.Num(n))))
       |            )
       |        }
       |    )
       |}
       |
       |enum JSONMain {
       |    case Obj(List[(String, JSONMainJVal)])
       |}
       |
       |enum JSONMainJVal {
       |    case Obj(JSONMain)
       |    case Arr(Vector[JSONMainJVal])
       |    case JSONMainLit(JSONMainLit)
       |}
       |
       |enum JSONMainLit {
       |    case Str(String)
       |    case Num(Int64)
       |    case Null
       |}
       |
       |instance ToString[JSONMain] {
       |    pub def toString(x: JSONMain): String = match x {
       |        case JSONMain.Obj(kvs) =>
       |            let str = kvs
       |                |> List.map(match (k, v) -> "$${JSONMain.quote(k)}:$${ToString.toString(v)}")
       |                |> List.join(",");
       |            "{$${str}}"
       |    }
       |}
       |
       |
       |instance ToString[JSONMainJVal] {
       |    pub def toString(x: JSONMainJVal): String = match x {
       |        case JSONMainJVal.Obj(obj) => ToString.toString(obj)
       |        case JSONMainJVal.Arr(arr) => "[$${Vector.join(",", arr)}]"
       |        case JSONMainJVal.JSONMainLit(lit) => ToString.toString(lit)
       |    }
       |}
       |
       |
       |instance ToString[JSONMainLit] {
       |    pub def toString(x: JSONMainLit): String = match x {
       |        case JSONMainLit.Str(s) => JSONMain.quote(s)
       |        case JSONMainLit.Num(n) => Int64.toString(n)
       |        case JSONMainLit.Null   => "null"
       |    }
       |}
       |
       |
       |mod JSONMain {
       |    pub def quote(s: String): String = {
       |        let escaped = s
       |            |> String.replace(src = "\\\\", dst = "\\\\\\\\")
       |            |> String.replace(src = "\\\"", dst = "\\\\\\"");
       |        String.concat(escaped, "\\\"") |> String.concat("\\\"")
       |    }
       |}
       |""".stripMargin
  }

  private def listFilter: String = {
    """
      |pub def runBenchmark(): Unit \ IO = {
      |    List.range(0, 10_000) |> List.filter(x -> Int32.modulo(x, 2) == 0) |> blackhole
      |}
      |""".stripMargin
  }

  private def listFoldLeft: String = {
    """
      |pub def runBenchmark(): Unit \ IO = {
      |    List.range(0, 10_000) |> List.foldLeft(Add.add, 0) |> blackhole
      |}
      |""".stripMargin
  }

  private def listFoldRight: String = {
    """
      |pub def runBenchmark(): Unit \ IO = {
      |    List.range(0, 10_000) |> List.foldRight(Add.add, 0) |> blackhole
      |}
      |""".stripMargin
  }

  private def listMap: String = {
    """
      |pub def runBenchmark(): Unit \ IO = {
      |    List.range(0, 10_000) |> List.map(x -> x + 1) |> blackhole
      |}
      |""".stripMargin
  }

  private def listLength: String = {
    """
      |pub def runBenchmark(): Unit \ IO = {
      |    List.range(0, 10_000) |> List.length |> blackhole
      |}
      |""".stripMargin
  }

  private def listReverse: String = {
    """
      |pub def runBenchmark(): Unit \ IO = {
      |    List.range(0, 10_000) |> List.reverse |> blackhole
      |}
      |""".stripMargin
  }

  private def listFilterMap: String = {
    """
      |pub def runBenchmark(): Unit \ IO = {
      |    List.range(0, 10_000) |> List.filterMap(x -> if (Int32.remainder(x, 2) == 0) Some(x) else None) |> blackhole
      |}
      |""".stripMargin
  }

  private def map10K: String = {
    """
      |pub def runBenchmark(): Unit \ IO = {
      |    let l1 = range(0, 10_000);
      |    let l2 = map(x -> x + 1, l1);
      |    let l3 = length(l2);
      |    blackhole(l3)
      |}
      |
      |pub def map(f: a -> b, l: List[a]) : List[b] = {
      |    def mp(xs, acc) = match xs {
      |        case Nil     => acc
      |        case z :: zs => mp(zs, f(z) :: acc)
      |    };
      |    rev(mp(l, Nil))
      |}
      |
      |pub def rev(l: List[a]): List[a] = {
      |    def rv(xs, acc) = match xs {
      |        case Nil     => acc
      |        case z :: zs => rv(zs, z :: acc)
      |    };
      |    rv(l, Nil)
      |}
      |
      |pub def range(bot: Int32, top: Int32): List[Int32] = {
      |    def rng(i, acc) = if (i < bot) acc else rng(i - 1, i :: acc);
      |    rng(top - 1, Nil)
      |}
      |
      |pub def length(l: List[a]): Int32 = {
      |    def len(xs, acc) = match xs {
      |        case Nil     => acc
      |        case _ :: zs => len(zs, acc + 1)
      |    };
      |    len(l, 0)
      |}
      |""".stripMargin
  }

  private def map10KOptimized: String = {
    """
      |pub def runBenchmark(): Unit \ IO = {
      |    let top = 10_000 - 1;
      |    let l1 = rng(top, Nil);
      |    let l2 = mp(l1, Nil);
      |    let l3 = rv(l2, Nil);
      |    let l4 = ln(l3, 0);
      |    blackhole(l4)
      |}
      |
      |pub def mp(xs: List[Int32], acc: List[Int32]): List[Int32] = match xs {
      |    case Nil     => acc
      |    case z :: zs => mp(zs, z + 1 :: acc)
      |}
      |
      |pub def rv(xs: List[a], acc: List[a]): List[a] = match xs {
      |    case Nil     => acc
      |    case z :: zs => rv(zs, z :: acc)
      |}
      |
      |pub def ln(xs: List[a], acc: Int32): Int32 = match xs {
      |    case Nil     => acc
      |    case _ :: zs => ln(zs, acc + 1)
      |}
      |
      |pub def rng(i: Int32, acc: List[Int32]): List[Int32] = if (i < 0) acc else rng(i - 1, i :: acc)
      |""".stripMargin
  }

  private def filterMap10K: String = {
    """
      |pub def runBenchmark(): Unit \ IO = {
      |    let l1 = range(0, 10_000);
      |    let l2 = filterMap(x -> if (Int32.remainder(x, 2) == 0) Some(x) else None, l1);
      |    blackhole(l2)
      |}
      |
      |pub def filterMap(f: a -> Option[b] \ ef, l: List[a]): List[b] \ ef = {
      |    def fmp(ll, acc) = match ll {
      |        case Nil     => acc
      |        case x :: xs => match f(x) {
      |            case None    => fmp(xs, acc)
      |            case Some(y) => fmp(xs, y :: acc)
      |        }
      |    };
      |    rev(fmp(l, Nil))
      |}
      |
      |pub def rev(l: List[a]): List[a] = {
      |    def rv(xs, acc) = match xs {
      |        case Nil     => acc
      |        case z :: zs => rv(zs, z :: acc)
      |    };
      |    rv(l, Nil)
      |}
      |
      |pub def range(bot: Int32, top: Int32): List[Int32] = {
      |    def rng(i, acc) = if (i < bot) acc else rng(i - 1, i :: acc);
      |    rng(top - 1, Nil)
      |}
      |""".stripMargin

  }

  private def filterMap10KOptimized: String = {
    """
      |pub def runBenchmark(): Unit \ IO = {
      |    let top = 10_000 - 1;
      |    let l1 = rng(top, Nil);
      |    let l2 = fmp(l1, Nil);
      |    let l3 = rv(l2, Nil);
      |    blackhole(l3)
      |}
      |
      |pub def fmp(l: List[Int32], acc: List[Int32]): List[Int32] = match l {
      |    case Nil     => acc
      |    case x :: xs =>
      |        if (Int32.remainder(x, 2) == 0)
      |            fmp(xs, acc)
      |        else
      |            fmp(xs, x :: acc)
      |}
      |
      |pub def rv(xs: List[a], acc: List[a]): List[a] = match xs {
      |    case Nil     => acc
      |    case z :: zs => rv(zs, z :: acc)
      |}
      |
      |pub def rng(i: Int32, acc: List[Int32]): List[Int32] = if (i < 0) acc else rng(i - 1, i :: acc)
      |""".stripMargin
  }

  private def mapFilter: String = {
    """
      |pub def runBenchmark(): Unit \ IO = {
      |    List.range(0, 100) |> List.toMapWith(k -> k) |> Map.filter(x -> Int32.modulo(x, 2) == 0) |> blackhole
      |}
      |""".stripMargin
  }

  private def mapFoldLeft: String = {
    """
      |pub def runBenchmark(): Unit \ IO = {
      |    List.range(0, 100) |> List.toMapWith(k -> k) |> Map.foldLeft(Add.add, 0) |> blackhole
      |}
      |""".stripMargin
  }

  private def mapFoldRight: String = {
    """
      |pub def runBenchmark(): Unit \ IO = {
      |    List.range(0, 100) |> List.toMapWith(k -> k) |> Map.foldRight(Add.add, 0) |> blackhole
      |}
      |""".stripMargin
  }

  private def libSetFilter: String = {
    """
      |pub def runBenchmark(): Unit \ IO = {
      |    Set.range(0, 100) |> Set.filter(x -> Int32.modulo(x, 2) == 0) |> blackhole
      |}
      |""".stripMargin
  }

  private def libSetFoldLeft: String = {
    """
      |pub def runBenchmark(): Unit \ IO = {
      |    Set.range(0, 100) |> Set.foldLeft(Add.add, 0) |> blackhole
      |}
      |""".stripMargin
  }

  private def libSetFoldRight: String = {
    """
      |pub def runBenchmark(): Unit \ IO = {
      |    Set.range(0, 100) |> Set.foldRight(Add.add, 0) |> blackhole
      |}
      |""".stripMargin
  }

  private def mutualRecursion: String = {
    """
      |def isOdd(n: Int32): Bool =
      |    if (n == 0) false else isEvn(n - 1)
      |
      |def isEvn(n: Int32): Bool =
      |    if (n == 0) true else isOdd(n - 1)
      |
      |def runBenchmark(): Unit \ IO =
      |    isOdd(12345) |> blackhole
      |""".stripMargin
  }

  private def imperativeForLoops: String = {
    """
      |def runBenchmark(): Unit \ IO = region rc {
      |    let l = 1 :: 2 :: 3 :: Nil;
      |
      |    foreach (x <- l)
      |        blackhole(x);
      |
      |    let z = Ref.fresh(rc, Nil);
      |    foreach (x <- l)
      |        Ref.put(x :: Ref.get(z), z);
      |
      |    let q = Ref.fresh(rc, Nil);
      |    List.iterator(rc, l) |>
      |    Iterator.forEach(match x -> Ref.put(x :: Ref.get(q), q));
      |
      |    let k = 4 :: 5 :: 6 :: Nil;
      |    let w = Ref.fresh(rc, Nil);
      |    foreach (a <- l) {
      |        Ref.put(a :: Ref.get(w), w);
      |        foreach (b <- k)
      |            Ref.put(b :: Ref.get(w), w)
      |    };
      |
      |    let v = Ref.fresh(rc, Nil);
      |    List.iterator(rc, l) |>
      |    Iterator.forEach(match a -> {
      |        Ref.put(a :: Ref.get(v), v);
      |        List.iterator(rc, k) |>
      |        Iterator.forEach(match b -> Ref.put(b :: Ref.get(v), v))
      |    });
      |
      |    let e = Ref.fresh(rc, Nil);
      |    foreach (a <- l;
      |             b <- k)
      |                Ref.put((a, b) :: Ref.get(e), e);
      |
      |    let e1 = Ref.fresh(rc, Nil);
      |    List.iterator(rc, l) |>
      |    Iterator.forEach(match a -> {
      |        List.iterator(rc, k) |>
      |        Iterator.forEach(match b -> Ref.put((a, b) :: Ref.get(e1), e1))
      |    });
      |
      |    let c = Ref.fresh(rc, Nil);
      |    foreach (a <- l;
      |             if a > 1;
      |             b <- k;
      |             if b < 6)
      |                Ref.put((a, b) :: Ref.get(c), c);
      |
      |    let d = Ref.fresh(rc, Nil);
      |    foreach (a <- l;
      |             b <- k;
      |             if a > 1 and b < 6)
      |                Ref.put((a, b) :: Ref.get(d), d);
      |
      |    let cf = Ref.fresh(rc, Nil);
      |    List.iterator(rc, l) |>
      |    Iterator.forEach(match a -> {
      |        List.iterator(rc, k) |>
      |        Iterator.forEach(match b -> {
      |            if (a > 1 and b < 6) Ref.put((a, b) :: Ref.get(cf), cf) else ()
      |        })
      |    });
      |
      |    (Ref.get(z) == Ref.get(q)) |> blackhole;
      |    (Ref.get(w) == 6 :: 5 :: 4 :: 3 :: 6 :: 5 :: 4 :: 2 :: 6 :: 5 :: 4 :: 1 :: Nil) |> blackhole;
      |    (Ref.get(w) == Ref.get(v)) |> blackhole;
      |    List.sortBy(match (a, _) -> a, Ref.get(e)) |> blackhole;
      |    (Ref.get(e) == Ref.get(e1)) |> blackhole;
      |    List.sortBy(match (a, _) -> a, Ref.get(c)) |> blackhole;
      |    (Ref.get(c) == Ref.get(d)) |> blackhole;
      |    (Ref.get(c) == Ref.get(cf)) |> blackhole
      |}
      |""".stripMargin
  }

  private def internalMutability: String = {
    """
      |def deduplicate(l: List[a]): List[a] with Order[a] =
      |    region rc {
      |
      |        let s = MutSet.empty(rc);
      |
      |        List.filter(x -> {
      |            if (MutSet.memberOf(x, s))
      |                false // `x` has already been seen.
      |            else {
      |                MutSet.add(x, s);
      |                true
      |            }
      |        }, l)
      |    }
      |
      |def runBenchmark(): Unit \ IO =
      |    let l = 1 :: 1 :: 2 :: 2 :: 3 :: 3 :: Nil;
      |    deduplicate(l) |> blackhole
      |
      |""".stripMargin
  }

  private def connectGraph: String = {
    """
      |pub type alias Edge[node] = (node, node)
      |
      |pub type alias Graph[node] = {
      |    nodes = Set[node],
      |    edges = Set[Edge[node]]
      |}
      |
      |pub def connectedComponentRep(g: Graph[node]): #{ ComponentRep(node, node) | r } with Order[node] =
      |    let nodes = inject g#nodes into Node;
      |    let edges = inject g#edges into Edge;
      |    let reachability = #{
      |        Reachable(n, n) :- Node(n).
      |        Reachable(n1, n2) :- Edge(n1, n2).
      |        Reachable(n1, n2) :- Edge(n2, n1).
      |        Reachable(n1, n2) :- Reachable(n1, m), Reachable(m, n2).
      |        ReachUp(n1) :- Reachable(n1, n2), if (n1 < n2).
      |        ComponentRep(n, rep) :- Reachable(n, rep), not ReachUp(rep).
      |    };
      |    solve nodes, edges, reachability project ComponentRep
      |
      |pub def connectGraph(g: Graph[node]): #{ Edge(Set[node], Set[node]) | r } with Order[node] =
      |    let missingEdges = #{
      |        Component(rep; Set#{n}) :- ComponentRep(n, rep).
      |        Edge(c1, c2) :- fix Component(_; c1), fix Component(_; c2), if (c1 < c2).
      |    };
      |    solve connectedComponentRep(g), missingEdges project Edge
      |
      |def runBenchmark(): Unit \ IO =
      |    let graph = {
      |        nodes = Set.range(0, 8),
      |        edges = Set#{(0, 4), (0, 7), (2, 3), (1, 6), (5, 6)}
      |    };
      |    let connectedGraph = connectGraph(graph);
      |    let result = query connectedGraph select (c1, c2) from Edge(c1, c2);
      |    result |> blackhole
      |
      |""".stripMargin
  }

  private def deliveryDate: String = {
    """
      |def runBenchmark(): Unit \ IO =
      |    let p = #{
      |        PartDepends("Car",       "Chassis").
      |        PartDepends("Car",       "Engine").
      |        PartDepends("Engine",    "Piston").
      |        PartDepends("Engine",    "Ignition").
      |
      |        AssemblyTime("Car",     7).
      |        AssemblyTime("Engine",  2).
      |
      |        DeliveryDate("Chassis";  2).
      |        DeliveryDate("Piston";   1).
      |        DeliveryDate("Ignition"; 7).
      |
      |        ReadyDate(part; date) :-
      |            DeliveryDate(part; date).
      |
      |        ReadyDate(part; assemblyTime + componentDate) :-
      |            PartDepends(part, component),
      |            AssemblyTime(part, assemblyTime),
      |            ReadyDate(component; componentDate).
      |    };
      |
      |    query p select (c, d) from ReadyDate(c; d) |> Vector.toMap |> blackhole
      |
      |""".stripMargin
  }

  private def topSort: String = {
    """
      |def genEdges(n: Int32): #{Edge(Int32, Int32) | _} = {
      |    if (n <= 0) #{}
      |    else #{
      |        Edge(n, n*2).
      |        Edge(n, n*2+1).
      |    } <+> genEdges(n-1)
      |}
      |
      |def runBenchmark(): Unit \ IO = {
      |    let edges = genEdges(20);
      |
      |    let lp = #{
      |
      |        IndicesPlusOne(x, i+1) :- Indices(x, i).
      |        EdgeSecond(x) :- Edge(_, x).
      |        EdgeFirst(x) :- Edge(x, _).
      |
      |        Vertex(v) :- Edge(v,_).
      |        Vertex(v) :- Edge(_,v).
      |
      |        IsBefore(x, y) :- Edge(x, y).
      |
      |        IsBefore(x, y) :-
      |            IsBefore(x, z),
      |            IsBefore(z, y).
      |
      |        IsAfter(x, y) :-
      |            Edge(y, x).
      |
      |        IsAfter(x, y) :-
      |            IsAfter(z, x),
      |            IsAfter(y, z).
      |
      |        Indices(x, 0) :-
      |            Vertex(x),
      |            not EdgeSecond(x),
      |            not EdgeFirst(x).
      |
      |        Indices(x, 1) :-
      |            Vertex(x),
      |            not EdgeSecond(x),
      |            Edge(x, _).
      |
      |        Indices(x, i+1) :-
      |            IsBefore(y, x),
      |            not IsBefore(x, y),
      |            IsAfter(x, y),
      |            Indices(y, i).
      |
      |        Index(x, i) :-
      |            Indices(x, i),
      |            not IndicesPlusOne(x, i).
      |    };
      |
      |    query lp <+> edges select (x, i) from Index(x, i) |> blackhole
      |}
      |""".stripMargin
  }

  private def turingMachine: String = {
    """
      |use Functor.map
      |
      |enum Tape[t] {
      |    case Tape({
      |        left = List[t],
      |        middle = t,
      |        right = List[t],
      |        zero = t
      |    })
      |}
      |
      |instance ToString[Tape[t]] with ToString[t] {
      |    pub def toString(x: Tape[t]): String = {
      |        use ToString.toString;
      |        let t = ex(x);
      |        def tapeString(xx: List[t]) = xx |> map(toString) |> String.intercalate("");
      |        let lstring = tapeString(t#left |> List.reverse);
      |        let padding = String.repeat(String.length(lstring), " ");
      |        "${padding}v\n${lstring}${t#middle}${tapeString(t#right)}"
      |    }
      |}
      |
      |def ex(t: Tape[t]): {left = List[t], middle = t, right = List[t], zero = t} = match t {
      |    case Tape.Tape(x) => x
      |}
      |
      |def popOrElse(l: List[t], zero: t): (t, List[t]) = match l {
      |    case Nil => (zero, Nil)
      |    case next :: tail => (next, tail)
      |}
      |
      |def moveLeft(t0: Tape[t]): Tape[t] = {
      |    let t = ex(t0);
      |    let (middle, left) = popOrElse(t#left, t#zero);
      |    Tape.Tape({
      |        left = left,
      |        middle = middle,
      |        right = t#middle :: t#right,
      |        zero = t#zero
      |    })
      |}
      |
      |def moveRight(t0: Tape[t]): Tape[t] = {
      |    let t = ex(t0);
      |    let (middle, right) = popOrElse(t#right, t#zero);
      |    Tape.Tape({
      |        left = t#middle :: t#left,
      |        middle = middle,
      |        right = right,
      |        zero = t#zero
      |    })
      |}
      |
      |def setMiddle(middle: t, t: Tape[t]): Tape[t] = {
      |    t |> ex |> (x -> {middle = middle | x}) |> Tape.Tape
      |}
      |
      |def tapeOf(initMargin: Int32, zero: t): Tape[t] = {
      |    let margin = List.repeat(initMargin, zero);
      |    Tape.Tape({
      |        left = margin,
      |        middle = zero,
      |        right = margin,
      |        zero = zero
      |    })
      |}
      |
      |enum Direction {case Left, Stay, Right}
      |
      |def moveDir(d: Direction, t: Tape[t]): Tape[t] = match d {
      |    case Direction.Left => moveLeft(t)
      |    case Direction.Stay => t
      |    case Direction.Right => moveRight(t)
      |}
      |
      |type alias Machine[t, state] = {
      |    start = state,
      |    transition = (t, state) -> (t, Direction, state),
      |    end = state
      |}
      |
      |type alias MachineRunState[t, state] = {
      |    currentState = state,
      |    tape = Tape[t]
      |}
      |
      |type alias Monitor[t: Type, state: Type, ef: Eff] = MachineRunState[t, state] -> Unit \ ef
      |
      |def runMachine(zero: t, initMargin: Int32, monitor: Monitor[t, state, ef], m: Machine[t, state]): Tape[t] \ ef with Eq[state]= {
      |    runMachineAux(m, monitor, tapeOf(initMargin, zero), m#start)
      |}
      |
      |def runMachineAux(m: Machine[t, state], monitor: Monitor[t, state, ef], t: Tape[t], current: state): Tape[t] \ ef with Eq[state] = {
      |    let rec = runMachineAux(m, monitor);
      |    if (current == m#end)
      |        t
      |    else {
      |        monitor({currentState = current, tape = t});
      |        let (elm, dir, next) = m#transition(ex(t)#middle, current);
      |        let nextTape = t |> setMiddle(elm) |> moveDir(dir);
      |        rec(nextTape, next)
      |    }
      |}
      |
      |enum SimpleState with Eq {case Running, Done}
      |def goUntil(d: Direction, pred: t -> Bool): Machine[t, SimpleState] = {
      |    use SimpleState.{Running, Done};
      |    def transition(t, state) = match state {
      |        case Done => (t, Direction.Stay, Done)
      |        case Running =>
      |            if (pred(t))
      |                (t, Direction.Stay, Done)
      |            else
      |                (t, d, Running)
      |    };
      |    {transition = transition, start = Running, end = Done}
      |}
      |
      |enum NumState with Eq {case Running(Int32), Done}
      |def mapN(n: Int32, d: Direction, f: t -> t): Machine[t, NumState] = {
      |    use NumState.{Running, Done};
      |    def transition(t, state) = match state {
      |        case Done => (t, Direction.Stay, Done)
      |        case Running(i) if i <= 0 => (t, Direction.Stay, Done)
      |        case Running(1) => (f(t), d, Done)
      |        case Running(i) => (f(t), d, Running(i-1))
      |    };
      |    {transition = transition, start = Running(n), end = Done}
      |}
      |
      |def repeatN(n: Int32, d: Direction, elm: t): Machine[t, NumState] = {
      |    mapN(n, d, _ -> elm)
      |}
      |
      |def moveN(n: Int32, d: Direction): Machine[t, NumState] = {
      |    mapN(n, d, t -> t)
      |}
      |
      |enum Either[a, b] {
      |    case Left(a)
      |    case Right(b)
      |}
      |
      |instance Eq[Either[a, b]] with Eq[a], Eq[b] {
      |    pub def eq(x: Either[a, b], y: Either[a, b]): Bool = match (x, y) {
      |        case (Either.Left(xx), Either.Left(yy)) => xx == yy
      |        case (Either.Right(xx), Either.Right(yy)) => xx == yy
      |        case _ => false
      |    }
      |}
      |
      |def mapThird(f: c -> d \ ef, p: (a, b, c)): (a, b, d) \ ef = match p { case (a, b, c) => (a, b, f(c)) }
      |
      |def sequence(m1: Machine[t, state1], m2: Machine[t, state2]): Machine[t, Either[state1, state2]] with Eq[state1] = {
      |    use Either.{Left, Right};
      |    def transition(t, state) = match state {
      |        case Left(state1) if state1 == m1#end =>
      |            m2#transition(t, m2#start) |> mapThird(Right)
      |        case Left(state1) =>
      |            m1#transition(t, state1) |> mapThird(Left)
      |        case Right(state2) =>
      |            m2#transition(t, state2) |> mapThird(Right)
      |    };
      |    {transition = transition, start = Left(m1#start), end = Right(m2#end)}
      |}
      |
      |def runBenchmark(): Unit \ IO = {
      |    let machine =
      |        mapN(10, Direction.Right, _ -> "s") `sequence`
      |        moveN(1, Direction.Left) `sequence`
      |        goUntil(Direction.Left, t -> t != "s");
      |    let result = runMachine("_", 0, ms -> blackhole(ms#tape), machine);
      |    blackhole(result)
      |}
      |
      |""".stripMargin
  }

  private def twoSat: String = {
    """
      |def runBenchmark(): Unit \ IO = {
      |    let clauses = #{
      |        Clause("Pos", "x0", "Pos", "x2").
      |        Clause("Pos", "x0", "Neg", "x3").
      |        Clause("Pos", "x2", "Neg", "x3").
      |        Clause("Pos", "x1", "Neg", "x4").
      |        Clause("Neg", "x2", "Neg", "x4").
      |        Clause("Neg", "x0", "Neg", "x5").
      |        Clause("Neg", "x1", "Neg", "x5").
      |        Clause("Neg", "x2", "Neg", "x5").
      |        Clause("Pos", "x3", "Pos", "x6").
      |        Clause("Pos", "x4", "Pos", "x6").
      |        Clause("Pos", "x5", "Pos", "x6").
      |        Clause("Pos", "x6", "Neg", "x2").
      |        Clause("Neg", "x6", "Pos", "x2").
      |        Clause("Neg", "x6", "Neg", "x2").
      |    };
      |
      |    let lp = #{
      |        AnyIncon() :- Incon(_).
      |
      |        Not("Pos", "Neg").
      |        Not("Neg", "Pos").
      |
      |        Impl(m, u, n, v) :- Not(m, p), Clause(p, u, n, v).
      |        Impl(m, u, n, v) :- Not(m, p), Clause(n, v, p, u).
      |
      |        Impl(m, u, n, v) :- Impl(m, u, p, w), Impl(p, w, n, v).
      |
      |        Incon(u) :- Impl("Pos", u, "Neg", u), Impl("Neg", u, "Pos", u).
      |
      |        Satisfiable("Yes") :- not AnyIncon().
      |        Satisfiable("No") :- AnyIncon().
      |    };
      |
      |    query lp <+> clauses select x from Satisfiable(x) |> blackhole
      |}
      |
      |""".stripMargin
  }

  private def palindrome: String = {
    """
      |def runBenchmark(): Unit \ IO = {
      |    def trial(input) = {
      |        input |>
      |        longestPalindromeSequence |>
      |        Option.map(match (b,e) -> String.slice(start = b, end = e+1, input)) |>
      |        Option.getWithDefault("nothing")
      |    };
      |
      |    trial("ABBAIsCool") |> blackhole;
      |    trial("Hello") |> blackhole;
      |    trial("YaddaYaddaYadda") |> blackhole;
      |    trial("abammabba") |> blackhole
      |}
      |
      |def longestPalindromeSequence(s: String): Option[(Int32, Int32)] = {
      |    let length = String.length(s);
      |    let sameChar = i -> j -> {
      |        if (i >= 0 and j < length and i <= j)
      |            String.charAt(i, s) == String.charAt(j, s)
      |        else false
      |    };
      |    let indices = inject List.range(0, length) into StringIndex;
      |    let p = #{
      |        LongestPalindrome(i, i; 1) :- StringIndex(i).
      |        LongestPalindrome(i, i+1; 2) :- StringIndex(i), if (sameChar(i, i+1)).
      |        LongestPalindrome(b-1, e+1; l+2) :- if (b <= e and b-1 >= 0 and e+1 < length),
      |            if (sameChar(b-1, e+1)), LongestPalindrome(b, e; l).
      |    };
      |    let solution = solve p <+> indices;
      |    forM (
      |        maxLength <- query solution select l from LongestPalindrome(_, _; l) |> Vector.maximum;
      |        res <- query solution select (b, e) from LongestPalindrome(b,e;maxLength) |> Vector.head
      |    ) yield res
      |
      |}
      |
      |""".stripMargin
  }

  private def fordFulkerson: String = {
    """
      |pub def runBenchmark(): Unit \ IO = {
      |    FordFulkerson.exampleGraph01() |> FordFulkerson.maxFlow(0, 5) |> blackhole
      |}
      |
      |mod FordFulkerson {
      |
      |    use Path.{Path, Bot};
      |
      |    pub def maxFlow(src: t, dst: t, g: m[(t, Int32, t)]): Int32 \ Foldable.Aef[m] with Foldable[m], Order[t] =
      |        def fordFulkerson(flowNetwork) = match augmentingPath(src, dst, flowNetwork) {
      |            case None       => getMaxFlow(dst, flowNetwork)
      |            case Some(path) =>
      |                let incr = minCapacity(path, flowNetwork);
      |                let updatedNetwork = increaseFlow(path, incr, flowNetwork);
      |                fordFulkerson(updatedNetwork)
      |        };
      |        fordFulkerson(zeroFlow(g))
      |
      |    def zeroFlow(g: m[(t, Int32, t)]): Vector[(t, Int32, Int32, t)] \ Foldable.Aef[m] with Foldable[m], Order[t] =
      |        Foldable.toVector(g) |> Vector.map(match (x, y, z) -> (x, y, 0, z))
      |
      |    def getMaxFlow(dst: t, g: m[(t, Int32, Int32, t)]): Int32 \ Foldable.Aef[m] with Foldable[m], Order[t] =
      |        g
      |        |> Foldable.toVector
      |        |> Vector.filterMap(match (_, _, f, d) -> if (d == dst) Some(f) else None)
      |        |> Vector.sum
      |
      |    def augmentingPath(src: t, dst: t, g: m[(t, Int32, Int32, t)]): Option[Path[t]] \ Foldable.Aef[m] with Foldable[m], Order[t] =
      |        let edges = inject g into Edge;
      |        let rules = #{
      |            Reach(x, y; init(y, x)) :- Edge(x, u, f, y),                 if ((u - f) > 0). // Forward edge
      |            Reach(x, z; cons(z, p)) :- Reach(x, y; p), Edge(y, u, f, z), if ((u - f) > 0). // Forward edge
      |            Reach(x, y; init(y, x)) :- Edge(y, u, f, x),                 if (f > 0).       // Back edge
      |            Reach(x, z; cons(z, p)) :- Reach(x, y; p), Edge(z, u, f, y), if (f > 0).       // Back edge
      |        };
      |        let result = query edges, rules select fn from Reach(src, dst; fn);
      |        Vector.head(result)
      |
      |    def minCapacity(p: Path[t], g: m[(t, Int32, Int32, t)]): Int32 \ Foldable.Aef[m] with Foldable[m], Order[t] =
      |        let onPath = (s, d) -> isForwardEdge(s, d, p) or isBackEdge(s, d, p);
      |        let optMin = g |> Foldable.filter(match (s, _, _, d) -> onPath(s, d))
      |            |> List.map(match (_, u, f, _) -> u - f)
      |            |> List.minimum;
      |        match optMin {
      |            case Some(u) => u
      |            case None    => unreachable!()
      |        }
      |
      |    def increaseFlow(p: Path[t], incr: Int32, g: m[(t, Int32, Int32, t)]): Vector[(t, Int32, Int32, t)] \ Foldable.Aef[m] with Foldable[m], Order[t] =
      |        g
      |        |> Foldable.toVector
      |        |> Vector.map(match (s, u, f, d) ->
      |            if (isForwardEdge(s, d, p))
      |                (s, u, f + incr, d)
      |            else if (isBackEdge(s, d, p))
      |                (s, u, f - incr, d)
      |            else
      |                (s, u, f, d)
      |        )
      |
      |    def isForwardEdge(src: t, dst: t, p: Path[t]): Bool with Eq[t] =
      |        match (indexOf(src, p), indexOf(dst, p)) { // A path is sorted in reverse order
      |            case (Some(si), Some(di)) if di + 1 == si => true
      |            case _ => false
      |        }
      |
      |    def isBackEdge(src: t, dst: t, p: Path[t]): Bool with Eq[t] =
      |        match (indexOf(src, p), indexOf(dst, p)) { // A path is sorted in reverse order
      |            case (Some(si), Some(di)) if si + 1 == di => true
      |            case _ => false
      |        }
      |
      |    pub enum Path[a] with ToString {
      |        case Path(List[a])
      |        case Bot // Infinitely long path
      |    }
      |
      |    instance Eq[Path[a]] {
      |        pub def eq(x: Path[a], y: Path[a]): Bool = match (x, y) {
      |            case (Bot, Bot)           => true
      |            case (Path(xs), Path(ys)) => List.length(xs) == List.length(ys)
      |            case _                    => false
      |        }
      |    }
      |
      |    instance Order[Path[a]] {
      |        pub def compare(x: Path[a], y: Path[a]): Comparison = match (x, y) {
      |            case (Bot, Bot)           => Comparison.EqualTo
      |            case (Bot, _)             => Comparison.LessThan
      |            case (_, Bot)             => Comparison.GreaterThan
      |            case (Path(xs), Path(ys)) => List.length(xs) <=> List.length(ys)
      |        }
      |    }
      |
      |    instance LowerBound[Path[a]] {
      |        pub def minValue(): Path[a] = Bot
      |    }
      |
      |    instance PartialOrder[Path[a]] {
      |        pub def lessEqual(x: Path[a], y: Path[a]): Bool = match (x, y) {
      |            case (Bot, _)             => true
      |            case (Path(xs), Path(ys)) => List.length(xs) >= List.length(ys)
      |            case _                    => false
      |        }
      |    }
      |
      |    instance JoinLattice[Path[a]] {
      |        pub def leastUpperBound(x: Path[a], y: Path[a]): Path[a] = match (x, y) {
      |            case (Bot, p)             => p
      |            case (p, Bot)             => p
      |            case (Path(xs), Path(ys)) => if (List.length(xs) <= List.length(ys)) x else y
      |        }
      |    }
      |
      |    instance MeetLattice[Path[a]] {
      |        pub def greatestLowerBound(x: Path[a], y: Path[a]): Path[a] = match (x, y) {
      |            case (Bot, _)             => Bot
      |            case (_, Bot)             => Bot
      |            case (Path(xs), Path(ys)) => if (List.length(xs) > List.length(ys)) x else y
      |        }
      |    }
      |
      |    pub def init(y: a, x: a): Path[a] =
      |        Path(y :: x :: Nil)
      |
      |    pub def cons(z: a, p: Path[a]): Path[a] = match p {
      |        case Bot      => Bot
      |        case Path(xs) => Path(z :: xs)
      |    }
      |
      |    pub def indexOf(x: a, p: Path[a]): Option[Int32] with Eq[a] = match p {
      |        case Bot      => None
      |        case Path(xs) => List.indexOf(x, xs)
      |    }
      |
      |    pub def exampleGraph01(): Set[(Int32, Int32, Int32)] =
      |        Set#{ (0, 10, 1), (0, 10, 3), (1, 2, 3), (1, 4, 2), (1, 8, 4), (2, 10, 5), (3, 9, 4), (4, 6, 2), (4, 10, 5) }
      |}
      |""".stripMargin
  }

  private def ansiTerminal: String = {
    """
      |mod Terminal {
      |
      |    pub def cursorUp(n: Int32): Unit \ Console =
      |        if (n <= 0) () else
      |        output(Terminal.String.cursorUp(n))
      |
      |    pub def cursorDown(n: Int32): Unit \ Console =
      |        if (n <= 0) () else
      |        output(Terminal.String.cursorDown(n))
      |
      |    pub def cursorForward(n: Int32): Unit \ Console =
      |        if (n <= 0) () else
      |        output(Terminal.String.cursorForward(n))
      |
      |    pub def cursorBack(n: Int32): Unit \ Console =
      |        if (n <= 0) () else
      |        output(Terminal.String.cursorBack(n))
      |
      |    pub def cursorTo(row: {row = Int32}, column: Int32): Unit \ Console =
      |        if (row#row < 0 or column < 0) () else
      |        output(Terminal.String.cursorTo(row, column))
      |
      |    pub def clearScreenAfterCursor(): Unit \ Console =
      |        output(Terminal.String.clearScreenAfterCursor())
      |
      |    pub def clearScreenBeforeCursor(): Unit \ Console =
      |        output(Terminal.String.clearScreenBeforeCursor())
      |
      |    pub def clearScreenAndReset(): Unit \ Console =
      |        output(Terminal.String.clearScreenAndReset())
      |
      |    pub def clearLineAfterCursor(): Unit \ Console =
      |        output(Terminal.String.clearLineAfterCursor())
      |
      |    pub def clearLineBeforeCursor(): Unit \ Console =
      |        output(Terminal.String.clearLineBeforeCursor())
      |
      |    pub def clearLine(): Unit \ Console =
      |        output(Terminal.String.clearLine())
      |
      |    pub def saveCursor(): Unit \ Console =
      |        output(Terminal.String.saveCursor())
      |
      |    pub def restoreCursor(): Unit \ Console =
      |        output(Terminal.String.restoreCursor())
      |
      |    mod String {
      |        use Terminal.csi
      |
      |        pub def cursorUp(n: Int32): String =
      |            if (n <= 0) "" else csi("${n}A")
      |
      |        pub def cursorDown(n: Int32): String =
      |            if (n <= 0) "" else csi("${n}B")
      |
      |        pub def cursorForward(n: Int32): String =
      |            if (n <= 0) "" else csi("${n}C")
      |
      |        pub def cursorBack(n: Int32): String =
      |            if (n <= 0) "" else csi("${n}D")
      |
      |        pub def cursorTo(row: {row = Int32}, column: Int32): String =
      |            if (row#row < 0 or column < 0) "" else
      |            csi("${row#row+1};${column+1}H")
      |
      |        pub def clearScreenAfterCursor(): String =
      |            csi("J")
      |
      |        pub def clearScreenBeforeCursor(): String =
      |            csi("1J")
      |
      |        pub def clearScreenAndReset(): String =
      |            csi("2J") + cursorTo(row = 0, 0)
      |
      |        pub def clearLineAfterCursor(): String =
      |            csi("K")
      |
      |        pub def clearLineBeforeCursor(): String =
      |            csi("1K")
      |
      |        pub def clearLine(): String =
      |            csi("2K")
      |
      |        pub def saveCursor(): String =
      |            csi("s")
      |
      |        pub def restoreCursor(): String =
      |            csi("u")
      |    }
      |
      |    def output(x: s): Unit \ Console with ToString[s] =
      |        Console.print(ToString.toString(x))
      |
      |    def csi(s: String): String = {
      |        let escapeByte = "\\u001B";
      |        "${escapeByte}[${s}"
      |    }
      |
      |}
      |
      |mod TestTerminal {
      |
      |pub def runWithIO(f: Unit -> b \ ef): b \ (ef - Console) + IO =
      |    run {
      |        f()
      |    } with handler Console {
      |        def readln(k)      = { k("input") }
      |        def print(s, k)    = { blackhole(s); k() }
      |        def eprint(s, k)   = { blackhole(s); k() }
      |        def println(s, k)  = { blackhole(s); k() }
      |        def eprintln(s, k) = { blackhole(s); k() }
      |    }
      |
      |    def output(x: t): Unit \ Console with ToString[t] =
      |        Console.print(ToString.toString(x))
      |
      |    def outputln(x: t): Unit \ Console with ToString[t] =
      |        Console.println(ToString.toString(x))
      |
      |    def sleep(millis: Int64): Unit \ IO =
      |        blackhole(millis)
      |
      |    def sleepTime(): Int64 = 1000i64
      |
      |    def nextLineIsh(): Unit \ Console = {
      |        Terminal.cursorDown(1);
      |        outputln("")
      |    }
      |
      |    pub def testSaveAndRestore(): Unit \ IO = runWithIO(() -> {
      |        outputln("Expected Line: <<<x>>>");
      |
      |        // avoid scrolling
      |        outputln("");
      |        Terminal.cursorUp(1);
      |
      |        output("<<<");
      |        Terminal.saveCursor();
      |        outputln(" >>>");
      |
      |        sleep(sleepTime());
      |        Terminal.restoreCursor();
      |        sleep(sleepTime());
      |
      |        output("x");
      |        nextLineIsh()
      |    })
      |
      |}
      |
      |def runBenchmark(): Unit \ IO = {
      |    TestTerminal.testSaveAndRestore()
      |}
      |
      |""".stripMargin
  }

  private def floydWarshall: String = {
    """
      |enum Dist with Eq, Order, ToString {
      |  case Bot,
      |  case Dst(Int32),
      |  case Top
      |}
      |
      |instance LowerBound[Dist] {
      |    pub def minValue(): Dist = Dist.Bot
      |}
      |
      |instance PartialOrder[Dist] {
      |    pub def lessEqual(x: Dist, y: Dist): Bool = match (x, y) {
      |        case (_, Dist.Top)                => true
      |        case (Dist.Bot, _)                => true
      |        case (Dist.Dst(n1), Dist.Dst(n2)) => n1 >= n2
      |        case _                            => false
      |    }
      |}
      |
      |instance JoinLattice[Dist] {
      |    pub def leastUpperBound(x: Dist, y: Dist): Dist = match (x, y) {
      |        case (Dist.Bot, _)                => y
      |        case (_, Dist.Bot)                => x
      |        case (Dist.Dst(n1), Dist.Dst(n2)) => Dist.Dst(Int32.min(n1, n2))
      |        case _                            => Dist.Top
      |    }
      |}
      |
      |instance MeetLattice[Dist] {
      |    pub def greatestLowerBound(x: Dist, y: Dist): Dist = match (x, y) {
      |        case (Dist.Top, z)                => z
      |        case (z, Dist.Top)                => z
      |        case (Dist.Dst(n1), Dist.Dst(n2)) => Dist.Dst(Int32.max(n1, n2))
      |        case _                            => Dist.Bot
      |    }
      |}
      |
      |def sum(e1: Dist, e2: Dist): Dist = match (e1, e2) {
      |  case (Dist.Top, _)                => Dist.Top
      |  case (_, Dist.Top)                => Dist.Top
      |  case (Dist.Dst(n1), Dist.Dst(n2)) => Dist.Dst(n1 + n2)
      |  case _                            => Dist.Bot
      |}
      |
      |def negativeDist(d: Dist): Bool = match d {
      |  case Dist.Top    => true
      |  case Dist.Dst(x) => x < 0
      |  case _           => false
      |}
      |
      |def runBenchmark(): Unit \ IO = {
      |    let p = #{
      |        ShortestDist(a, b; Dist.Dst(d)) :- Edge(a, b, d).
      |        ShortestDist(a, c; sum(d1, d2)) :- ShortestDist(a, b; d1), ShortestDist(b, c; d2).
      |        ShortestDist(a, a; Dist.Top) :- ShortestDist(a, a; d), if (negativeDist(d)).
      |
      |        Edge("a", "b", 1).
      |        Edge("b", "c", 2).
      |        Edge("c", "a", 3).
      |        Edge("c", "d", 4).
      |        Edge("d", "e", 7).
      |        Edge("d", "f", 11).
      |        Edge("f", "e", 23).
      |
      |        Edge("1", "2", -3).
      |        Edge("2", "3", 1).
      |        Edge("3", "1", 1).
      |        Edge("3", "4", 30).
      |    };
      |    let res = query p select (x, y, z) from ShortestDist(x, y; z);
      |    blackhole(res)
      |}
      |""".stripMargin
  }

  private def ide: String = {
    """
      |mod IDE {
      |    type alias IDE[p, n, d, f, l] = {
      |        zero            = d,
      |        main            = p,
      |        cfg             = List[(n, n)],
      |        startNodes      = List[(p, n)],
      |        endNodes        = List[(p, n)],
      |        callGraph       = List[(n, p)],
      |        eshIntra        = (n, d) -> Vector[(d, f)],
      |        eshCallStart    = (n, d, p) -> Vector[(d, f)],
      |        eshEndReturn    = (p, d, n) -> Vector[(d, f)],
      |        id              = f,
      |        apply           = (f, l) -> l,
      |        compose         = (f, f) -> f
      |    }
      |    pub def runSolver(ide: IDE[p, n, d, f, l]): Vector[(n, d, l)]
      |        with LowerBound[f], JoinLattice[f], MeetLattice[f],
      |             LowerBound[l], UpperBound[l], JoinLattice[l], MeetLattice[l],
      |             Order[n], Order[d], Order[p], Order[f],  Order[l] =
      |
      |        let main = ide#main;
      |
      |        let apply = ide#apply;
      |        let compose = ide#compose;
      |
      |        def prependId(v) = Vector#{(ide#zero, ide#id)} ++ v;
      |        def augmentForZero(d, v) = if (d == ide#zero) prependId(v) else v;
      |
      |        def eshIntra1(n, d) = augmentForZero(d, ide#eshIntra(n, d));
      |        def eshCallStart1(n, d, p) = augmentForZero(d, ide#eshCallStart(n, d, p));
      |        def eshEndReturn1(p, d, n) = augmentForZero(d, ide#eshEndReturn(p, d, n));
      |
      |        let p = #{
      |            InProc(p, start) :- StartNode(p, start).
      |            InProc(p, m) :- InProc(p, n), CFG(n, m).
      |            Proc(p) :- InProc(p, _).
      |
      |            JumpFn(d1, m, d3; compose(long, short)) :-
      |                CFG(n, m),
      |                JumpFn(d1, n, d2; long),
      |                let (d3, short) = eshIntra1(n, d2).
      |
      |            JumpFn(d1, m, d3; compose(caller, summary)) :-
      |                CFG(n, m),
      |                JumpFn(d1, n, d2; caller),
      |                SummaryFn(n, d2, d3; summary).
      |
      |            EshCallStart(call, d2, target, d3, f) :-
      |                JumpFn(_d1, call, d2; nonbottom1),
      |                CallGraph(call, target),
      |                let (d3, f) = eshCallStart1(call, d2, target).
      |
      |            JumpFn(d3, start, d3; ide#id) :-
      |                EshCallStart(call, d2, target, d3, nonbottom2),
      |                StartNode(target, start).
      |
      |            JumpFn(ide#zero, n, ide#zero; ide#id) :- StartNode(main, n).
      |
      |            SummaryFn(call, d4, d5; compose(compose(cs, se), er)) :-
      |                CallGraph(call, target),
      |                StartNode(target, _start),
      |                EndNode(target, end),
      |                EshCallStart(call, d4, target, d1, cs),
      |                JumpFn(d1, end, d2; se),
      |                let (d5, er) = eshEndReturn1(target, d2, call).
      |
      |            ResultProc(proc, dp; apply(cs,v)) :-
      |                Results(call, d; v),
      |                EshCallStart(call, d, proc, dp, cs).
      |
      |            ResultProc(ide#main, ide#zero; UpperBound.maxValue()).
      |
      |            Results(n, d; apply(fn, vp)) :-
      |                ResultProc(proc, dp; vp),
      |                InProc(proc, n),
      |                JumpFn(dp, n, d; fn).
      |        };
      |
      |        let f1 = inject ide#cfg, ide#callGraph, ide#startNodes, ide#endNodes into CFG, CallGraph, StartNode, EndNode;
      |        query p, f1 select (n, d, l) from Results(n, d; l)
      |}
      |
      |mod ConstantProp {
      |
      |    pub enum Const with Eq, Order, ToString {
      |        case Bot,
      |        case Cst(Int32),
      |        case Top
      |    }
      |
      |    instance LowerBound[Const] {
      |        pub def minValue(): Const = Const.Bot
      |    }
      |
      |    instance UpperBound[Const] {
      |        pub def maxValue(): Const = Const.Top
      |    }
      |
      |    instance PartialOrder[Const] {
      |        pub def lessEqual(x: Const, y: Const): Bool = match (x, y) {
      |            case (Const.Bot, _)                 => true
      |            case (Const.Cst(n1), Const.Cst(n2)) => n1 == n2
      |            case (_, Const.Top)                 => true
      |            case _                              => false
      |        }
      |    }
      |
      |    instance JoinLattice[Const] {
      |        pub def leastUpperBound(x: Const, y: Const): Const = match (x, y) {
      |            case (Const.Bot, _)                    => y
      |            case (_, Const.Bot)                    => x
      |            case (Const.Cst(n1), Const.Cst(n2)) => if (n1 == n2) Const.Cst(n1) else Const.Top
      |            case _                                 => Const.Top
      |        }
      |    }
      |
      |    instance MeetLattice[Const] {
      |        pub def greatestLowerBound(x: Const, y: Const): Const = match (x, y) {
      |            case (Const.Top, _)                 => y
      |            case (_, Const.Top)                 => x
      |            case (Const.Cst(n1), Const.Cst(n2)) => if (n1 == n2) Const.Cst(n1) else Const.Bot
      |            case _                              => Const.Bot
      |        }
      |    }
      |
      |    pub def lift(n: Int32): Const = Const.Cst(n)
      |
      |    pub def sum(x: Const, y: Const): Const = match (x, y) {
      |        case (Const.Bot, _)                 => Const.Bot
      |        case (_, Const.Bot)                 => Const.Bot
      |        case (Const.Cst(n1), Const.Cst(n2)) => Const.Cst(n1 + n2)
      |        case _                              => Const.Top
      |    }
      |
      |    pub def mul(x: Const, y: Const): Const = match (x, y) {
      |        case (Const.Bot, _)                 => Const.Bot
      |        case (_, Const.Bot)                 => Const.Bot
      |        case (Const.Cst(0), _)              => Const.Cst(0)
      |        case (_, Const.Cst(0))              => Const.Cst(0)
      |        case (Const.Cst(n1), Const.Cst(n2)) => Const.Cst(n1 * n2)
      |        case _                              => Const.Top
      |    }
      |
      |    pub enum MicroFunction with Eq, Order, ToString {
      |        case Bot,
      |
      |        case NonBot(Int32, Int32, ConstantProp.Const)
      |    }
      |
      |    instance LowerBound[MicroFunction] {
      |        pub def minValue(): MicroFunction = MicroFunction.Bot
      |    }
      |
      |    instance PartialOrder[MicroFunction] {
      |        pub def lessEqual(x: MicroFunction, y: MicroFunction): Bool = y == JoinLattice.leastUpperBound(x, y)
      |    }
      |
      |    instance JoinLattice[MicroFunction] {
      |        pub def leastUpperBound(x: MicroFunction, y: MicroFunction): MicroFunction =
      |            use JoinLattice.{leastUpperBound => lub};
      |            match (x, y) {
      |                case (MicroFunction.Bot, _) => y
      |                case (_, MicroFunction.Bot) => x
      |                case (MicroFunction.NonBot(a1, b1, c1), MicroFunction.NonBot(a2, b2, c2)) =>
      |                    if (a1 == a2 and b1 == b2)
      |                        MicroFunction.NonBot(a1, b1, lub(c1, c2))
      |                    else if((a2-a1) != 0 and 0 == (b1 - b2) `Int32.remainder` (a2 - a1))
      |                        // Divisible.
      |                        MicroFunction.NonBot(a1, b2, lub(Const.Cst(a1 * (b1 - b2) / (a2 - a1) + b1), lub(c1, c2)))
      |                    else
      |                        // Indivisible.
      |                        MicroFunction.NonBot(1, 0, Const.Top)
      |            }
      |    }
      |
      |    instance MeetLattice[MicroFunction] {
      |        pub def greatestLowerBound(_x: MicroFunction, _y: MicroFunction): MicroFunction = bug!("Not Implemented")
      |    }
      |
      |    pub def id(): MicroFunction = MicroFunction.NonBot(1, 0, Const.Bot)
      |
      |    pub def compose(f1: MicroFunction, f2: MicroFunction): MicroFunction = match (f1, f2) {
      |        case (_, MicroFunction.Bot) => MicroFunction.Bot
      |        case (MicroFunction.Bot, MicroFunction.NonBot(_, _, c)) => match c {
      |            case Const.Bot     => MicroFunction.Bot
      |            case Const.Top     => MicroFunction.NonBot(0, 0, Const.Top)
      |            case Const.Cst(cc) => MicroFunction.NonBot(0, cc, c)
      |        }
      |        case (MicroFunction.NonBot(a2, b2, c2), MicroFunction.NonBot(a1, b1, c1)) =>
      |            use JoinLattice.{leastUpperBound => lub};
      |            MicroFunction.NonBot(a1 * a2, (a1 * b2) + b1, lub(sum(mul(c2, lift(a1)), lift(b1)), c1))
      |    }
      |
      |    pub def apply(f: MicroFunction, l: ConstantProp.Const): ConstantProp.Const = match f {
      |        case MicroFunction.Bot             => Const.Bot
      |        case MicroFunction.NonBot(a, b, c) => match l {
      |            case Const.Bot => Const.Bot
      |            case _         =>
      |                JoinLattice.leastUpperBound(sum(mul(l, lift(a)), lift(b)),c)
      |        }
      |    }
      |}
      |
      |pub enum IR with Eq {
      |    case MainEntry(Vector[String]),
      |    case Nop,
      |    case CallConst(String, Int32),
      |    case CallVar(String, String),
      |    case Assign(String, Int32, String, Int32)
      |}
      |
      |def runBenchmark(): Unit \ IO = {
      |    blackhole("Running IDE");
      |
      |    let cfg =
      |        ("smain","n1") ::
      |        ("n1","n2") ::
      |        ("n2","n3") ::
      |        ("n3","emain") ::
      |
      |        ("sp","n4") ::
      |        ("n4","n5") ::
      |        ("n4","n9") ::
      |        ("n5","n6") ::
      |        ("n6","n7") ::
      |        ("n7","n8") ::
      |        ("n8","n9") ::
      |        ("n9","ep") :: Nil;
      |
      |    let callGraph =
      |        ("n1","p") ::
      |        ("n6","p") :: Nil;
      |
      |    let startNodes =
      |        ("main","smain") ::
      |        ("p","sp") :: Nil;
      |
      |    let endNodes =
      |        ("main","emain") ::
      |        ("p","ep") :: Nil;
      |
      |    def procedureParameters(p) = match p {
      |        case "p" => "a"
      |        case _ => ?unreachable
      |    };
      |
      |    let globalVars = Set#{"x"};
      |    def isGlobalVar(v) = Set.memberOf(v, globalVars);
      |
      |    def instruction(n) = match n {
      |        case "smain" => IR.MainEntry(Vector#{"x"})
      |        case "n1" => IR.CallConst("p", 7)
      |        case "n2" => IR.Nop
      |        case "n3" => IR.Nop
      |        case "emain" => IR.Nop
      |
      |        case "sp" => IR.Nop
      |        case "n4" => IR.Nop
      |        case "n5" => IR.Assign("a", 1, "a", -2)
      |        case "n6" => IR.CallVar("p", "a")
      |        case "n7" => IR.Nop
      |        case "n8" => IR.Assign("a", 1, "a", 2)
      |        case "n9" => IR.Assign("x", -2, "a", 5)
      |        case "ep" => IR.Nop
      |
      |        case _ => ?unreachable
      |    };
      |
      |    def eshIntra(n, d) = match instruction(n) {
      |        case IR.MainEntry(vars) =>
      |            if (d == "zero") Vector.map(v -> (v, ConstantProp.MicroFunction.Bot), vars)
      |            else Vector#{}
      |        case IR.Assign(v1, c1, v2, c2) =>
      |          let kill = if (d == v1) Vector#{} else Vector#{(d, ConstantProp.id())};
      |          let microfn = ConstantProp.MicroFunction.NonBot(c1, c2, ConstantProp.Const.Bot);
      |          let gen = if (d == v2) Vector#{(v1, microfn)} else Vector#{};
      |          kill ++ gen
      |        case IR.CallConst(_, _) if isGlobalVar(d) => Vector#{}
      |        case IR.CallVar(_, _) if isGlobalVar(d) => Vector#{}
      |        case _ => Vector#{(d, ConstantProp.id())}
      |    };
      |
      |    def eshCallStart(n, d, p) = match instruction(n) {
      |        case IR.CallConst(proc, arg) if (proc == p) =>
      |          let parm = procedureParameters(proc);
      |          if (d == "zero") Vector#{(parm,ConstantProp.MicroFunction.NonBot(0,arg,ConstantProp.Const.Bot))}
      |          else if (d == parm) Vector#{}
      |          else Vector#{(d, ConstantProp.id())}
      |        case IR.CallVar(proc, arg) if (proc == p) =>
      |          let parm = procedureParameters(proc);
      |          if (d == arg) Vector#{(parm,ConstantProp.id())}
      |          else if (d == parm) Vector#{}
      |          else Vector#{(d, ConstantProp.id())}
      |        case _ => Vector#{}
      |    };
      |
      |    def eshEndReturn(p, d, n) = match instruction(n) {
      |        case IR.CallConst(proc,_) if p == proc and isGlobalVar(d) => Vector#{(d, ConstantProp.id())}
      |        case IR.CallVar(proc,_) if p == proc and isGlobalVar(d) => Vector#{(d, ConstantProp.id())}
      |        case _ => Vector#{}
      |    };
      |
      |    let result = IDE.runSolver({
      |        zero            = "zero",
      |        main            = "main",
      |        cfg             = cfg,
      |        startNodes      = startNodes,
      |        endNodes        = endNodes,
      |        callGraph       = callGraph,
      |        eshIntra        = eshIntra,
      |        eshCallStart    = eshCallStart,
      |        eshEndReturn    = eshEndReturn,
      |        id              = ConstantProp.id(),
      |        apply           = ConstantProp.apply,
      |        compose         = ConstantProp.compose
      |        });
      |
      |    blackhole(result)
      |}
      |""".stripMargin
  }

  private def ifds: String = {
    """
      |mod IFDS {
      |    type alias IFDS[p, n, d] = {
      |        zero            = d,
      |        main            = p,
      |        cfg             = List[(n, n)],
      |        startNodes      = List[(p, n)],
      |        endNodes        = List[(p, n)],
      |        callGraph       = List[(n, p)],
      |        eshIntra        = (n, d) -> Vector[d],
      |        eshCallStart    = (n, d, p) -> Vector[d],
      |        eshEndReturn    = (p, d, n) -> Vector[d]
      |    }
      |
      |    pub def runSolver(ifds: IFDS[p, n, d]): Vector[(n, d)]
      |        with Order[n], Order[d], Order[p] =
      |
      |        let main = ifds#main;
      |
      |        def prependZero(v) = Vector#{ifds#zero} ++ v;
      |        def augmentForZero(d, v) = if (d == ifds#zero) prependZero(v) else v;
      |
      |        def eshIntra1(n, d) = augmentForZero(d, ifds#eshIntra(n, d));
      |        def eshCallStart1(n, d, p) = augmentForZero(d, ifds#eshCallStart(n, d, p));
      |        def eshEndReturn1(p, d, n) = augmentForZero(d, ifds#eshEndReturn(p, d, n));
      |        let p = #{
      |            InProc(p, start) :- StartNode(p, start).
      |            InProc(p, m) :- InProc(p, n), CFG(n, m).
      |
      |            Proc(p) :- InProc(p, _).
      |
      |            PathEdge(d1, m, d3) :-
      |                CFG(n, m),
      |                PathEdge(d1, n, d2),
      |                let d3 = eshIntra1(n, d2).
      |
      |            PathEdge(d1, m, d3) :-
      |                CFG(n, m),
      |                PathEdge(d1, n, d2),
      |                SummaryEdge(n, d2, d3).
      |
      |            EshCallStart(call, d2, target, d3) :-
      |                PathEdge(_d1, call, d2),
      |                CallGraph(call, target),
      |                let d3 = eshCallStart1(call, d2, target).
      |
      |            PathEdge(d3, start, d3) :-
      |                EshCallStart(call, d2, target, d3),
      |                StartNode(target, start).
      |
      |            PathEdge(ifds#zero, n, ifds#zero) :- StartNode(main, n).
      |
      |            SummaryEdge(call, d4, d5) :-
      |                CallGraph(call, target),
      |                StartNode(target, _start),
      |                EndNode(target, end),
      |                EshCallStart(call, d4, target, d1),
      |                PathEdge(d1, end, d2),
      |                let d5 = eshEndReturn1(target, d2, call).
      |
      |            Results(n, d2) :- PathEdge(_,n,d2).
      |        };
      |
      |
      |        let f1 = inject ifds#cfg, ifds#callGraph, ifds#startNodes, ifds#endNodes into CFG, CallGraph, StartNode, EndNode;
      |
      |        query p, f1 select (n, d) from Results(n, d)
      |
      |}
      |
      |pub enum IR with Eq {
      |    case MainEntry(Vector[String]),
      |    case Nop,
      |    case Call(String, String),
      |    case Read(String),
      |    case Assign(String, String, String)
      |}
      |
      |def runBenchmark(): Unit \ IO = {
      |    let cfg =
      |        ("smain","n1") ::
      |        ("n1","n2") ::
      |        ("n2","n3") ::
      |        ("n3","emain") ::
      |
      |        ("sp","n4") ::
      |        ("n4","n5") ::
      |        ("n4","ep") ::
      |        ("n5","n6") ::
      |        ("n6","n7") ::
      |        ("n7","n8") ::
      |        ("n8","n9") ::
      |        ("n9","ep") :: Nil;
      |
      |    let callGraph =
      |        ("n2","p") ::
      |        ("n7","p") :: Nil;
      |
      |    let startNodes =
      |        ("main","smain") ::
      |        ("p","sp") :: Nil;
      |
      |    let endNodes =
      |        ("main","emain") ::
      |        ("p","ep") :: Nil;
      |
      |    def procedureParameters(p) = match p {
      |        case "p" => "a"
      |        case _ => ?unreachable
      |    };
      |
      |    let globalVars = Set#{"g"};
      |    def isGlobalVar(v) = Set.memberOf(v, globalVars);
      |
      |    let allVars = Set#{"a", "x"} ++ globalVars;
      |
      |    def instruction(n) = match n {
      |        case "smain" => IR.MainEntry(Vector#{"x"})
      |        case "n1" => IR.Read("x")
      |        case "n2" => IR.Call("p", "x")
      |        case "n3" => IR.Nop
      |        case "emain" => IR.Nop
      |
      |        case "sp" => IR.Nop
      |        case "n4" => IR.Nop
      |        case "n5" => IR.Read("g")
      |        case "n6" => IR.Assign("a", "a", "g")
      |        case "n7" => IR.Call("p", "a")
      |        case "n8" => IR.Nop
      |        case "n9" => IR.Nop
      |        case "ep" => IR.Nop
      |
      |        case _ => ?unreachable
      |    };
      |
      |    def eshIntra(n, d) = match instruction(n) {
      |        case IR.MainEntry(vars) =>
      |            if (d == "zero") vars ++ Foldable.toVector(globalVars)
      |            else Vector#{}
      |        case IR.Nop => Vector#{d}
      |        case IR.Call(target, arg) =>
      |            if (isGlobalVar(d)) Vector#{} else Vector#{d}
      |        case IR.Read(v) =>
      |            if (d == v) Vector#{} else Vector#{d}
      |        case IR.Assign(v1, v2, v3) =>
      |            let kill = if (d == v1) Vector#{} else Vector#{d};
      |            let gen = if (d == v2 or d == v3) Vector#{v1} else Vector#{};
      |            kill ++ gen
      |    };
      |
      |    def eshCallStart(n, d, p) = match instruction(n) {
      |        case IR.Call(proc, arg) if (proc == p) =>
      |          let parm = procedureParameters(proc);
      |          if (d == arg) Vector#{parm}
      |          else if (d == parm) Vector#{}
      |          else Vector#{d}
      |        case _ => Vector#{}
      |    };
      |
      |    def eshEndReturn(p, d, n) = match instruction(n) {
      |        case IR.Call(proc,_) if p == proc and isGlobalVar(d) =>
      |          Vector#{d}
      |        case _ => Vector#{}
      |    };
      |
      |    let result = IFDS.runSolver({
      |        zero            = "zero",
      |        main            = "main",
      |        cfg             = cfg,
      |        startNodes      = startNodes,
      |        endNodes        = endNodes,
      |        callGraph       = callGraph,
      |        eshIntra        = eshIntra,
      |        eshCallStart    = eshCallStart,
      |        eshEndReturn    = eshEndReturn
      |        });
      |
      |    blackhole(result)
      |}
      |""".stripMargin
  }

  private def interpreter: String = {
    """
      |enum AExp {
      |    case Cst(Int32),
      |    case Plus(AExp, AExp),
      |    case Minus(AExp, AExp),
      |    case Times(AExp, AExp),
      |    case IfThenElse(BExp, AExp, AExp)
      |}
      |
      |enum BExp {
      |    case True,
      |    case False,
      |    case Not(BExp),
      |    case Conj(BExp, BExp),
      |    case Disj(BExp, BExp),
      |    case Eq(AExp, AExp),
      |    case Neq(AExp, AExp)
      |}
      |
      |def evalAExp(e: AExp): Int32 = match e {
      |    case AExp.Cst(i)                 => i
      |    case AExp.Plus(e1, e2)           => evalAExp(e1) + evalAExp(e2)
      |    case AExp.Minus(e1, e2)          => evalAExp(e1) - evalAExp(e2)
      |    case AExp.Times(e1, e2)          => evalAExp(e1) * evalAExp(e2)
      |    case AExp.IfThenElse(e1, e2, e3) =>
      |        let cond = evalBExp(e1);
      |            if (cond) evalAExp(e2) else evalAExp(e3)
      |}
      |
      |def evalBExp(e: BExp): Bool = match e {
      |    case BExp.True           => true
      |    case BExp.False          => false
      |    case BExp.Not(e1)        => not evalBExp(e1)
      |    case BExp.Conj(e1, e2)   => evalBExp(e1) and evalBExp(e2)
      |    case BExp.Disj(e1, e2)   => evalBExp(e1) or evalBExp(e2)
      |    case BExp.Eq(e1, e2)     => evalAExp(e1) == evalAExp(e2)
      |    case BExp.Neq(e1,e2)     => evalAExp(e1) != evalAExp(e2)
      |}
      |
      |enum Inst {
      |    case Push(Int32),
      |    case Add,
      |    case Sub,
      |    case Mul,
      |    case Neg,
      |    case And,
      |    case Or,
      |    case Cmp,
      |    case Branch(List[Inst], List[Inst])
      |}
      |
      |def compileAExp(e: AExp): List[Inst] = match e {
      |    case AExp.Cst(i)         => Inst.Push(i) :: Nil
      |    case AExp.Plus(e1, e2)   =>
      |        let is1 = compileAExp(e1);
      |        let is2 = compileAExp(e2);
      |            is2 ::: is1 ::: Inst.Add :: Nil
      |    case AExp.Minus(e1, e2)  =>
      |        let is1 = compileAExp(e1);
      |        let is2 = compileAExp(e2);
      |            is2 ::: is1 ::: Inst.Sub :: Nil
      |    case AExp.Times(e1, e2)  =>
      |        let is1 = compileAExp(e1);
      |        let is2 = compileAExp(e2);
      |            is2 ::: is1 ::: Inst.Mul :: Nil
      |    case AExp.IfThenElse(e1, e2, e3)  =>
      |        let is1 = compileBExp(e1);
      |        let is2 = compileAExp(e2);
      |        let is3 = compileAExp(e3);
      |            is1 ::: Inst.Branch(is2, is3) :: Nil
      |}
      |
      |def compileBExp(e: BExp): List[Inst] = match e {
      |    case BExp.True           => Inst.Push(1) :: Nil
      |    case BExp.False          => Inst.Push(0) :: Nil
      |    case BExp.Not(e1)         =>
      |        let is = compileBExp(e1);
      |            is ::: Inst.Neg :: Nil
      |    case BExp.Conj(e1, e2)   =>
      |        let is1 = compileBExp(e1);
      |        let is2 = compileBExp(e2);
      |            is2 ::: is1 ::: Inst.And :: Nil
      |    case BExp.Disj(e1, e2)   =>
      |        let is1 = compileBExp(e1);
      |        let is2 = compileBExp(e2);
      |            is2 ::: is1 ::: Inst.Or :: Nil
      |    case BExp.Eq(e1, e2)     =>
      |        let is1 = compileAExp(e1);
      |        let is2 = compileAExp(e2);
      |            is2 ::: is1 ::: Inst.Cmp :: Nil
      |    case BExp.Neq(e1, e2)    =>
      |        let is1 = compileAExp(e1);
      |        let is2 = compileAExp(e2);
      |            is2 ::: is1 ::: Inst.Neg :: Inst.Cmp :: Nil
      |}
      |
      |def evalInst(instructions: List[Inst], stack: List[Int32]): Int32 = match (instructions, stack) {
      |    case (Nil, x :: _) => x
      |    case ((Inst.Push(i)) :: rs, st) => evalInst(rs, i :: st)
      |    case (Inst.Add :: rs, i1 :: i2 :: st) => evalInst(rs, (i1 + i2) :: st)
      |    case (Inst.Sub :: rs, i1 :: i2 :: st) => evalInst(rs, (i1 - i2) :: st)
      |    case (Inst.Mul :: rs, i1 :: i2 :: st) => evalInst(rs, (i1 * i2) :: st)
      |    case (Inst.Neg :: rs, i :: st) =>
      |        if (i == 0)
      |            evalInst(rs, 1 :: st)
      |        else
      |            evalInst(rs, 0 :: st)
      |    case (Inst.And :: rs, i1 :: i2 :: st) =>
      |        if (i1 != 0 and i2 != 0)
      |            evalInst(rs, 1 :: st)
      |        else
      |            evalInst(rs, 0 :: st)
      |    case (Inst.Or :: rs, i1 :: i2 :: st) =>
      |        if (i1 != 0 or i2 != 0)
      |            evalInst(rs, 1 :: st)
      |        else
      |            evalInst(rs, 0 :: st)
      |    case (Inst.Cmp :: rs, i1 :: i2 :: st) =>
      |        if (i1 == i2)
      |            evalInst(rs, 1 :: st)
      |        else
      |            evalInst(rs, 0 :: st)
      |    case ((Inst.Branch(is1, is2)) :: _, i :: st) =>
      |        if (i != 0)
      |            evalInst(is1, st)
      |        else
      |            evalInst(is2, st)
      |    case _ => ???
      |}
      |
      |def runBenchmark(): Unit \ IO = {
      |    let e = AExp.IfThenElse(BExp.Eq(AExp.Cst(1), AExp.Cst(2)), AExp.Cst(42), AExp.Times(AExp.Cst(21), AExp.Cst(82)));
      |    let a = evalAExp(e);
      |    let b = evalInst(compileAExp(e), Nil);
      |    blackhole(a == b)
      |}
      |
      |""".stripMargin
  }

  private def listSet: String = {
    """
      |mod JonathanStarup {
      |pub enum ListSet[t](List[t])
      |
      |instance Eq[ListSet[t]] with Eq[t] {
      |    pub def eq(x: ListSet[t], y: ListSet[t]): Bool =
      |        ListSet.eq(x, y)
      |}
      |
      |instance ToString[ListSet[t]] with ToString[t], Eq[t] {
      |    pub def toString(x: ListSet[t]): String =
      |        ListSet.toString(x)
      |}
      |
      |instance LowerBound[ListSet[t]] with Eq[t] {
      |    pub def minValue(): ListSet[t] =
      |        ListSet.empty()
      |}
      |
      |instance PartialOrder[ListSet[t]] with Eq[t] {
      |    pub def lessEqual(x: ListSet[t], y: ListSet[t]): Bool =
      |        ListSet.isSubsetOf(x, y)
      |}
      |
      |instance JoinLattice[ListSet[t]] with Eq[t] {
      |    pub def leastUpperBound(x: ListSet[t], y: ListSet[t]): ListSet[t] =
      |        ListSet.union(x, y)
      |}
      |
      |instance MeetLattice[ListSet[t]] with Eq[t] {
      |    pub def greatestLowerBound(x: ListSet[t], y: ListSet[t]): ListSet[t] =
      |        ListSet.intersection(x, y)
      |}
      |
      |instance SemiGroup[ListSet[t]] with Eq[t] {
      |    pub def combine(x: ListSet[t], y: ListSet[t]): ListSet[t] =
      |        ListSet.union(x, y)
      |}
      |
      |instance CommutativeSemiGroup[ListSet[t]] with Eq[t]
      |
      |instance Collectable[ListSet[t]] with Eq[t] {
      |    type Elm = t
      |    type Aef = {}
      |    pub def collect(iter: Iterator[t, ef, r]): ListSet[t] \ ef + r =
      |        ListSet.collect(iter)
      |}
      |
      |mod ListSet {
      |    use Eq.{eq, neq}
      |    use Foldable.foldLeft
      |    use JonathanStarup.{UnorderedList => UList}
      |    use JonathanStarup.ListOps
      |
      |    def extract(s: ListSet[t]): List[t] = {
      |        let ListSet(l) = s;
      |        l
      |    }
      |
      |    pub def empty(): ListSet[t] with Eq[t] =
      |        ListSet(Nil)
      |
      |    pub def insert(x: t, s: ListSet[t]): ListSet[t] with Eq[t] =
      |        s |> extract |> listInsert(x) |> ListSet
      |
      |    def listInsert(x: t, l: List[t]): List[t] with Eq[t] =
      |        if (List.memberOf(x, l)) l else x :: l
      |
      |    pub def remove(x: t, s: ListSet[t]): ListSet[t] with Eq[t] =
      |        s |> extract |> listRemove(x) |> ListSet
      |
      |    def listRemove(x: t, l: List[t]): List[t] with Eq[t] =
      |        listRemoveHelper(x, Nil, l)
      |
      |    def listRemoveHelper(x: t, acc: List[t], l: List[t]): List[t] with Eq[t] =
      |        match l {
      |            case hd :: tl =>
      |                if (hd == x) UList.append(acc, tl)
      |                else listRemoveHelper(x, hd :: acc, tl)
      |            case Nil => acc
      |        }
      |
      |    pub def memberOf(x: t, s: ListSet[t]): Bool with Eq[t] =
      |        s |> extract |> List.memberOf(x)
      |
      |    pub def union(s1: ListSet[t], s2: ListSet[t]): ListSet[t] with Eq[t] =
      |        listUnion(extract(s1), extract(s2)) |> ListSet
      |
      |    def listUnion(l1: List[t], l2: List[t]): List[t] with Eq[t] =
      |        (l1, l2) ||> foldLeft(acc -> elm -> listInsert(elm, acc))
      |
      |    pub def intersection(
      |        s1: ListSet[t], s2: ListSet[t]
      |    ): ListSet[t] with Eq[t] =
      |        listIntersection(extract(s1), extract(s2)) |> ListSet
      |
      |    def listIntersection(l1: List[t], l2: List[t]): List[t] with Eq[t] =
      |        l1 |> UList.filter(elm -> List.memberOf(elm, l2))
      |
      |    pub def difference(s1: ListSet[t], s2: ListSet[t]): ListSet[t] with Eq[t] =
      |        listDifference(extract(s1), extract(s2)) |> ListSet
      |
      |    def listDifference(l1: List[t], l2: List[t]): List[t] with Eq[t] =
      |        (l1, l2) ||> foldLeft(acc -> elm -> listRemove(elm, acc))
      |
      |    pub def eq(s1: ListSet[t], s2: ListSet[t]): Bool with Eq[t] =
      |        listEq(extract(s1), extract(s2))
      |
      |    def listEq(l1: List[t], l2: List[t]): Bool with Eq[t] =
      |        ListOps.sizeEq(l1, l2) and listIsSubsetOf(l1, l2)
      |
      |    pub def isSubsetOf(s1: ListSet[t], s2: ListSet[t]): Bool with Eq[t] =
      |        listIsSubsetOf(extract(s1), extract(s2))
      |
      |    def listIsSubsetOf(l1: List[t], l2: List[t]): Bool with Eq[t] =
      |        l1 |> List.forAll(elm -> List.memberOf(elm, l2))
      |
      |    pub def size(s: ListSet[t]): Int32 with Eq[t] =
      |        s |> extract |> List.size
      |
      |    pub def toString(s: ListSet[t]): String with ToString[t], Eq[t] = {
      |        use StringBuilder.appendString;
      |        region rc {
      |            let sb = StringBuilder.empty(rc);
      |            appendString("ListSet(", sb);
      |            match extract(s) {
      |                case hd :: tl =>
      |                    appendString("${hd}", sb);
      |                    tl |> List.forEach(x -> appendString(", ${x}", sb))
      |                case Nil => ()
      |            };
      |            appendString(")", sb);
      |            StringBuilder.toString(sb)
      |        }
      |    }
      |
      |    pub def collect(iter: Iterator[t, ef, r]): ListSet[t] \ ef + r with Eq[t] =
      |        (Nil, iter) ||>
      |            Iterator.foldLeft(s -> elm -> listInsert(elm, s)) |>
      |            ListSet
      |
      |    pub def fromIterable(iter: i): ListSet[elm] \ Iterable.Aef[i] with Iterable[i], Eq[elm] where Iterable.Elm[i] ~ elm =
      |        region local {
      |            iter |> Iterable.iterator(local) |> collect
      |        }
      |
      |    pub def toOrderedSet(f: t -> tt, s: ListSet[t]): Set[tt] with Eq[t], Order[tt] =
      |        region local {
      |            s |> extract |> List.iterator(local) |> Iterator.map(f) |> Collectable.collect
      |        }
      |
      |    pub def eqSizes(s1: ListSet[t], s2: ListSet[t]): Bool with Eq[t] =
      |        ListOps.sizeEq(extract(s1), extract(s2))
      |
      |    pub def count(f: t -> Bool, s: ListSet[t]): Int32 with Eq[t] =
      |        s |> extract |> List.count(f)
      |
      |    pub def exists(f: t -> Bool, s: ListSet[t]): Bool with Eq[t] =
      |        s |> extract |> List.exists(f)
      |
      |    pub def filter(f: t -> Bool, s: ListSet[t]): ListSet[t] with Eq[t] =
      |        s |> extract |> UList.filter(f) |> ListSet
      |
      |    pub def filterMap(
      |        f: t -> Option[tt], s: ListSet[t]
      |    ): ListSet[tt] with Eq[t], Eq[tt] =
      |        s |> extract |> listFilterMap(f) |> ListSet
      |
      |    def listFilterMap(f: t -> Option[tt], l: List[t]): List[tt] with Eq[tt] =
      |        listFilterMapHelper(f, Nil, l)
      |
      |    def listFilterMapHelper(
      |        f: t -> Option[tt], acc: List[tt], l: List[t]
      |    ): List[tt] with Eq[tt] = match l {
      |        case hd :: tl => match f(hd) {
      |            case Some(v) => listFilterMapHelper(f, listInsert(v, acc), tl)
      |            case None => listFilterMapHelper(f, acc, tl)
      |        }
      |        case Nil => acc
      |    }
      |
      |    pub def flatten(s: ListSet[ListSet[t]]): ListSet[t] with Eq[t] =
      |        (Nil, extract(s)) ||>
      |            List.foldLeft(acc -> extract >> listUnion(acc)) |>
      |            ListSet
      |
      |    pub def forAll(f: t -> Bool, s: ListSet[t]): Bool with Eq[t] =
      |        s |> extract |> List.forAll(f)
      |
      |    pub def isEmpty(s: ListSet[t]): Bool with Eq[t] =
      |        s |> extract |> List.isEmpty
      |
      |    pub def nonEmpty(s: ListSet[t]): Bool with Eq[t] =
      |        s |> extract |> List.nonEmpty
      |
      |    pub def isProperSubsetOf(s1: ListSet[t], s2: ListSet[t]): Bool with Eq[t] =
      |        listIsProperSubsetOf(extract(s1), extract(s2))
      |
      |    def listIsProperSubsetOf(l1: List[t], l2: List[t]): Bool with Eq[t] =
      |        ListOps.sizeLessThan(l1, l2) and listIsSubsetOf(l1, l2)
      |
      |    pub def map(f: t -> tt, s: ListSet[t]): ListSet[tt] with Eq[t], Eq[tt] =
      |        s |> extract |> listMap(f) |> ListSet
      |
      |    def listMap(f: t -> tt, l: List[t]): List[tt] with Eq[tt] =
      |        listMapHelper(f, Nil, l)
      |
      |    def listMapHelper(
      |        f: t -> tt, acc: List[tt], l: List[t]
      |    ): List[tt] with Eq[tt] = match l {
      |        case hd :: tl => listMapHelper(f, listInsert(f(hd), acc), tl)
      |        case Nil => acc
      |    }
      |
      |    pub def maximumBy(
      |        cmp: t -> t -> Comparison, s: ListSet[t]
      |    ): Option[t] with Eq[t] =
      |        s |> extract |> List.maximumBy(cmp)
      |
      |    pub def minimumBy(
      |        cmp: t -> t -> Comparison, s: ListSet[t]
      |    ): Option[t] with Eq[t] =
      |        s |> extract |> List.minimumBy(cmp)
      |
      |    pub def partition(
      |        f: t -> Bool, s: ListSet[t]
      |    ): (ListSet[t], ListSet[t]) with Eq[t] =
      |        s |>
      |            extract |>
      |            UList.partition(f) |>
      |            (match (x, y) -> (ListSet(x), ListSet(y)))
      |
      |    pub def range(b: Int32, e: Int32): ListSet[Int32] =
      |        List.range(b, e) |> ListSet
      |
      |    pub def replace(
      |        src: {src = t}, dst: {dst = t}, s: ListSet[t]
      |    ): ListSet[t] with Eq[t] =
      |        s |> extract |> listReplace(src, dst) |> ListSet
      |
      |    def listReplace(
      |        src: {src = t}, dst: {dst = t}, l: List[t]
      |    ): List[t] with Eq[t] =
      |        match UList.removeOpt(src#src, l) {
      |            case Some(removed) => listInsert(dst#dst, removed)
      |            case None => l
      |        }
      |
      |    pub def unfold(
      |        f: state -> Option[(t, state)] \ ef, state: state
      |    ): ListSet[t] \ ef with Eq[t] =
      |        listUnfold(f, Nil, state) |> ListSet
      |
      |    def listUnfold(
      |        f: state -> Option[(t, state)] \ ef, acc: List[t], state0: state
      |    ): List[t] \ ef with Eq[t] =
      |        match f(state0) {
      |            case Some((v, state1)) => listUnfold(f, listInsert(v, acc), state1)
      |            case None => acc
      |        }
      |
      |    pub def unfoldWithIter(
      |        f: Unit -> Option[t] \ ef
      |    ): ListSet[t] \ ef with Eq[t] =
      |        listUnfoldWithIter(f, Nil) |> ListSet
      |
      |    def listUnfoldWithIter(
      |        f: Unit -> Option[t] \ ef, acc: List[t]
      |    ): List[t] \ ef with Eq[t] =
      |        match f() {
      |            case Some(v) => listUnfoldWithIter(f, listInsert(v, acc))
      |            case None => acc
      |        }
      |
      |    pub def sumWith(f: t -> Int32, s: ListSet[t]): Int32 with Eq[t] =
      |        s |> extract |> List.sumWith(f)
      |
      |    pub def subsets(s: ListSet[t]): ListSet[ListSet[t]] with Eq[t] =
      |        s |> extract |> listSubsets |> List.map(ListSet) |> ListSet
      |
      |    def listSubsets(l: List[t]): List[List[t]] with Eq[t] =
      |        (Nil :: Nil, l) ||>
      |            List.foldLeft(
      |                acc -> elm -> listUnion(acc |> List.map(listInsert(elm)), acc)
      |            )
      |
      |    pub def singleton(x: t): ListSet[t] with Eq[t] =
      |        ListSet(x :: Nil)
      |
      |}
      |
      |mod UnorderedList {
      |
      |    pub def append(l1: List[t], l2: List[t]): List[t] = match l1 {
      |        case hd :: tl => append(tl, hd :: l2)
      |        case Nil => l2
      |    }
      |
      |    pub def removeOpt(x: t, l: List[t]): Option[List[t]] with Eq[t] =
      |        removeOptHelper(x, Nil, l)
      |
      |    def removeOptHelper(
      |        x: t, acc: List[t], l: List[t]
      |    ): Option[List[t]] with Eq[t] =
      |        match l {
      |            case hd :: tl =>
      |                if (hd == x) Some(append(acc, tl))
      |                else removeOptHelper(x, hd :: acc, tl)
      |            case Nil => None
      |        }
      |
      |    pub def partition(f: t -> Bool, l: List[t]): (List[t], List[t]) =
      |        partitionHelper(f, Nil, Nil, l)
      |
      |    def partitionHelper(
      |        f: t -> Bool, accTrue: List[t], accFalse: List[t], l: List[t]
      |    ): (List[t], List[t]) =
      |        match l {
      |            case hd :: tl =>
      |                if (f(hd)) partitionHelper(f, hd :: accTrue, accFalse, tl)
      |                else partitionHelper(f, accTrue, hd :: accFalse, tl)
      |            case Nil => (accTrue, accFalse)
      |        }
      |
      |    pub def filter(f: t -> Bool, l: List[t]): List[t] with Eq[t] =
      |        filterHelper(f, Nil, l)
      |
      |    def filterHelper(
      |        f: t -> Bool, acc: List[t], l: List[t]
      |    ): List[t] with Eq[t] =
      |        match l {
      |            case hd :: tl =>
      |                if (f(hd)) filterHelper(f, hd :: acc, tl)
      |                else filterHelper(f, acc, tl)
      |            case Nil => acc
      |        }
      |
      |}
      |
      |mod ListOps {
      |
      |    pub def sizeLessThan(l1: List[t], l2: List[t]): Bool = match (l1, l2) {
      |        case (_ :: tl1, _ :: tl2) => sizeLessThan(tl1, tl2)
      |        case (Nil, _ :: _) => true
      |        case (_, Nil) => false
      |    }
      |
      |    pub def sizeEq(l1: List[t], l2: List[t]): Bool = match (l1, l2) {
      |        case (_ :: next1, _ :: next2) => sizeEq(next1, next2)
      |        case (Nil, Nil) => true
      |        case _ => false
      |    }
      |
      |}
      |
      |}
      |
      |mod JonathanStarup.Test.Property.ListSetGenerator {
      |    use Collectable.collect
      |    use JonathanStarup.ListSet
      |    use Result.Err
      |    use Result.Ok
      |
      |    pub def fromLength(length: Int32): c \ Collectable.Aef[c] + Random with Collectable[c] where Collectable.Elm[c] ~ Int32 =
      |        region local {
      |            fromLengthIterator(local, length) |> collect
      |        }
      |
      |    def fromLengthIterator(rc: Region[r], length: Int32): Iterator[Int32, r + Random, r] \ r =
      |        use Ref.{fresh, get, transform};
      |        let runningLength = fresh(rc, length);
      |        Iterator.iterate(rc, () -> {
      |            if (get(runningLength) <= 0) None
      |            else {
      |                runningLength |> transform(Sub.sub(1));
      |                Some(Random.randomInt32())
      |            }
      |        })
      |
      |    pub def randomIterator(
      |        rc: Region[r], amount: Int32
      |    ): Iterator[c, r + Random + aef, r] \ r
      |    with Collectable[c] where Collectable.Elm[c] ~ Int32, Collectable.Aef[c] ~ aef = {
      |        use Ref.{fresh, get, transform};
      |        let runningAmount = fresh(rc, amount);
      |        let runningLen = fresh(rc, 2);
      |        let iter = Iterator.iterate(rc)(() -> {
      |            if (get(runningAmount) <= 0) None
      |            else {
      |                runningAmount |> transform(x -> x - 1);
      |                let lenInc = nextNatWithMax(5) + 1;
      |                runningLen |> transform(Add.add(lenInc));
      |                Some(fromLength(get(runningLen)))
      |            }
      |        });
      |        def consThing(k, it) = {
      |            let justK = Iterator.singleton(rc, () -> checked_ecast(fromLength(k))) |> Iterator.map(f -> f());
      |            Iterator.append(justK, it)
      |        };
      |        iter |>
      |            consThing(2) |>
      |            consThing(1) |>
      |            consThing(0)
      |    }
      |
      |    def nextNatWithMax(max: Int32): Int32 \ Random = {
      |        Int32.modulo(Random.randomInt32(), Int32.max(max, 1))
      |    }
      |}
      |
      |mod JonathanStarup.Test.Property.TestListSet {
      |    use JonathanStarup.ListSet
      |    use JonathanStarup.Test.Property.ListSetGenerator
      |    use Abort.abort
      |
      |    def runCrash(f: Unit -> Unit \ ef): Bool \ ef + IO - Abort =
      |        run {f(); true} with handler Abort {
      |            def abort(msg, _) = {
      |                blackhole("Test failed: ${msg}");
      |                false
      |            }
      |        }
      |
      |    def _assertEq(x: t, y: t): Unit \ Abort with Eq[t], ToString[t] = {
      |        if (x == y) ()
      |        else abort("${x} != ${y}")
      |    }
      |
      |    def assertExpect(expect: {expect = t}, actual: t): Unit \ Abort with Eq[t], ToString[t] = {
      |        if (expect#expect == actual) ()
      |        else abort("found ${actual} but expected ${expect#expect}")
      |    }
      |
      |    def runTest(
      |        tests: Int32, seed: Int64, prop: c -> Unit \ Abort
      |    ): Bool \ IO + (Collectable.Aef[c] - Abort - Random)
      |    with Collectable[c] where Collectable.Elm[c] ~ Int32 = region local {
      |        let f = () ->
      |            ListSetGenerator.randomIterator(local, tests) |>
      |                Iterator.forEach(prop);
      |        let g = () -> runCrash(f);
      |        Random.runWithSeed(seed, g)
      |    }
      |
      |    pub def testInsertRedundant(): Bool \ IO = {
      |        def prop(l) = {
      |            let s1 = ListSet.fromIterable(l);
      |            let s2 = l |>
      |                List.head |>
      |                Option.map(hd -> ListSet.insert(hd, s1)) |>
      |                Option.getWithDefault(s1);
      |            assertExpect(expect = s1, s2)
      |        };
      |        prop |> runTest(1_000, -6859625i64)
      |    }
      |
      |}
      |
      |pub def runBenchmark(): Unit \ IO = {
      |    JonathanStarup.Test.Property.TestListSet.testInsertRedundant() |> blackhole
      |}
      |""".stripMargin
  }

  private def introduction: String = {
    """
      |enum LocalVar({k = String, v = Constant})
      |
      |enum Constant {
      |      case Top,
      |    case Cst(Int32),
      |      case Bot
      |}
      |
      |instance LowerBound[Constant] {
      |    pub def minValue(): Constant = Constant.Bot
      |}
      |
      |instance Eq[Constant] {
      |    pub def eq(x: Constant, y: Constant): Bool = match (x, y) {
      |        case (Constant.Top, Constant.Top)       => true
      |        case (Constant.Cst(a), Constant.Cst(b)) => a == b
      |        case (Constant.Bot, Constant.Bot)       => true
      |        case _                                  => false
      |    }
      |}
      |
      |instance PartialOrder[Constant] {
      |    pub def lessEqual(e1: Constant, e2: Constant): Bool = match (e1, e2) {
      |        case (Constant.Bot, _)                    => true
      |        case (Constant.Cst(n1), Constant.Cst(n2)) => n1 == n2
      |        case (_, Constant.Top)                    => true
      |        case _                                    => false
      |    }
      |}
      |
      |instance JoinLattice[Constant] {
      |    pub def leastUpperBound(x: Constant, y: Constant): Constant = match (x, y) {
      |        case (Constant.Bot, _)                    => y
      |        case (_, Constant.Bot)                    => x
      |        case (Constant.Cst(n1), Constant.Cst(n2)) => if (n1 == n2) x else Constant.Top
      |        case _                                    => Constant.Top
      |    }
      |}
      |
      |instance MeetLattice[Constant] {
      |    pub def greatestLowerBound(e1: Constant, e2: Constant): Constant = match (e1, e2) {
      |        case (Constant.Top, x)                    => x
      |        case (x, Constant.Top)                    => x
      |        case (Constant.Cst(n1), Constant.Cst(n2)) => if (n1 == n2) e1 else Constant.Bot
      |        case _                                    => Constant.Bot
      |    }
      |}
      |
      |instance Order[Constant] {
      |    pub def compare(x: Constant, y: Constant): Comparison = match (x, y) {
      |        case (Constant.Bot, Constant.Bot)         => Comparison.EqualTo
      |        case (Constant.Bot, Constant.Cst(_))      => Comparison.LessThan
      |        case (Constant.Bot, Constant.Top)         => Comparison.LessThan
      |        case (Constant.Cst(_), Constant.Bot)      => Comparison.GreaterThan
      |        case (Constant.Cst(v1), Constant.Cst(v2)) => v1 <=> v2
      |        case (Constant.Cst(_), Constant.Top)      => Comparison.LessThan
      |        case (Constant.Top, Constant.Bot)         => Comparison.GreaterThan
      |        case (Constant.Top, Constant.Cst(_))      => Comparison.GreaterThan
      |        case (Constant.Top, Constant.Top)         => Comparison.EqualTo
      |    }
      |}
      |
      |instance ToString[Constant] {
      |    pub def toString(x: Constant): String = match x {
      |        case Constant.Top    => "Constant.Top"
      |        case Constant.Cst(n) => "Constant.Cst(${n})"
      |        case Constant.Bot    => "Constant.Bot"
      |    }
      |}
      |
      |def alpha(i: Int32): Constant = Constant.Cst(i)
      |
      |def sum(e1: Constant, e2: Constant): Constant = match (e1, e2) {
      |    case (Constant.Bot, _)                    => Constant.Bot
      |    case (_, Constant.Bot)                    => Constant.Bot
      |    case (Constant.Cst(n1), Constant.Cst(n2)) => Constant.Cst(n1 + n2)
      |    case _                                    => Constant.Top
      |}
      |
      |def div(e1: Constant, e2: Constant): Constant = match (e1, e2) {
      |    case (_, Constant.Bot)                    => Constant.Bot
      |    case (Constant.Bot, _)                    => Constant.Bot
      |    case (Constant.Cst(n1), Constant.Cst(n2)) => if (n2 == 0) Constant.Bot else Constant.Cst(n1 / n2)
      |    case _                                    => Constant.Top
      |}
      |
      |def isMaybeZero(e: Constant): Bool = match e {
      |    case Constant.Bot    => false
      |    case Constant.Cst(n) => n == 0
      |    case Constant.Top    => true
      |}
      |
      |def runBenchmark(): Unit \ IO = {
      |    let p = #{
      |        LocalVar(r; alpha(c)) :- LitStm(r, c).
      |        LocalVar(r; sum(v1, v2)) :- AddStm(r, x, y),
      |                                    LocalVar(x; v1),
      |                                    LocalVar(y; v2).
      |
      |        LocalVar(r; div(v1, v2)) :- DivStm(r, x, y),
      |                                    LocalVar(x; v1),
      |                                    LocalVar(y; v2).
      |
      |        ArithmeticError(r) :- DivStm(r, _n, d),
      |                              LocalVar(d; y),
      |                              if (isMaybeZero(y)).
      |
      |        LitStm("x", 3).        // x = 3
      |        LitStm("y", 7).        // y = 7
      |        LitStm("z", 0).        // z = 0
      |        AddStm("w", "x", "y"). // w = x + y
      |        DivStm("v", "w", "z"). // v = w / z
      |    };
      |    let vars = query p select (a, b) from LocalVar(a; b);
      |    let errs = query p select r from ArithmeticError(r);
      |    blackhole(vars);
      |    blackhole(errs)
      |}
      |
      |""".stripMargin
  }

  private def parsers: String = {
    """
      |pub def runBenchmark(): Unit \ IO = {
      |    ArithParser.parse("1+((2/3+4*(5*(6/7)))+41)")
      |    |> Option.map(eval)
      |    |> blackhole
      |}
      |
      |enum Exp with Eq, ToString {
      |    case Num(Int32),
      |    case Add(Exp, Exp),
      |    case Sub(Exp, Exp),
      |    case Mul(Exp, Exp),
      |    case Div(Exp, Exp)
      |}
      |
      |def eval(exp0: Exp): Int32 = match exp0 {
      |    case Exp.Num(n)          => n
      |    case Exp.Add(exp1, exp2) => eval(exp1) + eval(exp2)
      |    case Exp.Sub(exp1, exp2) => eval(exp1) - eval(exp2)
      |    case Exp.Mul(exp1, exp2) => eval(exp1) * eval(exp2)
      |    case Exp.Div(exp1, exp2) => eval(exp1) / eval(exp2)
      |}
      |
      |mod ArithParser {
      |    use Parser.{nibble, number, literal, using, otherwise, then, thenIgnoringLeft, thenIgnoringRight};
      |
      |    pub def parse(s: String): Option[Exp] =
      |        let prog = Parser.fromString(s) |> exp;
      |        prog |> DelayList.head |> Option.map(fst)
      |
      |    def exp(input: Input[Char]): ParseResult[Exp, Char] = input |> (
      |        ((term `thenIgnoringRight` literal('+') `then` term) `using` plus)  `otherwise`
      |        ((term `thenIgnoringRight` literal('-') `then` term) `using` minus) `otherwise`
      |        term
      |    )
      |
      |    def term(input: Input[Char]): ParseResult[Exp, Char] = input |> (
      |        ((factor `thenIgnoringRight` literal('*') `then` factor) `using` times)  `otherwise`
      |        ((factor `thenIgnoringRight` literal('/') `then` factor) `using` divide) `otherwise`
      |        factor
      |    )
      |
      |    def factor(input: Input[Char]): ParseResult[Exp, Char] = input |> (
      |        (nibble(number) `using` value) `otherwise`
      |        (nibble(literal('(')) `thenIgnoringLeft` exp `thenIgnoringRight` nibble(literal(')')))
      |    )
      |
      |    def value(nums: Input[Char]): Exp =
      |        let optInt = Parser.stringify(nums) |> Int32.fromString;
      |        match optInt {
      |            case Some(n) => Exp.Num(n)
      |            case None    => unreachable!()
      |        }
      |
      |    def plus(exp: (Exp, Exp)): Exp = match exp {
      |        case (left, right) => Exp.Add(left, right)
      |    }
      |
      |    def minus(exp: (Exp, Exp)): Exp = match exp {
      |        case (left, right) => Exp.Sub(left, right)
      |    }
      |
      |    def times(exp: (Exp, Exp)): Exp = match exp {
      |        case (left, right) => Exp.Mul(left, right)
      |    }
      |
      |    def divide(exp: (Exp, Exp)): Exp = match exp {
      |        case (left, right) => Exp.Div(left, right)
      |    }
      |}
      |
      |pub type alias Input[a] = DelayList[a]
      |
      |pub type alias ParseResult[a, b] = DelayList[(a, Input[b])]
      |
      |pub type alias Parser[a, b] = Input[b] -> ParseResult[a, b]
      |
      |mod Parser {
      |
      |    use DelayList.{ENil, ECons, LCons, LList};
      |
      |    pub def succeed(a: a): Parser[a, b] =
      |        inp -> ECons((a, inp), ENil)
      |
      |    pub def fail(_: Input[b]): ParseResult[a, b] =
      |        ENil
      |
      |    pub def satisfy(p: a -> Bool): Parser[a, a] =
      |        inp -> match inp {
      |            case ENil                 => fail(inp)
      |            case ECons(x, xs) if p(x) => succeed(x,       xs)
      |            case LCons(x, xs) if p(x) => succeed(x, force xs)
      |            case LList(xs)            => LList(lazy satisfy(p, force xs))
      |            case _                    => fail(inp)
      |        }
      |
      |    pub def literal(a: a): Parser[a, a] with Eq[a] =
      |        satisfy(Eq.eq(a))
      |
      |    pub def otherwise(p1: Parser[a, b], p2: Parser[a, b]): Parser[a, b] =
      |        inp -> DelayList.append(p1(inp), p2(inp))
      |
      |    pub def then(p1: Parser[a, b], p2: Parser[c, b]): Parser[(a, c), b] =
      |        inp ->
      |            forM (
      |                (x1, rest1) <- p1(inp);
      |                (x2, rest2) <- p2(rest1)
      |            ) yield ((x1, x2), rest2)
      |
      |    pub def thenIgnoringLeft(p1: Parser[a, b], p2: Parser[c, b]): Parser[c, b] =
      |        (p1 `then` p2) `using` snd
      |
      |    pub def thenIgnoringRight(p1: Parser[a, b], p2: Parser[c, b]): Parser[a, b] =
      |        (p1 `then` p2) `using` fst
      |
      |    pub def using(p: Parser[a, b], f: a -> c): Parser[c, b] =
      |        inp ->
      |            forM (
      |                (x, rest) <- p(inp)
      |            ) yield (f(x), rest)
      |
      |    pub def many(p: Parser[a, b]): Parser[DelayList[a], b] =
      |        inp -> inp // Wrap in lambda so the recursive call does not immediately happen
      |            |> (((p `then` many(p)) `using` cons) `otherwise` succeed(ENil))
      |
      |    pub def some(p: Parser[a, b]): Parser[DelayList[a], b] =
      |        (p `then` many(p)) `using` cons
      |
      |    pub def number(inp: Input[Char]): ParseResult[DelayList[Char], Char] =
      |        let digit = c -> '0' <= c and c <= '9';
      |        inp |> some(satisfy(digit))
      |
      |    pub def word(inp: Input[Char]): ParseResult[DelayList[Char], Char] =
      |        let lowercase = c -> 'a' <= c and c <= 'z';
      |        let uppercase = c -> 'A' <= c and c <= 'Z';
      |        let letter = c -> lowercase(c) or uppercase(c);
      |        inp |> some(satisfy(letter))
      |
      |    pub def literalSequence(lit: m[a]): Parser[DelayList[a], a] \ Foldable.Aef[m] with Eq[a], Foldable[m] =
      |        literalSequenceHelper(Foldable.toList(lit))
      |
      |    def literalSequenceHelper(lit: List[a]): Parser[DelayList[a], a] with Eq[a] =
      |        inp -> inp // Wrap in lambda so the recursive call does not immediately happen
      |            |> match lit {
      |                case Nil     => succeed(ENil)
      |                case x :: xs => (literal(x) `then` (literalSequenceHelper(xs))) `using` cons
      |            }
      |
      |    pub def return(p: Parser[a, b], c: c): Parser[c, b] =
      |        p `using` constant(c)
      |
      |    pub def string(s: String): Parser[DelayList[Char], Char] =
      |        s |> (String.toList >> literalSequence)
      |
      |    pub def nibble(p: Parser[a, Char]): Parser[a, Char] =
      |        whitespace `thenIgnoringLeft` p `thenIgnoringRight` whitespace
      |
      |    pub def whitespace(inp: Input[Char]): ParseResult[DelayList[Char], Char] =
      |        let chars = String.toList(" \t\n");
      |        inp |> (many(any(literal, chars)))
      |
      |    pub def any(f: a -> Parser[b, c], syms: m[a]): Parser[b, c] \ Foldable.Aef[m] with Foldable[m] =
      |        Foldable.foldRight(f >> otherwise, fail, syms)
      |
      |    pub def fromString(s: String): Input[Char] =
      |        String.toList(s) |> List.toDelayList
      |
      |    pub def stringify(chars: m[Char]): String \ Foldable.Aef[m] with Foldable[m] = region r {
      |        let sb = StringBuilder.empty(r);
      |        let ap = sb |> flip(StringBuilder.append);
      |        Foldable.forEach(ap, chars);
      |        StringBuilder.toString(sb)
      |    }
      |
      |    def cons(xs: (a, DelayList[a])): DelayList[a] =
      |        ECons(fst(xs), snd(xs))
      |}
      |""".stripMargin
  }

  private def railRoadNetwork: String = {
    """
      |def safeConnects(src: n, links: f[(n, n)]): {safe = Vector[n], unsafe1 = Vector[n]} \ Foldable.Aef[f] with Foldable[f], Order[n] =
      |    let db = inject links into Link;
      |    let pr = #{
      |        Linked(a, b) :- Link(a, b).
      |        Linked(a, b) :- Link(b, a).
      |
      |        Connected(a, b) :- Linked(a, b).
      |        Connected(a, b) :- Connected(a, c), Linked(c, b).
      |
      |        Cutpoint(x, a, b) :- Connected(a, b), Station(x), not Circumvent(x, a, b).
      |
      |        Circumvent(x, a, b) :- Linked(a, b), if (x != a), Station(x), if (x != b).
      |        Circumvent(x, a, b) :- Circumvent(x, a, c), Circumvent(x, c, b).
      |
      |        HasICutPoint(a, b) :- Cutpoint(x, a, b), if (x != a), if (x != b).
      |        SafelyConnected(a, b) :- Connected(a, b), not HasICutPoint(a, b).
      |        UnsafelyConnected(a, b) :- Station(a), Station(b), not SafelyConnected(a, b).
      |        Station(src).
      |        Station(x) :- Linked(x, _).
      |    };
      |    let model = solve db <+> pr;
      |    let safe = query model select b from SafelyConnected(src, b);
      |    let unsafe1 = query model select b from UnsafelyConnected(src, b);
      |    {safe = safe, unsafe1 = unsafe1}
      |
      |def exampleGraph(): Set[(String, String)] =
      |    let _graphString =
      |        "             ┌───────┐   ┌───────┐             " ::
      |        "     ┌───────┤ semel ├───┤  bis  │             " ::
      |        "     │       └───┬───┘   └───┬───┘             " ::
      |        "     │           │           │                 " ::
      |        " ┌───┴───┐   ┌───┴───┐   ┌───┴───┐   ┌───────┐ " ::
      |        " │ clote ├───┤quincy ├───┤  ter  ├───┤ olfe  │ " ::
      |        " └───┬───┘   └───┬───┘   └───┬───┘   └───────┘ " ::
      |        "     │           │           │                 " ::
      |        "     │       ┌───┴───┐   ┌───┴───┐             " ::
      |        "     └───────┤ mamuk ├───┤ icsi  │             " ::
      |        "             └┬─────┬┘   └───────┘             " ::
      |        "              │     │                          " ::
      |        "       ┌──────┴┐   ┌┴──────┐                   " ::
      |        "       │ dalte ├───┤quater │                   " ::
      |        "       └───────┘   └───────┘                   " ::
      |        Nil;
      |    Set#{
      |        ("semel", "bis"   ),
      |        ("semel", "quincy"),
      |        ("semel", "clote" ),
      |        ("bis"  , "ter"   ),
      |        ("ter"  , "olfe"  ),
      |        ("ter"  , "quincy"),
      |        ("ter"  , "icsi"  ),
      |        ("icsi" , "mamuk" ),
      |        ("mamuk", "quincy"),
      |        ("mamuk", "clote" ),
      |        ("mamuk", "quater"),
      |        ("mamuk", "dalte" ),
      |        ("clote", "quincy"),
      |        ("dalte", "quater")
      |    }
      |
      |def runBenchmark(): Unit \ IO = {
      |    safeConnects("bis", exampleGraph()) |> blackhole
      |}
      |""".stripMargin
  }

  private def sequence: String = {
    """
      |def runBenchmark(): Unit \ IO = {
      |
      |    let numLetters = #{ NumLetters(20). };
      |
      |    let lp = #{
      |
      |        ////////////// Arithmetic ////////////////
      |
      |        N(0).
      |        N(x + 1) :- N(x), NumLetters(n), if (x < n).
      |
      |        S(x, x+1) :- N(x).
      |
      |        Add(x, 0, x) :- N(x).
      |        Add(x, y, r) :- S(py,y), Add(x, py, pr), S(pr, r).
      |
      |        Mul(x,0,0) :- N(x).
      |        Mul(x, y, r) :- S(py, y), Mul(x, py, pr), Add(pr, x, r).
      |
      |        Exp(x,0,1) :- N(x).
      |        Exp(x, y, r) :- S(py, y), Exp(x, py, pr), Mul(pr, x, r).
      |
      |        Log(x, b, r) :- Exp(b, r, y), S(r, sr), Exp(b, sr, y2), N(x), if (y <= x and x < y2).
      |
      |        Div(x, y, r) :- Mul(r, y, a), Add(a, z, x), if (0 <= z and z < y).
      |
      |        Mod(x, y, r) :- Mul(y, _, z), Add(z, r, x), if (0 <= r and r < y).
      |
      |        ////////////// Trie ////////////////
      |
      |        TrieLetter(i, r) :- S(x, i), NumLetters(n), Mod(x, n, r).
      |
      |        TrieLevelEnd(0, 0).
      |        TrieLevelEnd(l, i) :- NumLetters(n), S(pl, l), TrieLevelEnd(pl, b), Exp(n, l, p), Add(b, p, i).
      |
      |        TrieLevelStart(0, 0).
      |        TrieLevelStart(l, i) :- S(pl, l), TrieLevelEnd(pl, b), Add(b, 1, i).
      |
      |        TrieLevel(0, 0).
      |        TrieLevel(i, b) :- N(i), S(a, b), TrieLevelEnd(a, low), TrieLevelEnd(b, high), if (low < i and i <= high).
      |
      |        TrieParent(i, p) :- NumLetters(n), TrieLevel(i, l), S(pl, l), TrieLevelStart(l, b), Add(b, x, i), Div(x, n, o), TrieLevelStart(pl, c), Add(c, o, p).
      |
      |        TrieRoot(0).
      |
      |        Trie(x) :- TrieLetter(x,_).
      |
      |        ////////////// all Strings over the alphabet ////////////////
      |
      |        Str(x) :- Trie(x).
      |
      |        StrLen(id, l) :- TrieLevel(id, l).
      |
      |        StrChain(id, id) :- Trie(id).
      |        StrChain(id, p) :- StrChain(id, x), TrieParent(x, p).
      |
      |        StrLetterAt(id, pos, l) :- StrChain(id, p), TrieLevel(p, pos), TrieLetter(p, l).
      |
      |        ////////////// example sequences ////////////////////
      |
      |        // search all Palindrome
      |        PalinAux(s, x, x) :- Str(s), N(x), StrLen(s, l), if (x <= l).
      |        PalinAux(s, x, x+1) :- StrLetterAt(s, x, _).
      |        PalinAux(s, x, sy) :- StrLetterAt(s, x, a), S(x, sx), PalinAux(s, sx, y), StrLetterAt(s, y, a), S(y, sy).
      |
      |        Palindrome(s) :- StrLen(s, 0).
      |        Palindrome(s) :- PalinAux(s, 1, sl), StrLen(s, l), S(l, sl).
      |
      |        DebugStr(18).
      |
      |        Read(x,y) :- DebugStr(s), StrLetterAt(s,x,y).
      |
      |    };
      |    query lp <+> numLetters select (x, y) from Read(x, y) |> blackhole
      |}
      |
      |""".stripMargin
  }

  private def singleSourceShortestDistance: String = {
    """
      |mod ShortestDistance {
      |
      |    use Down.Down;
      |
      |    pub def sssd(src: t, g: m[(t, Int32, t)]): Map[t, Int32] \ Foldable.Aef[m] with Foldable[m], Order[t] = {
      |        let edges = inject g into Edge;
      |        let dists = #{
      |            Dist(src; Down(0)).
      |            Dist(y; d + Down(w)) :- Dist(x; d), Edge(x, w, y).
      |        };
      |        let res = query edges, dists select (x, coerce(d)) from Dist(x; d);
      |        res |> Vector.toMap
      |    }
      |
      |    pub def exampleGraph04(): Set[(Int32, Int32, Int32)] =
      |        Set#{  (0, 10, 1), (0, 10, 4 ), (0, 10, 7 ), (1, 20, 2), (2, 5, 3),
      |               (2, 10, 5), (3, 5 , 10), (4, 15, 1 ), (4, 20, 5), (5, 5, 7),
      |               (5, 30, 6), (6, 2 , 9 ), (6, 5 , 2 ), (6, 20, 10), (7, 5 , 8),
      |               (8, 5 , 6), (8, 10, 9 ), (9, 30, 10)
      |            }
      |}
      |
      |def runBenchmark(): Unit \ IO = {
      |    ShortestDistance.sssd(0, ShortestDistance.exampleGraph04()) |> blackhole
      |}
      |
      |""".stripMargin
  }

  private def singleSourceShortestPaths: String = {
    """
      |mod ShortestPath {
      |
      |    use Path.{Path, Bot};
      |
      |    pub def sssp(src: t, g: m[(t, t)]): Map[t, Vector[t]] \ Foldable.Aef[m] with Foldable[m], Order[t] = {
      |        let edges = inject g into Edge;
      |        let rules = #{
      |            Reach(x, y; init(y, x)) :- Edge(x, y).
      |            Reach(x, z; cons(z, p)) :- Reach(x, y; p), Edge(y, z).
      |        };
      |        let res = query edges, rules select (t, p) from Reach(src, t; p);
      |        res |> Functor.map(match (t, p) -> (t, Foldable.toVector(p) |> Vector.reverse))
      |            |> Foldable.toMap
      |    }
      |
      |    pub enum Path[a] with ToString {
      |        case Path(List[a])
      |        case Bot
      |    }
      |
      |    instance Eq[Path[a]] {
      |        pub def eq(x: Path[a], y: Path[a]): Bool = match (x, y) {
      |            case (Bot, Bot)           => true
      |            case (Path(xs), Path(ys)) => List.length(xs) == List.length(ys)
      |            case _                    => false
      |        }
      |    }
      |
      |    instance Order[Path[a]] with Order[a] {
      |        pub def compare(x: Path[a], y: Path[a]): Comparison = match (x, y) {
      |            case (Bot, Bot)                 => Comparison.EqualTo
      |            case (Bot, _)                   => Comparison.LessThan
      |            case (_, Bot)                   => Comparison.GreaterThan
      |            case (Path(list1), Path(list2)) => list1 <=> list2
      |        }
      |    }
      |
      |    instance LowerBound[Path[a]] {
      |        // The longest list
      |        pub def minValue(): Path[a] = Bot
      |    }
      |
      |    instance PartialOrder[Path[a]] {
      |        pub def lessEqual(x: Path[a], y: Path[a]): Bool = match (x, y) {
      |            case (Bot, _)             => true
      |            case (Path(xs), Path(ys)) => List.length(xs) >= List.length(ys)
      |            case _                    => false
      |        }
      |    }
      |
      |    instance JoinLattice[Path[a]] {
      |        pub def leastUpperBound(x: Path[a], y: Path[a]): Path[a] = match (x, y) {
      |            case (Bot, p)             => p
      |            case (p, Bot)             => p
      |            case (Path(xs), Path(ys)) => if (List.length(xs) <= List.length(ys)) x else y
      |        }
      |    }
      |
      |    instance MeetLattice[Path[a]] {
      |        pub def greatestLowerBound(x: Path[a], y: Path[a]): Path[a] = match (x, y) {
      |            case (Bot, _)             => Bot
      |            case (_, Bot)             => Bot
      |            case (Path(xs), Path(ys)) => if (List.length(xs) > List.length(ys)) x else y
      |        }
      |    }
      |
      |    instance Foldable[Path] {
      |        pub def foldLeft(f: b -> (a -> b \ ef), s: b, t: Path[a]): b \ ef = match t {
      |            case Bot     => s
      |            case Path(p) => Foldable.foldLeft(f, s, p)
      |        }
      |
      |        pub def foldRight(f: a -> (b -> b \ ef), s: b, t: Path[a]): b \ ef = match t {
      |            case Bot     => s
      |            case Path(p) => Foldable.foldRight(f, s, p)
      |        }
      |
      |        pub def foldRightWithCont(f: a -> ((Unit -> b \ ef) -> b \ ef), s: b, t: Path[a]): b \ ef = match t {
      |            case Bot     => s
      |            case Path(p) => Foldable.foldRightWithCont(f, s, p)
      |        }
      |    }
      |
      |    pub def init(y: a, x: a): Path[a] =
      |        Path(y :: x :: Nil)
      |
      |    pub def cons(z: a, p: Path[a]): Path[a] = match p {
      |        case Bot      => Bot
      |        case Path(xs) => Path(z :: xs)
      |    }
      |
      |    pub def exampleGraph01(): Set[(Int32, Int32)] =
      |        Set#{ (0, 1), (0, 3), (1, 4), (1, 2), (1, 3), (2, 5), (3, 4), (4, 2), (4, 5) }
      |}
      |
      |def runBenchmark(): Unit \ IO = {
      |    ShortestPath.sssp(0, ShortestPath.exampleGraph01()) |> blackhole
      |}
      |
      |""".stripMargin
  }

  private def singleSourceShortestPathsArbitrary: String = {
    """
      |mod ShortestPathN {
      |
      |    use Path.{Path, Bot};
      |
      |    pub def ssspn(src: t, g: m[(t, Int32, t)]): Map[t, Vector[t]] \Foldable.Aef[m] with Foldable[m], Order[t] = {
      |        let edges = inject g into Edge;
      |        let rules = #{
      |            Reach(x, y; init(y, l, x)) :- Edge(x, l, y).
      |            Reach(x, z; cons(z, l, p)) :- Reach(x, y; p), Edge(y, l, z).
      |        };
      |        let res = query edges, rules select (t, p) from Reach(src, t; p);
      |        res |> Functor.map(match (t, p) -> (t, Foldable.toVector(p) |> Vector.reverse))
      |            |> Foldable.toMap
      |    }
      |
      |    pub enum Path[a] with ToString {
      |        case Path(List[a], Int32)
      |        case Bot
      |    }
      |
      |    instance Eq[Path[a]] {
      |        pub def eq(x: Path[a], y: Path[a]): Bool = match (x, y) {
      |            case (Bot, Bot)                 => true
      |            case (Path(_, l1), Path(_, l2)) => l1 == l2
      |            case _                          => false
      |        }
      |    }
      |
      |    instance Order[Path[a]] with Order[a] {
      |        pub def compare(x: Path[a], y: Path[a]): Comparison = match (x, y) {
      |            case (Bot, Bot)                 => Comparison.EqualTo
      |            case (Bot, _)                   => Comparison.LessThan
      |            case (_, Bot)                   => Comparison.GreaterThan
      |            case (Path(list1, l1), Path(list2, l2)) =>
      |                let comp1 = l1 <=> l2;
      |                if(comp1 != Comparison.EqualTo) {
      |                    comp1
      |                } else {
      |                    list1 <=> list2
      |                }
      |        }
      |    }
      |
      |    instance LowerBound[Path[a]] {
      |        pub def minValue(): Path[a] = Bot
      |    }
      |
      |    instance PartialOrder[Path[a]] {
      |        pub def lessEqual(x: Path[a], y: Path[a]): Bool = match (x, y) {
      |            case (Bot, _)                   => true
      |            case (Path(_, l1), Path(_, l2)) => l1 >= l2
      |            case _                          => false
      |        }
      |    }
      |
      |    instance JoinLattice[Path[a]] {
      |        pub def leastUpperBound(x: Path[a], y: Path[a]): Path[a] = match (x, y) {
      |            case (Bot, p)                   => p
      |            case (p, Bot)                   => p
      |            case (Path(_, l1), Path(_, l2)) => if (l1 <= l2) x else y
      |        }
      |    }
      |
      |    instance MeetLattice[Path[a]] {
      |        pub def greatestLowerBound(x: Path[a], y: Path[a]): Path[a] = match (x, y) {
      |            case (Bot, _)                   => Bot
      |            case (_, Bot)                   => Bot
      |            case (Path(_, l1), Path(_, l2)) => if (l1 > l2) x else y
      |        }
      |    }
      |
      |    instance Foldable[Path] {
      |        pub def foldLeft(f: b -> (a -> b \ ef), s: b, t: Path[a]): b \ ef = match t {
      |            case Bot     => s
      |            case Path(p, _) => Foldable.foldLeft(f, s, p)
      |        }
      |
      |        pub def foldRight(f: a -> (b -> b \ ef), s: b, t: Path[a]): b \ ef = match t {
      |            case Bot     => s
      |            case Path(p, _) => Foldable.foldRight(f, s, p)
      |        }
      |
      |        pub def foldRightWithCont(f: a -> ((Unit -> b \ ef) -> b \ ef), s: b, t: Path[a]): b \ ef = match t {
      |            case Bot     => s
      |            case Path(p, _) => Foldable.foldRightWithCont(f, s, p)
      |        }
      |    }
      |
      |    pub def init(y: a,  l: Int32, x: a): Path[a] =
      |        Path(y :: x :: Nil, l)
      |
      |    pub def cons(z: a, l: Int32, p: Path[a]): Path[a] = match (p) {
      |        case Bot          => Bot
      |        case Path(xs, l1) => Path(z :: xs, l1 + l)
      |    }
      |
      |    pub def indexOf(x: a, p: Path[a]): Option[Int32] with Eq[a] = match p {
      |        case Bot         => None
      |        case Path(xs, _) => List.indexOf(x, xs)
      |    }
      |
      |    pub def exampleGraph04(): Set[(Int32, Int32, Int32)] =
      |        Set#{  (0, 1, 1), (0, 3 , 4 ), (0, 10, 7 ), (1, 1, 2 ), (2, 1 , 3),
      |               (2, 1, 5), (3, 1 , 10), (4, 1 , 1 ), (4, 3, 5 ), (5, 1 , 7),
      |               (5, 3, 6), (6, 1 , 9 ), (6, 1 , 2 ), (6, 3, 10), (7, 10, 8),
      |               (8, 1, 6), (8, 10, 9 ), (9, 10, 10)
      |            }
      |}
      |
      |def runBenchmark(): Unit \ IO = {
      |    ShortestPathN.ssspn(0, ShortestPathN.exampleGraph04()) |> blackhole
      |}
      |
      |""".stripMargin
  }

  private def stratifier: String = {
    """
      |mod Stratifier {
      |    use Int32.max
      |    use List.{map, flatMap, partition}
      |
      |    pub enum Program(List[Constraint])
      |    pub enum Constraint(HeadAtom, List[BodyAtom])
      |    pub enum Atom(PredicateSymbol)
      |    pub enum HeadAtom(Atom)
      |    pub enum BodyAtom {
      |        case Positive(Atom)
      |        case Negative(Atom)
      |    }
      |    pub enum PredicateSymbol(String) with ToString, Eq, Order
      |
      |    type alias PrecedenceEdge = (PredicateSymbol, Bool, PredicateSymbol)
      |    type alias PrecedenceGraph = List[PrecedenceEdge]
      |
      |    def convertProgram(p: Program): PrecedenceGraph =
      |        let Program.Program(c) = p;
      |        flatMap(convertConstraint, c)
      |
      |    def convertConstraint(c: Constraint): PrecedenceGraph =
      |        let Constraint.Constraint(HeadAtom.HeadAtom(Atom.Atom(a0)), b) = c;
      |        let unfoldBodyAtom = ba -> match ba {
      |            case BodyAtom.Positive(Atom.Atom(ps)) => (true, ps),
      |            case BodyAtom.Negative(Atom.Atom(ps)) => (false, ps)
      |        };
      |        b |> map(unfoldBodyAtom) |> map(pna -> match pna {case (pn, a) => (a0, pn, a)})
      |
      |    pub def ullman(p: Program, numberOfPredicates: Int32): Option[Map[PredicateSymbol, Int32]] =
      |        let pg: PrecedenceGraph = convertProgram(p);
      |        let (pos, neg) = partition(e -> match e {case (_, b, _) => b}, pg);
      |        let removeBool = triple -> match triple {case (a, _, b) => (a, b)};
      |        let facts = inject map(removeBool, pos), map(removeBool, neg) into PositiveDependencyEdge, NegativeDependencyEdge;
      |        let rules = #{
      |            Stratum(pd; 0) :- PositiveDependencyEdge(pd, _).
      |            Stratum(pd; 0) :- PositiveDependencyEdge(_, pd).
      |            Stratum(pd; 0) :- NegativeDependencyEdge(pd, _).
      |            Stratum(pd; 0) :- NegativeDependencyEdge(_, pd).
      |            Stratum(ph; max(pbs, phs)) :- PositiveDependencyEdge(ph, pb), Stratum(pb; pbs), Stratum(ph; phs).
      |            Stratum(ph; max(pbs + 1, phs)) :-
      |                NegativeDependencyEdge(ph, pb),
      |                Stratum(pb; pbs),
      |                Stratum(ph; phs),
      |                if (pbs < numberOfPredicates).
      |                // allow one level of strata above the bound for a stratification check later
      |        };
      |        let solution = solve facts, rules;
      |        let m = query solution select (pd, s) from Stratum(pd; s) |> Vector.toMap;
      |        let notStratified = Map.exists((_, stratum) -> stratum >= numberOfPredicates, m);
      |        if (notStratified)
      |            None
      |        else
      |            Some(m)
      |
      |}
      |
      |def runBenchmark(): Unit \ IO = {
      |    use Stratifier.{Program, Constraint, Atom, HeadAtom, BodyAtom, PredicateSymbol};
      |    let p = Program.Program(
      |        Constraint.Constraint(HeadAtom.HeadAtom(Atom.Atom(PredicateSymbol.PredicateSymbol("A"))), BodyAtom.Positive(Atom.Atom(PredicateSymbol.PredicateSymbol("B"))) :: BodyAtom.Positive(Atom.Atom(PredicateSymbol.PredicateSymbol("C"))) :: Nil) ::
      |        Constraint.Constraint(HeadAtom.HeadAtom(Atom.Atom(PredicateSymbol.PredicateSymbol("B"))), BodyAtom.Positive(Atom.Atom(PredicateSymbol.PredicateSymbol("D"))) :: Nil) ::
      |        Constraint.Constraint(HeadAtom.HeadAtom(Atom.Atom(PredicateSymbol.PredicateSymbol("C"))), BodyAtom.Negative(Atom.Atom(PredicateSymbol.PredicateSymbol("D"))) :: Nil) ::
      |        Constraint.Constraint(HeadAtom.HeadAtom(Atom.Atom(PredicateSymbol.PredicateSymbol("D"))), BodyAtom.Negative(Atom.Atom(PredicateSymbol.PredicateSymbol("A"))) :: Nil) ::
      |        Nil
      |    );
      |    let result = Stratifier.ullman(p, 4);
      |    let rs = match result {
      |        case None => "Not Stratified"
      |        case Some(res) => ToString.toString(res)
      |    };
      |    "Output:\n${rs}\nExpected:\nNot Stratified" |> blackhole
      |}
      |
      |""".stripMargin
  }

  private def talpin1992: String = {
    Files.lines(Path.of("./Talpin1992.flix").normalize()).toArray.mkString("\n")
  }

  private def flixJson: String = {
    Files.lines(Path.of("./FlixJson.flix").normalize()).toArray.mkString("\n")
  }

  private def Python: String =
    """
      |# $ pip install matplotlib numpy
      |
      |import json
      |import matplotlib.pyplot as plt
      |import matplotlib.lines as mlines
      |import numpy as np
      |
      |def get_normalized_data_with_program(metric: str, inliner_type: str, data):
      |    \"\"\"
      |    Returns the data for a given metric and inliner type sampled from all runs in the shape
      |    of a list of 3-tuples.
      |    For an entry `[pr, xs, ys]`, `pr` is the name of the program, `xs` is the number of inlining rounds
      |    and `ys` is the metric normalized by the same metric when no inlining was made.
      |    \"\"\"
      |    ps = []
      |    for obj in data['programs']:
      |        pr = obj['programName']
      |        xs = []
      |        ys = []
      |        norm = None # Should crash if we do not find the norm first
      |        for run in obj['results']:
      |            if run['inlinerType'] == 'NoInliner':
      |                norm = run[metric]
      |        for run in obj['results']:
      |            if run['inlinerType'].lower() == inliner_type.lower():
      |                xs.append(run['inliningRounds'])
      |                ys.append(run[metric] / norm)
      |        ps.append([pr, xs, ys])
      |    return ps
      |
      |def get_data_for(metric: str, inliner_type: str, inliner_rounds: int, data):
      |    result = []
      |    for benchmark in data['programs']:
      |        for run in benchmark['results']:
      |            it = run['inlinerType'].lower()
      |            ir = run['inliningRounds']
      |            if it == inliner_type.lower() and ir == inliner_rounds:
      |                result.append([benchmark['programName'], run[metric]])
      |    return result
      |
      |def gen_colors(n):
      |    \"\"\"
      |    Returns n distinct colors, up to 13.
      |    \"\"\"
      |    lim = 13
      |    if n > lim:
      |        raise Exception(f"parameter n was {n} but can at most be {lim}")
      |    colors = list(map(lambda i: 'C' + str(i), range(n)))
      |    if n > 10:
      |        colors[-1] = 'purple'
      |    if n > 11:
      |        colors[-2] = '#764B00'
      |    if n > 12:
      |        colors[-3] = 'yellow'
      |    return colors
      |
      |def get_color_map(progs):
      |    colors = gen_colors(len(progs))
      |    result = {}
      |    for p, c in zip(progs, colors):
      |        result[p] = c
      |    return result
      |
      |def get_summary_data(benchmark: str, metric: str, data):
      |    keys = []
      |    values = []
      |    for obj in data['programs']:
      |        keys.append(obj['programName'])
      |        values.append(obj['summary'][benchmark][metric])
      |    return [keys, values]
      |
      |def nanos_to_milis(n):
      |    return n / 1_000_000
      |
      |with open("programsBenchmark.json") as file:
      |    data = json.load(file)
      |    COLOR_MAP = get_color_map(list(map(lambda obj: obj['programName'], data['programs'])))
      |
      |
      |    #################################################################
      |    ####### WORST RUNNING TIMES PER PROGRAM #########################
      |    #################################################################
      |
      |    fig, ax = plt.subplots()
      |    keys, values = get_summary_data('runningTime', 'worst', data)
      |    times = list(map(nanos_to_milis, values))
      |    colors = list(map(lambda k: COLOR_MAP[k], keys))
      |    bar_container = ax.bar(keys, times, label=keys, color=colors)
      |    ax.bar_label(bar_container, fmt='{:,.1f}')
      |    ax.set_xticks(ax.get_xticks(), labels=[]) # Remove program names from x-axis
      |    ax.set_xlabel('Programs')
      |    ax.set_ylabel('Running time (ms)')
      |    ax.set_yscale('linear')
      |    ax.set_ylim(top=round(max(times))+250)
      |    ax.set_title('Slowest running times')
      |    ax.legend(title='Program', loc='upper left', ncols=3, fontsize=7)
      |    plt.savefig('worstRunningTimes.png', dpi=300)
      |
      |
      |    #################################################################
      |    ####### BEST RUNNING TIMES PER PROGRAM ##########################
      |    #################################################################
      |
      |    fig, ax = plt.subplots()
      |    keys, values = get_summary_data('runningTime', 'best', data)
      |    times = list(map(nanos_to_milis, values))
      |    colors = list(map(lambda k: COLOR_MAP[k], keys))
      |    bar_container = ax.bar(keys, times, label=keys, color=colors)
      |    ax.bar_label(bar_container, fmt='{:,.1f}')
      |    ax.set_xticks(ax.get_xticks(), labels=[]) # Remove program names from x-axis
      |    ax.set_xlabel('Programs')
      |    ax.set_ylabel('Running time (ms)')
      |    ax.set_yscale('linear')
      |    ax.set_ylim(top=round(max(times))+250)
      |    ax.set_title('Fastest running times')
      |    ax.legend(title='Program', loc='upper left', ncols=3, fontsize=7)
      |    plt.savefig('bestRunningTimes.png', dpi=300)
      |
      |
      |    #################################################################
      |    ####### CODE SIZE PER INLINING ROUND AND TYPE ###################
      |    #################################################################
      |
      |    cross_figure = mlines.Line2D([], [], color='gray', marker='x', markersize=8, linestyle='', label='New Inliner')
      |    circle_figure = mlines.Line2D([], [], color='gray', marker='o', markersize=8, linestyle='', label='Old Inliner')
      |
      |    fig, ax = plt.subplots()
      |    old_data = get_normalized_data_with_program('codeSize', 'Old', data)
      |    new_data = get_normalized_data_with_program('codeSize', 'New', data)
      |
      |    for pr, xs, ys in old_data:
      |        ax.plot(xs, ys, 'o', color=COLOR_MAP[pr])
      |
      |    for pr, xs, ys in new_data:
      |        ax.plot(xs, ys, 'x', color=COLOR_MAP[pr])
      |
      |    ax.set_title('Code size (normalized by code size without inlining)')
      |    ax.set_xlabel('Inlining Rounds')
      |    ax.set_ylabel('Factor')
      |    ax.grid(visible=True, which='both')
      |    ax.legend(handles=[cross_figure, circle_figure], title='Inliner Used', loc='upper right')
      |    plt.savefig('codeSizePerRounds.png', dpi=300)
      |
      |
      |    #################################################################
      |    ####### RUNNING TIME PER INLINING ROUND AND TYPE ################
      |    #################################################################
      |
      |    fig, ax = plt.subplots()
      |    old_data = get_normalized_data_with_program('runningTime', 'Old', data)
      |    new_data = get_normalized_data_with_program('runningTime', 'New', data)
      |
      |    for pr, xs, ys in old_data:
      |        ax.plot(xs, ys, 'o', color=COLOR_MAP[pr])
      |
      |    for pr, xs, ys in new_data:
      |        ax.plot(xs, ys, 'x', color=COLOR_MAP[pr])
      |
      |    ax.set_title('Running Time (normalized by running time without inlining)')
      |    ax.set_xlabel('Inlining Rounds')
      |    ax.set_ylabel('Factor')
      |    ax.grid(visible=True, which='both')
      |    ax.legend(handles=[cross_figure, circle_figure], title='Inliner Used', loc='upper right')
      |    plt.savefig('runningTimePerRounds.png', dpi=300)
      |
      |
      |    #################################################################
      |    ####### COMPILATION TIME PER INLINING ROUND AND TYPE ############
      |    #################################################################
      |
      |    fig, ax = plt.subplots()
      |    old_data = get_normalized_data_with_program('compilationTime', 'Old', data)
      |    new_data = get_normalized_data_with_program('compilationTime', 'New', data)
      |
      |    for pr, xs, ys in old_data:
      |        ax.plot(xs, ys, 'o', color=COLOR_MAP[pr])
      |
      |    for pr, xs, ys in new_data:
      |        ax.plot(xs, ys, 'x', color=COLOR_MAP[pr])
      |
      |    ax.set_title('Compilation Time (normalized by compilation time without inlining)')
      |    ax.set_xlabel('Inlining Rounds')
      |    ax.set_ylabel('Factor')
      |    ax.grid(visible=True, which='both')
      |    ax.legend(handles=[cross_figure, circle_figure], title='Inliner Used', loc='upper right')
      |    plt.savefig('compilationTimePerRounds.png', dpi=300)
      |
      |
      |    #################################################################
      |    ####### SPEEDUP PER PROGRAM VS NO INLINING ######################
      |    #################################################################
      |
      |    fig, ax = plt.subplots(layout='constrained')
      |    old_data = get_data_for(metric='runningTime', inliner_type='NoInliner', inliner_rounds=0, data=data)
      |    new_data = get_data_for(metric='runningTime', inliner_type='New', inliner_rounds=3, data=data)
      |
      |    progs = []
      |    tmp = []
      |    for p0, r0 in old_data:
      |        progs.append(p0)
      |        for p1, r1 in new_data:
      |            if p0 == p1:
      |                tmp.append(r0 / r1)
      |
      |    speedups = {}
      |    speedups['baseline'] = np.repeat(1, len(progs))
      |    speedups['speedup'] = np.array(tmp)
      |
      |    x = np.arange(len(old_data))
      |    width = 0.4
      |    multiplier = 0
      |
      |    for attr, val in speedups.items():
      |        offset = width * multiplier
      |        rects = ax.bar(x + offset, val, width, label=attr)
      |        ax.bar_label(rects, padding=3, fmt='{:,.1f}x' if attr == 'speedup' else '')
      |        multiplier += 1
      |
      |    ax.set_ylabel('Speedup')
      |    ax.set_title('Median Running Time Speedup')
      |    ax.set_xticks(x + (width / 2), np.arange(len(old_data)) + 1)
      |    ylim_top = round(max(tmp)) + 2
      |    ax.set_ylim(top=ylim_top)
      |    ax.set_yticks(range(ylim_top + 1), labels=list(map(lambda x: f"{x}x" if x != 0 else '', range(ylim_top + 1))))
      |
      |    plt.savefig('runningTimeSpeedup.png', dpi=300)
      |
      |
      |    #################################################################
      |    ####### SPEEDUP PER PROGRAM VS OLD INLINER ######################
      |    #################################################################
      |
      |    fig, ax = plt.subplots(layout='constrained')
      |    old_data = get_data_for(metric='runningTime', inliner_type='Old', inliner_rounds=3, data=data)
      |    new_data = get_data_for(metric='runningTime', inliner_type='New', inliner_rounds=3, data=data)
      |
      |    progs = []
      |    tmp = []
      |    for p0, r0 in old_data:
      |        progs.append(p0)
      |        for p1, r1 in new_data:
      |            if p0 == p1:
      |                tmp.append(r0 / r1)
      |
      |    speedups = {}
      |    speedups['baseline'] = np.repeat(1, len(progs))
      |    speedups['speedup'] = np.array(tmp)
      |
      |    x = np.arange(len(old_data))
      |    width = 0.4
      |    multiplier = 0
      |
      |    for attr, val in speedups.items():
      |        offset = width * multiplier
      |        rects = ax.bar(x + offset, val, width, label=attr)
      |        ax.bar_label(rects, padding=3, fmt='{:,.1f}x' if attr == 'speedup' else '')
      |        multiplier += 1
      |
      |    ax.set_ylabel('Speedup')
      |    ax.set_title('Median Running Time Speedup vs. Old Inliner')
      |    ax.set_xticks(x + (width / 2), np.arange(len(old_data)) + 1)
      |    ylim_top = round(max(tmp)) + 1
      |    ax.set_ylim(top=ylim_top)
      |    ax.set_yticks(range(ylim_top + 1), labels=list(map(lambda x: f"{x}x" if x != 0 else '', range(ylim_top + 1))))
      |
      |    plt.savefig('runningTimeSpeedupOldInliner.png', dpi=300)
      |
      |    print(list(zip(range(1, len(progs) + 1), progs)))
      |
      |""".stripMargin

}
