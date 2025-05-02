import Dependencies._

val paradiseVersion = "2.1.0"

lazy val root = (project in file(".")).
  settings(
    inThisBuild(List(
      organization := "com.example",
      scalaVersion := "2.12.10", // for squid
      //scalaVersion := "2.13.4",
      version      := "0.1.0-SNAPSHOT",
      autoCompilerPlugins := true
    )),
    name := "types",
    //libraryDependencies += scalaTest % Test,
    resolvers += Resolver.sonatypeRepo("releases"),
    resolvers += Resolver.sonatypeRepo("snapshots"),
    libraryDependencies += "ch.epfl.data" %% "squid" % "0.4.0-SNAPSHOT",
    //libraryDependencies += "org.scala-lang.plugins" % "scala-continuations-library_2.12" % "1.0.3",
    libraryDependencies += "org.scala-lang.plugins" %% "scala-continuations-library" % "1.0.3",
    addCompilerPlugin("org.typelevel" %% "kind-projector" % "0.10.3"),
    addCompilerPlugin("org.scalamacros" % "paradise" % paradiseVersion cross CrossVersion.full),
    addCompilerPlugin("org.scala-lang.plugins" % "scala-continuations-plugin_2.12.2" % "1.0.3"),
    parallelExecution in Test := false,
    scalacOptions += "-P:continuations:enable",
  )

