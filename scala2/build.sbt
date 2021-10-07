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
    addCompilerPlugin("org.typelevel" %% "kind-projector" % "0.10.3"),
    resolvers += Resolver.sonatypeRepo("snapshots"),
    libraryDependencies += "ch.epfl.data" %% "squid" % "0.4.0-SNAPSHOT",
    addCompilerPlugin("org.scalamacros" % "paradise" % paradiseVersion cross CrossVersion.full)
  )
