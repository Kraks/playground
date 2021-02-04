import Dependencies._

lazy val root = (project in file(".")).
  settings(
    inThisBuild(List(
      organization := "com.example",
      scalaVersion := "2.13.4",
      version      := "0.1.0-SNAPSHOT"
    )),
    name := "types",
    //libraryDependencies += scalaTest % Test,
    resolvers += Resolver.sonatypeRepo("releases"),
    addCompilerPlugin("org.typelevel" %% "kind-projector" % "0.10.3")
  )
