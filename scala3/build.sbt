val scala3Version = "3.7.0"

lazy val root = project
  .in(file("."))
  .settings(
    name := "new",
    version := "0.1.0-SNAPSHOT",

    scalaVersion := scala3Version,

    libraryDependencies += "com.novocode" % "junit-interface" % "0.11" % "test",
    libraryDependencies += "org.scala-lang" %% "scala3-staging" % scalaVersion.value,
  )

scalacOptions ++= Seq(
  "-Xcheck-macros",
  "-explain"
)