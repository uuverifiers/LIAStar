val scala3Version = "3.8.3"

lazy val root = project
  .in(file("."))
  .settings(
    name := "LIAStarSolver",
    version := "0.1.0-SNAPSHOT",

    scalaVersion := scala3Version,

    libraryDependencies ++= Seq(
        "org.scalameta" %% "munit" % "1.3.1" % Test,
        ("io.github.uuverifiers" %% "princess" % "2026-05-20").cross(CrossVersion.for3Use2_13)
    )
  )
