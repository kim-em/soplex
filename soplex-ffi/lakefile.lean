import Lake
open System Lake DSL

/-! # `soplex-ffi` build configuration

  This package owns the direct SoPlex binding: the vendored SoPlex
  build, the C++ bridge, and the thin Lean API in `SoplexFFI`.
-/

def macSdkPath : String :=
  "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk"

def packageRoot : FilePath := __dir__

/-! ## Sanitizer (ASan/UBSan) opt-in.

    Pass `-Ksanitize=1` to `lake build` to instrument SoPlex, the
    bridge, and final executables consistently.
-/
def sanitizerEnabled : Bool :=
  match get_config? sanitize with
  | some s => s != "0" && s != "false"
  | none => false

def sanitizerArgs : Array String :=
  if sanitizerEnabled then
    #["-fsanitize=address", "-fsanitize=undefined",
      "-fno-sanitize=vptr,function",
      "-fno-omit-frame-pointer", "-g"]
  else
    #[]

def soplexRuntimeLinkArgs : Array String :=
  if System.Platform.isOSX then
    #[s!"-Wl,-syslibroot,{macSdkPath}",
      "-L/opt/homebrew/lib",
      "-L/usr/local/lib",
      "-lgmpxx", "-lgmp",
      "-lc++"]
  else if System.Platform.isWindows then
    let mingwLibDir := packageRoot / "vendor" / "mingw-libs"
    #["-Wl,--allow-multiple-definition",
      (mingwLibDir / "libstdc++.a").toString,
      (mingwLibDir / "libgmpxx.a").toString,
      (mingwLibDir / "libgmp.a").toString,
      s!"-L{mingwLibDir}",
      "-lgcc_s",
      "-lmingwex",
      "-lmsvcrt"]
  else
    #["-L/usr/lib/x86_64-linux-gnu",
      "-L/usr/lib/aarch64-linux-gnu",
      "-L/usr/lib64",
      "-L/usr/lib",
      "-lgmpxx", "-lgmp",
      "-lm"] ++ sanitizerArgs

package soplexFfi where
  moreLinkArgs := soplexRuntimeLinkArgs

def soplexObjsDir (pkgDir : FilePath) : FilePath :=
  pkgDir / defaultBuildDir / "soplex-objs"

def soplexBuildDir (pkgDir : FilePath) : FilePath :=
  pkgDir / if sanitizerEnabled then "build-soplex-sanitize" else "build-soplex"

def soplexReadyFile (pkgDir : FilePath) : FilePath :=
  soplexObjsDir pkgDir / ".ready"

def soplexSubmoduleHelp (srcDir : FilePath) : String :=
  s!"SoPlex submodule not found at {srcDir}.\n" ++
  "Run `git submodule update --init --recursive` from the repo root, " ++
  "or clone with `git clone --recurse-submodules`."

def isSoplexInput (path : FilePath) : Bool :=
  match path.extension with
  | some "c" | some "cc" | some "cpp" | some "h" | some "hh" | some "hpp" => true
  | some "cmake" | some "txt" => true
  | _ => false

def soplexCxxFlags : IO String := do
  let base ← IO.getEnv "CXXFLAGS"
  let isLinux := !(System.Platform.isOSX || System.Platform.isWindows)
  let base := base.getD <| if isLinux then "-stdlib=libc++" else ""
  let san := " ".intercalate sanitizerArgs.toList
  pure <| if san.isEmpty then base else if base.isEmpty then san else base ++ " " ++ san

def soplexBuildEnv : JobM (Array (String × Option String)) := do
  let mut env : Array (String × Option String) := #[]
  if !(System.Platform.isOSX || System.Platform.isWindows) then
    if (← IO.getEnv "CC").isNone then
      env := env.push ("CC", some "clang")
    if (← IO.getEnv "CXX").isNone then
      env := env.push ("CXX", some "clang++")
  let cxxFlags ← soplexCxxFlags
  if !cxxFlags.isEmpty then
    env := env.push ("CXXFLAGS", some cxxFlags)
  pure env

def stageMingwLibs (pkgDir : FilePath) : JobM Unit := do
  if System.Platform.isWindows then
    let some mingwPrefix ← IO.getEnv "MINGW_PREFIX"
      | error "MINGW_PREFIX is not set; run Lake from an MSYS2 MINGW64 shell."
    let srcDir := FilePath.mk mingwPrefix / "lib"
    let outDir := pkgDir / "vendor" / "mingw-libs"
    IO.FS.createDirAll outDir
    for lib in #[
      "libstdc++.a", "libstdc++.dll.a",
      "libgmp.a", "libgmp.dll.a", "libgmpxx.a", "libgmpxx.dll.a",
      "libgcc_s.a", "libwinpthread.a", "libwinpthread.dll.a",
      "libmingw32.a", "libmingwex.a", "libmsvcrt.a", "libmsvcrt-os.a",
      "libstdc++exp.a", "libstdc++fs.a"
    ] do
      let src := srcDir / lib
      if (← src.pathExists) then
        proc {cmd := "cp", args := #[src.toString, (outDir / lib).toString]}
    for lib in #["libstdc++.a", "libgmpxx.a", "libgmp.a"] do
      if !(← (outDir / lib).pathExists) then
        error s!"missing required MSYS2 archive: {srcDir / lib}"

def removeOldSoplexObjs (dir : FilePath) : IO Unit := do
  if (← dir.pathExists) then
    for e in (← dir.readDir) do
      let n := e.fileName
      if n.endsWith ".o" || n.endsWith ".obj" then
        IO.FS.removeFile e.path

def listObjectFiles (dir : FilePath) : IO (Array FilePath) := do
  let entries ← dir.readDir
  let mut out : Array FilePath := #[]
  for e in entries do
    let n := e.fileName
    if n.endsWith ".o" || n.endsWith ".obj" then
      out := out.push e.path
  pure out

def buildSoplexObjects (pkgDir : FilePath) : JobM Unit := do
  let srcDir := pkgDir / "vendor" / "soplex"
  let cmakeFile := srcDir / "CMakeLists.txt"
  if !(← cmakeFile.pathExists) then
    logWarning <| soplexSubmoduleHelp srcDir
    error <| soplexSubmoduleHelp srcDir
  stageMingwLibs pkgDir
  let buildDir := soplexBuildDir pkgDir
  let objsDir := soplexObjsDir pkgDir
  IO.FS.createDirAll objsDir
  let env ← soplexBuildEnv
  let cmakeArgs := #[
    "-S", srcDir.toString,
    "-B", buildDir.toString,
    "-DCMAKE_BUILD_TYPE=Release",
    "-DCMAKE_POSITION_INDEPENDENT_CODE=ON",
    "-DBOOST=ON",
    "-DGMP=ON",
    "-DPAPILO=OFF",
    "-DMPFR=OFF",
    "-DBUILD_TESTING=OFF",
    "-DZLIB=OFF"
  ]
  proc {cmd := "cmake", args := cmakeArgs, cwd := some pkgDir, env := env}
  let buildArgs := #["--build", buildDir.toString, "--target", "libsoplex", "--parallel"]
  proc {cmd := "cmake", args := buildArgs, cwd := some pkgDir, env := env}
  let lib := buildDir / "lib" / nameToStaticLib "soplex"
  if !(← lib.pathExists) then
    error s!"SoPlex archive was not produced at {lib}"
  removeOldSoplexObjs objsDir
  proc {cmd := (← getLeanAr).toString, args := #["x", lib.toString], cwd := some objsDir}
  let objs ← listObjectFiles objsDir
  if objs.size < 5 then
    error s!"expected SoPlex archive to contain many objects, found {objs.size}"
  IO.FS.writeFile (soplexReadyFile pkgDir) "ready\n"

def listSoplexObjs (pkgDir : FilePath) : IO (Array FilePath) := do
  let dir := soplexObjsDir pkgDir
  let marker := soplexReadyFile pkgDir
  if !(← marker.pathExists) then
    throw <| IO.userError <|
      s!"SoPlex objects were not built at {dir}."
  listObjectFiles dir

private def soplexObjectsTarget (pkg : Package) : FetchM (Job FilePath) := do
  let srcDir := pkg.dir / "vendor" / "soplex"
  let cmakeFile := srcDir / "CMakeLists.txt"
  let srcTarget ←
    if (← cmakeFile.pathExists) then
      inputDir srcDir (text := false) isSoplexInput
    else
      (← inputTextFile (pkg.dir / ".." / ".gitmodules")).mapM fun p => pure #[p]
  buildFileAfterDep (soplexReadyFile pkg.dir) srcTarget fun _ => do
    addPlatformTrace
    addPureTrace sanitizerEnabled "sanitize"
    buildSoplexObjects pkg.dir

def bridgeSrcs : Array String := #["lean_soplex.cpp", "lean_soplex_bridge.cpp"]

def systemIncludeArgs : Array String :=
  if System.Platform.isOSX then
    #["-I/opt/homebrew/include", "-I/usr/local/include"]
  else if System.Platform.isWindows then
    #["-IC:/msys64/mingw64/include"]
  else
    #["-I/usr/include"]

def bridgeCxxDriver : String :=
  if System.Platform.isOSX ∨ System.Platform.isWindows then "c++" else "clang++"

def bridgeStdlibArgs : Array String :=
  if System.Platform.isOSX ∨ System.Platform.isWindows then #[]
  else #["-stdlib=libc++"]

private def bridgeOTarget (pkg : Package) (src : String) :
    FetchM (Job FilePath) := do
  let stem := src.dropEnd 4
  let oFile := pkg.dir / defaultBuildDir / "ffi" / s!"{stem}.o"
  let srcTarget ← inputTextFile <| pkg.dir / "ffi" / src
  buildFileAfterDep oFile srcTarget fun srcFile => do
    let leanInc        := (← getLeanIncludeDir).toString
    let ffiInc         := (pkg.dir / "ffi").toString
    let soplexSrcInc   := (pkg.dir / "vendor" / "soplex" / "src").toString
    let soplexBuildInc := (soplexBuildDir pkg.dir).toString
    compileO oFile srcFile (#[
      "-O2", "-fPIC", "-std=c++17",
      "-I", leanInc,
      "-I", ffiInc,
      "-I", soplexSrcInc,
      "-I", soplexBuildInc
    ] ++ bridgeStdlibArgs ++ systemIncludeArgs ++ sanitizerArgs) bridgeCxxDriver

extern_lib soplexffi (pkg) := do
  let name := nameToStaticLib "soplexffi"
  let outLib := pkg.staticLibDir / name
  let soplexReady ← soplexObjectsTarget pkg
  let bridgeOJobs ← bridgeSrcs.mapM (bridgeOTarget pkg)
  let bridgeOsJob := Job.collectArray bridgeOJobs "bridge objs"
  soplexReady.mapM fun _ => do
    let soplexOs ← listSoplexObjs pkg.dir
    let bridgeOs ← bridgeOsJob.await
    let art ← buildArtifactUnlessUpToDate outLib (ext := "a") (restore := true) do
      compileStaticLib outLib (soplexOs ++ bridgeOs) (← getLeanAr)
    return art.path

@[default_target]
lean_lib SoplexFFI where
  roots := #[`SoplexFFI]
  globs := #[`SoplexFFI, `SoplexFFI.Basic, `SoplexFFI.Types, `SoplexFFI.Validate]
  precompileModules := !sanitizerEnabled
  moreLinkArgs := soplexRuntimeLinkArgs
