/-
Copyright (c) 2026 Harrison Goldstein. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Segev Elazar-Mittelman
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Util.Path

/-!
# The `#fuzz` command

`#fuzz prop` runs a coverage-guided campaign for the property `prop` from the editor and reports the
counterexample, if it finds one, as an error on the command. The campaign cannot run in the Lean
server: it needs instrumented native code, libFuzzer `abort()`s on a failure, and its driver starts
once per process. So the command builds an executable in a fuzz workspace, `.lake/fuzz` under the
current workspace, which requires Basalt with the `fuzz` option and the current package as it is.
It then runs that executable as a child process and reads back its report.

The executable imports the current module as it is on disk, so save the file first. Like `#eval`, a
`#fuzz` in a file also runs when the file is built, except in the fuzz workspace's own build of it.
-/

public meta section

open Lean Elab Command

namespace Basalt.Fuzz.Command

/-- One `(key := value)` option: `runs` (default 1000000) or `seconds` (default 60), whichever
    ends the campaign first. -/
syntax fuzzArg := atomic("(" ident " := ") num ")"

/-- Run a coverage-guided campaign for a property polymorphic in its generator monad, reporting a
counterexample as an error.

```
#fuzz propSortLength
#fuzz (seconds := 10) propSortLength
```
-/
syntax (name := fuzzCmd) "#fuzz " fuzzArg* ident : command

/-- Set in the fuzz workspace's build, so that building the module that holds a `#fuzz` does not
start another campaign. -/
def inFuzzBuildVar : String := "BASALT_FUZZ_BUILD"

/-- The nearest directory at or above `dir` with a lakefile. -/
partial def workspaceRoot (dir : System.FilePath) : IO (Option System.FilePath) := do
  if (← (dir / "lakefile.lean").pathExists) || (← (dir / "lakefile.toml").pathExists) then
    return some dir
  match dir.parent with
  | some p => if p == dir then return none else workspaceRoot p
  | none => return none

/-- Basalt's package directory, from where `Basalt.Fuzz.Runner`'s olean was found:
`<pkg>/.lake/<build>/lib/lean/Basalt/Fuzz/Runner.olean`. -/
def basaltDir : IO System.FilePath := do
  let olean ← findOLean `Basalt.Fuzz.Runner
  let some dir := (List.range 7).foldlM (fun (p : System.FilePath) _ => p.parent) olean
    | throw <| IO.userError s!"#fuzz: cannot find Basalt's package from {olean}"
  return dir

/-- The current package's name, from its manifest. -/
def packageName (root : System.FilePath) : IO String := do
  let manifest ← IO.FS.readFile (root / "lake-manifest.json")
  let .ok json := Json.parse manifest
    | throw <| IO.userError "#fuzz: cannot parse lake-manifest.json"
  let .ok name := json.getObjValAs? String "name"
    | throw <| IO.userError "#fuzz: lake-manifest.json names no package"
  return name

/-- Write the fuzz workspace: a package requiring Basalt's fuzz build and the current package, and
an executable whose root runs `prop`. It shares the current workspace's packages, so nothing is
fetched again. -/
def writeWorkspace (fuzzDir root basalt : System.FilePath) (pkg : String) (mod prop : Name) :
    IO Unit := do
  IO.FS.createDirAll fuzzDir
  if (← (root / "lean-toolchain").pathExists) then
    IO.FS.writeFile (fuzzDir / "lean-toolchain") (← IO.FS.readFile (root / "lean-toolchain"))
  IO.FS.writeFile (fuzzDir / "lakefile.lean") s!"import Lake
open Lake DSL

package «basalt-fuzz-workspace» where
  packagesDir := \"../packages\"

require basalt from \"{basalt}\" with NameMap.empty.insert `fuzz \"true\"
require «{pkg}» from \"{root}\"

lean_exe fuzz where
  root := `FuzzMain
  moreLeancArgs := #[\"-O1\", \"-fsanitize=fuzzer-no-link\"]
  moreLinkArgs := #[\"@{basalt / "fuzz-run" / "obj" / "link.rsp"}\"]
"
  IO.FS.writeFile (fuzzDir / "FuzzMain.lean") s!"import {mod}
import Basalt.Fuzz.Runner

def main (args : List String) : IO Unit :=
  Basalt.Fuzz.go ({prop} : Basalt.PBT.PropM Basalt.Fuzz.FuzzGen Unit) args.toArray
"

/-- The lines of the property's report: Basalt's banner and its `key : value` lines, without what
libFuzzer prints after them. -/
def failureReport (out : String) : Option String := do
  let lines := out.splitOn "\n"
  let start ← lines.findIdx? (·.startsWith "*** BASALT PROPERTY FAILED")
  let block := (lines.drop start).take 1 ++ ((lines.drop (start + 1)).takeWhile (·.contains " : "))
  return "\n".intercalate block

elab_rules : command
  | `(#fuzz $args:fuzzArg* $prop:ident) => do
    if (← IO.getEnv inFuzzBuildVar).isSome then return
    let mut runs := 1000000
    let mut seconds := 60
    for arg in args do
      match arg with
      | `(fuzzArg| ($k:ident := $v:num)) =>
        match k.getId with
        | `runs => runs := v.getNat
        | `seconds => seconds := v.getNat
        | k => throwErrorAt arg "#fuzz: unknown option {k}; expected runs or seconds"
      | _ => throwUnsupportedSyntax
    let propName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo prop
    -- Relative when run from the command line; the workspace paths written below must not be.
    let file ← IO.FS.realPath (← getFileName)
    let some root ← workspaceRoot (file.parent.getD ".")
      | throwError "#fuzz: {file} is not in a Lake workspace"
    let basalt ← basaltDir
    let pkg ← packageName root
    let fuzzDir := root / ".lake" / "fuzz"
    unless ← (basalt / "fuzz-run" / "obj" / "link.rsp").pathExists do
      throwError "#fuzz: run {basalt / "fuzz-run" / "build.sh"} once, to build the libFuzzer runtime \
        and the C bridge"
    writeWorkspace fuzzDir root basalt pkg (← getMainModule) propName
    let build ← IO.Process.output {
      cmd := "lake", args := #["build", "fuzz"], cwd := fuzzDir,
      env := #[(inFuzzBuildVar, some "1")] }
    unless build.exitCode == 0 do
      throwError "#fuzz: building the fuzz executable failed:\n{build.stdout}{build.stderr}"
    let artifacts := fuzzDir / "artifacts"
    IO.FS.createDirAll artifacts
    let run ← IO.Process.output {
      cmd := (fuzzDir / ".lake" / "build" / "bin" / "fuzz").toString,
      args := #[s!"-runs={runs}", s!"-max_total_time={seconds}",
        s!"-artifact_prefix={artifacts}/"],
      cwd := fuzzDir }
    let out := run.stdout ++ run.stderr
    match failureReport out with
    | some report =>
      let artifact := (out.splitOn "\n").find? (·.contains "Test unit written to")
      throwError "{report}\n{artifact.getD ""}"
    | none =>
      if run.exitCode == 0 then
        let done := (out.splitOn "\n").find? (·.startsWith "Done ")
        logInfo m!"#fuzz: no counterexample ({done.getD s!"exit {run.exitCode}"})"
      else
        throwError "#fuzz: the campaign exited with {run.exitCode}:\n{out}"

end Basalt.Fuzz.Command
