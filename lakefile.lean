import Lake
open Lake DSL

/-! Basalt's build. The SanitizerCoverage instrumentation that coverage-guided fuzzing needs is opt-in:
it is on only under the `fuzz` option (`lake build -K fuzz=true …` at the root, or
`require basalt … with NameMap.empty.insert `fuzz "true"` from a dependent), and an instrumented
build lives in its own build directory. So a dependent's executable links Basalt's ordinary objects,
and switching between fuzz and ordinary builds rebuilds neither. -/

/-- Whether this build is a fuzz build. -/
def fuzz : Bool := (get_config? fuzz).isSome

/-- `-fsanitize=fuzzer-no-link` here is *not* about fuzzing Basalt: it is about what libFuzzer can see
of a generator's progress. Where a staged benchmark writes its guards itself (`chain-n`), coverage of
this library adds nothing; where progress means "the generator's loop ran one more iteration"
(`long-n`), the edges that distinguish iteration depth are in `Fuzz/` and `Combinators.lean`, and
dropping the flag here costs `long-16` a third of its success rate at a fixed budget and `long-64`
nearly two thirds of its own (measured, fuzz-run/README.md). `-O1` throughout the instrumented set,
since edge granularity is an artifact of inlining. -/
def fuzzLeancArgs : Array String := if fuzz then #["-O1", "-fsanitize=fuzzer-no-link"] else #[]

package basalt where
  -- TODO: Remove this if/when the Lean folks fix the way arguments get abstracted in
  -- `partial_fixpoint`s with modules.
  leanOptions := #[⟨`backward.proofsInPublic, true⟩]
  buildDir := if fuzz then ".lake" / "build-fuzz" else defaultBuildDir

require "leanprover-community" / mathlib @ git "v4.35.0"
require splitmix from git "https://github.com/hgoldstein95/splitmix" @ "splitmix-0.3.0"

@[default_target]
lean_lib Basalt where
  globs := #[.andSubmodules `Basalt]
  moreLeancArgs := fuzzLeancArgs

@[default_target]
lean_lib BasaltExamples where
  globs := #[.submodules `BasaltExamples]

@[default_target]
lean_lib BasaltTest where
  globs := #[.submodules `BasaltTest]

/-- The code `basalt-fuzz` fuzzes: generators, properties, and the buggy operations under test.
Together with `Basalt` above and the executable root below, this is the instrumented set — every
first-party module in the link closure; `fuzz-run/build.sh` asserts each object carries the sancov
section. These modules must not be matched by any other library's globs: Lake resolves a module
claimed by two libraries to one of their configurations silently. A default target, which costs
`lake build` only elaboration, so that `Staged`, which nothing else imports, is type-checked. -/
@[default_target]
lean_lib BasaltFuzz where
  globs := #[.submodules `BasaltFuzz]
  moreLeancArgs := fuzzLeancArgs

/-- The opt-in fuzzing executable, built by `fuzz-run/build.sh` in a fuzz build, which writes the
`link.rsp` naming this platform's libFuzzer runtime. The root is instrumented because Lean
specializes each generator and property into the module that registers them. -/
lean_exe «basalt-fuzz» where
  root := `BasaltFuzzMain
  moreLeancArgs := fuzzLeancArgs
  moreLinkArgs := #["@fuzz-run/obj/link.rsp"]
