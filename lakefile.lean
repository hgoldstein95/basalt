import Lake
open Lake DSL

package basalt where
  version := v!"0.1.0"
  -- TODO: Remove this if/when the Lean folks fix the way arguments get abstracted in
  -- `partial_fixpoint`s with modules.
  leanOptions := #[⟨`backward.proofsInPublic, true⟩]

require "leanprover-community" / mathlib @ git "v4.35.0"

require splitmix from git "https://github.com/hgoldstein95/splitmix" @ "splitmix-0.3.0"

/-- SanitizerCoverage for `basalt-fuzz`: on only under `lake -R -Kfuzz=1`, which
`fuzz-run/build.sh` passes, and off otherwise.

It cannot be on unconditionally. Lake compiles a library's C with that library's `moreLeancArgs`
whenever an executable links its modules, and every executable that imports `Basalt` links some of
them. An instrumented `Basalt` therefore reaches every downstream executable, which then fails to
link: nothing but `basalt-fuzz` supplies the libFuzzer runtime that defines `__sanitizer_cov_*`.
`-K` options are the root package's alone, so a package that requires Basalt never sees `fuzz`. -/
def fuzzLeancArgs : Array String :=
  if (get_config? fuzz).isSome then #["-O1", "-fsanitize=fuzzer-no-link"] else #[]

/-
Under `-Kfuzz`, `-fsanitize=fuzzer-no-link` here is *not* about fuzzing Basalt: it is about what
libFuzzer can see of a generator's progress. Where a staged benchmark writes its guards itself
(`chain-n`), coverage of this library adds nothing; where progress means "the generator's loop ran
one more iteration" (`long-n`), the edges that distinguish iteration depth are in `Fuzz/` and
`Combinators.lean`, and dropping the flag here costs `long-16` a third of its success rate at a
fixed budget and `long-64` nearly two thirds of its own (measured, fuzz-run/README.md). The cost is
25% throughput, paid only by `basalt-fuzz`.
-/
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

/-
The code `basalt-fuzz` fuzzes: generators, properties, and the buggy operations under test.
Together with `Basalt` above and the executable root below, this is the instrumented set — every
first-party module in the link closure; `fuzz-run/build.sh` asserts each object carries the sancov
section.

These modules must not be matched by any other library's globs. Lake resolves a module claimed by
two libraries to one of their configurations silently, and an uninstrumented `BasaltFuzz` still
builds a fuzzer that runs and finds shallow bugs.

A default target, which costs `lake build` only elaboration: `moreLeancArgs` applies when something
asks for these modules' C objects, and only the executable does. Dropping it from the default
targets would stop type-checking `Staged`, which nothing else imports.
-/
@[default_target]
lean_lib BasaltFuzz where
  globs := #[.submodules `BasaltFuzz]
  moreLeancArgs := fuzzLeancArgs

/-
The opt-in fuzzing executable, never built by `lake build` and reached only through
`fuzz-run/build.sh`, which writes the `link.rsp` naming this platform's libFuzzer runtime and builds
with `-Kfuzz`. The root is instrumented for a reason of its own: Lean specializes each generator and
property into the module that registers them, so `BasaltFuzzMain` holds their live code and the
generic copies left in `Basalt/Combinators.lean` are dead. `-O1` matches the libraries so the whole
instrumented set is compiled alike — edge granularity is an artifact of inlining, so a split
optimization level would make its halves incomparable.
-/
lean_exe «basalt-fuzz» where
  root := `BasaltFuzzMain
  moreLeancArgs := fuzzLeancArgs
  moreLinkArgs := #["@fuzz-run/obj/link.rsp"]
