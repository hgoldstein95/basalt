import Basalt
import Basalt.Experiments.BDT.BSTGenerator
import Basalt.Experiments.BDT.Properties
import Basalt.Examples.HowToSpecifyIt.BST
import Basalt.Examples.HowToSpecifyIt.BST0
import Basalt.Examples.HowToSpecifyIt.BST1
import Basalt.Examples.HowToSpecifyIt.BST2
import Basalt.Examples.HowToSpecifyIt.BST3
import Basalt.Examples.HowToSpecifyIt.BST4
import Basalt.Examples.HowToSpecifyIt.BST5
import Basalt.Examples.HowToSpecifyIt.BST6
import Basalt.Examples.HowToSpecifyIt.BST7
import Basalt.Examples.HowToSpecifyIt.BST8

namespace BDTExperiments

open BST

/-- Statistics from a test run -/
structure TestStats where
  /-- Number of tests run before finding a bug (or max if no bug found) -/
  testsUntilFailure : Nat
  /-- Whether a bug was found -/
  bugFound : Bool
  deriving Repr

/-- Run a property test multiple times and return when it first fails -/
def runUntilFailure (prop : Gen Bool) (maxTests : Nat := 1000) : IO TestStats := do
  let mut testsRun := 0
  for _ in [0:maxTests] do
    testsRun := testsRun + 1
    let result ← Gen.runIO prop
    if !result then
      return { testsUntilFailure := testsRun, bugFound := true }
  return { testsUntilFailure := testsRun, bugFound := false }

/-- Configuration for a BST implementation to test -/
structure BSTImpl where
  name : String
  insert : Nat → Nat → BST Nat Nat → BST Nat Nat
  delete : Nat → BST Nat Nat → BST Nat Nat
  union : BST Nat Nat → BST Nat Nat → BST Nat Nat

/-- All BST implementations (correct and buggy) -/
def allImpls : List BSTImpl := [
  { name := "BST0 (correct)"
  , insert := HowToSpecifyIt.insert
  , delete := HowToSpecifyIt.delete
  , union := HowToSpecifyIt.union },
  { name := "BST1 (insert discards tree)"
  , insert := HowToSpecifyIt.BST1.insert
  , delete := HowToSpecifyIt.BST1.delete
  , union := HowToSpecifyIt.BST1.union },
  { name := "BST2 (insert creates duplicates)"
  , insert := HowToSpecifyIt.BST2.insert
  , delete := HowToSpecifyIt.BST2.delete
  , union := HowToSpecifyIt.BST2.union },
  { name := "BST3 (insert doesn't update)"
  , insert := HowToSpecifyIt.BST3.insert
  , delete := HowToSpecifyIt.BST3.delete
  , union := HowToSpecifyIt.BST3.union },
  { name := "BST4 (delete doesn't rebuild)"
  , insert := HowToSpecifyIt.BST4.insert
  , delete := HowToSpecifyIt.BST4.delete
  , union := HowToSpecifyIt.BST4.union },
  { name := "BST5 (delete reversed comparisons)"
  , insert := HowToSpecifyIt.BST5.insert
  , delete := HowToSpecifyIt.BST5.delete
  , union := HowToSpecifyIt.BST5.union },
  { name := "BST6 (union assumes ordering)"
  , insert := HowToSpecifyIt.BST6.insert
  , delete := HowToSpecifyIt.BST6.delete
  , union := HowToSpecifyIt.BST6.union },
  { name := "BST7 (union wrong assumption)"
  , insert := HowToSpecifyIt.BST7.insert
  , delete := HowToSpecifyIt.BST7.delete
  , union := HowToSpecifyIt.BST7.union },
  { name := "BST8 (union priority bug)"
  , insert := HowToSpecifyIt.BST8.insert
  , delete := HowToSpecifyIt.BST8.delete
  , union := HowToSpecifyIt.BST8.union }
]

/-- Property specification for testing -/
structure PropertySpec where
  name : String
  test : BDTParams → BSTImpl → BST Nat Nat → Gen Bool

/-- All properties to test -/
def allProperties : List PropertySpec := [
  { name := "insert-find"
  , test := fun _params impl tree => prop_insert_find tree impl.insert BST.find },
  { name := "insert-insert"
  , test := fun _params impl tree => prop_insert_insert tree impl.insert BST.find },
  { name := "delete-find"
  , test := fun _params impl tree => prop_delete_find tree impl.delete BST.find },
  { name := "insert-size"
  , test := fun _params impl tree => prop_insert_size tree impl.insert BST.size },
  { name := "delete-size"
  , test := fun _params impl tree => prop_delete_size tree impl.delete BST.size },
  { name := "insert-valid"
  , test := fun _params impl tree => prop_insert_valid tree impl.insert BST.valid },
  { name := "delete-valid"
  , test := fun _params impl tree => prop_delete_valid tree impl.delete BST.valid },
  { name := "toList-sorted"
  , test := fun _params _impl tree => prop_toList_sorted tree BST.toList },
  { name := "union-contains"
  , test := fun params impl tree => prop_union_contains tree params impl.union BST.find },
  { name := "union-left-priority"
  , test := fun params impl tree => prop_union_left_priority tree params impl.union BST.find },
  { name := "union-valid"
  , test := fun params impl tree => prop_union_valid tree params impl.union BST.valid }
]

/-- Result of testing one property -/
structure PropertyTestResult where
  propertyName : String
  stats : TestStats
  deriving Repr

/-- Result of testing one implementation -/
structure ImplTestResult where
  implName : String
  propertyResults : List PropertyTestResult
  deriving Repr

/-- Test all properties for a single implementation -/
def testProperties (params : BDTParams) (impl : BSTImpl) (maxTests : Nat := 1000)
    : IO (List PropertyTestResult) := do
  let mut results := []
  for prop in allProperties do
    let testGen : Gen Bool := do
      let tree ← genBST params
      prop.test params impl tree
    let stats ← runUntilFailure testGen maxTests
    results := { propertyName := prop.name, stats := stats } :: results
  return results.reverse

/-- Test a single BST implementation against all properties -/
def testImplementation (params : BDTParams) (impl : BSTImpl)
    (maxTests : Nat := 1000) : IO ImplTestResult := do
  let propertyResults ← testProperties params impl maxTests
  return { implName := impl.name, propertyResults := propertyResults }

/-- Test all implementations with given parameters -/
def testAllImplementations (params : BDTParams) (maxTests : Nat := 1000)
    : IO (List ImplTestResult) := do
  let mut results := []
  for impl in allImpls do
    let result ← testImplementation params impl maxTests
    results := result :: results
  return results.reverse

/-- Result from a single hyperparameter configuration -/
structure ExperimentResult where
  params : BDTParams
  results : List ImplTestResult
  deriving Repr

/-- Test a single specific hyperparameter configuration -/
def runSingleExperiment (alpha0 t0 t2 decay : Float) (maxTests : Nat := 1000)
    : IO ExperimentResult := do
  let params : BDTParams := { alpha0, t0, t2, decay }
  let results ← testAllImplementations params maxTests
  return { params, results }

end BDTExperiments
