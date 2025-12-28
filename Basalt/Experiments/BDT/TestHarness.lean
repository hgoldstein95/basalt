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

/-- Result of running a single test -/
inductive TestResult where
  | Pass : TestResult
  | Fail : TestResult
  deriving BEq, Repr

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

/-- Test a single implementation against a single property -/
def testProperty (params : BDTParams) (propName : String)
    (prop : BST Nat Nat → Gen Bool) (maxTests : Nat := 1000) : IO TestStats := do
  IO.println s!"Testing {propName}..."
  let testGen : Gen Bool := do
    let tree ← genBST params
    prop tree
  runUntilFailure testGen maxTests

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

/-- Result of testing one implementation -/
structure ImplTestResult where
  implName : String
  insertFindStats : TestStats
  insertInsertStats : TestStats
  deleteFindStats : TestStats
  insertSizeStats : TestStats
  deleteSizeStats : TestStats
  deriving Repr

/-- Test a single BST implementation against all properties -/
def testImplementation (params : BDTParams) (impl : BSTImpl)
    (maxTests : Nat := 1000) : IO ImplTestResult := do
  IO.println s!"\n=== Testing {impl.name} ==="

  -- Test insert-find property
  let insertFindStats ← testProperty params "insert-find" (fun tree => do
    let key ← RandomChoice.choose 0 100 (by omega)
    let val ← RandomChoice.choose 0 100 (by omega)
    return prop_insert_find tree key val impl.insert BST.find) maxTests

  -- Test insert-insert property
  let insertInsertStats ← testProperty params "insert-insert" (fun tree => do
    let key ← RandomChoice.choose 0 100 (by omega)
    let val1 ← RandomChoice.choose 0 100 (by omega)
    let val2 ← RandomChoice.choose 0 100 (by omega)
    return prop_insert_insert tree key val1 val2 impl.insert BST.find) maxTests

  -- Test delete-find property
  let deleteFindStats ← testProperty params "delete-find" (fun tree => do
    let key ← RandomChoice.choose 0 100 (by omega)
    return prop_delete_find tree key impl.delete BST.find) maxTests

  -- Test insert-size property
  let insertSizeStats ← testProperty params "insert-size" (fun tree => do
    let key ← RandomChoice.choose 0 100 (by omega)
    let val ← RandomChoice.choose 0 100 (by omega)
    return prop_insert_size tree key val impl.insert BST.size) maxTests

  -- Test delete-size property
  let deleteSizeStats ← testProperty params "delete-size" (fun tree => do
    let key ← RandomChoice.choose 0 100 (by omega)
    return prop_delete_size tree key impl.delete BST.size) maxTests

  return {
    implName := impl.name
    insertFindStats := insertFindStats
    insertInsertStats := insertInsertStats
    deleteFindStats := deleteFindStats
    insertSizeStats := insertSizeStats
    deleteSizeStats := deleteSizeStats
  }

/-- Test all implementations with given parameters -/
def testAllImplementations (params : BDTParams) (maxTests : Nat := 1000)
    : IO (List ImplTestResult) := do
  let mut results := []
  for impl in allImpls do
    let result ← testImplementation params impl maxTests
    results := result :: results
  return results.reverse

end BDTExperiments
