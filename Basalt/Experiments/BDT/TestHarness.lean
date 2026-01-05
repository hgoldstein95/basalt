import Basalt
import Basalt.Experiments.BDT.Hyperparameters

namespace BDTExperiments

/-- Statistics from a test run -/
structure TestStats where
  /-- No. of tests run before finding a bug (or `maxTests` if no bug found) -/
  testsUntilFailure : Nat
  /-- Whether a bug was found -/
  bugFound : Bool
  deriving Repr

/-- Runs a property-based test for `maxTests`, terminating when it first fails -/
def runUntilFailure (prop : Gen Bool) (maxTests : Nat := 1000) : IO TestStats := do
  let mut testsRun := 0
  for _ in [0:maxTests] do
    testsRun := testsRun + 1
    let testResult ← Gen.runIO prop
    if !testResult then
      return { testsUntilFailure := testsRun, bugFound := true }
  return { testsUntilFailure := testsRun, bugFound := false }

/-- Result of testing one specific property on a particular implementation -/
structure PropertyTestResult where
  propertyName : String
  stats : TestStats
  deriving Repr

/-- Result of testing *all* properties on one implementation -/
structure ImplTestResult where
  implName : String
  propertyResults : List PropertyTestResult
  deriving Repr

/-- Result from a single hyperparameter configuration -/
structure ExperimentResult where
  params : BDTParams
  results : List ImplTestResult
  deriving Repr

/-- Generic property specification polymorphic over implementation and data types -/
structure PropertySpec (Impl Data : Type) where
  name : String
  test : BDTParams → Impl → Data → Gen Bool

/-- Test all properties for a single implementation (generic version) -/
def testProperties {Impl Data : Type}
    (params : BDTParams)
    (impl : Impl)
    (generator : BDTParams → Gen Data)
    (properties : List (PropertySpec Impl Data))
    (maxTests : Nat := 1000)
    : IO (List PropertyTestResult) := do
  properties.mapM $ fun prop => do
    let testGen : Gen Bool := do
      let data ← generator params
      prop.test params impl data
    let stats ← runUntilFailure testGen maxTests
    return { propertyName := prop.name, stats }

/-- Test all implementations with given parameters (generic version) -/
def testAllImplementations {Impl Data : Type}
    (params : BDTParams)
    (implementations : List Impl)
    (generator : BDTParams → Gen Data)
    (properties : List (PropertySpec Impl Data))
    (getName : Impl → String)
    (maxTests : Nat := 1000)
    : IO (List ImplTestResult) := do
  implementations.mapM $ fun impl => do
    let propertyResults ← testProperties params impl generator properties maxTests
    return { implName := getName impl, propertyResults }

end BDTExperiments
