import PakFixedPolyomino.ULogConcreteMicroCutoffMonotonicity
import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerPhysicalCapacityCounts

/-! ALL physical cutoffs, including the unsaturated near-horizon band.
Every actual raw count is bounded by the ordinary source count, and every
actual shortage gives zero, without a minimum-time premise. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginScannerAllCutoffBounds
open ULogCompiler ULogBootstrapExecution ULogProgram ULogConcreteMicroTimeCounts ULogConcreteMicroCutoffMonotonicity
open ULogTernaryGeneratedMarginScanner (input states input_polyBitTime)
open ULogTernaryGeneratedMarginScannerPhysicalFuel
open ULogTernaryGeneratedMarginScannerPhysicalCapacityCounts
open PakULogGeneralCapacityBootstrap
open StandardNondeterministicMachine (Machine RunsAtMost acceptingCount)
variable {ns nt : Nat}

theorem all_cutoff_source_upper (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (K T : Nat) :
    acceptingMicroPaths T
      (.running ULogControl.qStart (generalCapacityCoreZipper (input M p x) K)) ≤
      acceptingCount M x (2 ^ p.eval x.length) := by
  have mono := accepting_micro_paths_mono
    (.running ULogControl.qStart (generalCapacityCoreZipper (input M p x) K))
    T (max T (totalPhysicalFuelBound M p x)) (le_max_left _ _)
  have counted := all_physical_capacity_time_count M p x ht K
    (max T (totalPhysicalFuelBound M p x)) (le_max_right _ _)
  rw [counted] at mono
  split_ifs at mono <;> omega

theorem all_cutoff_shortage_zero (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (K T : Nat)
    (shortage : K < ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 +
      (states M p - 1) + 4) :
    acceptingMicroPaths T
      (.running ULogControl.qStart (generalCapacityCoreZipper (input M p x) K)) = 0 := by
  have mono := accepting_micro_paths_mono
    (.running ULogControl.qStart (generalCapacityCoreZipper (input M p x) K))
    T (max T (totalPhysicalFuelBound M p x)) (le_max_left _ _)
  have counted := all_physical_capacity_time_count M p x ht K
    (max T (totalPhysicalFuelBound M p x)) (le_max_right _ _)
  rw [counted, if_neg (by omega)] at mono
  omega

end PakFixedPolyomino.ULogTernaryGeneratedMarginScannerAllCutoffBounds
