import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerAllCapacityMicroCounts

/-! The actual physical workspace coordinate, including values zero through
three that are not a shifted semantic capacity. Every raw path and every
large-enough microtime cutoff is counted; the threshold is derived from
the real selected guard and bootstrap workspace, not supplied as a witness. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginScannerPhysicalCapacityCounts
open ULogCompiler ULogBootstrapExecution ULogProgram
open ULogTernaryGeneratedMarginScanner (input states input_polyBitTime)
open ULogTernaryGeneratedMarginScannerBootstrapFrame
open ULogTernaryGeneratedMarginScannerBootstrapShortage
open ULogTernaryGeneratedMarginScannerAllCapacityMicroCounts
open ULogTernaryGeneratedMarginScannerPhysicalFuel ULogConcreteMicroTimeCounts
open PakULogGeneralCapacityBootstrap
open StandardNondeterministicMachine (Machine RunsAtMost acceptingCount)
open MStarParserExecution (Zipper)
variable {ns nt : Nat}

theorem physical_accepting_sharp_capacity_necessary
    (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (K : Nat)
    (labels : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath
      (.running ULogControl.qStart (generalCapacityCoreZipper (input M p x) K))
      labels (.accepted tape)) :
    ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) + 4 ≤ K := by
  have six := physical_accepting_capacity_ge_six M p x K labels tape raw
  have same : (K - 4) + 4 = K := by omega
  have shifted : ConcreteMicroPath (bootstrapStart M p x (K - 4)) labels (.accepted tape) := by
    simpa only [bootstrapStart, same] using raw
  have bound := bootstrap_accepting_sharp_capacity_necessary M p x ht (K - 4)
    labels tape shifted
  omega

theorem all_physical_capacity_raw_length_le
    (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (K : Nat)
    (labels : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath
      (.running ULogControl.qStart (generalCapacityCoreZipper (input M p x) K))
      labels (.accepted tape)) : labels.length ≤ totalPhysicalFuelBound M p x := by
  have six := physical_accepting_capacity_ge_six M p x K labels tape raw
  have same : (K - 4) + 4 = K := by omega
  apply all_capacity_bootstrap_raw_length_le M p x ht (K - 4) labels tape
  simpa only [bootstrapStart, same] using raw

theorem all_physical_capacity_time_count
    (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (K T : Nat)
    (time : totalPhysicalFuelBound M p x ≤ T) :
    acceptingMicroPaths T
      (.running ULogControl.qStart (generalCapacityCoreZipper (input M p x) K)) =
      if ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) + 4 ≤ K
      then acceptingCount M x (2 ^ p.eval x.length) else 0 := by
  by_cases four : 4 ≤ K
  · have same : (K - 4) + 4 = K := by omega
    have count := all_capacity_bootstrap_time_count M p x ht (K - 4) T time
    have threshold :
        (ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ K - 4) ↔
        (ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) + 4 ≤ K) := by
      omega
    simpa only [bootstrapStart, same, threshold] using count
  · have small : K < 6 := by omega
    have threshold : ¬ ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 +
        (states M p - 1) + 4 ≤ K := by omega
    rw [if_neg threshold]
    exact physical_shortage_time_count_zero M p x K T small

theorem all_physical_capacity_count_time_spec
    (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) :
    StandardBitTime.PolyBitTime (input M p) ∧
    totalPhysicalFuelBound M p x < (PakOuterULogBridge.copiedCoreRadius (input M p x)) ^ 9 ∧
    ∀ K, (∀ labels tape,
      ConcreteMicroPath (.running ULogControl.qStart (generalCapacityCoreZipper (input M p x) K))
        labels (.accepted tape) → labels.length ≤ totalPhysicalFuelBound M p x) ∧
      ∀ T, totalPhysicalFuelBound M p x ≤ T →
        acceptingMicroPaths T
          (.running ULogControl.qStart (generalCapacityCoreZipper (input M p x) K)) =
          if ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) + 4 ≤ K
          then acceptingCount M x (2 ^ p.eval x.length) else 0 :=
  ⟨input_polyBitTime M p, total_physical_fuel_lt_copied_pow_nine M p x,
    fun K => ⟨all_physical_capacity_raw_length_le M p x ht K,
      all_physical_capacity_time_count M p x ht K⟩⟩

end PakFixedPolyomino.ULogTernaryGeneratedMarginScannerPhysicalCapacityCounts
