import PakFixedPolyomino.StandardMachineAcceptingCountBound
import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerAllCutoffBounds
import PakFixedPolyomino.PakWeightedCapacityCeilingReadout

/-! The weighted ceiling readout for ALL literal physical qStart words of
the ordinary-machine encoding. Count bounds and shortages are proved here,
not provided as certificates. The numerical capacity interval and its actual
time slack remain explicit; the outer full-frame census is a separate task. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginScannerWeightedRawReadout
noncomputable section
open ULogCompiler ULogBootstrapExecution ULogConcreteMicroTimeCounts
open ULogTernaryGeneratedMarginScanner (input states)
open ULogTernaryGeneratedMarginScannerPhysicalFuel
open ULogTernaryGeneratedMarginScannerPhysicalCapacityCounts
open ULogTernaryGeneratedMarginScannerAllCutoffBounds
open PakULogGeneralCapacityBootstrap PakWeightedCapacityCeilingReadout
open StandardNondeterministicMachine (Machine RunsAtMost acceptingCount)
variable {ns nt : Nat}

def firstSaturatedCapacity (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) : Nat :=
  ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) + 4

def rawCapacityCounts (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (cutoff : Nat → Nat) (K : Nat) : Nat :=
  acceptingMicroPaths (cutoff K)
    (.running ULogControl.qStart (generalCapacityCoreZipper (input M p x) K))

theorem weighted_raw_readout (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (S H : Nat) (cutoff : Nat → Nat)
    (inside : H ≤ S)
    (padding : firstSaturatedCapacity M p x + (2 ^ p.eval x.length + 1) + 2 ≤ H)
    (time : ∀ K, firstSaturatedCapacity M p x ≤ K → K < H →
      totalPhysicalFuelBound M p x ≤ cutoff K) :
    (weightedCapacitySum S (rawCapacityCounts M p x cutoff) +
        fullCapacityWeight S (firstSaturatedCapacity M p x) - 1) /
      fullCapacityWeight S (firstSaturatedCapacity M p x) =
        acceptingCount M x (2 ^ p.eval x.length) := by
  have source_nonneg : 0 ≤ (2 ^ p.eval x.length : Nat) := Nat.zero_le _
  have strict : firstSaturatedCapacity M p x < H := by omega
  apply weighted_capacity_ceiling_readout S (firstSaturatedCapacity M p x) H
    (2 ^ p.eval x.length + 1) (acceptingCount M x (2 ^ p.eval x.length))
    (rawCapacityCounts M p x cutoff)
  · exact strict
  · exact inside
  · exact padding
  · exact StandardMachineAcceptingCountBound.accepting_count_le_two_pow M x _
  · intro K _
    exact all_cutoff_source_upper M p x ht K (cutoff K)
  · intro K shortage
    exact all_cutoff_shortage_zero M p x ht K (cutoff K) shortage
  · intro K enough before
    have counted := all_physical_capacity_time_count M p x ht K (cutoff K)
      (time K enough before)
    change ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 +
      (states M p - 1) + 4 ≤ K at enough
    rw [if_pos enough] at counted
    exact counted

end
end PakFixedPolyomino.ULogTernaryGeneratedMarginScannerWeightedRawReadout
