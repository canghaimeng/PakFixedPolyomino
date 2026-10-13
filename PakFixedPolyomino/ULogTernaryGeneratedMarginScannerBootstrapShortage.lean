import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerBootstrapFrame
import PakFixedPolyomino.PakULogGeneralCapacityUnderCapacityNoAccept
import PakFixedPolyomino.ULogConcreteMicroTimeCounts

/-! All six genuinely undersized physical bootstrap workspaces reject the
actual nonempty OWN payload. These are literal raw micro-path statements,
including every cutoff and the two shifted semantic capacities zero/one. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginScannerBootstrapShortage
open ULogCompiler ULogBootstrapExecution ULogProgram
open ULogTernaryGeneratedMarginScanner (program input)
open ULogTernaryGeneratedMarginScannerBootstrapFrame
open PakULogGeneralCapacityBootstrap
open ULogFiniteTapeNondeterministicMicroCounts (RawAcceptingMicroWords)
open ULogConcreteMicroTimeCounts
open StandardNondeterministicMachine (Machine)
open MStarParserExecution (Zipper)
variable {ns nt : Nat}

theorem physical_accepting_capacity_ge_six (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (K : Nat) (labels : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath
      (.running ULogControl.qStart (generalCapacityCoreZipper (input M p x) K))
      labels (.accepted tape)) : 6 ≤ K := by
  have bound := PakULogGeneralCapacityUnderCapacityNoAccept.bootstrapWorkspaceOverhead_le_of_acceptingMicroPath
    (input M p x) (compile (program M p)) (payload nt p x)
    (ULogPayloadClockBitWrapper.padding (payload nt p x)) K rfl labels tape raw
  rw [workspace_overhead] at bound
  exact bound

theorem physical_shortage_no_accept (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (K : Nat) (shortage : K < 6)
    (labels : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath
      (.running ULogControl.qStart (generalCapacityCoreZipper (input M p x) K))
      labels (.accepted tape)) : False := by
  exact (Nat.not_le_of_gt shortage)
    (physical_accepting_capacity_ge_six M p x K labels tape raw)

theorem physical_shortage_raw_card_zero (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (K : Nat) (shortage : K < 6) :
    Nat.card (RawAcceptingMicroWords
      (.running ULogControl.qStart (generalCapacityCoreZipper (input M p x) K))) = 0 := by
  apply Nat.card_eq_zero.mpr
  refine Or.inl ⟨?_⟩
  intro word
  obtain ⟨tape, raw⟩ := word.property
  exact physical_shortage_no_accept M p x K shortage word.val tape raw

theorem physical_shortage_time_count_zero (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (K T : Nat) (shortage : K < 6) :
    acceptingMicroPaths T
      (.running ULogControl.qStart (generalCapacityCoreZipper (input M p x) K)) = 0 := by
  unfold acceptingMicroPaths
  apply Nat.card_eq_zero.mpr
  refine Or.inl ⟨?_⟩
  intro word
  obtain ⟨tape, raw⟩ := word.property.2
  exact physical_shortage_no_accept M p x K shortage word.val tape raw

theorem bootstrap_accepting_semantic_capacity_ge_two
    (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) (C : Nat)
    (labels : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath (bootstrapStart M p x C) labels (.accepted tape)) : 2 ≤ C := by
  have bound := physical_accepting_capacity_ge_six M p x (C + 4) labels tape raw
  omega

end PakFixedPolyomino.ULogTernaryGeneratedMarginScannerBootstrapShortage
