import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerAllPrefixGrowth
import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerCompiledNonempty
import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerBootstrapTimeCounts
import PakFixedPolyomino.ULogFiniteTapeLogicalSemanticCounts

/-! Internally instantiate the ALL-word physical inverse/count/time bridge
for the actual whole scanner and OWN compact input at sufficient capacity.
The counted raw domain contains only genuine physical edges and labels.
Insufficient capacity and the outer square/full-frame census remain separate. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginScannerAllPhysicalCounts
open ULogCompiler ULogFiniteTapeZipperRun ULogBootstrapExecution ULogProgram
open ULogConcreteSlotMicroExpansion ULogTernaryGeneratedMarginScanner
open ULogTernaryGeneratedMarginScannerBootstrapFrame
open ULogTernaryGeneratedMarginScannerPhysicalFuel
open ULogFiniteTapeNondeterministicMicroCounts
open ULogConcreteMicroTimeCounts
open StandardNondeterministicMachine (Machine RunsAtMost acceptingCount)
variable {ns nt : Nat}

set_option maxHeartbeats 1000000 in
theorem whole_nd_physical_spec (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) (C : Nat) (tail : List Tape)
    (capacity : ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C) :
    (∀ labels tape, ConcreteMicroPath (frame M p x C tail).encode labels (.accepted tape) →
      ∃ w hf out, run (program M p) 2 w 0 (initial M p x) = some (hf, out) ∧
        out.state.val = 0 ∧ SlotMicroExpansion (frame M p x C tail).encode w labels (.accepted tape)) ∧
    (∀ w hf out, run (program M p) 2 w 0 (initial M p x) = some (hf, out) →
      out.state.val = 0 → ExactConcreteAcceptingSlotTrace (frame M p x C tail).encode w) := by
  refine ULogFiniteTapeNondeterministicResourceBridge.bounded_growth_nd_physical_spec
    (program M p) (ULogTernaryGeneratedMarginScannerCompiledNonempty.compiled_program_nonempty M p)
    (ULogTernaryGeneratedMarginScannerCounts.budget M p x) 0 (initial M p x) 1
    (ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1) C tail
    (ULogTernaryGeneratedMarginScannerAllPrefixGrowth.whole_all_prefix_growth M p x ht)
    (ULogTernaryGeneratedMarginScannerCounts.all_raw_length M p x ht) capacity
    (initial_not_halted M p x) (frame M p x C tail) ?_ rfl ?_ clock_separator_passive
    (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x)
    (frame_clock_decode M p x C tail) (ULogTernaryGeneratedMarginScannerClockSlack.budget_lt_clock M p x)
  · simpa only [frame] using (start_input M p x)
  · simp only [frame, List.replicate_one, List.cons_append, List.nil_append]

set_option maxHeartbeats 1000000 in
theorem all_frame_micro_card_eq (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) (C : Nat) (tail : List Tape)
    (capacity : ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C) :
    Nat.card (LogicalAcceptingWords (program M p) 0 (initial M p x)) =
      Nat.card (RawAcceptingMicroWords (frame M p x C tail).encode) := by
  refine ULogFiniteTapeNondeterministicMicroCounts.all_micro_card_eq
    (program M p) (ULogTernaryGeneratedMarginScannerCompiledNonempty.compiled_program_nonempty M p)
    (ULogTernaryGeneratedMarginScannerCounts.budget M p x) 0 (initial M p x) 1
    (ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1) C tail
    (ULogTernaryGeneratedMarginScannerAllPrefixGrowth.whole_all_prefix_growth M p x ht)
    (ULogTernaryGeneratedMarginScannerCounts.all_raw_length M p x ht) capacity
    (initial_not_halted M p x) (frame M p x C tail) ?_ rfl ?_ clock_separator_passive
    (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x)
    (frame_clock_decode M p x C tail) (ULogTernaryGeneratedMarginScannerClockSlack.budget_lt_clock M p x)
  · simpa only [frame] using (start_input M p x)
  · simp only [frame, List.replicate_one, List.cons_append, List.nil_append]

theorem ordinary_frame_micro_card_eq (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) (C : Nat) (tail : List Tape)
    (capacity : ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C) :
    acceptingCount M x (2 ^ p.eval x.length) =
      Nat.card (RawAcceptingMicroWords (frame M p x C tail).encode) :=
  (ULogTernaryGeneratedMarginScannerCounts.ordinary_count M p x ht).trans
    ((ULogFiniteTapeLogicalSemanticCounts.logical_semantic_card_eq (program M p) 0
      (initial M p x)).symm.trans (all_frame_micro_card_eq M p x ht C tail capacity))

theorem ordinary_bootstrap_micro_card_eq (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) (C : Nat)
    (capacity : ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C) :
    acceptingCount M x (2 ^ p.eval x.length) =
      Nat.card (RawAcceptingMicroWords (bootstrapStart M p x C)) := by
  have hC : 2 ≤ C := by have hs := states_ge M p; omega
  exact (ordinary_frame_micro_card_eq M p x ht C (outerTail M p x) capacity).trans
    (all_bootstrap_micro_card_eq M p x C hC).symm

theorem all_frame_raw_length_le (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) (C : Nat) (tail : List Tape)
    (capacity : ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C)
    (labels : List (Fin 2)) (tape : MStarParserExecution.Zipper Tape)
    (path : ConcreteMicroPath (frame M p x C tail).encode labels (.accepted tape)) :
    labels.length ≤ physicalFuelBound M p x := by
  obtain ⟨w, hf, out, word, accepts, expansion⟩ :=
    (whole_nd_physical_spec M p x ht C tail capacity).1 labels tape path
  exact every_accepting_expansion_length_le M p x ht C tail capacity w hf out word accepts
    labels tape expansion

theorem all_bootstrap_raw_length_le (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) (C : Nat)
    (capacity : ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C)
    (labels : List (Fin 2)) (tape : MStarParserExecution.Zipper Tape)
    (path : ConcreteMicroPath (bootstrapStart M p x C) labels (.accepted tape)) :
    labels.length ≤ totalPhysicalFuelBound M p x := by
  have hC : 2 ≤ C := by have hs := states_ge M p; omega
  exact ULogTernaryGeneratedMarginScannerBootstrapTimeCounts.bootstrap_all_raw_length_transfer
    M p x C hC (physicalFuelBound M p x)
    (all_frame_raw_length_le M p x ht C (outerTail M p x) capacity) labels tape path

theorem ordinary_bootstrap_time_count (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) (C : Nat)
    (capacity : ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C)
    (T : Nat) (time : totalPhysicalFuelBound M p x ≤ T) :
    acceptingCount M x (2 ^ p.eval x.length) = acceptingMicroPaths T (bootstrapStart M p x C) :=
  (ordinary_bootstrap_micro_card_eq M p x ht C capacity).trans
    (common_time_count (totalPhysicalFuelBound M p x) T
      (all_bootstrap_raw_length_le M p x ht C capacity) time).symm

theorem whole_all_physical_count_time_spec (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) :
    StandardBitTime.PolyBitTime (input M p) ∧
    totalPhysicalFuelBound M p x < (PakOuterULogBridge.copiedCoreRadius (input M p x)) ^ 9 ∧
    ∀ C, ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C →
      (∀ labels tape, ConcreteMicroPath (bootstrapStart M p x C) labels (.accepted tape) →
        labels.length ≤ totalPhysicalFuelBound M p x) ∧
      ∀ T, totalPhysicalFuelBound M p x ≤ T →
        acceptingCount M x (2 ^ p.eval x.length) = acceptingMicroPaths T (bootstrapStart M p x C) :=
  ⟨input_polyBitTime M p, total_physical_fuel_lt_copied_pow_nine M p x,
    fun C hc => ⟨all_bootstrap_raw_length_le M p x ht C hc,
      ordinary_bootstrap_time_count M p x ht C hc⟩⟩

end PakFixedPolyomino.ULogTernaryGeneratedMarginScannerAllPhysicalCounts
