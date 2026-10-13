import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerBootstrapFrame
import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerResources

/-! Every actual accepting logical word of the whole ordinary-source
scanner has a literal physical trace from its OWN decoded input frame,
and from its genuine qStart bootstrap. Resources and logical clock are
derived internally; the arbitrary physical converse and time are separate. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginScannerPhysicalForward
open ULogCompiler ULogFiniteTapeZipperRun ULogBootstrapExecution ULogProgram
open ULogConcreteSlotMicroExpansion ULogTernaryGeneratedMarginScanner
open ULogTernaryGeneratedMarginScannerBootstrapFrame
open StandardNondeterministicMachine (Machine RunsAtMost)
open MStarParserExecution (Zipper)
variable {ns nt : Nat}

set_option maxHeartbeats 1000000 in
theorem every_logical_accepting_word_physical (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length))
    (C : Nat) (tail : List Tape)
    (capacity : ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C)
    (w : List Bool) (hf : Int) (out : BoundedConfig (states M p) 3)
    (word : run (program M p) 2 w 0 (initial M p x) = some (hf, out))
    (accepts : out.state.val = 0) :
    ExactConcreteAcceptingSlotTrace (frame M p x C tail).encode w := by
  have active := (ULogTernaryGeneratedMarginScannerResources.accepting_capacity_iff
    M p x ht w hf out word accepts C tail).2 capacity
  refine ULogFiniteTapeActiveExactTrace.accepting_run_exact (program M p) w 0 hf
    (initial M p x) out C (MStarConcreteAlphabet.work :: tail) active word accepts
    (initial_not_halted M p x) (frame M p x C tail) ?_ rfl rfl
    clock_separator_passive (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x) ?_ ?_
  · simpa only [frame] using (start_input M p x)
  · exact frame_clock_decode M p x C tail
  · exact (ULogTernaryGeneratedMarginScannerCounts.all_raw_length M p x ht w hf out word).trans
      (ULogTernaryGeneratedMarginScannerClock.budget_le_clock M p x)

set_option maxHeartbeats 1000000 in
theorem every_logical_accepting_word_bootstrap (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) (C : Nat)
    (capacity : ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C)
    (w : List Bool) (hf : Int) (out : BoundedConfig (states M p) 3)
    (word : run (program M p) 2 w 0 (initial M p x) = some (hf, out))
    (accepts : out.state.val = 0) :
    ∃ labels tape, ConcreteMicroPath (bootstrapStart M p x C) labels (.accepted tape) ∧
      ∃ rest, labels = List.replicate (actual_bootstrap_prefix M p x C (by
        have hs := states_ge M p; omega)).steps (0 : Fin 2) ++ rest ∧
        SlotMicroExpansion (frame M p x C (outerTail M p x)).encode w rest (.accepted tape) := by
  have hC : 2 ≤ C := by have hs := states_ge M p; omega
  obtain ⟨rest, tape, expansion⟩ :=
    ULogFiniteTapeNondeterministicMicroCounts.accepting_trace_has_expansion
      (every_logical_accepting_word_physical M p x ht C (outerTail M p x) capacity w hf out word accepts)
  let hit := actual_bootstrap_prefix M p x C hC
  refine ⟨List.replicate hit.steps 0 ++ rest, tape, ?_, rest, rfl, expansion⟩
  exact (ULogBootstrapMicroPrefix.zero_run_micro_path hit.valid).append (to_micro_path expansion)

end PakFixedPolyomino.ULogTernaryGeneratedMarginScannerPhysicalForward
