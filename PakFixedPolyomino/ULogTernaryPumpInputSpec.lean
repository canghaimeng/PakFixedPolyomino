import PakFixedPolyomino.ULogTernaryPolynomialPumpClockInput
import PakFixedPolyomino.ULogScheduledContinuation

/-! Closed decoded ternary generator/input/count/alphabet interface. Every
raw successful word is included. The real ordinary input builder covers
every polynomial width and preserves the original source under headers.
Physical source parsing, frame readiness/time/counting remain separate. -/

namespace PakFixedPolyomino.ULogTernaryPumpInputSpec

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogBootstrapExecution
open ULogTernaryPolynomialPumpClockInput (input width source clockWidth)

theorem lift_symbols {ns : Nat} (p : BoundedProgram ns 3) (z : BoundedConfig ns 3) :
    SemanticTapeSymbolsLtThree (liftConfig p z) := by
  refine { focus := z.focus.isLt, left := ?_, right := ?_ }
  · intro a ha
    change a ∈ z.leftRev.map Fin.val at ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact b.isLt
  · intro a ha
    change a ∈ z.right.map Fin.val at ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact b.isLt

theorem every_raw_symbols (k : Nat) (src : List Bool) (w : List Bool)
    (out : ULogSemantics.Config)
    (hr : semanticRun (ULogSemantics.start (ULogTernaryRetainedCounterPump.input k src)) w = some out) :
    SemanticTapeSymbolsLtThree out := by
  rw [← ULogTernaryRetainedPumpCounts.initial_lift k src] at hr
  obtain ⟨⟨hf, zf⟩, hzip, hlift⟩ := successful_semantic_of_zipper (2 : Fin 3) rfl
    ULogTernaryRetainedCounterPump.program hr (head := 0)
  rw [← hlift]
  exact lift_symbols _ zf

theorem actual_encoded_run (p : Polynomial Nat) (x : List Bool) :
    semanticRun (ULogSemantics.start (input p x))
      (List.replicate (ULogTernaryRetainedPumpCounts.deadline (width p x) (source p x)) false) =
      some (ULogTernaryRetainedPumpCounts.finalConfig (width p x) (source p x)) := by
  rw [ULogTernaryPolynomialPumpClockInput.start_input]
  exact ULogTernaryRetainedPumpCounts.encoded_semantic_run _ _

theorem all_cutoff_counts (p : Polynomial Nat) (x : List Bool) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input p x)) =
      if ULogTernaryRetainedPumpCounts.deadline (width p x) (source p x) ≤ T then 1 else 0 := by
  rw [ULogTernaryPolynomialPumpClockInput.start_input]
  exact ULogTernaryRetainedPumpCounts.acceptingPaths_threshold _ T _

theorem every_raw_clock_symbols (p : Polynomial Nat) (x w : List Bool)
    (out : ULogSemantics.Config)
    (hr : semanticRun (ULogSemantics.start (input p x)) w = some out) :
    w.length ≤ 2 ^ (clockWidth p x) ∧ SemanticTapeSymbolsLtThree out := by
  refine ⟨ULogTernaryPolynomialPumpClockInput.every_raw_word_clock_bound p x w out hr, ?_⟩
  rw [ULogTernaryPolynomialPumpClockInput.start_input] at hr
  exact every_raw_symbols _ _ w out hr

theorem ternary_counted_clock_input_spec (p : Polynomial Nat) :
    StandardBitTime.PolyBitTime (input p) ∧
    (∀ x, p.eval x.length ≤ width p x) ∧
    (∀ x, semanticRun (ULogSemantics.start (input p x))
      (List.replicate (ULogTernaryRetainedPumpCounts.deadline (width p x) (source p x)) false) =
      some (ULogTernaryRetainedPumpCounts.finalConfig (width p x) (source p x))) ∧
    (∀ x T, ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input p x)) =
      if ULogTernaryRetainedPumpCounts.deadline (width p x) (source p x) ≤ T then 1 else 0) ∧
    (∀ x, (ULogTernaryRetainedPumpCounts.finalConfig (width p x) (source p x)).right =
      (source p x).map ULogSemantics.bitCode ++ List.replicate (2 ^ width p x) 0) ∧
    (∀ x w out, semanticRun (ULogSemantics.start (input p x)) w = some out →
      w.length ≤ 2 ^ (clockWidth p x) ∧ SemanticTapeSymbolsLtThree out) ∧
    (∀ x, StandardBitPolynomialPayload.recover p (StandardBitPolynomialPayload.payload p x) = x) ∧
    (∀ r ∈ compile ULogTernaryRetainedCounterPump.program, r.read < 3 ∧ r.action.write < 3) :=
  ⟨ULogTernaryPolynomialPumpClockInput.input_polyBitTime p,
    StandardBitPolynomialPayload.width_dominates p, actual_encoded_run p, all_cutoff_counts p,
    (fun x => ULogTernaryRetainedPumpResourceBounds.final_right _ _), every_raw_clock_symbols p,
    StandardBitPolynomialPayload.recover_payload p, ULogTernaryRetainedCounterPump.compiled_symbols_ternary⟩

end PakFixedPolyomino.ULogTernaryPumpInputSpec
