import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerPhysicalForward
import PakFixedPolyomino.ULogFiniteTapeActiveBoundedTrace
import PakFixedPolyomino.ULogLocalTimeMicroFuel

/-! Actual microstep fuel for every whole logical accepting word, including
the literal qStart bootstrap. Bounds are independent of excess physical
capacity. An arbitrary raw micro-path is covered once its logical inverse
is supplied by the separate concrete ALL-prefix resource proof. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginScannerPhysicalFuel
open ULogCompiler ULogFiniteTapeZipperRun ULogBootstrapExecution ULogProgram
open ULogConcreteSlotMicroExpansion ULogTernaryGeneratedMarginScanner
open ULogTernaryGeneratedMarginScannerBootstrapFrame
open StandardNondeterministicMachine (Machine RunsAtMost)
open PakULogCycleResourceBound PakULogTraceResourceBound
open PakULogGeneralCapacityBootstrapFirstHit
variable {ns nt : Nat}

theorem clock_width_le_input_length (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x ≤ (input M p x).length := by
  have length := ULogPayloadClockBitWrapper.length_wrap (program M p) (payload nt p x)
  change (input M p x).length = _ at length
  have clock := padding_length nt p x
  simp only [ULogPayloadClockBitWrapper.padding, List.length_replicate] at clock
  omega

theorem budget_le_copied_radius (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    ULogTernaryGeneratedMarginScannerCounts.budget M p x ≤
      PakOuterULogBridge.copiedCoreRadius (input M p x) := by
  have clock := clock_width_le_input_length M p x
  have exponent : ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x ≤
      MStarParserCopySpec.timeExponent (input M p x).length := by
    unfold MStarParserCopySpec.timeExponent
    omega
  exact (ULogTernaryGeneratedMarginScannerClock.budget_le_clock M p x).trans
    (Nat.pow_le_pow_right (by decide) exponent)

theorem actual_global_envelope (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (C : Nat) (tail : List Tape) : GlobalCopiedEnvelope (input M p x) (frame M p x C tail) 0 := by
  rw [frame_eq_bootstrap]
  exact bootstrapSemanticFrame_globalEnvelope (input M p x) (compile (program M p))
    (payload nt p x) (ULogPayloadClockBitWrapper.padding (payload nt p x)) C tail rfl

noncomputable def physicalFuelBound (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) : Nat :=
  ULogTernaryGeneratedMarginScannerCounts.budget M p x *
    globalCyclePolynomial (PakOuterULogBridge.copiedCoreRadius (input M p x))

theorem physical_fuel_lt_copied_pow_eight (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) : physicalFuelBound M p x < (PakOuterULogBridge.copiedCoreRadius (input M p x)) ^ 8 :=
  (Nat.mul_le_mul_right _ (budget_le_copied_radius M p x)).trans_lt
    (radius_mul_globalCyclePolynomial_lt_pow_eight (PakOuterULogBridge.copiedCoreRadius_ge_256 _))

set_option maxHeartbeats 1000000 in
theorem every_logical_accepting_word_bounded (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) (C : Nat) (tail : List Tape)
    (capacity : ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C)
    (w : List Bool) (hf : Int) (out : BoundedConfig (states M p) 3)
    (word : run (program M p) 2 w 0 (initial M p x) = some (hf, out))
    (accepts : out.state.val = 0) :
    ExactConcreteAcceptingBoundedFuel
      (globalCyclePolynomial (PakOuterULogBridge.copiedCoreRadius (input M p x)))
      (frame M p x C tail).encode w := by
  have active := (ULogTernaryGeneratedMarginScannerResources.accepting_capacity_iff
    M p x ht w hf out word accepts C tail).2 capacity
  refine ULogFiniteTapeActiveBoundedTrace.accepting_run_bounded (program M p) w 0 hf
    (initial M p x) out C (MStarConcreteAlphabet.work :: tail) active word accepts
    (initial_not_halted M p x) (frame M p x C tail) ?_ rfl rfl clock_separator_passive
    (2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x) ?_ ?_
    (input M p x) 0 (actual_global_envelope M p x C tail) ?_
  · simpa only [frame] using (start_input M p x)
  · exact frame_clock_decode M p x C tail
  · exact (ULogTernaryGeneratedMarginScannerCounts.all_raw_length M p x ht w hf out word).trans
      (ULogTernaryGeneratedMarginScannerClock.budget_le_clock M p x)
  · simpa only [Nat.zero_add] using
      (ULogTernaryGeneratedMarginScannerCounts.all_raw_length M p x ht w hf out word).trans
        (budget_le_copied_radius M p x)

theorem every_accepting_expansion_length_le (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) (C : Nat) (tail : List Tape)
    (capacity : ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C)
    (w : List Bool) (hf : Int) (out : BoundedConfig (states M p) 3)
    (word : run (program M p) 2 w 0 (initial M p x) = some (hf, out))
    (accepts : out.state.val = 0) (labels : List (Fin 2))
    (tape : MStarParserExecution.Zipper Tape)
    (expansion : SlotMicroExpansion (frame M p x C tail).encode w labels (.accepted tape)) :
    labels.length ≤ physicalFuelBound M p x := by
  obtain ⟨finish, actual, fuel, ha, bounded⟩ :=
    every_logical_accepting_word_bounded M p x ht C tail capacity w hf out word accepts
  obtain ⟨given, generated, length⟩ := ULogLocalTimeMicroFuel.bounded_fuel_expansion bounded
  have same := word_and_finish_unique expansion generated
  have size := exactSlotRunFuel_le_length_mul bounded
  rw [same.1, length]
  exact size.trans (Nat.mul_le_mul_right _
    (ULogTernaryGeneratedMarginScannerCounts.all_raw_length M p x ht w hf out word))

noncomputable def bootstrapFuel (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) : Nat :=
  generalCapacityBootstrapAllFuel (input M p x) (compile (program M p)) (payload nt p x)
    (ULogPayloadClockBitWrapper.padding (payload nt p x))

noncomputable def totalPhysicalFuelBound (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) : Nat := bootstrapFuel M p x + physicalFuelBound M p x

theorem bootstrap_fuel_lt_copied_pow_eight (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) : bootstrapFuel M p x < (PakOuterULogBridge.copiedCoreRadius (input M p x)) ^ 8 :=
  PakULogBootstrapExplicitFuel.bootstrapAllFuel_lt_radius_pow_eight (input M p x)
    (compile (program M p)) (payload nt p x) (ULogPayloadClockBitWrapper.padding (payload nt p x)) rfl

theorem total_physical_fuel_lt_copied_pow_nine (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) : totalPhysicalFuelBound M p x < (PakOuterULogBridge.copiedCoreRadius (input M p x)) ^ 9 :=
  add_two_pow_eight_bounds_lt_pow_nine (PakOuterULogBridge.copiedCoreRadius_ge_256 (input M p x))
    (bootstrap_fuel_lt_copied_pow_eight M p x) (physical_fuel_lt_copied_pow_eight M p x)

theorem bootstrap_steps_le (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (C : Nat) (hC : 2 ≤ C) : (actual_bootstrap_prefix M p x C hC).steps ≤ bootstrapFuel M p x := by
  have actual := run_generalCapacityBootstrapAllFuel_exact (input M p x) (compile (program M p))
    (payload nt p x) (ULogPayloadClockBitWrapper.padding (payload nt p x)) (C + 4) rfl (by
      rw [workspace_overhead]; omega)
  rw [← actual_frame_eq_general_capacity M p x C hC] at actual
  have path : ULogBootstrapExecution.run (bootstrapFuel M p x) (bootstrapStart M p x C) =
      (frame M p x C (outerTail M p x)).encode := actual
  by_contra high
  have before := (actual_bootstrap_prefix M p x C hC).before (bootstrapFuel M p x) (by omega)
  change ¬ IsConcreteCycleBoundary
    (ULogBootstrapExecution.run (bootstrapFuel M p x) (bootstrapStart M p x C)) at before
  rw [path] at before
  exact before (actual_bootstrap_prefix M p x C hC).hit

theorem every_logical_accepting_word_bootstrap_bounded (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) (C : Nat)
    (capacity : ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C)
    (w : List Bool) (hf : Int) (out : BoundedConfig (states M p) 3)
    (word : run (program M p) 2 w 0 (initial M p x) = some (hf, out))
    (accepts : out.state.val = 0) :
    ∃ labels tape, ConcreteMicroPath (bootstrapStart M p x C) labels (.accepted tape) ∧
      labels.length ≤ totalPhysicalFuelBound M p x := by
  have hC : 2 ≤ C := by have hs := states_ge M p; omega
  obtain ⟨labels, tape, path, rest, split, expansion⟩ :=
    ULogTernaryGeneratedMarginScannerPhysicalForward.every_logical_accepting_word_bootstrap
      M p x ht C capacity w hf out word accepts
  refine ⟨labels, tape, path, ?_⟩
  rw [split]
  simp only [List.length_append, List.length_replicate]
  exact Nat.add_le_add (bootstrap_steps_le M p x C hC)
    (every_accepting_expansion_length_le M p x ht C (outerTail M p x) capacity
      w hf out word accepts rest tape expansion)

theorem whole_logical_to_physical_fuel_spec (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) :
    StandardBitTime.PolyBitTime (input M p) ∧
    totalPhysicalFuelBound M p x < (PakOuterULogBridge.copiedCoreRadius (input M p x)) ^ 9 ∧
    ∀ C, ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) ≤ C →
      ∀ w hf out, run (program M p) 2 w 0 (initial M p x) = some (hf, out) →
        out.state.val = 0 →
        ∃ labels tape, ConcreteMicroPath (bootstrapStart M p x C) labels (.accepted tape) ∧
          labels.length ≤ totalPhysicalFuelBound M p x :=
  ⟨input_polyBitTime M p, total_physical_fuel_lt_copied_pow_nine M p x,
    fun C hc w hf out word accepts =>
      every_logical_accepting_word_bootstrap_bounded M p x ht C hc w hf out word accepts⟩

end PakFixedPolyomino.ULogTernaryGeneratedMarginScannerPhysicalFuel
