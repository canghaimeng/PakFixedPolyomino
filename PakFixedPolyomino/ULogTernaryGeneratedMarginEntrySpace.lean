import PakFixedPolyomino.ULogTernaryGeneratedMarginEntryChecked

/-! Occupied cells of EVERY raw compact entry path. The reserve seal adds
one real RIGHT cell; subsequent conditional work consumes allocated zeros.
This is a peak bound, not all-capacity rejection or physical-time closure. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginEntrySpace
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeStageComposition ULogFiniteTapeGrowthLedger
open ULogTernaryGeneratedMarginEntry
open ULogTernaryGeneratedHeadedSourceReturn (sourceBits retained)
variable {nt : Nat}

set_option maxHeartbeats 2000000 in
theorem sealed_raw_space (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (k d c : Nat)
    (hc : 0 < c) (x : List Bool)
    (hfit : ULogTernaryGeneratedHeadedSourceExpansion.reserveCost nt x ≤ 2 ^ k - 1)
    {w : List Bool} {hf : Int} {out : BoundedConfig (sealedStates nt d c) 3}
    (hw : run (sealedProgram hnt codes d c) 2 w 0 (sealedInitial nt k d c x) = some (hf, out)) :
    cellCount out ≤ ULogTernaryGuardedPumpDelimiterSpace.peak k d c x + 1 := by
  unfold sealedProgram sealedInitial at hw
  have split := @ULogFiniteTapeStageCompositionRuns.deterministic_first_stage_split
    (ULogTernaryGeneratedHeadedSourceReturn.states nt d c) 7 3
    (ULogTernaryGeneratedHeadedSourceReturn.program hnt codes d c) ULogTernaryReserveEndSeal.program
    (return_states_ge nt d c) (by decide) .stay (2 : Fin 3)
    (ULogTernaryGeneratedHeadedSourceReturn.program_falseOnly hnt codes d c)
    (ULogTernaryGeneratedHeadedSourceReturn.deadline nt k d c x) 0
    (ULogTernaryGeneratedHeadedSourceReturn.finalHead nt k d c x)
    (ULogTernaryGeneratedHeadedSourceReturn.initial nt k d c x)
    (ULogTernaryGeneratedHeadedSourceReturn.final codes k d c x)
    (ULogTernaryGeneratedHeadedSourceReturn.actual_run hnt codes k d c hc x hfit)
    (ULogTernaryGeneratedHeadedSourceReturn.final_accepts codes k d c x) w hf out hw
  rcases split with ⟨_, zp, hp, rfl⟩ | ⟨v, zq, _, hq, rfl⟩
  · have hs := ULogTernaryGeneratedHeadedSourceReturn.every_raw_space hnt codes k d c hc x hfit hp
    change cellCount zp ≤ _
    omega
  · have count : cellCount (secondStart (by decide : 3 ≤ 7) (2 : Fin 3) .stay
        (ULogTernaryGeneratedHeadedSourceReturn.final codes k d c x)) =
        cellCount (ULogTernaryGeneratedHeadedSourceReturn.final codes k d c x) := by
      simp [secondStart, applyBounded, cellCount]
    rw [seal_second_start codes k d c x hfit] at count
    rw [seal_second_start codes k d c x hfit, FiniteOneTapeSemantics.moveHead] at hq
    have child := ULogTernaryReserveEndSeal.every_raw (sourceBits codes x) (retained k d c x)
      (zeroCount nt k x) (ULogTernaryGeneratedHeadedSourceReturn.finalHead nt k d c x) hq
    have hs := ULogTernaryGeneratedHeadedSourceReturn.every_raw_space hnt codes k d c hc x hfit
      (ULogTernaryGeneratedHeadedSourceReturn.actual_run hnt codes k d c hc x hfit)
    have hc := child.2.2.2.1
    change cellCount zq ≤ _
    omega

set_option maxHeartbeats 2000000 in
theorem every_raw_space (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (blank : Fin nt)
    (k d c : Nat) (hc : 0 < c) (x : List Bool)
    (hfit : ULogTernaryGeneratedHeadedSourceExpansion.reserveCost nt x ≤ 2 ^ k - 1)
    (hpool : nt + 1 ≤ zeroCount nt k x)
    {w : List Bool} {hf : Int} {out : BoundedConfig (states nt d c) 3}
    (hw : run (program hnt codes blank d c) 2 w 0 (initial nt k d c x) = some (hf, out)) :
    cellCount out ≤ ULogTernaryGuardedPumpDelimiterSpace.peak k d c x + 1 := by
  unfold ULogTernaryGeneratedMarginEntry.program ULogTernaryGeneratedMarginEntry.initial at hw
  have falseOnly : FalseOnly (sealedProgram hnt codes d c) :=
    ULogFiniteTapeStageCompositionRuns.program_falseOnly _ _ _ _ .stay
      (ULogTernaryGeneratedHeadedSourceReturn.program_falseOnly hnt codes d c)
      ULogTernaryReserveEndSeal.program_falseOnly
  have split := @ULogFiniteTapeStageCompositionRuns.deterministic_first_stage_split
    (sealedStates nt d c) (ULogTernaryConditionalRightMargin.states nt) 3
    (sealedProgram hnt codes d c) (ULogTernaryConditionalRightMargin.program hnt blank)
    (sealed_states_ge nt d c) (conditional_states_ge nt) .stay (2 : Fin 3) falseOnly
    (sealedDeadline nt k d c x) 0 (ULogTernaryGeneratedHeadedSourceReturn.finalHead nt k d c x)
    (sealedInitial nt k d c x) (sealedFinal codes k d c x)
    (sealed_actual_run hnt codes k d c hc x hfit) (sealed_accepts codes k d c x) w hf out hw
  rcases split with ⟨_, zp, hp, rfl⟩ | ⟨v, zq, _, hq, rfl⟩
  · simpa only [cellCount, leftConfig] using
      sealed_raw_space (nt := nt) hnt codes k d c hc x hfit (w := w) (hf := hf) (out := zp) hp
  · have count : cellCount (secondStart (conditional_states_ge nt) (2 : Fin 3) .stay
        (sealedFinal codes k d c x)) = cellCount (sealedFinal codes k d c x) := by
      simp [secondStart, applyBounded, cellCount]
    rw [conditional_second_start codes k d c x hpool] at count
    rw [conditional_second_start codes k d c x hpool, FiniteOneTapeSemantics.moveHead] at hq
    have child := ULogTernaryConditionalRightMargin.every_raw hnt blank x.length (sourceBits codes x)
      (ULogTernaryGuardedPumpDelimiter.under k d c x) (sealBuffer nt k x)
      (ULogTernaryGeneratedHeadedSourceReturn.finalHead nt k d c x) hq
    have hs := sealed_raw_space hnt codes k d c hc x hfit
      (sealed_actual_run hnt codes k d c hc x hfit)
    have he := child.2.2.1
    change cellCount zq ≤ _
    omega

theorem compact_entry_space_spec (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (blank : Fin nt)
    (p : Polynomial Nat) (x : List Bool) :
    ∀ w hf out, run (compactProgram hnt codes blank p) 2 w 0 (compactInitial nt p x) = some (hf, out) →
      cellCount out ≤ ULogTernaryGuardedPumpDelimiterSpace.peak
        (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x)
        (ULogTernaryGuardedPumpDelimiterInput.depth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
        (ULogTernaryGuardedPumpDelimiterInput.seedWidth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)) x + 1 := by
  intro w hf out hw
  exact every_raw_space hnt codes blank _ _ _ (ULogTernaryGuardedPumpDelimiterInput.seed_positive _) x
    (ULogTernaryGeneratedHeadedSourceExpansion.compact_reserve_fits nt p x) (compact_pool_fits nt p x) hw

end PakFixedPolyomino.ULogTernaryGeneratedMarginEntrySpace
