import PakFixedPolyomino.PakParserKernelNoncoreRejection

/-! The actual ALL accepting scan-pad zipper split with kernel-only leaves. -/
namespace PakFixedPolyomino.PakParserScanPadStandard
open MStarParserMicrocode MStarParserExecution MStarParserSoundness MStarConcreteAlphabet

theorem scanPad_wrong_core_rejected
    (left right : List (MStarOuterProgram.Tape CoreTape)) (a : CoreTape)
    (hz : a ≠ zero) (ho : a ≠ one) :
    oneStep zero one work (.running scanPad ⟨left, .core a, right⟩) = .rejected := by
  unfold oneStep
  change (if scanPad = copyStart then _ else _) = _
  rw [if_neg PakParserKernelTableFacts.scanPad_ne_copyStart, parserStep_scanPad_core]
  simp [MStarParserMicrocode.coreEq, hz, ho, MStarParserMicrocode.reject, applyAction]

theorem scanPad_canAccept_split
    (left : List (MStarOuterProgram.Tape CoreTape)) (focus : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape))
    (hacc : CanAcceptResult (.running scanPad ⟨left, focus, right⟩)) :
    ∃ n y ys,
      focus :: right = List.replicate n (.core zero) ++ .core one :: y :: ys ∧
      CanAcceptResult (.running scanLen
        ⟨sepPad :: List.replicate n (.core zero) ++ left, y, ys⟩) := by
  induction right generalizing left focus with
  | nil =>
      obtain ⟨a, ha⟩ := PakParserKernelNoncoreRejection.scanPad_accepting_core left [] focus hacc
      subst focus
      have hnext := (canAcceptResult_oneStep_iff _).2 hacc
      by_cases hz : a = zero
      · subst a
        rw [oneStep_scanPad_zero_nil] at hnext
        exact (not_canAcceptResult_stuck hnext).elim
      · by_cases ho : a = one
        · subst a
          rw [oneStep_scanPad_one_nil] at hnext
          exact (not_canAcceptResult_stuck hnext).elim
        · rw [scanPad_wrong_core_rejected _ _ _ hz ho] at hnext
          exact (not_canAcceptResult_rejected hnext).elim
  | cons y ys ih =>
      obtain ⟨a, ha⟩ := PakParserKernelNoncoreRejection.scanPad_accepting_core left (y :: ys) focus hacc
      subst focus
      have hnext := (canAcceptResult_oneStep_iff _).2 hacc
      by_cases hz : a = zero
      · subst a
        rw [MStarConcreteAlphabet.oneStep_scanPad_zero] at hnext
        obtain ⟨n, z, zs, hshape, hfinal⟩ := ih (.core zero :: left) y hnext
        refine ⟨n + 1, z, zs, ?_, ?_⟩
        · simp [hshape, List.replicate_succ, List.append_assoc]
        · simpa [List.replicate_succ, replicate_cons_rotate, List.append_assoc] using hfinal
      · by_cases ho : a = one
        · subst a
          rw [MStarConcreteAlphabet.oneStep_scanPad_separator] at hnext
          exact ⟨0, y, ys, rfl, hnext⟩
        · rw [scanPad_wrong_core_rejected _ _ _ hz ho] at hnext
          exact (not_canAcceptResult_rejected hnext).elim

end PakFixedPolyomino.PakParserScanPadStandard
