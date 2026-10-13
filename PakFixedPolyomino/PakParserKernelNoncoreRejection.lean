import PakFixedPolyomino.PakParserKernelTableFacts

/-! Reject actual non-core parser focuses using kernel-only state facts.
The accepting property and machine are the inherited literal definitions. -/
namespace PakFixedPolyomino.PakParserKernelNoncoreRejection
open MStarParserMicrocode MStarParserExecution MStarConcreteAlphabet
abbrev PTape := PakParserOuterBridge.OuterTape

theorem scanPad_noncore_rejected (left right : List PTape) (focus : PTape)
    (noncore : ∀ a, focus ≠ .core a) :
    oneStep zero one work (.running scanPad ⟨left, focus, right⟩) = .rejected := by
  unfold oneStep
  change (if scanPad = copyStart then _ else _) = _
  rw [if_neg PakParserKernelTableFacts.scanPad_ne_copyStart,
    MStarParserSoundness.parserStep_scanPad_noncore focus noncore]
  simp [MStarParserMicrocode.reject, applyAction]

theorem scanLen_noncore_rejected (left right : List PTape) (focus : PTape)
    (noncore : ∀ a, focus ≠ .core a) :
    oneStep zero one work (.running scanLen ⟨left, focus, right⟩) = .rejected := by
  unfold oneStep
  change (if scanLen = copyStart then _ else _) = _
  rw [if_neg PakParserKernelTableFacts.scanLen_ne_copyStart,
    MStarParserSoundness.parserStep_scanLen_noncore focus noncore]
  simp [MStarParserMicrocode.reject, applyAction]

theorem scanPad_accepting_core (left right : List PTape) (focus : PTape)
    (accepted : MStarParserSoundness.CanAcceptResult
      (.running scanPad ⟨left, focus, right⟩)) : ∃ a, focus = .core a := by
  classical
  by_contra missing
  have noncore : ∀ a, focus ≠ .core a := by
    intro a equality
    exact missing ⟨a, equality⟩
  have after := (MStarParserSoundness.canAcceptResult_oneStep_iff _).2 accepted
  rw [scanPad_noncore_rejected left right focus noncore] at after
  exact MStarParserSoundness.not_canAcceptResult_rejected after

theorem scanLen_accepting_core (left right : List PTape) (focus : PTape)
    (accepted : MStarParserSoundness.CanAcceptResult
      (.running scanLen ⟨left, focus, right⟩)) : ∃ a, focus = .core a := by
  classical
  by_contra missing
  have noncore : ∀ a, focus ≠ .core a := by
    intro a equality
    exact missing ⟨a, equality⟩
  have after := (MStarParserSoundness.canAcceptResult_oneStep_iff _).2 accepted
  rw [scanLen_noncore_rejected left right focus noncore] at after
  exact MStarParserSoundness.not_canAcceptResult_rejected after

end PakFixedPolyomino.PakParserKernelNoncoreRejection
