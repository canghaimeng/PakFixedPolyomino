import PakFixedPolyomino.MStarParserSoundness

/-! The original parser run and rejection semantics, with kernel proofs of
the four literal state inequalities. Arbitrary exterior zipper cells remain
in the statements. This repairs compiler-trust leaves in tail readback. -/
namespace PakFixedPolyomino.MStarParserStageStandard
open MStarOuterProgram MStarParserMicrocode MStarParserExecution
open MStarConcreteAlphabet MStarParserSoundness
set_option maxHeartbeats 2000000

theorem returnLen_ne_copyStart : returnLen ≠ copyStart := by
  decide

theorem seekPayload_ne_copyStart : seekPayload ≠ copyStart := by
  decide

theorem verifyPayload_ne_copyStart : verifyPayload ≠ copyStart := by
  decide

theorem verifyHigh_ne_copyStart : verifyHigh ≠ copyStart := by
  decide

theorem oneStep_returnLen_other (left right : List (Tape CoreTape))
    (x : Tape CoreTape) (hx : x ≠ lenDone) :
    oneStep zero one work (.running returnLen ⟨left, x, right⟩) =
      .running scanLen ⟨left, x, right⟩ := by
  unfold oneStep
  change (if returnLen = copyStart then _ else _) = _
  rw [if_neg returnLen_ne_copyStart, parserStep_returnLen]
  simp [hx, MStarParserMicrocode.go, applyAction]

theorem reaches_length_zero_iteration (paid extra : ℕ)
    (next : Tape CoreTape) (right : List (Tape CoreTape))
    (hnext : next ≠ lenDone) :
    Reaches zero one work
      (lengthState paid (72 + extra) (.core zero) (next :: right))
      (lengthState (paid + 1) extra next right) := by
  have h₀ := reaches_generalFirstUnmarked paid extra next right
  have h₁ := reaches_generalAfterCross paid extra next right
  have h₂ := reaches_generalReturnStarted paid extra next right
  have h₃ := reaches_generalReturnAtSep paid extra next right
  have h₄ := reaches_generalReturnLenStarted paid extra next right
  have h₅ := reaches_generalReturnAtNext paid extra next right
  have h₆ : Reaches zero one work
      (generalReturnAtNext paid extra next right)
      (lengthState (paid + 1) extra next right) := by
    apply reaches_of_oneStep
    simpa [generalReturnAtNext, lengthState, afterRightRepeat,
      List.append_assoc] using
      oneStep_returnLen_other
        (List.replicate (paid + 1) lenDone ++
          (sepPad ::
            (List.replicate (72 * (paid + 1)) padDone ++
              (List.replicate extra (Tape.core zero) ++ fixedPaddingTail))))
        right next hnext
  exact reaches_trans zero one work h₀
    (reaches_trans zero one work h₁
      (reaches_trans zero one work h₂
        (reaches_trans zero one work h₃
          (reaches_trans zero one work h₄
            (reaches_trans zero one work h₅ h₆)))))

theorem oneStep_seekPayload_wrong_core
    (left right : List (Tape CoreTape)) (a : CoreTape)
    (hz : a ≠ zero) (ho : a ≠ one) :
    oneStep zero one work (.running seekPayload ⟨left, .core a, right⟩) =
      .rejected := by
  unfold oneStep
  change (if seekPayload = copyStart then _ else _) = _
  rw [if_neg seekPayload_ne_copyStart, parserStep_seekPayload_core]
  simp [MStarParserMicrocode.coreEq, hz, ho,
    MStarParserMicrocode.reject, applyAction]

theorem pairRawAtPayload_canAccept_forces_bit
    (done : List Bool) (remaining : ℕ)
    (left right : List (Tape CoreTape)) (a : CoreTape)
    (hacc : CanAcceptResult
      (.running seekPayload ⟨left, .core a, right⟩)) :
    a = zero ∨ a = one := by
  by_contra h
  push Not at h
  have hnext := (canAcceptResult_oneStep_iff _).2 hacc
  rw [oneStep_seekPayload_wrong_core left right a h.1 h.2] at hnext
  exact not_canAcceptResult_rejected hnext

theorem oneStep_verifyPayload_wrong_core
    (left right : List (Tape CoreTape)) (a : CoreTape) (ha : a ≠ one) :
    oneStep zero one work (.running verifyPayload ⟨left, .core a, right⟩) =
      .rejected := by
  unfold oneStep
  change (if verifyPayload = copyStart then _ else _) = _
  rw [if_neg verifyPayload_ne_copyStart, parserStep_verifyPayload_core]
  simp [MStarParserMicrocode.coreEq, ha,
    MStarParserMicrocode.reject, applyAction]

theorem oneStep_verifyHigh_wrong_core
    (left right : List (Tape CoreTape)) (a : CoreTape) (ha : a ≠ work) :
    oneStep zero one work (.running verifyHigh ⟨left, .core a, right⟩) =
      .rejected := by
  unfold oneStep
  change (if verifyHigh = copyStart then _ else _) = _
  rw [if_neg verifyHigh_ne_copyStart, parserStep_verifyHigh_core]
  simp [MStarParserMicrocode.coreEq, ha,
    MStarParserMicrocode.reject, applyAction]

end PakFixedPolyomino.MStarParserStageStandard
