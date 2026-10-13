import PakFixedPolyomino.MStarParserTailSoundness
import PakFixedPolyomino.MStarParserStageStandard
import PakFixedPolyomino.PakParserKernelNoncoreRejection

/-! Tail-preserving payload and suffix readback using the original allowed
scanner letters, zipper, and executable acceptance predicate. These proofs
replace only the five parser-related compiler-trust leaves; scanner path
invariants are handled separately. -/
namespace PakFixedPolyomino.MStarParserTailSoundnessStandard
open MStarParserExecution MStarParserMicrocode MStarConcreteAlphabet
open MStarParserSoundness MStarOuterProgram MStarParserTailSoundness
set_option maxHeartbeats 2000000

theorem not_canAccept_lengthState_zero_empty
    (paid padding : ℕ) :
    ¬ CanAcceptResult (lengthState paid padding (.core zero) []) := by
  intro hacc
  have hpad : 72 ≤ padding :=
    lengthState_zero_canAccept_forces_padding paid padding [] hacc
  obtain ⟨extra, hpadding⟩ := Nat.exists_eq_add_of_le hpad
  have hext : CanAcceptResult
      (lengthState paid padding (.core zero) [.hash]) := by
    have := CanAcceptResult_extendRight
      (lengthState paid padding (.core zero) []) [.hash] hacc
    simpa [lengthState, extendResultRight, extendRight, List.append_assoc] using this
  have hstart : CanAcceptResult
      (lengthState paid (72 + extra) (.core zero) [.hash]) := by
    simpa [hpadding] using hext
  have hnext := canAcceptResult_reaches_forward
    (MStarParserStageStandard.reaches_length_zero_iteration paid extra .hash [] (by
      intro h
      cases h)) hstart
  have hreject := (canAcceptResult_oneStep_iff _).2 hnext
  unfold lengthState at hreject
  rw [PakParserKernelNoncoreRejection.scanLen_noncore_rejected _ _ .hash (by simp)] at hreject
  exact not_canAcceptResult_rejected hreject

theorem pairRaw_canAccept_step_allowed
    (done : List Bool) (remaining : ℕ) (cells : List (Tape CoreTape))
    (hallowed : ∀ x ∈ cells, ScannerAllowedTape x)
    (hacc : CanAcceptResult (pairRawBefore done remaining cells)) :
    ∃ b rest,
      cells = bitCell zero one b :: rest ∧
      CanAcceptResult (pairRawNextState done remaining b rest) := by
  cases hcells : cells with
  | nil =>
      exact (not_canAccept_pairRawBefore_empty done remaining
        (by simpa [hcells] using hacc)).elim
  | cons focus rest =>
      have hfocusAllowed : ScannerAllowedTape focus := hallowed focus (by simp [hcells])
      have hat := canAcceptResult_reaches_forward
        (reaches_pairRawAtPayload done remaining focus rest)
        (by simpa [hcells] using hacc)
      unfold pairRawAtPayload at hat
      simp only [afterRightList] at hat
      cases focus with
      | core a =>
          have hab := MStarParserStageStandard.pairRawAtPayload_canAccept_forces_bit done remaining
            _ rest a hat
          rcases hab with hzero | hone
          · subst a
            refine ⟨false, rest, by simpa [hcells, bitCell], ?_⟩
            exact canAcceptResult_reaches_forward
              (reaches_pairRaw_iteration done remaining false rest)
              (by simpa [hcells, bitCell] using hacc)
          · subst a
            refine ⟨true, rest, by simpa [hcells, bitCell], ?_⟩
            exact canAcceptResult_reaches_forward
              (reaches_pairRaw_iteration done remaining true rest)
              (by simpa [hcells, bitCell] using hacc)
      | hash =>
          have hnext := (canAcceptResult_oneStep_iff _).2 hat
          rw [oneStep_seekPayload_allowed_noncore _ _ .hash
            hfocusAllowed (by simp)] at hnext
          exact (not_canAcceptResult_rejected hnext).elim
      | markL => change False at hfocusAllowed; exact hfocusAllowed.elim
      | markR => change False at hfocusAllowed; exact hfocusAllowed.elim
      | scratch i =>
          have hnext := (canAcceptResult_oneStep_iff _).2 hat
          rw [oneStep_seekPayload_allowed_noncore _ _ (.scratch i)
            hfocusAllowed (by simp)] at hnext
          exact (not_canAcceptResult_rejected hnext).elim

theorem pairRaw_canAccept_fold_allowed
    (done : List Bool) (remaining : ℕ) (cells : List (Tape CoreTape))
    (hallowed : ∀ x ∈ cells, ScannerAllowedTape x)
    (hacc : CanAcceptResult (pairRawBefore done remaining cells)) :
    ∃ bits rest,
      bits.length = remaining + 1 ∧
      cells = bits.map (bitCell zero one) ++ rest ∧
      CanAcceptResult (pairRawFinished (done ++ bits) rest) := by
  induction remaining generalizing done cells with
  | zero =>
      rcases pairRaw_canAccept_step_allowed done 0 cells hallowed hacc with
        ⟨b, rest, hcells, hfinal⟩
      exact ⟨[b], rest, by simp, by simpa [hcells],
        by simpa [pairRawNextState] using hfinal⟩
  | succ remaining ih =>
      rcases pairRaw_canAccept_step_allowed done (remaining + 1) cells
          hallowed hacc with ⟨b, rest, hcells, hnext⟩
      have hallowedRest : ∀ x ∈ rest, ScannerAllowedTape x := by
        intro x hx
        apply hallowed x
        rw [hcells]
        simp [hx]
      rcases ih (done ++ [b]) rest hallowedRest hnext with
        ⟨bits, tail, hlen, hrest, hfinal⟩
      refine ⟨b :: bits, tail, ?_, ?_, ?_⟩
      · simp [hlen]
      · rw [hcells, hrest]
        simp [List.append_assoc]
      · simpa [List.append_assoc] using hfinal

theorem pairingRaw_canAccept_extract_allowed
    (m : ℕ) (cells : List (Tape CoreTape))
    (hallowed : ∀ x ∈ cells, ScannerAllowedTape x)
    (hacc : CanAcceptResult (pairingRawStarted m cells)) :
    ∃ bits rest,
      bits.length = m ∧
      cells = bits.map (bitCell zero one) ++ rest ∧
      CanAcceptResult (pairRawFinished bits rest) := by
  cases m with
  | zero =>
      rw [pairingRawStarted_zero_eq_finished] at hacc
      exact ⟨[], cells, rfl, rfl, hacc⟩
  | succ remaining =>
      rw [pairingRawStarted_succ_eq_before] at hacc
      rcases pairRaw_canAccept_fold_allowed [] remaining cells hallowed hacc with
        ⟨bits, rest, hlen, hcells, hfinal⟩
      exact ⟨bits, rest, by omega, hcells, by simpa using hfinal⟩

theorem pairRawFinished_canAccept_forces_suffix_allowed
    (bits : List Bool) (cells : List (Tape CoreTape))
    (hallowed : ∀ x ∈ cells, ScannerAllowedTape x)
    (hacc : CanAcceptResult (pairRawFinished bits cells)) :
    ∃ tail, cells = [.core one, .core work] ++ tail := by
  cases hcells : cells with
  | nil =>
      exact (not_canAccept_pairRawFinished_empty bits (by simpa [hcells] using hacc)).elim
  | cons focus right =>
      have hfocusAllowed : ScannerAllowedTape focus := hallowed focus (by simp [hcells])
      have hsuffix := canAcceptResult_reaches_forward
        (reaches_verifyRawAtSuffix bits focus right) (by simpa [hcells] using hacc)
      unfold verifyRawAtSuffix at hsuffix
      simp only [afterRightList] at hsuffix
      cases focus with
      | core a =>
          by_cases ha : a = one
          · subst a
            cases hright : right with
            | nil =>
                have hnext := (canAcceptResult_oneStep_iff _).2 hsuffix
                rw [hright, oneStep_verifyPayload_one_nil] at hnext
                exact (not_canAcceptResult_stuck hnext).elim
            | cons next tail =>
                have hnextAllowed : ScannerAllowedTape next :=
                  hallowed next (by simp [hcells, hright])
                have hhigh := (canAcceptResult_oneStep_iff _).2 hsuffix
                rw [hright, oneStep_verifyPayload_one_cons] at hhigh
                cases next with
                | core b =>
                    by_cases hb : b = work
                    · subst b
                      exact ⟨tail, by simp [hcells, hright]⟩
                    · have hnext := (canAcceptResult_oneStep_iff _).2 hhigh
                      rw [MStarParserStageStandard.oneStep_verifyHigh_wrong_core _ _ _ hb] at hnext
                      exact (not_canAcceptResult_rejected hnext).elim
                | hash =>
                    have hnext := (canAcceptResult_oneStep_iff _).2 hhigh
                    rw [oneStep_verifyHigh_allowed_noncore _ _ .hash
                      hnextAllowed (by simp)] at hnext
                    exact (not_canAcceptResult_rejected hnext).elim
                | markL => change False at hnextAllowed; exact hnextAllowed.elim
                | markR => change False at hnextAllowed; exact hnextAllowed.elim
                | scratch i =>
                    have hnext := (canAcceptResult_oneStep_iff _).2 hhigh
                    rw [oneStep_verifyHigh_allowed_noncore _ _ (.scratch i)
                      hnextAllowed (by simp)] at hnext
                    exact (not_canAcceptResult_rejected hnext).elim
          · have hnext := (canAcceptResult_oneStep_iff _).2 hsuffix
            rw [MStarParserStageStandard.oneStep_verifyPayload_wrong_core _ _ _ ha] at hnext
            exact (not_canAcceptResult_rejected hnext).elim
      | hash =>
          have hnext := (canAcceptResult_oneStep_iff _).2 hsuffix
          rw [oneStep_verifyPayload_allowed_noncore _ _ .hash
            hfocusAllowed (by simp)] at hnext
          exact (not_canAcceptResult_rejected hnext).elim
      | markL => change False at hfocusAllowed; exact hfocusAllowed.elim
      | markR => change False at hfocusAllowed; exact hfocusAllowed.elim
      | scratch i =>
          have hnext := (canAcceptResult_oneStep_iff _).2 hsuffix
          rw [oneStep_verifyPayload_allowed_noncore _ _ (.scratch i)
            hfocusAllowed (by simp)] at hnext
          exact (not_canAcceptResult_rejected hnext).elim

theorem pairingRaw_canAccept_payload_suffix
    (m : ℕ) (cells : List (Tape CoreTape))
    (hallowed : ∀ x ∈ cells, ScannerAllowedTape x)
    (hacc : CanAcceptResult (pairingRawStarted m cells)) :
    ∃ (bits : List Bool) (tail : List (Tape CoreTape)), bits.length = m ∧
      cells = bits.map (bitCell zero one) ++ [.core one, .core work] ++ tail := by
  obtain ⟨bits, rest, hlen, hcells, hfinal⟩ :=
    pairingRaw_canAccept_extract_allowed m cells hallowed hacc
  have hallRest : ∀ x ∈ rest, ScannerAllowedTape x := by
    intro x hx
    apply hallowed x
    rw [hcells]
    simp [hx]
  obtain ⟨tail, hrest⟩ :=
    pairRawFinished_canAccept_forces_suffix_allowed bits rest hallRest hfinal
  exact ⟨bits, tail, hlen, by rw [hcells, hrest]; simp [List.append_assoc]⟩

end PakFixedPolyomino.MStarParserTailSoundnessStandard
