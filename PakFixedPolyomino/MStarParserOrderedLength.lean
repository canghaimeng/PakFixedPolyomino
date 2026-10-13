import PakFixedPolyomino.PakScannerRawShape

/-! # Ordered scanner-tail length soundness

This module isolates the ordered tail (`core*`, optional right-end, hash*)
used by the generalized scan-length converse. -/

namespace PakFixedPolyomino.MStarParserOrderedLength

open MStarParserExecution MStarParserMicrocode MStarConcreteAlphabet
open MStarParserSoundness MStarOuterProgram
open MStarParserTailSoundness

def OrderedScannerTail (cores : List CoreTape) (hasRightEnd : Bool)
    (hashCount : ℕ) : List (Tape CoreTape) :=
  cores.map Tape.core ++
    (if hasRightEnd then [.scratch ⟨2, by decide⟩] else []) ++
      List.replicate hashCount .hash

/-- The exact initial-to-return part of a zero length-marker iteration.  The
remaining return/scan continuation is kept separate because it is where an
ordered right-end/hash suffix is ruled out. -/
def lengthZeroReturnPrefix (paid extra : ℕ) (next : Tape CoreTape)
    (right : List (Tape CoreTape)) : Result CoreTape :=
  generalReturnAtNext paid extra next right

theorem reaches_lengthZeroReturnPrefix (paid extra : ℕ)
    (next : Tape CoreTape) (right : List (Tape CoreTape)) :
    Reaches zero one work
      (lengthState paid (72 + extra) (.core zero) (next :: right))
      (lengthZeroReturnPrefix paid extra next right) := by
  have h₀ := reaches_generalFirstUnmarked paid extra next right
  have h₁ := reaches_generalAfterCross paid extra next right
  have h₂ := reaches_generalReturnStarted paid extra next right
  have h₃ := reaches_generalReturnAtSep paid extra next right
  have h₄ := reaches_generalReturnLenStarted paid extra next right
  have h₅ := reaches_generalReturnAtNext paid extra next right
  unfold lengthZeroReturnPrefix
  exact reaches_trans zero one work h₀
    (reaches_trans zero one work h₁
      (reaches_trans zero one work h₂
        (reaches_trans zero one work h₃
          (reaches_trans zero one work h₄ h₅))))

theorem not_canAccept_lengthZeroReturnPrefix_rightEnd (paid extra hashes : ℕ) :
    ¬ CanAcceptResult
      (lengthZeroReturnPrefix paid extra lenDone
        (List.replicate hashes Tape.hash)) := by
  intro hacc
  cases hashes with
  | zero =>
      have hnext := (canAcceptResult_oneStep_iff _).2 hacc
      have hstep : oneStep zero one work
          (lengthZeroReturnPrefix paid extra lenDone []) = .stuck := by
        simp [lengthZeroReturnPrefix, generalReturnAtNext, afterRightRepeat,
          oneStep, returnLen_ne_copyStart, parserStep_returnLen,
          MStarParserMicrocode.go, applyAction]
      have hnext' : CanAcceptResult
          (oneStep zero one work
            (lengthZeroReturnPrefix paid extra lenDone [])) := by
        simpa using hnext
      rw [hstep] at hnext'
      exact (not_canAcceptResult_stuck hnext').elim
  | succ hashes =>
      let left : List (Tape CoreTape) :=
        List.replicate (paid + 1) lenDone ++
          (sepPad :: List.replicate (72 * (paid + 1)) padDone ++
            List.replicate extra (Tape.core zero) ++ fixedPaddingTail)
      have h₁ := (canAcceptResult_oneStep_iff _).2 hacc
      have hone : oneStep zero one work
          (lengthZeroReturnPrefix paid extra lenDone
            (List.replicate (hashes + 1) Tape.hash)) =
          .running returnLen ⟨lenDone :: left, Tape.hash,
            List.replicate hashes Tape.hash⟩ := by
        simpa [lengthZeroReturnPrefix, generalReturnAtNext, afterRightRepeat,
          left, List.replicate_succ] using
          (MStarConcreteAlphabet.oneStep_returnLen_done
            left Tape.hash (List.replicate hashes Tape.hash))
      rw [hone] at h₁
      have h₂ := (canAcceptResult_oneStep_iff _).2 h₁
      rw [oneStep_returnLen_other (lenDone :: left)
        (List.replicate hashes Tape.hash) Tape.hash (by
          intro h
          cases h)] at h₂
      have h₃ := (canAcceptResult_oneStep_iff _).2 h₂
      rw [oneStep_scanLen_noncore (lenDone :: left)
        (List.replicate hashes Tape.hash) Tape.hash (by
          intro a h
          cases h)] at h₃
      exact (not_canAcceptResult_rejected h₃).elim

def lengthListState (paid padding : ℕ) : List (Tape CoreTape) → Result CoreTape
  | [] => .stuck
  | focus :: right => lengthState paid padding focus right

theorem not_canAccept_lengthListState_noncore (paid padding : ℕ)
    (x : Tape CoreTape) (right : List (Tape CoreTape))
    (hx : ∀ a, x ≠ .core a) :
    ¬ CanAcceptResult (lengthListState paid padding (x :: right)) := by
  intro hacc
  have hnext := (canAcceptResult_oneStep_iff _).2 hacc
  unfold lengthListState lengthState at hnext
  rw [oneStep_scanLen_noncore _ _ x hx] at hnext
  exact (not_canAcceptResult_rejected hnext).elim

theorem not_canAccept_lengthListState_wrongCore (paid padding : ℕ)
    (a : CoreTape) (right : List (Tape CoreTape))
    (hz : a ≠ zero) (ho : a ≠ one) :
    ¬ CanAcceptResult
      (lengthListState paid padding (Tape.core a :: right)) := by
  intro hacc
  have hnext := (canAcceptResult_oneStep_iff _).2 hacc
  unfold lengthListState lengthState at hnext
  rw [oneStep_scanLen_wrong_core _ _ a hz ho] at hnext
  exact (not_canAcceptResult_rejected hnext).elim

theorem lengthListState_ordered_split (cores : List CoreTape)
    (hasRightEnd : Bool) (hashes paid padding : ℕ)
    (hacc : CanAcceptResult
      (lengthListState paid padding
        (OrderedScannerTail cores hasRightEnd hashes))) :
    ∃ m y ys,
      OrderedScannerTail cores hasRightEnd hashes =
        List.replicate m (Tape.core zero) ++ Tape.core one :: y :: ys ∧
      72 * m ≤ padding ∧
      CanAcceptResult
        (lengthState (paid + m) (padding - 72 * m) (.core one) (y :: ys)) := by
  induction cores generalizing paid padding with
  | nil =>
      cases hasRightEnd with
      | false =>
          cases hashes with
          | zero =>
              have hstuck : CanAcceptResult (.stuck : Result CoreTape) := by
                simpa [OrderedScannerTail, lengthListState] using hacc
              exact (not_canAcceptResult_stuck hstuck).elim
          | succ hashes =>
              have hbad := not_canAccept_lengthListState_noncore paid padding
                Tape.hash (List.replicate hashes Tape.hash) (by
                  intro a h
                  cases h)
              apply False.elim
              apply hbad
              simpa [OrderedScannerTail, List.replicate_succ] using hacc
      | true =>
          have hbad := not_canAccept_lengthListState_noncore paid padding
            lenDone (List.replicate hashes Tape.hash) (by
              intro a h
              cases h)
          apply False.elim
          apply hbad
          simpa [OrderedScannerTail, lenDone] using hacc
  | cons a rest ih =>
      have hacc₀ : CanAcceptResult
          (lengthState paid padding (.core a)
            (OrderedScannerTail rest hasRightEnd hashes)) := by
        change CanAcceptResult
          (lengthState paid padding (.core a)
            (OrderedScannerTail rest hasRightEnd hashes)) at hacc
        exact hacc
      by_cases hz : a = zero
      · subst a
        have hpad : 72 ≤ padding :=
          lengthState_zero_canAccept_forces_padding paid padding
            (OrderedScannerTail rest hasRightEnd hashes) hacc₀
        obtain ⟨extra, hpadding⟩ := Nat.exists_eq_add_of_le hpad
        cases rest with
        | nil =>
            cases hasRightEnd with
            | false =>
                cases hashes with
                | zero =>
                    have hbad := not_canAccept_lengthState_zero_empty paid padding
                    exact (hbad (by
                      simpa [OrderedScannerTail] using hacc₀)).elim
                | succ hashes =>
                    have hstart : CanAcceptResult
                        (lengthState paid (72 + extra) (.core zero)
                          (Tape.hash :: List.replicate hashes Tape.hash)) := by
                      simpa [hpadding, OrderedScannerTail,
                        List.replicate_succ] using hacc₀
                    have hnext := canAcceptResult_reaches_forward
                      (reaches_length_zero_iteration paid extra Tape.hash
                        (List.replicate hashes Tape.hash) (by
                          intro h
                          cases h)) hstart
                    have hbad := not_canAccept_lengthListState_noncore
                      (paid + 1) extra Tape.hash
                      (List.replicate hashes Tape.hash) (by
                        intro a h
                        cases h)
                    exact (hbad (by
                      simpa [lengthListState] using hnext)).elim
            | true =>
                have hstart : CanAcceptResult
                    (lengthState paid (72 + extra) (.core zero)
                      (lenDone :: List.replicate hashes Tape.hash)) := by
                  simpa [hpadding, OrderedScannerTail, lenDone] using hacc₀
                have hprefix := canAcceptResult_reaches_forward
                  (reaches_lengthZeroReturnPrefix paid extra lenDone
                    (List.replicate hashes Tape.hash)) hstart
                exact (not_canAccept_lengthZeroReturnPrefix_rightEnd
                  paid extra hashes hprefix).elim
        | cons b bs =>
            have hstart : CanAcceptResult
                (lengthState paid (72 + extra) (.core zero)
                  (.core b :: OrderedScannerTail bs hasRightEnd hashes)) := by
              simpa [hpadding, OrderedScannerTail] using hacc₀
            have hnext := canAcceptResult_reaches_forward
              (reaches_length_zero_iteration paid extra (.core b)
                (OrderedScannerTail bs hasRightEnd hashes) (by
                  simp [lenDone])) hstart
            have hnextList : CanAcceptResult
                (lengthListState (paid + 1) extra
                  (OrderedScannerTail (b :: bs) hasRightEnd hashes)) := by
              simpa [lengthListState, OrderedScannerTail] using hnext
            rcases ih (paid + 1) extra hnextList with
              ⟨m, y, ys, hshape, hbound, hfinal⟩
            refine ⟨m + 1, y, ys, ?_, ?_, ?_⟩
            · change Tape.core zero ::
                OrderedScannerTail (b :: bs) hasRightEnd hashes = _
              rw [hshape]
              simp [List.replicate_succ]
            · omega
            · have hpaid : paid + (m + 1) = paid + 1 + m := by omega
              have hmul : 72 * (m + 1) = 72 * m + 72 := by ring
              have hrem : padding - 72 * (m + 1) = extra - 72 * m := by
                rw [hpadding, hmul]
                omega
              rw [hpaid, hrem]
              exact hfinal
      · by_cases ho : a = one
        · subst a
          cases htail : OrderedScannerTail rest hasRightEnd hashes with
          | nil =>
              exact (not_canAccept_lengthState_one_empty paid padding
                (by simpa [htail] using hacc₀)).elim
          | cons y ys =>
              have hremaining := lengthState_one_canAccept_forces_no_padding
                paid padding (y :: ys) (by simpa [htail] using hacc₀)
              subst padding
              refine ⟨0, y, ys, ?_, by simp, ?_⟩
              · change Tape.core one ::
                  OrderedScannerTail rest hasRightEnd hashes = _
                rw [htail]
                rfl
              · simpa [htail] using hacc₀
        · exact (not_canAccept_lengthListState_wrongCore paid padding a
            (OrderedScannerTail rest hasRightEnd hashes) hz ho (by
              simpa [lengthListState, OrderedScannerTail] using hacc₀)).elim

theorem OrderedScannerTail_prefix_cancel (pre cores : List CoreTape)
    (hasRightEnd : Bool) (hashes : ℕ) (rest : List (Tape CoreTape))
    (h : OrderedScannerTail cores hasRightEnd hashes =
      pre.map Tape.core ++ rest) :
    ∃ cores', cores = pre ++ cores' ∧
      rest = OrderedScannerTail cores' hasRightEnd hashes := by
  induction pre generalizing cores rest with
  | nil =>
      exact ⟨cores, rfl, by simpa using h.symm⟩
  | cons p ps ih =>
      cases cores with
      | nil =>
          cases hasRightEnd with
          | false =>
              cases hashes <;>
                simp [OrderedScannerTail, List.replicate_succ] at h
          | true =>
              simp [OrderedScannerTail] at h
      | cons c cs =>
          have hc : c = p := by
            have := congrArg List.head? h
            simpa [OrderedScannerTail] using this
          have htail : OrderedScannerTail cs hasRightEnd hashes =
              ps.map Tape.core ++ rest := by
            have := congrArg List.tail h
            simpa [OrderedScannerTail] using this
          rcases ih cs rest htail with ⟨cores', hcores, hrest⟩
          subst c
          refine ⟨cores', ?_, hrest⟩
          simp [hcores]

theorem slotOneTrimmedZipper_hasEncodedPrefix {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    HasEncodedPrefix (PakSlotOneParserDecode.slotOneTrimmedZipper F) := by
  let z := PakSlotOneParserDecode.slotOneTrimmedZipper F
  have haccept : CanAcceptResult
      (.running (fixed ⟨0, by decide⟩) z) := by
    simpa [z] using PakSlotOneParserDecode.slotOneTrimmedZipper_canAccept F
  rcases PakSlotOneParserDecode.canAccept_fixed0_after_scanPad_split z haccept with
    ⟨padding, focus, right, hscan, hlengthLeft⟩
  have hlength : CanAcceptResult (lengthState 0 padding focus right) := by
    simpa [z, PakSlotOneParserDecode.slotOneTrimmedZipper,
      PakSlotOneParserDecode.lengthStateWithLeft, lengthState,
      List.append_assoc] using hlengthLeft
  rcases PakScannerRawShape.slotOneTrimmedZipper_ordered_tape_shape F with
    ⟨cores, hasRightEnd, hashes, hordered⟩
  have hzordered : z.focus :: z.right =
      OrderedScannerTail cores hasRightEnd hashes := by
    simpa [z, OrderedScannerTail] using hordered
  let pre : List CoreTape :=
    List.replicate 72 zero ++ List.replicate padding zero ++ [one]
  have hpre : z.focus :: z.right =
      pre.map Tape.core ++ focus :: right := by
    rw [hscan]
    simp [pre, List.map_append, List.append_assoc]
  have hcancel : OrderedScannerTail cores hasRightEnd hashes =
      pre.map Tape.core ++ focus :: right := hzordered.symm.trans hpre
  rcases OrderedScannerTail_prefix_cancel pre cores hasRightEnd hashes
      (focus :: right) hcancel with ⟨remainingCores, hcores, hrest⟩
  have hlengthOrdered : CanAcceptResult
      (lengthListState 0 padding
        (OrderedScannerTail remainingCores hasRightEnd hashes)) := by
    rw [← hrest]
    simpa [lengthListState] using hlength
  rcases lengthListState_ordered_split remainingCores hasRightEnd hashes
      0 padding hlengthOrdered with
    ⟨m, y, ys, hlengthShape, hbound, hfinal⟩
  have hremaining := lengthState_one_canAccept_forces_no_padding
    m (padding - 72 * m) (y :: ys) (by simpa using hfinal)
  have hpadding : padding = 72 * m := by omega
  have hfinal₀ : CanAcceptResult
      (lengthState m 0 (.core one) (y :: ys)) := by
    simpa [hpadding] using hfinal
  have hpair : CanAcceptResult (pairingRawStarted m (y :: ys)) :=
    canAcceptResult_reaches_forward (reaches_pairingRawStarted m (y :: ys))
      hfinal₀
  have hallTotal := MStarParserTailSoundness.slotOneTrimmedZipper_all_allowed F
  have hallCells : ∀ x ∈ y :: ys,
      MStarParserTailSoundness.ScannerAllowedTape x := by
    intro x hx
    apply hallTotal x
    rw [hscan, hrest, hlengthShape]
    simp [hx]
  rcases MStarParserTailSoundness.pairingRaw_canAccept_extract_allowed
      m (y :: ys) hallCells hpair with
    ⟨bits, rest, hbitsLen, hcells, hfinished⟩
  have hallRest : ∀ x ∈ rest,
      MStarParserTailSoundness.ScannerAllowedTape x := by
    intro x hx
    apply hallCells x
    rw [hcells]
    simp [hx]
  rcases MStarParserTailSoundness.pairRawFinished_canAccept_forces_suffix_allowed
      bits rest hallRest hfinished with ⟨tail, htail⟩
  refine ⟨bits.reverse, tail, ?_⟩
  rw [hscan, hrest, hlengthShape, hcells, htail, hpadding]
  rw [MStarParserExecution.inputCells_encodedWord]
  have hpad : ConcretePakSide.paddingLength bits.reverse.length =
      72 + 72 * m := by
    simp [ConcretePakSide.paddingLength, hbitsLen]
    omega
  rw [hpad, List.replicate_add]
  simp [hbitsLen, List.append_assoc]

end PakFixedPolyomino.MStarParserOrderedLength
