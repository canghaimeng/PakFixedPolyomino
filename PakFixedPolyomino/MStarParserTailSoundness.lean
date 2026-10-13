import PakFixedPolyomino.PakSlotOneParserDecode

/-! # Tail-preserving parser soundness

This module is reserved for the local-prefix variant of parser soundness:
unread cells after the first verified `work` marker are retained as an
arbitrary tail rather than assumed to be part of a canonical input word.
-/

namespace PakFixedPolyomino.MStarParserTailSoundness

open MStarParserExecution MStarParserMicrocode MStarConcreteAlphabet
open MStarParserSoundness
open MStarOuterProgram

def verifyPayloadNoSuffix (left : List (Tape CoreTape)) : List Bool → Result CoreTape
  | [] => .stuck
  | b :: bs => .running verifyPayload
      ⟨left, MStarConcreteAlphabet.payloadMarker b,
        bs.map MStarConcreteAlphabet.payloadMarker⟩

theorem oneStep_verifyPayloadNoSuffix
    (left : List (Tape CoreTape)) (b : Bool) (bs : List Bool) :
    oneStep zero one work (verifyPayloadNoSuffix left (b :: bs)) =
      verifyPayloadNoSuffix (MStarConcreteAlphabet.payloadMarker b :: left) bs := by
  cases bs with
  | nil => cases b <;> rfl
  | cons c cs => cases b <;> rfl

theorem run_verifyPayloadNoSuffix
    (left : List (Tape CoreTape)) (bits : List Bool) :
    run zero one work bits.length (verifyPayloadNoSuffix left bits) = .stuck := by
  induction bits generalizing left with
  | nil => rfl
  | cons b bs ih =>
      change run zero one work (bs.length + 1)
        (verifyPayloadNoSuffix left (b :: bs)) = .stuck
      rw [run_succ, oneStep_verifyPayloadNoSuffix, ih]

theorem verifyRawAtSepLen_empty_reaches_stuck (bits : List Bool) :
    Reaches zero one work (verifyRawAtSepLen bits []) .stuck := by
  cases bits with
  | nil =>
      refine ⟨1, ?_⟩
      rfl
  | cons b bits =>
      let left : List (Tape CoreTape) :=
        sepLen :: List.replicate (b :: bits).length pairedLen ++
          sepPad :: rawPairPad (b :: bits).length
      refine ⟨1 + (b :: bits).length, ?_⟩
      rw [run_add]
      have hfirst : run zero one work 1
          (verifyRawAtSepLen (b :: bits) []) =
          verifyPayloadNoSuffix left (b :: bits) := by
        simp [verifyRawAtSepLen, afterRightRepeat,
          verifyPayloadNoSuffix, left,
          MStarConcreteAlphabet.oneStep_verifySeek_separator,
          List.replicate_succ, List.append_assoc]
      rw [hfirst]
      exact run_verifyPayloadNoSuffix left (b :: bits)

theorem pairRawFinished_empty_reaches_stuck (bits : List Bool) :
    Reaches zero one work (pairRawFinished bits []) .stuck := by
  have h₀₁ : Reaches zero one work (pairRawFinished bits [])
      (verifyRawStarted bits []) := by
    apply reaches_of_oneStep
    cases bits <;>
      simp [pairRawFinished, verifyRawStarted, beforeRightRepeat,
        MStarConcreteAlphabet.oneStep_findLen_finished,
        rawPairPad, List.replicate_succ, List.append_assoc]
  have h₁₂ : Reaches zero one work (verifyRawStarted bits [])
      (verifyRawAtSepLen bits []) := by
    refine ⟨bits.length, ?_⟩
    simpa [verifyRawStarted, verifyRawAtSepLen, List.map_append,
      List.append_assoc] using
      (MStarConcreteAlphabet.run_verifySeek_paired bits.length
        (sepPad :: rawPairPad bits.length) sepLen
        (bits.map MStarConcreteAlphabet.payloadMarker))
  exact reaches_trans zero one work h₀₁
    (reaches_trans zero one work h₁₂
      (verifyRawAtSepLen_empty_reaches_stuck bits))

theorem not_canAccept_pairRawFinished_empty (bits : List Bool) :
    ¬ CanAcceptResult (pairRawFinished bits []) := by
  intro hacc
  have hstuck := canAcceptResult_reaches_forward
    (pairRawFinished_empty_reaches_stuck bits) hacc
  exact not_canAcceptResult_stuck hstuck

/-! ## Scanner-letter invariant -/

/-- Literal letters that can be read from an unmodified scanner/tableau tape.
Payload markers (scratch 5 and 6) are deliberately excluded. -/
def ScannerAllowedTape : Tape CoreTape → Prop
  | .core _ => True
  | .hash => True
  | .scratch i => i = (⟨2, by decide⟩ : Fin 8)
  | _ => False

def scannerBufferRank : ConcretePakScanner.Buffer → ℕ
  | .zero | .one | .work | .headZero | .headOne => 0
  | .rightEnd => 1
  | .hash => 2

def scannerRawStateOKB (s : ConcretePakScanner.State) : Bool :=
  match s.phase with
  | .bot => decide (s.centre = .hash)
  | .top | .cap => decide (s.centre = .hash)
  | .mid =>
      if s.centre = .headZero ∨ s.centre = .headOne then true
      else if s.mode = .tail then
        decide (s.centre = .rightEnd ∨ s.centre = .hash)
      else decide (scannerBufferRank s.centre = 0)

def ScannerRawStateOK (s : ConcretePakScanner.State) : Prop :=
  scannerRawStateOKB s = true

instance (s : ConcretePakScanner.State) : Decidable (ScannerRawStateOK s) :=
  by
    unfold ScannerRawStateOK
    infer_instance

private theorem legalScan_preserves_rawState_and_rank :
    ∀ (s t : ConcretePakScanner.State) (b : Bool),
      ScannerRawStateOK s → s.phase ≠ .bot →
      ConcretePakScanner.LegalScan s t b →
        ScannerRawStateOK t ∧
          scannerBufferRank s.centre ≤ scannerBufferRank t.centre := by
  native_decide

private theorem legalScan_from_bottom_rawState :
    ∀ (t : ConcretePakScanner.State) (b : Bool),
      ConcretePakScanner.LegalScan PakCouplingGenerated.scannerBottom t b →
        ScannerRawStateOK t ∧ scannerBufferRank t.centre = 0 := by
  native_decide

theorem scannerPath_phase_ne_bot_of_pos {n : ℕ}
    (P : PakScannerBaselineAutomaton.ScannerPath n)
    (j : Fin (n + 1)) (hj : 0 < j.1) : (P.states j).phase ≠ .bot := by
  let i : Fin n := ⟨j.1 - 1, by omega⟩
  have htarget : P.states ⟨i.1 + 1, by omega⟩ = P.states j := by
    apply congrArg P.states
    apply Fin.ext
    dsimp [i]
    omega
  intro hbot
  apply ConcretePakScanner.no_clause_to_bot
    (P.states ⟨i.1, Nat.lt_succ_of_lt i.2⟩) (P.states j) (n.testBit i.1)
    hbot
  rw [← htarget]
  exact P.legal i

theorem scannerPath_state_succ_rawState {n : ℕ}
    (P : PakScannerBaselineAutomaton.ScannerPath n) :
    ∀ (k : ℕ) (hk : k + 1 ≤ n),
      ScannerRawStateOK (P.states ⟨k + 1, by omega⟩) := by
  intro k
  induction k with
  | zero =>
      intro hk
      apply (legalScan_from_bottom_rawState
        (P.states ⟨1, by omega⟩) (n.testBit 0) ?_).1
      rw [← P.bottom]
      simpa using P.legal ⟨0, by omega⟩
  | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      let jpos : Fin (n + 1) := ⟨k + 1, by have := hk; omega⟩
      have hjpos : 0 < jpos.1 := by simp [jpos]
      exact (legalScan_preserves_rawState_and_rank
        (P.states ⟨k + 1, by omega⟩) (P.states ⟨k + 2, by omega⟩)
        (n.testBit (k + 1)) hprev
        (scannerPath_phase_ne_bot_of_pos P jpos hjpos)
        (by simpa using P.legal ⟨k + 1, by omega⟩)).1

theorem scannerPath_rank_mono_adjacent_of_pos {n : ℕ}
    (P : PakScannerBaselineAutomaton.ScannerPath n)
    (j : Fin n) (hj : 0 < j.1) :
    scannerBufferRank
        (P.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩).centre ≤
      scannerBufferRank (P.states ⟨j.1 + 1, by omega⟩).centre := by
  have hok := scannerPath_state_succ_rawState P (j.1 - 1) (by omega)
  have hstate : P.states ⟨j.1 - 1 + 1, by omega⟩ =
      P.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩ := by
    apply congrArg P.states
    apply Fin.ext
    change j.1 - 1 + 1 = j.1
    omega
  rw [hstate] at hok
  exact (legalScan_preserves_rawState_and_rank
    (P.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
    (P.states ⟨j.1 + 1, by omega⟩) (n.testBit j.1) hok
    (scannerPath_phase_ne_bot_of_pos P _ hj) (P.legal j)).2

theorem scannerAllowed_bufferCell (b : ConcretePakScanner.Buffer) :
    ScannerAllowedTape (OneTapeTableau.cellLetter
      (PakCouplingGenerated.bufferCell MStarULogAssembly.boundaryData b)) := by
  cases b with
  | hash => change True; trivial
  | zero => change True; trivial
  | one => change True; trivial
  | work => change True; trivial
  | rightEnd => change (⟨2, by decide⟩ : Fin 8) = ⟨2, by decide⟩; rfl
  | headZero => change True; trivial
  | headOne => change True; trivial

/-! ## Empty pairing payload -/

def seekPayloadNoSuffix (left : List (Tape CoreTape)) : List Bool → Result CoreTape
  | [] => .stuck
  | b :: bs => .running seekPayload
      ⟨left, MStarConcreteAlphabet.payloadMarker b,
        bs.map MStarConcreteAlphabet.payloadMarker⟩

theorem oneStep_seekPayloadNoSuffix
    (left : List (Tape CoreTape)) (b : Bool) (bs : List Bool) :
    oneStep zero one work (seekPayloadNoSuffix left (b :: bs)) =
      seekPayloadNoSuffix (MStarConcreteAlphabet.payloadMarker b :: left) bs := by
  cases bs <;> cases b <;> rfl

theorem run_seekPayloadNoSuffix
    (left : List (Tape CoreTape)) (bits : List Bool) :
    run zero one work bits.length (seekPayloadNoSuffix left bits) = .stuck := by
  induction bits generalizing left with
  | nil => rfl
  | cons b bs ih =>
      change run zero one work (bs.length + 1)
        (seekPayloadNoSuffix left (b :: bs)) = .stuck
      rw [run_succ, oneStep_seekPayloadNoSuffix, ih]

theorem pairRawAtSepLen_empty_reaches_stuck
    (done : List Bool) (remaining : ℕ) :
    Reaches zero one work (pairRawAtSepLen done remaining []) .stuck := by
  cases done with
  | nil =>
      refine ⟨1, ?_⟩
      rfl
  | cons b done =>
      let left : List (Tape CoreTape) :=
        sepLen :: List.replicate ((b :: done).length + 1) pairedLen ++
          List.replicate remaining lenDone ++ sepPad ::
            rawPairPad ((b :: done).length + remaining + 1)
      refine ⟨1 + (b :: done).length, ?_⟩
      rw [run_add]
      have hfirst : run zero one work 1
          (pairRawAtSepLen (b :: done) remaining []) =
          seekPayloadNoSuffix left (b :: done) := by
        simp [pairRawAtSepLen, afterRightRepeat, seekPayloadNoSuffix, left,
          MStarConcreteAlphabet.oneStep_seekSepLen_separator,
          MStarConcreteAlphabet.replicate_cons_rotate,
          List.replicate_succ, List.append_assoc]
      rw [hfirst]
      exact run_seekPayloadNoSuffix left (b :: done)

theorem pairRawBefore_empty_reaches_stuck
    (done : List Bool) (remaining : ℕ) :
    Reaches zero one work (pairRawBefore done remaining []) .stuck := by
  have h₀₁ : Reaches zero one work (pairRawBefore done remaining [])
      (pairRawFindAtFresh done remaining []) := by
    refine ⟨done.length, ?_⟩
    simpa [pairRawBefore, pairRawFindAtFresh] using
      (MStarConcreteAlphabet.run_findLen_paired done.length
        (List.replicate remaining lenDone ++ sepPad ::
          rawPairPad (done.length + remaining + 1)) lenDone
        (sepLen :: done.map MStarConcreteAlphabet.payloadMarker))
  have h₁₂ : Reaches zero one work (pairRawFindAtFresh done remaining [])
      (pairRawFreshMarked done remaining []) := by
    apply reaches_of_oneStep
    cases done <;>
      simp [pairRawFindAtFresh, pairRawFreshMarked,
        afterLeftRepeat, beforeRightRepeat,
        MStarConcreteAlphabet.oneStep_findLen_fresh,
        List.replicate_succ, List.append_assoc]
  have h₂₃ : Reaches zero one work (pairRawFreshMarked done remaining [])
      (pairRawAtSepLen done remaining []) := by
    refine ⟨done.length, ?_⟩
    simpa [pairRawFreshMarked, pairRawAtSepLen] using
      (MStarConcreteAlphabet.run_seekSepLen_paired done.length
        (pairedLen :: (List.replicate remaining lenDone ++ sepPad ::
          rawPairPad (done.length + remaining + 1))) sepLen
        (done.map MStarConcreteAlphabet.payloadMarker))
  exact reaches_trans zero one work h₀₁
    (reaches_trans zero one work h₁₂
      (reaches_trans zero one work h₂₃
        (pairRawAtSepLen_empty_reaches_stuck done remaining)))

theorem not_canAccept_pairRawBefore_empty
    (done : List Bool) (remaining : ℕ) :
    ¬ CanAcceptResult (pairRawBefore done remaining []) := by
  intro hacc
  have hstuck := canAcceptResult_reaches_forward
    (pairRawBefore_empty_reaches_stuck done remaining) hacc
  exact not_canAcceptResult_stuck hstuck

theorem oneStep_seekPayload_allowed_noncore
    (left right : List (Tape CoreTape)) (x : Tape CoreTape)
    (hallowed : ScannerAllowedTape x) (hx : ∀ a, x ≠ .core a) :
    oneStep zero one work (.running seekPayload ⟨left, x, right⟩) =
      .rejected := by
  cases x with
  | core a => exact (hx a rfl).elim
  | hash => rfl
  | markL => change False at hallowed; exact hallowed.elim
  | markR => change False at hallowed; exact hallowed.elim
  | scratch i =>
      change i = (⟨2, by decide⟩ : Fin 8) at hallowed
      subst i
      rfl

theorem not_canAccept_pairingRawStarted_empty (m : ℕ) :
    ¬ CanAcceptResult (pairingRawStarted m []) := by
  cases m with
  | zero =>
      rw [pairingRawStarted_zero_eq_finished]
      exact not_canAccept_pairRawFinished_empty []
  | succ r =>
      rw [pairingRawStarted_succ_eq_before]
      exact not_canAccept_pairRawBefore_empty [] r

theorem not_canAccept_lengthState_one_empty
    (paid remaining : ℕ) :
    ¬ CanAcceptResult (lengthState paid remaining (.core one) []) := by
  intro hacc
  have hnone := lengthState_one_canAccept_forces_no_padding paid remaining [] hacc
  subst remaining
  have hpair := canAcceptResult_reaches_forward
    (reaches_pairingRawStarted paid []) hacc
  exact not_canAccept_pairingRawStarted_empty paid hpair

theorem CanAcceptResult_extendRight
    (r : Result CoreTape) (tail : List (Tape CoreTape))
    (hacc : CanAcceptResult r) :
    CanAcceptResult (extendResultRight r tail) := by
  rcases hacc with ⟨fuel, z, hrun⟩
  refine ⟨fuel, extendRight z tail, ?_⟩
  exact run_extendResultRight_to_copyReady zero one work fuel r z tail hrun

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
    (reaches_length_zero_iteration paid extra .hash [] (by
      intro h
      cases h)) hstart
  have hreject := (canAcceptResult_oneStep_iff _).2 hnext
  unfold lengthState at hreject
  rw [oneStep_scanLen_noncore _ _ .hash (by simp)] at hreject
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
          have hab := pairRawAtPayload_canAccept_forces_bit done remaining
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

theorem slotOne_timeZero_tape_allowed {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) (j : Fin n) :
    ScannerAllowedTape
      (((PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).config
        ⟨0, Nat.zero_lt_succ n⟩).tape j.1) := by
  let R := PakFullFrameTableauReadback.FullFrame.tableau_column_readback F.1
    (PakMStarCouplingCorrectness.eastIndex F.1.width_pos)
  have hconfig :
      (PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).config
        ⟨0, Nat.zero_lt_succ n⟩ = R.before := by
    change PakFullFrameTableauReadback.FullFrame.reverse_tableau_config F.1
      ⟨0, Nat.zero_lt_succ n⟩ = R.before
    simp [PakFullFrameTableauReadback.FullFrame.reverse_tableau_config,
      F.1.width_pos, PakFullFrameTableauReadback.reverseColumn,
      PakMStarCouplingCorrectness.eastIndex, R]
  rw [hconfig]
  change ScannerAllowedTape (R.oldTape j.1)
  rw [R.oldTape_at j]
  rcases F.1.east_emits_tableau_window j with ⟨s, t, hscan, hold⟩
  have hstrip : R.oldStrip j =
      PakCouplingGenerated.emittedWindow MStarULogAssembly.boundaryData s t := by
    simpa [R] using hold
  rw [hstrip]
  exact scannerAllowed_bufferCell s.centre

theorem slotOne_firstArrow_write_eq_read {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    (FiniteOneTapeProgram.transition MStarULogAssembly.program
      ((PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).arrow
        ⟨0, F.1.width_pos⟩)).write =
      (FiniteOneTapeProgram.transition MStarULogAssembly.program
        ((PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).arrow
          ⟨0, F.1.width_pos⟩)).read := by
  let A := (PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).arrow
    ⟨0, F.1.width_pos⟩
  change (FiniteOneTapeProgram.transition MStarULogAssembly.program A).write =
    (FiniteOneTapeProgram.transition MStarULogAssembly.program A).read
  have hsource : A.1.1.1 = MStarOuterProgram.State.start := by
    change (FiniteOneTapeProgram.transition MStarULogAssembly.program A).sourceState = _
    exact PakSlotOneFullFrameReflection.slotOne_first_source_start F
  have hslot : A.1.2 = 1 := F.2
  generalize harrow : A = a at hsource hslot ⊢
  rcases a with ⟨⟨⟨q, x⟩, slot⟩, hoccupied⟩
  change q = MStarOuterProgram.State.start at hsource
  subst q
  change slot = 1 at hslot
  subst slot
  cases x with
  | core x =>
      by_cases hinitial : MStarOuterProgram.isInitialLetter MStarULogAssembly.data x = true
      · let act : FiniteOneTapeProgram.Action MStarULogAssembly.State
            MStarULogAssembly.Tape :=
          { write := .core x
            target := .parser MStarULogAssembly.data.parserStart
            move := .stay }
        have hrule : MStarULogAssembly.program.rule .start (.core x) 1 =
            some act := by
          simpa [act] using MStarOuterProgram.start_slot_one
            MStarULogAssembly.data hinitial
        have haction : FiniteOneTapeProgram.actionOf MStarULogAssembly.program
            ⟨((MStarOuterProgram.State.start, .core x), (1 : Fin 2)), hoccupied⟩ =
              act :=
          PakCanonicalFullTrack.actionOf_eq_of_rule_eq _ _ _ hrule
        change (FiniteOneTapeProgram.actionOf MStarULogAssembly.program
          ⟨((MStarOuterProgram.State.start, .core x), (1 : Fin 2)), hoccupied⟩).write =
            .core x
        rw [haction]
      · exact (hoccupied (by
          simp [MStarULogAssembly.program, MStarOuterProgram.program,
            hinitial])).elim
  | hash => exact (hoccupied (by
      simp [MStarULogAssembly.program, MStarOuterProgram.program])).elim
  | markL => exact (hoccupied (by
      simp [MStarULogAssembly.program, MStarOuterProgram.program])).elim
  | markR => exact (hoccupied (by
      simp [MStarULogAssembly.program, MStarOuterProgram.program])).elim
  | scratch i => exact (hoccupied (by
      simp [MStarULogAssembly.program, MStarOuterProgram.program])).elim

theorem slotOne_timeOne_tape_eq_timeZero {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    ((PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).config
      ⟨1, Nat.succ_lt_succ F.1.width_pos⟩).tape =
    ((PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).config
      ⟨0, Nat.zero_lt_succ n⟩).tape := by
  let U := PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1
  have hstep := PakSlotOneFullFrameReflection.slotOne_first_step F
  have hsource := FiniteOneTapeSemantics.step_some_forces_source
    MStarULogAssembly.program MStarOuterProgram.movable
    (U.config ⟨0, Nat.zero_lt_succ n⟩)
    (U.config ⟨1, Nat.succ_lt_succ F.1.width_pos⟩)
    (U.arrow ⟨0, F.1.width_pos⟩) (by simpa [U] using hstep)
  have hwrite := slotOne_firstArrow_write_eq_read F
  have hwritten : FiniteOneTapeSemantics.writtenTape
      (U.config ⟨0, Nat.zero_lt_succ n⟩)
      (FiniteOneTapeProgram.transition MStarULogAssembly.program
        (U.arrow ⟨0, F.1.width_pos⟩)).write =
      (U.config ⟨0, Nat.zero_lt_succ n⟩).tape := by
    funext z
    by_cases hz : z = (U.config ⟨0, Nat.zero_lt_succ n⟩).head
    · subst z
      unfold FiniteOneTapeSemantics.writtenTape
      rw [Function.update_apply, if_pos rfl]
      exact hwrite.trans hsource.2.symm
    · unfold FiniteOneTapeSemantics.writtenTape
      rw [Function.update_apply, if_neg hz]
  unfold FiniteOneTapeSemantics.step at hstep
  dsimp only at hstep
  split at hstep
  · simp at hstep
  · split at hstep
    · have hc := Option.some.inj hstep
      have ht := congrArg (fun c : PakMStarCouplingCorrectness.MStarConfig => c.tape) hc
      change FiniteOneTapeSemantics.writtenTape
        (U.config ⟨0, Nat.zero_lt_succ n⟩)
        (FiniteOneTapeProgram.transition MStarULogAssembly.program
          (U.arrow ⟨0, F.1.width_pos⟩)).write =
        (U.config ⟨1, Nat.succ_lt_succ F.1.width_pos⟩).tape at ht
      exact ht.symm.trans hwritten
    · simp at hstep

theorem slotOne_timeOne_tape_allowed {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) (j : Fin n) :
    ScannerAllowedTape
      (((PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).config
        ⟨1, Nat.succ_lt_succ F.1.width_pos⟩).tape j.1) := by
  rw [slotOne_timeOne_tape_eq_timeZero F]
  exact slotOne_timeZero_tape_allowed F j

theorem slotOneTrimmedZipper_all_allowed {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    ∀ x ∈ (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right,
      ScannerAllowedTape x := by
  let c := (PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).config
    ⟨1, Nat.succ_lt_succ F.1.width_pos⟩
  let h := (PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).head_index
    ⟨1, Nat.succ_lt_succ F.1.width_pos⟩
  have hall : ∀ x ∈ PakOuterParserReflection.windowCells n c,
      ScannerAllowedTape x := by
    intro x hx
    rw [PakOuterParserReflection.windowCells, List.mem_ofFn] at hx
    rcases hx with ⟨j, rfl⟩
    exact slotOne_timeOne_tape_allowed F j
  intro x hx
  have hx' : x = (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ∨
      x ∈ (PakSlotOneParserDecode.slotOneTrimmedZipper F).right :=
    List.mem_cons.mp hx
  rcases hx' with hx | hx
  · subst x
    change ScannerAllowedTape (c.tape h.1)
    exact slotOne_timeOne_tape_allowed F h
  · apply hall x
    change x ∈ (PakOuterParserReflection.windowCells n c).drop (h.1 + 1) at hx
    apply List.mem_of_mem_drop hx

theorem oneStep_verifyPayload_allowed_noncore
    (left right : List (Tape CoreTape)) (x : Tape CoreTape)
    (hallowed : ScannerAllowedTape x) (hx : ∀ a, x ≠ .core a) :
    oneStep zero one work (.running verifyPayload ⟨left, x, right⟩) =
      .rejected := by
  cases x with
  | core a => exact (hx a rfl).elim
  | hash => rfl
  | markL => change False at hallowed; exact hallowed.elim
  | markR => change False at hallowed; exact hallowed.elim
  | scratch i =>
      change i = (⟨2, by decide⟩ : Fin 8) at hallowed
      subst i
      rfl

theorem oneStep_verifyHigh_allowed_noncore
    (left right : List (Tape CoreTape)) (x : Tape CoreTape)
    (hallowed : ScannerAllowedTape x) (hx : ∀ a, x ≠ .core a) :
    oneStep zero one work (.running verifyHigh ⟨left, x, right⟩) =
      .rejected := by
  cases x with
  | core a => exact (hx a rfl).elim
  | hash => rfl
  | markL => change False at hallowed; exact hallowed.elim
  | markR => change False at hallowed; exact hallowed.elim
  | scratch i =>
      change i = (⟨2, by decide⟩ : Fin 8) at hallowed
      subst i
      rfl

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
                      rw [oneStep_verifyHigh_wrong_core _ _ _ hb] at hnext
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
            rw [oneStep_verifyPayload_wrong_core _ _ _ ha] at hnext
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

/-- Target form for the generalized fixed-zero parser converse. -/
def HasEncodedPrefix (z : Zipper (Tape CoreTape)) : Prop :=
  ∃ x tail,
    z.focus :: z.right =
      inputCells zero one work (ConcretePakSide.encodedWord x) ++ tail

end PakFixedPolyomino.MStarParserTailSoundness
