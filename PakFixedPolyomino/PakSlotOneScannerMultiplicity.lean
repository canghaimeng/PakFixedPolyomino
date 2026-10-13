import PakFixedPolyomino.PakSideScannerRow
import PakFixedPolyomino.PakSlotOneExactCount

/-!
# Scanner multiplicity indexed by terminal slack

The optional scanner terminator may occur after additional high-zero work
cells.  Its genuine finite parameter is the number of extra work cells after
the minimum parser/copier reserve.  This file constructs the corresponding
literal scanner path for every permitted slack and proves that these paths
are distinct.  Thus the canonical scanner contribution is the explicit
factor `scannerSlackCount x` rather than an unjustified factor one.
-/

namespace PakFixedPolyomino.PakSlotOneScannerMultiplicity

open ConcretePakScanner
open PakScannerBaselineAutomaton

def scannerSlackCount (x : ConcretePakSide.Word) : ℕ :=
  (PakSideScanner.sideScannerBits x).length -
    PakSideScanner.scannerTerminalIndex x

abbrev ScannerSlack (x : ConcretePakSide.Word) := Fin (scannerSlackCount x)

def slackTerminalIndex (x : ConcretePakSide.Word) (s : ScannerSlack x) : ℕ :=
  PakSideScanner.scannerTerminalIndex x + s.1

theorem scannerSlackCount_pos (x : ConcretePakSide.Word) :
    0 < scannerSlackCount x := by
  unfold scannerSlackCount
  have h := PakSideScanner.scannerTerminalIndex_lt x
  omega

theorem slackTerminalIndex_pos (x : ConcretePakSide.Word)
    (s : ScannerSlack x) : 0 < slackTerminalIndex x s := by
  unfold slackTerminalIndex
  exact Nat.add_pos_left (PakSideScanner.scannerTerminalIndex_pos x) _

theorem slackTerminalIndex_lt (x : ConcretePakSide.Word)
    (s : ScannerSlack x) :
    slackTerminalIndex x s < (PakSideScanner.sideScannerBits x).length := by
  have hs := s.2
  unfold ScannerSlack scannerSlackCount at hs
  have hterminal := PakSideScanner.scannerTerminalIndex_lt x
  unfold slackTerminalIndex
  omega

theorem scannerSlackCount_eq_hashTail_succ (x : ConcretePakSide.Word) :
    scannerSlackCount x =
      (PakSideScanner.sideCopierHashTail x).length + 1 := by
  unfold scannerSlackCount PakSideScanner.sideCopierHashTail
    PakSideScanner.scannerTerminalIndex
  rw [List.length_replicate]
  have hp := PakSideScanner.parserCells_le_sideScannerBits_length x
  have hr := PakSideScanner.parserCopierReserve_le_sideScannerBits_sub x
  have hpos : 0 < (MStarCopierExecution.parserCopierReserve x).length := by
    rw [PakSideScannerRow.parserCopierReserve_length_shape]
    omega
  omega

def extractedSlackNat (x : ConcretePakSide.Word)
    (remaining : List MStarULogAssembly.CoreTape) : ℕ :=
  remaining.length - PakSideScannerRow.copierWorkCount x.length

private theorem legalScan_to_cap_forces_source_top
    (s t : ConcretePakScanner.State) (b : Bool)
    (hlegal : ConcretePakScanner.LegalScan s t b)
    (ht : t.phase = .cap) : s.phase = .top := by
  rcases hlegal with ⟨clause, hclause⟩
  cases clause <;>
    simp [ConcretePakScanner.LegalClause, ht] at hclause ⊢ <;>
    simp_all

/-- The final scanner source is a genuine top state, so at least one hash
cell follows the physical terminator. -/
theorem terminalIndex_lt_sideScannerBits {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word)
    (remaining : List MStarULogAssembly.CoreTape) (hashes : ℕ)
    (hshape : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        MStarParserExecution.inputCells MStarConcreteAlphabet.zero
            MStarConcreteAlphabet.one MStarConcreteAlphabet.work
            (ConcretePakSide.encodedWord x) ++
          [MStarOuterProgram.Tape.core MStarConcreteAlphabet.work,
            MStarOuterProgram.Tape.core MStarConcreteAlphabet.work] ++
          remaining.map MStarOuterProgram.Tape.core ++
          [MStarCopierMicrocode.rightEnd] ++
          List.replicate hashes MStarOuterProgram.Tape.hash)
    (hside : n = ConcretePakSide.sideValue x) :
    PakSlotOneSideValueReflection.terminalIndex x remaining <
      (PakSideScanner.sideScannerBits x).length := by
  have htweak := PakSlotOneSideValueReflection.terminalIndex_lt
    F x remaining hashes hshape
  have hheight := PakSideScanner.sideScannerHeight x
  have hle : PakSlotOneSideValueReflection.terminalIndex x remaining ≤
      (PakSideScanner.sideScannerBits x).length := by
    rw [hside, ← hheight] at htweak
    omega
  by_contra hnot
  have heq : PakSlotOneSideValueReflection.terminalIndex x remaining =
      (PakSideScanner.sideScannerBits x).length := by omega
  let P := PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1
  have htail :=
    (PakSlotOneSideValueReflection.terminal_edge_false_and_tail
      F x remaining hashes hshape).2
  have hnpos : 0 < n := F.1.width_pos
  have hlast : PakSlotOneSideValueReflection.terminalIndex x remaining + 1 =
      n - 1 := by
    rw [hside, ← hheight, heq]
    omega
  have hlegal := P.legal (⟨n - 1, by omega⟩ : Fin n)
  have hsucc : n - 1 + 1 = n := by omega
  have hlegal' : ConcretePakScanner.LegalScan
      (P.states ⟨n - 1, by omega⟩) (P.states ⟨n, by omega⟩)
      (n.testBit (n - 1)) := by
    simpa only [hsucc] using hlegal
  have htarget : (P.states ⟨n, by omega⟩).phase = .cap := by
    rw [P.top]
    rfl
  have hsource : (P.states ⟨n - 1, by omega⟩).phase = .top :=
    legalScan_to_cap_forces_source_top _ _ _ hlegal' htarget
  have hsame :
      (P.states ⟨PakSlotOneSideValueReflection.terminalIndex x remaining + 1,
        by omega⟩).phase = (P.states ⟨n - 1, by omega⟩).phase := by
    exact congrArg (fun q : Fin (n + 1) => (P.states q).phase)
      (Fin.ext hlast)
  have hmid : (P.states
      ⟨PakSlotOneSideValueReflection.terminalIndex x remaining + 1,
        by omega⟩).phase = .mid := by
    simpa [P] using htail.1
  have : (P.states
      ⟨PakSlotOneSideValueReflection.terminalIndex x remaining + 1,
        by omega⟩).phase = .top := hsame.trans hsource
  have hbad : ConcretePakScanner.Phase.mid = .top := hmid.symm.trans this
  exact ConcretePakScanner.Phase.noConfusion hbad

/-- Once successful-copy soundness supplies the minimum-reserve inequality,
the physical terminal position canonically determines an allowed slack. -/
def extractedScannerSlack {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word)
    (remaining : List MStarULogAssembly.CoreTape) (hashes : ℕ)
    (hshape : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        MStarParserExecution.inputCells MStarConcreteAlphabet.zero
            MStarConcreteAlphabet.one MStarConcreteAlphabet.work
            (ConcretePakSide.encodedWord x) ++
          [MStarOuterProgram.Tape.core MStarConcreteAlphabet.work,
            MStarOuterProgram.Tape.core MStarConcreteAlphabet.work] ++
          remaining.map MStarOuterProgram.Tape.core ++
          [MStarCopierMicrocode.rightEnd] ++
          List.replicate hashes MStarOuterProgram.Tape.hash)
    (hside : n = ConcretePakSide.sideValue x)
    (hreserve : PakSideScannerRow.copierWorkCount x.length ≤
      remaining.length) : ScannerSlack x := by
  refine ⟨extractedSlackNat x remaining, ?_⟩
  have ht := terminalIndex_lt_sideScannerBits
    F x remaining hashes hshape hside
  have hheight := PakSideScanner.sideScannerHeight x
  have hparser := PakSideScanner.parserCells_length x
  have hreserveLen := PakSideScannerRow.parserCopierReserve_length_shape x
  have hcanonical :
      PakSideScanner.scannerTerminalIndex x =
        (ConcretePakSide.encodedWord x).length + 3 +
          PakSideScannerRow.copierWorkCount x.length := by
    rw [PakSideScannerRow.scannerTerminalIndex_eq,
      PakSideScanner.parserCells_length,
      ConcretePakSide.encodedWord_length]
    unfold PakSideScannerRow.parserCopierWorkCount
    omega
  have hactual :
      PakSlotOneSideValueReflection.terminalIndex x remaining =
        (ConcretePakSide.encodedWord x).length + 3 + remaining.length := rfl
  unfold extractedSlackNat scannerSlackCount
  rw [hactual] at ht
  rw [hcanonical]
  omega

theorem terminalIndex_eq_slackTerminalIndex_of_extracted {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word)
    (remaining : List MStarULogAssembly.CoreTape) (hashes : ℕ)
    (hshape : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        MStarParserExecution.inputCells MStarConcreteAlphabet.zero
            MStarConcreteAlphabet.one MStarConcreteAlphabet.work
            (ConcretePakSide.encodedWord x) ++
          [MStarOuterProgram.Tape.core MStarConcreteAlphabet.work,
            MStarOuterProgram.Tape.core MStarConcreteAlphabet.work] ++
          remaining.map MStarOuterProgram.Tape.core ++
          [MStarCopierMicrocode.rightEnd] ++
          List.replicate hashes MStarOuterProgram.Tape.hash)
    (hside : n = ConcretePakSide.sideValue x)
    (hreserve : PakSideScannerRow.copierWorkCount x.length ≤
      remaining.length) :
    PakSlotOneSideValueReflection.terminalIndex x remaining =
      slackTerminalIndex x
        (extractedScannerSlack F x remaining hashes hshape hside hreserve) := by
  change PakSlotOneSideValueReflection.terminalIndex x remaining =
    PakSideScanner.scannerTerminalIndex x + extractedSlackNat x remaining
  have hcanonical :
      PakSideScanner.scannerTerminalIndex x =
        (ConcretePakSide.encodedWord x).length + 3 +
          PakSideScannerRow.copierWorkCount x.length := by
    rw [PakSideScannerRow.scannerTerminalIndex_eq,
      PakSideScanner.parserCells_length,
      ConcretePakSide.encodedWord_length]
    unfold PakSideScannerRow.parserCopierWorkCount
    omega
  rw [hcanonical]
  unfold extractedSlackNat PakSlotOneSideValueReflection.terminalIndex
  omega

theorem hashes_eq_of_extractedSlack {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word)
    (remaining : List MStarULogAssembly.CoreTape) (hashes : ℕ)
    (hshape : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        MStarParserExecution.inputCells MStarConcreteAlphabet.zero
            MStarConcreteAlphabet.one MStarConcreteAlphabet.work
            (ConcretePakSide.encodedWord x) ++
          [MStarOuterProgram.Tape.core MStarConcreteAlphabet.work,
            MStarOuterProgram.Tape.core MStarConcreteAlphabet.work] ++
          remaining.map MStarOuterProgram.Tape.core ++
          [MStarCopierMicrocode.rightEnd] ++
          List.replicate hashes MStarOuterProgram.Tape.hash)
    (hside : n = ConcretePakSide.sideValue x)
    (hreserve : PakSideScannerRow.copierWorkCount x.length ≤
      remaining.length) :
    hashes + extractedSlackNat x remaining = scannerSlackCount x := by
  have hlen := congrArg List.length hshape
  have hwindow :
      ((PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right).length = n - 1 := by
    rw [PakScannerRawShape.slotOneTrimmedZipper_cells_eq_scannerBufferPrefix F]
    rw [PakScannerRawShape.scannerBufferPrefix_eq_ofFn]
    simp
  rw [hwindow] at hlen
  have hheight := PakSideScanner.sideScannerHeight x
  unfold MStarParserExecution.inputCells at hlen
  simp only [List.length_append, List.length_reverse, List.length_map,
    List.length_cons, List.length_nil, List.length_replicate] at hlen
  have hlist :
      (ConcretePakSide.encodedWord x).length + 1 + 2 +
          remaining.length + 1 + hashes = n - 1 := by
    omega
  have hcanonical :
      PakSideScanner.scannerTerminalIndex x =
        (ConcretePakSide.encodedWord x).length + 3 +
          PakSideScannerRow.copierWorkCount x.length := by
    rw [PakSideScannerRow.scannerTerminalIndex_eq,
      PakSideScanner.parserCells_length,
      ConcretePakSide.encodedWord_length]
    unfold PakSideScannerRow.parserCopierWorkCount
    omega
  have hremaining : PakSideScannerRow.copierWorkCount x.length +
      extractedSlackNat x remaining = remaining.length := by
    unfold extractedSlackNat
    exact Nat.add_sub_of_le hreserve
  rw [hside, ← hheight] at hlist
  rw [ConcretePakSide.encodedWord_length] at hlist
  have hsum :
      (hashes + extractedSlackNat x remaining) +
          PakSideScanner.scannerTerminalIndex x =
        (PakSideScanner.sideScannerBits x).length := by
    rw [hcanonical, ConcretePakSide.encodedWord_length]
    omega
  unfold scannerSlackCount
  exact Nat.eq_sub_of_add_eq hsum

/-! ## Local uniqueness tools for the reverse scanner classification -/

theorem scannerPath_internal_phase_mid {n : ℕ} (P : ScannerPath n)
    (k : ℕ) (hk0 : 0 < k) (hklast : k + 1 < n) :
    (P.states ⟨k, by omega⟩).phase = .mid := by
  let prev : Fin n := ⟨k - 1, by omega⟩
  let here : Fin n := ⟨k, by omega⟩
  have hprev := P.legal prev
  have hnext := P.legal here
  have hpredIndex : (prev.1 + 1 : ℕ) = k := by
    dsimp [prev]
    omega
  have hsuccIndex : (here.1 : ℕ) = k := rfl
  cases hphase : (P.states ⟨k, by omega⟩).phase with
  | bot =>
      have hbad := ConcretePakScanner.no_clause_to_bot
        (P.states ⟨k - 1, by omega⟩) (P.states ⟨k, by omega⟩)
        (n.testBit (k - 1)) hphase
      apply False.elim
      apply hbad
      simpa only [prev, hpredIndex] using hprev
  | mid => rfl
  | top =>
      exact (PakSlotOneSideValueReflection.ScannerPath.phase_ne_top_before_last
        P k hklast hphase).elim
  | cap =>
      have hbad := ConcretePakScanner.no_clause_from_cap
        (P.states ⟨k, by omega⟩) (P.states ⟨k + 1, by omega⟩)
        (n.testBit k) hphase
      apply False.elim
      apply hbad
      simpa only [here, hsuccIndex] using hnext

private theorem legalScan_mid_to_mid_nontail_mode
    (s t : ConcretePakScanner.State) (b : Bool)
    (hlegal : ConcretePakScanner.LegalScan s t b)
    (hs : s.phase = .mid) (ht : t.phase = .mid)
    (hnt : t.mode ≠ .tail) :
    s.mode = ConcretePakScanner.modeOut b t.mode := by
  rcases hlegal with ⟨clause, hclause⟩
  cases clause <;>
    simp [ConcretePakScanner.LegalClause, hs, ht] at hclause ⊢ <;>
    simp_all

private theorem legalScan_from_bottom_fields
    (t : ConcretePakScanner.State) (b : Bool)
    (hlegal : ConcretePakScanner.LegalScan
      PakCouplingGenerated.scannerBottom t b) :
    t.phase = .mid ∧ t.left = .hash ∧
      t.centre = ConcretePakScanner.headBuffer b ∧
      t.lookahead = .lh0 := by
  rcases hlegal with ⟨clause, hclause⟩
  cases clause <;>
    simp [ConcretePakScanner.LegalClause, ConcretePakScanner.Shift,
      PakCouplingGenerated.scannerBottom] at hclause ⊢ <;>
    simp_all

private theorem legalScan_mid_to_mid_nontail_target_fields
    (s t : ConcretePakScanner.State) (b : Bool)
    (hlegal : ConcretePakScanner.LegalScan s t b)
    (hs : s.phase = .mid) (ht : t.phase = .mid)
    (hnt : t.mode ≠ .tail) :
    t.left = s.centre ∧
      t.centre = ConcretePakScanner.newMid b t.mode ∧
      t.lookahead = .lh0 := by
  rcases hlegal with ⟨clause, hclause⟩
  cases clause <;>
    simp [ConcretePakScanner.LegalClause, ConcretePakScanner.Shift,
      hs, ht] at hclause ⊢ <;>
    simp_all

/-- Before a late terminator, one high-mode state fixes every preceding
scanner mode by the right-to-left modeOut recursion.  This is the formal
guard excluding the two-path ambiguity immediately after the last true bit. -/
theorem scannerPath_mode_eq_suffixMode_before_late_terminal
    {n : ℕ} (P : ScannerPath n) (bits : List Bool) (terminal : ℕ)
    (hsize : n = bits.length + 2)
    (hterminal0 : 0 < terminal)
    (hterminal : terminal < bits.length)
    (hbit : ∀ k < terminal, n.testBit k = bits.getD k false)
    (hmode : (P.states ⟨terminal, by omega⟩).mode = .high)
    (hsuffix : PakScannerPath.suffixMode bits terminal = .high) :
    ∀ (k : ℕ) (_hk0 : 0 < k) (_hkT : k ≤ terminal),
      (P.states ⟨k, by omega⟩).mode =
        PakScannerPath.suffixMode bits k := by
  intro k hk0 hkT
  refine (Nat.decreasingInduction' (n := terminal) (m := k)
    (P := fun i => ∀ (_hiT : i ≤ terminal) (_hi0 : 0 < i),
      (P.states ⟨i, by omega⟩).mode = PakScannerPath.suffixMode bits i)
    ?_ hkT ?_) hkT hk0
  · intro i hiT hiK ih hiBound hi0
    have hiBits : i + 1 < bits.length := by omega
    have hiN : i + 1 + 1 < n := by omega
    have hsource := scannerPath_internal_phase_mid P i hi0 (by omega)
    have htarget := scannerPath_internal_phase_mid P (i + 1) (by omega) hiN
    have hlegal := P.legal (⟨i, by omega⟩ : Fin n)
    have htargetMode :
        (P.states ⟨i + 1, by omega⟩).mode =
        PakScannerPath.suffixMode bits (i + 1) := ih (by omega) (by omega)
    have hnontail :
        (P.states ⟨i + 1, by omega⟩).mode ≠ .tail := by
      rw [htargetMode]
      exact PakScannerPath.suffixMode_ne_tail bits (i + 1)
    have hrec := legalScan_mid_to_mid_nontail_mode
      (P.states ⟨i, by omega⟩) (P.states ⟨i + 1, by omega⟩)
      (n.testBit i) (by simpa using hlegal) hsource htarget hnontail
    calc
      (P.states ⟨i, by omega⟩).mode =
          ConcretePakScanner.modeOut (n.testBit i)
            (P.states ⟨i + 1, by omega⟩).mode := hrec
      _ = ConcretePakScanner.modeOut (bits.getD i false)
            (PakScannerPath.suffixMode bits (i + 1)) := by
          rw [hbit i (by omega), htargetMode]
      _ = PakScannerPath.suffixMode bits i :=
          (PakScannerPath.suffixMode_step bits i).symm
  · intro _ _
    simpa [hmode, hsuffix]

private theorem scannerPath_prefix_state_eq
    {n : ℕ} (P : ScannerPath n) (bits : List Bool) (terminal : ℕ)
    (hsize : n = bits.length + 2)
    (hterminal0 : 0 < terminal)
    (hterminal : terminal < bits.length)
    (hbit : ∀ k < terminal, n.testBit k = bits.getD k false)
    (hmode : (P.states ⟨terminal, by omega⟩).mode = .high)
    (hsuffix : PakScannerPath.suffixMode bits terminal = .high) :
    ∀ (k : ℕ) (_hk0 : 0 < k) (_hkT : k ≤ terminal),
      P.states ⟨k, by omega⟩ = PakScannerPath.midState bits k := by
  have hallMode := scannerPath_mode_eq_suffixMode_before_late_terminal
    P bits terminal hsize hterminal0 hterminal hbit hmode hsuffix
  intro k
  induction k with
  | zero => intro hk0; omega
  | succ k ih =>
      intro _ hkT
      have htargetPhase := scannerPath_internal_phase_mid P (k + 1)
        (by omega) (by omega)
      have htargetMode := hallMode (k + 1) (by omega) hkT
      have hlegal := P.legal (⟨k, by omega⟩ : Fin n)
      by_cases hk : k = 0
      · subst k
        have hsource := P.bottom
        have hlegal' : ConcretePakScanner.LegalScan
            PakCouplingGenerated.scannerBottom (P.states ⟨1, by omega⟩)
            (n.testBit 0) := by
          rw [← hsource]
          simpa using hlegal
        have hf := legalScan_from_bottom_fields _ _ hlegal'
        have hb := hbit 0 (by omega)
        apply ConcretePakScanner.State.ext
        · exact hf.1
        · simpa [PakScannerPath.midState] using hf.2.1
        · rw [hf.2.2.1, hb]
          rfl
        · exact hf.2.2.2
        · exact htargetMode
      · have hkpos : 0 < k := by omega
        have hsourceEq := ih hkpos (by omega)
        have hsourcePhase := scannerPath_internal_phase_mid P k hkpos (by omega)
        have hnontail :
            (P.states ⟨k + 1, by omega⟩).mode ≠ .tail := by
          rw [htargetMode]
          exact PakScannerPath.suffixMode_ne_tail bits (k + 1)
        have hf := legalScan_mid_to_mid_nontail_target_fields
          (P.states ⟨k, by omega⟩) (P.states ⟨k + 1, by omega⟩)
          (n.testBit k) (by simpa using hlegal)
          hsourcePhase htargetPhase hnontail
        obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
        apply ConcretePakScanner.State.ext
        · exact htargetPhase
        · rw [hf.1, hsourceEq]
          rfl
        · rw [hf.2.1, hbit (l + 1) (by omega), htargetMode]
          rfl
        · exact hf.2.2
        · exact htargetMode

private theorem legalScan_terminal_target_fields
    (s t : ConcretePakScanner.State) (b : Bool)
    (hlegal : ConcretePakScanner.LegalScan s t b)
    (hsphase : s.phase = .mid) (hsmode : s.mode = .high)
    (htphase : t.phase = .mid) (htcentre : t.centre = .rightEnd) :
    b = false ∧ t.left = s.centre ∧ t.lookahead = .lh0 ∧ t.mode = .tail := by
  native_decide +revert

private theorem legalScan_tail_target_fields
    (s t : ConcretePakScanner.State) (b : Bool)
    (hlegal : ConcretePakScanner.LegalScan s t b)
    (hsphase : s.phase = .mid) (hsmode : s.mode = .tail)
    (htphase : t.phase = .mid) :
    b = false ∧ t.left = s.centre ∧ t.centre = .hash ∧
      t.lookahead = .lh0 ∧ t.mode = .tail := by
  native_decide +revert

private theorem scannerPath_tail_state_eq
    {n : ℕ} (P : ScannerPath n) (bits : List Bool) (terminal : ℕ)
    (hsize : n = bits.length + 2)
    (hterminal0 : 0 < terminal)
    (hterminal : terminal < bits.length)
    (hsource : P.states ⟨terminal, by omega⟩ =
      PakScannerPath.midState bits terminal)
    (hsourceMode : PakScannerPath.suffixMode bits terminal = .high)
    (hright : (P.states ⟨terminal + 1, by omega⟩).centre = .rightEnd) :
    ∀ (j : ℕ) (_hlo : terminal + 1 ≤ j) (_hhi : j ≤ bits.length),
      P.states ⟨j, by omega⟩ =
        PakScannerTerminal.terminalTailState bits terminal j := by
  intro j hlo hhi
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hlo
  induction d with
  | zero =>
      have htphase := scannerPath_internal_phase_mid P (terminal + 1)
        (by omega) (by omega)
      have hlegal := P.legal (⟨terminal, by omega⟩ : Fin n)
      have hlegal' : ConcretePakScanner.LegalScan
          (P.states ⟨terminal, by omega⟩)
          (P.states ⟨terminal + 1, by omega⟩)
          (n.testBit terminal) := by simpa using hlegal
      have hf := legalScan_terminal_target_fields
        (P.states ⟨terminal, by omega⟩)
        (P.states ⟨terminal + 1, by omega⟩) (n.testBit terminal)
        hlegal' (by simpa [hsource, PakScannerPath.midState])
        (by simpa [hsource, PakScannerPath.midState, hsourceMode])
        htphase hright
      apply ConcretePakScanner.State.ext
      · exact htphase
      · rw [hf.2.1, hsource]
        simp [PakScannerTerminal.terminalTailState,
          PakScannerPath.midState, PakScannerTerminal.terminalDataCell,
          hterminal0] <;> omega
      · simpa [PakScannerTerminal.terminalTailState,
          PakScannerTerminal.terminalDataCell] using hright
      · exact hf.2.2.1
      · exact hf.2.2.2
  | succ d ih =>
      have hprevHi : terminal + 1 + d ≤ bits.length := by omega
      have hprev := ih (by omega) hprevHi
      let j := terminal + 1 + d
      have hjgt : terminal < j := by dsimp [j]; omega
      have hj0 : j ≠ 0 := by omega
      have hjne : j ≠ terminal := by omega
      have hjnotlt : ¬ j < terminal := by omega
      have hprev' : P.states ⟨j, by omega⟩ =
          PakScannerTerminal.terminalTailState bits terminal j := by
        simpa [j] using hprev
      have htphase := scannerPath_internal_phase_mid P (j + 1)
        (by omega) (by omega)
      have hlegal := P.legal (⟨j, by omega⟩ : Fin n)
      have hlegal' : ConcretePakScanner.LegalScan
          (P.states ⟨j, by omega⟩) (P.states ⟨j + 1, by omega⟩)
          (n.testBit j) := by simpa using hlegal
      have hf := legalScan_tail_target_fields
        (P.states ⟨j, by omega⟩) (P.states ⟨j + 1, by omega⟩)
        (n.testBit j) hlegal'
        (by simpa [hprev', PakScannerTerminal.terminalTailState])
        (by simpa [hprev', PakScannerTerminal.terminalTailState])
        htphase
      have hresult : P.states ⟨j + 1, by omega⟩ =
          PakScannerTerminal.terminalTailState bits terminal (j + 1) := by
        apply ConcretePakScanner.State.ext
        · exact htphase
        · rw [hf.2.1, hprev']
          simp [PakScannerTerminal.terminalTailState,
            PakScannerTerminal.terminalDataCell, hj0, hjne, hjnotlt]
        · rw [hf.2.2.1]
          simp [PakScannerTerminal.terminalTailState,
            PakScannerTerminal.terminalDataCell, hjne, hjnotlt]
        · exact hf.2.2.2.1
        · exact hf.2.2.2.2
      simpa only [show terminal + 1 + (d + 1) = j + 1 by
        dsimp [j]
        omega] using hresult

private theorem legalScan_preTop_target_fields
    (s t : ConcretePakScanner.State) (b : Bool)
    (hlegal : ConcretePakScanner.LegalScan s t b)
    (hsphase : s.phase = .mid) (hsmode : s.mode = .tail)
    (htphase : t.phase = .top) :
    b = false ∧ t.left = s.centre ∧ t.centre = .hash ∧
      t.lookahead = .lh1 ∧ t.mode = .high := by
  native_decide +revert

private theorem scannerPath_top_state_eq
    {n : ℕ} (P : ScannerPath n) (bits : List Bool) (terminal : ℕ)
    (hsize : n = bits.length + 2)
    (hterminal : terminal < bits.length)
    (htail : P.states ⟨bits.length, by omega⟩ =
      PakScannerTerminal.terminalTailState bits terminal bits.length) :
    P.states ⟨bits.length + 1, by omega⟩ =
      PakScannerTerminal.terminalTopState bits terminal := by
  have hcap : P.states ⟨bits.length + 2, by omega⟩ =
      ConcretePakScanner.topNorth := by
    have htop := P.top
    simpa [hsize] using htop
  have hlastLegal := P.legal (⟨bits.length + 1, by omega⟩ : Fin n)
  have hlastLegal' : ConcretePakScanner.LegalScan
      (P.states ⟨bits.length + 1, by omega⟩)
      (P.states ⟨bits.length + 2, by omega⟩)
      (n.testBit (bits.length + 1)) := by simpa using hlastLegal
  have htopPhase : (P.states ⟨bits.length + 1, by omega⟩).phase = .top :=
    legalScan_to_cap_forces_source_top _ _ _ hlastLegal' (by
      rw [hcap]
      rfl)
  have hlegal := P.legal (⟨bits.length, by omega⟩ : Fin n)
  have hlegal' : ConcretePakScanner.LegalScan
      (P.states ⟨bits.length, by omega⟩)
      (P.states ⟨bits.length + 1, by omega⟩)
      (n.testBit bits.length) := by simpa using hlegal
  have hf := legalScan_preTop_target_fields
    (P.states ⟨bits.length, by omega⟩)
    (P.states ⟨bits.length + 1, by omega⟩)
    (n.testBit bits.length) hlegal'
    (by simpa [htail, PakScannerTerminal.terminalTailState])
    (by simpa [htail, PakScannerTerminal.terminalTailState])
    htopPhase
  apply ConcretePakScanner.State.ext
  · exact htopPhase
  · rw [hf.2.1, htail]
    rfl
  · exact hf.2.2.1
  · exact hf.2.2.2.1
  · exact hf.2.2.2.2

/-- Once the minimum terminator is passed, all actual side bits are high
zeros.  Moving the terminator through that interval therefore preserves the
scanner labels. -/
theorem slackedTerminalBit_eq_testBit (x : ConcretePakSide.Word)
    (s : ScannerSlack x)
    (j : Fin ((PakSideScanner.sideScannerBits x).length + 2)) :
    (if j.1 < slackTerminalIndex x s then
        PakScannerPath.scannerBit
          (PakSideScanner.sideScannerBits x) false false j
     else if j.1 = slackTerminalIndex x s then false
     else if j.1 < (PakSideScanner.sideScannerBits x).length then false
     else if j.1 = (PakSideScanner.sideScannerBits x).length then false
     else false) = (ConcretePakSide.sideValue x).testBit j.1 := by
  by_cases hj : j.1 < slackTerminalIndex x s
  · simp only [if_pos hj]
    exact PakSideScanner.sideScannerBit_eq_testBit x j
  · have hminimum : PakSideScanner.scannerTerminalIndex x ≤ j.1 := by
      unfold slackTerminalIndex at hj
      omega
    have hcanonical := PakSideScanner.sideScannerTerminalBit_eq_testBit x j
    have hnotCanonical : ¬ j.1 < PakSideScanner.scannerTerminalIndex x := by
      omega
    have hzero : (ConcretePakSide.sideValue x).testBit j.1 = false := by
      rw [← hcanonical]
      simp [hnotCanonical]
    simp [hj, hzero]

/-- The raw scanner path before transporting along
`sideScannerHeight`. -/
def rawSlackedScannerPath (x : ConcretePakSide.Word) (s : ScannerSlack x) :
    ScannerPath ((PakSideScanner.sideScannerBits x).length + 2) where
  pos := by omega
  states := fun k => PakScannerTerminal.terminalScannerState
    (PakSideScanner.sideScannerBits x) (PakSideScanner.sideScannerBits_pos x)
    (slackTerminalIndex x s) k.1
  bottom := by
    simp [PakScannerTerminal.terminalScannerState]
  top := by
    have ht := slackTerminalIndex_lt x s
    have hzero : (PakSideScanner.sideScannerBits x).length + 2 ≠ 0 := by omega
    have hterminal : ¬ (PakSideScanner.sideScannerBits x).length + 2 ≤
        slackTerminalIndex x s := by omega
    have hlength : ¬ (PakSideScanner.sideScannerBits x).length + 2 ≤
        (PakSideScanner.sideScannerBits x).length := by omega
    have htop : (PakSideScanner.sideScannerBits x).length + 2 ≠
        (PakSideScanner.sideScannerBits x).length + 1 := by omega
    simp [PakScannerTerminal.terminalScannerState, hzero, hterminal,
      hlength, htop]
  legal := by
    intro j
    rcases PakScannerTerminal.terminalScannerColumn_legal
        (PakSideScanner.sideScannerBits x)
        (PakSideScanner.sideScannerBits_pos x)
        (slackTerminalIndex x s) (slackTerminalIndex_pos x s)
        (slackTerminalIndex_lt x s) false j with
      ⟨south, north, hcolumn, hlegal⟩
    have hpair :
        (PakScannerTerminal.terminalScannerState
            (PakSideScanner.sideScannerBits x)
            (PakSideScanner.sideScannerBits_pos x)
            (slackTerminalIndex x s) j.1,
          PakScannerTerminal.terminalScannerState
            (PakSideScanner.sideScannerBits x)
            (PakSideScanner.sideScannerBits_pos x)
            (slackTerminalIndex x s) (j.1 + 1)) =
          (south, north) := by
      exact Option.some.inj (by
        simpa [PakScannerTerminal.terminalScannerColumn] using hcolumn)
    have hsouth :
        PakScannerTerminal.terminalScannerState
            (PakSideScanner.sideScannerBits x)
            (PakSideScanner.sideScannerBits_pos x)
            (slackTerminalIndex x s) j.1 = south := by
      simpa only using congrArg Prod.fst hpair
    have hnorth :
        PakScannerTerminal.terminalScannerState
            (PakSideScanner.sideScannerBits x)
            (PakSideScanner.sideScannerBits_pos x)
            (slackTerminalIndex x s) (j.1 + 1) = north := by
      simpa only using congrArg Prod.snd hpair
    rw [hsouth, hnorth]
    have hlabel := slackedTerminalBit_eq_testBit x s j
    rw [← PakSideScanner.sideScannerHeight x] at hlabel
    rw [← hlabel]
    exact hlegal

/-- The same path at the actual square side. -/
def slackedScannerPath (x : ConcretePakSide.Word) (s : ScannerSlack x) :
    ScannerPath (ConcretePakSide.sideValue x) :=
  Equiv.cast (congrArg ScannerPath (PakSideScanner.sideScannerHeight x))
    (rawSlackedScannerPath x s)

theorem dataCell_ne_rightEnd (bits : List Bool) (k : ℕ) :
    PakScannerPath.dataCell bits k ≠ ConcretePakScanner.Buffer.rightEnd := by
  cases k with
  | zero =>
      change ConcretePakScanner.headBuffer (bits.getD 0 false) ≠
        ConcretePakScanner.Buffer.rightEnd
      cases bits.getD 0 false <;> decide
  | succ k =>
      change ConcretePakScanner.newMid (bits.getD (k + 1) false)
          (PakScannerPath.suffixMode bits (k + 2)) ≠
        ConcretePakScanner.Buffer.rightEnd
      cases bits.getD (k + 1) false <;>
        cases PakScannerPath.suffixMode bits (k + 2) <;> decide

/-- The distinguished `rightEnd` centre recovers the slack parameter, so two
different allowed slacks cannot produce the same scanner state path. -/
private theorem rawSlackedScannerPath_ne_of_lt (x : ConcretePakSide.Word)
    (s t : ScannerSlack x) (hst : s.1 < t.1) :
    rawSlackedScannerPath x s ≠ rawSlackedScannerPath x t := by
  intro hpath
  let k := slackTerminalIndex x s + 1
  have hk : k < (PakSideScanner.sideScannerBits x).length + 2 + 1 := by
    have hs := slackTerminalIndex_lt x s
    omega
  have hstate := congrArg
    (fun P : ScannerPath ((PakSideScanner.sideScannerBits x).length + 2) =>
      (P.states ⟨k, hk⟩).centre) hpath
  have hterminal :
      ((rawSlackedScannerPath x s).states ⟨k, hk⟩).centre =
        ConcretePakScanner.Buffer.rightEnd := by
    have ht := slackTerminalIndex_lt x s
    have hk0 : k ≠ 0 := by unfold k; omega
    have hnotle : ¬ k ≤ slackTerminalIndex x s := by unfold k; omega
    have hkle : k ≤ (PakSideScanner.sideScannerBits x).length := by
      unfold k
      omega
    simp [rawSlackedScannerPath, k,
      PakScannerTerminal.terminalScannerState,
      PakScannerTerminal.terminalTailState,
      PakScannerTerminal.terminalDataCell, hk0, hnotle, hkle]
  have hbefore : slackTerminalIndex x s < slackTerminalIndex x t := by
    unfold slackTerminalIndex
    omega
  have hkBefore : k ≤ slackTerminalIndex x t := by
    unfold k
    omega
  have hdata :
      ((rawSlackedScannerPath x t).states ⟨k, hk⟩).centre =
        PakScannerPath.dataCell (PakSideScanner.sideScannerBits x)
          (slackTerminalIndex x s) := by
    have hk0 : k ≠ 0 := by unfold k; omega
    simp [rawSlackedScannerPath, k,
      PakScannerTerminal.terminalScannerState, hk0, hkBefore,
      PakScannerPath.midState]
  rw [hterminal, hdata] at hstate
  exact dataCell_ne_rightEnd _ _ hstate.symm

theorem rawSlackedScannerPath_injective (x : ConcretePakSide.Word) :
    Function.Injective (rawSlackedScannerPath x) := by
  intro s t hpath
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · exact rawSlackedScannerPath_ne_of_lt x s t hst hpath
  · exact rawSlackedScannerPath_ne_of_lt x t s hts hpath.symm

theorem slackedScannerPath_injective (x : ConcretePakSide.Word) :
    Function.Injective (slackedScannerPath x) := by
  exact (Equiv.cast
    (congrArg ScannerPath (PakSideScanner.sideScannerHeight x))).injective.comp
      (rawSlackedScannerPath_injective x)

abbrev CanonicalSlackScannerPaths (x : ConcretePakSide.Word) :=
  Set.range (slackedScannerPath x)

noncomputable def scannerSlackEquiv (x : ConcretePakSide.Word) :
    ScannerSlack x ≃ CanonicalSlackScannerPaths x :=
  Equiv.ofInjective (slackedScannerPath x) (slackedScannerPath_injective x)

noncomputable instance canonicalSlackScannerPathsFintype
    (x : ConcretePakSide.Word) : Fintype (CanonicalSlackScannerPaths x) :=
  Fintype.ofEquiv (ScannerSlack x) (scannerSlackEquiv x)

/-- The exact multiplicity of the canonical terminal-slack scanner family. -/
theorem card_canonicalSlackScannerPaths (x : ConcretePakSide.Word) :
    Fintype.card (CanonicalSlackScannerPaths x) = scannerSlackCount x := by
  rw [← Fintype.card_congr (scannerSlackEquiv x)]
  simp [ScannerSlack]

/-- Explicit candidate scanner multiplier for the slot-one coefficient. -/
def slotOneScannerMultiplicity (n : ℕ) (x : ConcretePakSide.Word) : ℕ :=
  if n = ConcretePakSide.sideValue x then scannerSlackCount x else 0

theorem slotOneScannerMultiplicity_at_sideValue (x : ConcretePakSide.Word) :
    slotOneScannerMultiplicity (ConcretePakSide.sideValue x) x =
      scannerSlackCount x := by
  simp [slotOneScannerMultiplicity]

/-! ## Correct capacity-indexed scanner family

The old parser/copier reserve is sufficient but not minimal.  Therefore the
complete scanner parameter is the actual number of work cells between the
fixed two-cell copy entry and rightEnd.
-/

def scannerCapacityCount (x : ConcretePakSide.Word) : ℕ :=
  (PakSideScanner.sideScannerBits x).length -
    ((ConcretePakSide.encodedWord x).length + 3)

abbrev ScannerCapacity (x : ConcretePakSide.Word) :=
  Fin (scannerCapacityCount x)

def capacityTerminalIndex (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) : ℕ :=
  (ConcretePakSide.encodedWord x).length + 3 + c.1

theorem scannerCapacityCount_pos (x : ConcretePakSide.Word) :
    0 < scannerCapacityCount x := by
  unfold scannerCapacityCount
  have h := PakSideScanner.parserCopierReserve_le_sideScannerBits_sub x
  have hp := PakSideScanner.parserCells_length x
  have hr := PakSideScannerRow.parserCopierReserve_length_shape x
  have he := ConcretePakSide.encodedWord_length x
  unfold PakSideScannerRow.parserCopierWorkCount at hr
  omega

theorem capacityTerminalIndex_pos (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) : 0 < capacityTerminalIndex x c := by
  unfold capacityTerminalIndex
  omega

theorem capacityTerminalIndex_lt (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) :
    capacityTerminalIndex x c <
      (PakSideScanner.sideScannerBits x).length := by
  have hc := c.2
  unfold ScannerCapacity scannerCapacityCount at hc
  unfold capacityTerminalIndex
  have hbase :
      (ConcretePakSide.encodedWord x).length + 3 <
        (PakSideScanner.sideScannerBits x).length := by
    have h := PakSideScanner.parserCopierReserve_le_sideScannerBits_sub x
    have hp := PakSideScanner.parserCells_length x
    have hr := PakSideScannerRow.parserCopierReserve_length_shape x
    have he := ConcretePakSide.encodedWord_length x
    unfold PakSideScannerRow.parserCopierWorkCount at hr
    omega
  omega

theorem capacityTerminalBit_eq_testBit (x : ConcretePakSide.Word)
    (c : ScannerCapacity x)
    (j : Fin ((PakSideScanner.sideScannerBits x).length + 2)) :
    (if j.1 < capacityTerminalIndex x c then
        PakScannerPath.scannerBit
          (PakSideScanner.sideScannerBits x) false false j
     else if j.1 = capacityTerminalIndex x c then false
     else if j.1 < (PakSideScanner.sideScannerBits x).length then false
     else if j.1 = (PakSideScanner.sideScannerBits x).length then false
     else false) = (ConcretePakSide.sideValue x).testBit j.1 := by
  by_cases hj : j.1 < capacityTerminalIndex x c
  · simp only [if_pos hj]
    exact PakSideScanner.sideScannerBit_eq_testBit x j
  · have hencoded : (ConcretePakSide.encodedWord x).length ≤ j.1 := by
      unfold capacityTerminalIndex at hj
      omega
    have hzero :=
      PakSlotOneSideValueReflection.sideValue_testBit_false_of_encoded_length_le
        x j.1 hencoded
    simp [hj, hzero]

def rawCapacityScannerPath (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) :
    ScannerPath ((PakSideScanner.sideScannerBits x).length + 2) where
  pos := by omega
  states := fun k => PakScannerTerminal.terminalScannerState
    (PakSideScanner.sideScannerBits x) (PakSideScanner.sideScannerBits_pos x)
    (capacityTerminalIndex x c) k.1
  bottom := by simp [PakScannerTerminal.terminalScannerState]
  top := by
    have ht := capacityTerminalIndex_lt x c
    have hzero : (PakSideScanner.sideScannerBits x).length + 2 ≠ 0 := by omega
    have hterminal : ¬ (PakSideScanner.sideScannerBits x).length + 2 ≤
        capacityTerminalIndex x c := by omega
    have hlength : ¬ (PakSideScanner.sideScannerBits x).length + 2 ≤
        (PakSideScanner.sideScannerBits x).length := by omega
    have htop : (PakSideScanner.sideScannerBits x).length + 2 ≠
        (PakSideScanner.sideScannerBits x).length + 1 := by omega
    simp [PakScannerTerminal.terminalScannerState, hzero, hterminal,
      hlength, htop]
  legal := by
    intro j
    rcases PakScannerTerminal.terminalScannerColumn_legal
        (PakSideScanner.sideScannerBits x)
        (PakSideScanner.sideScannerBits_pos x)
        (capacityTerminalIndex x c) (capacityTerminalIndex_pos x c)
        (capacityTerminalIndex_lt x c) false j with
      ⟨south, north, hcolumn, hlegal⟩
    have hpair :
        (PakScannerTerminal.terminalScannerState
            (PakSideScanner.sideScannerBits x)
            (PakSideScanner.sideScannerBits_pos x)
            (capacityTerminalIndex x c) j.1,
          PakScannerTerminal.terminalScannerState
            (PakSideScanner.sideScannerBits x)
            (PakSideScanner.sideScannerBits_pos x)
            (capacityTerminalIndex x c) (j.1 + 1)) =
          (south, north) := by
      exact Option.some.inj (by
        simpa [PakScannerTerminal.terminalScannerColumn] using hcolumn)
    have hsouth : PakScannerTerminal.terminalScannerState
          (PakSideScanner.sideScannerBits x)
          (PakSideScanner.sideScannerBits_pos x)
          (capacityTerminalIndex x c) j.1 = south := by
      simpa only using congrArg Prod.fst hpair
    have hnorth : PakScannerTerminal.terminalScannerState
          (PakSideScanner.sideScannerBits x)
          (PakSideScanner.sideScannerBits_pos x)
          (capacityTerminalIndex x c) (j.1 + 1) = north := by
      simpa only using congrArg Prod.snd hpair
    rw [hsouth, hnorth]
    have hlabel := capacityTerminalBit_eq_testBit x c j
    rw [← PakSideScanner.sideScannerHeight x] at hlabel
    rw [← hlabel]
    exact hlegal

def capacityScannerPath (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) : ScannerPath (ConcretePakSide.sideValue x) :=
  Equiv.cast (congrArg ScannerPath (PakSideScanner.sideScannerHeight x))
    (rawCapacityScannerPath x c)

private theorem scannerPath_eq_of_states {n : ℕ} (P Q : ScannerPath n)
    (h : P.states = Q.states) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- A scanner path with the physical terminal at the given capacity is
exactly the literal path constructed above.  The high-mode premise is the
precise guard excluding the last-true adjacent ambiguity. -/
theorem scannerPath_eq_rawCapacityScannerPath_of_terminal
    (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (P : ScannerPath ((PakSideScanner.sideScannerBits x).length + 2))
    (hmode : (P.states ⟨capacityTerminalIndex x c, by
      have := capacityTerminalIndex_lt x c
      omega⟩).mode = .high)
    (hright : (P.states ⟨capacityTerminalIndex x c + 1, by
      have := capacityTerminalIndex_lt x c
      omega⟩).centre = .rightEnd) :
    P = rawCapacityScannerPath x c := by
  let bits := PakSideScanner.sideScannerBits x
  let terminal := capacityTerminalIndex x c
  have hterminal0 : 0 < terminal := capacityTerminalIndex_pos x c
  have hterminal : terminal < bits.length := capacityTerminalIndex_lt x c
  have hbit : ∀ k < terminal,
      (bits.length + 2).testBit k = bits.getD k false := by
    intro k hk
    have hkBits : k < bits.length := hk.trans hterminal
    have hkSide : k < ConcretePakSide.sideValue x - 2 := by
      simpa [bits, PakSideScanner.sideScannerBits_length] using hkBits
    have hread := PakSideScanner.sideScannerBits_getD x k hkSide
    rw [PakSideScanner.sideScannerHeight x]
    exact hread.symm
  have hsuffix : PakScannerPath.suffixMode bits terminal = .high := by
    apply PakSideScannerRow.sideSuffixMode_high
    unfold terminal capacityTerminalIndex
    omega
  have hprefix := scannerPath_prefix_state_eq P bits terminal rfl
    hterminal0 hterminal hbit (by simpa [terminal] using hmode) hsuffix
  have hsource := hprefix terminal hterminal0 le_rfl
  have htail := scannerPath_tail_state_eq P bits terminal rfl hterminal0
    hterminal hsource hsuffix (by simpa [terminal] using hright)
  have hlastTail := htail bits.length (by omega) le_rfl
  have htop := scannerPath_top_state_eq P bits terminal rfl hterminal hlastTail
  apply scannerPath_eq_of_states
  funext k
  change P.states k =
    PakScannerTerminal.terminalScannerState
      (PakSideScanner.sideScannerBits x)
      (PakSideScanner.sideScannerBits_pos x)
      (capacityTerminalIndex x c) k.1
  have hkBound : k.1 < bits.length + 3 := by
    simpa [bits] using k.2
  by_cases hk0 : k.1 = 0
  · have hk : k = ⟨0, by omega⟩ := Fin.ext hk0
    rw [hk, P.bottom]
    simp [PakScannerTerminal.terminalScannerState]
  · by_cases hkPrefix : k.1 ≤ terminal
    · have hp := hprefix k.1 (by omega) hkPrefix
      rw [show PakScannerTerminal.terminalScannerState
          (PakSideScanner.sideScannerBits x)
          (PakSideScanner.sideScannerBits_pos x)
          (capacityTerminalIndex x c) k.1 =
          PakScannerPath.midState bits k.1 by
        simp [PakScannerTerminal.terminalScannerState, hk0, hkPrefix,
          bits, terminal]]
      simpa using hp
    · have hkAfter : terminal < k.1 := by omega
      by_cases hkTail : k.1 ≤ bits.length
      · have ht := htail k.1 (by omega) hkTail
        rw [show PakScannerTerminal.terminalScannerState
            (PakSideScanner.sideScannerBits x)
            (PakSideScanner.sideScannerBits_pos x)
            (capacityTerminalIndex x c) k.1 =
            PakScannerTerminal.terminalTailState bits terminal k.1 by
          simp [PakScannerTerminal.terminalScannerState, hk0, hkPrefix,
            hkTail, bits, terminal]]
        simpa using ht
      · have hkCases : k.1 = bits.length + 1 ∨
          k.1 = bits.length + 2 := by
          omega
        rcases hkCases with hkTop | hkCap
        · have hk : k = ⟨bits.length + 1, by omega⟩ := Fin.ext hkTop
          have hnot : ¬ bits.length < terminal := by omega
          rw [hk]
          simpa [PakScannerTerminal.terminalScannerState, hterminal,
            hnot, bits, terminal] using htop
        · have hk : k = ⟨bits.length + 2, by omega⟩ := Fin.ext hkCap
          have hnot : ¬ bits.length + 2 ≤ terminal := by omega
          rw [hk, P.top]
          simp [PakScannerTerminal.terminalScannerState, hterminal,
            hnot, bits, terminal]

theorem rawCapacityScannerPath_terminal_mode
    (x : ConcretePakSide.Word) (c : ScannerCapacity x) :
    ((rawCapacityScannerPath x c).states
      ⟨capacityTerminalIndex x c, by
        have := capacityTerminalIndex_lt x c
        omega⟩).mode = .high := by
  have hsuffix := PakSideScannerRow.sideSuffixMode_high x
    (capacityTerminalIndex x c) (by
      unfold capacityTerminalIndex
      omega)
  have hpos := capacityTerminalIndex_pos x c
  have hne : capacityTerminalIndex x c ≠ 0 := Nat.ne_of_gt hpos
  simp [rawCapacityScannerPath,
    PakScannerTerminal.terminalScannerState,
    PakScannerPath.midState, hne, hsuffix]

theorem rawCapacityScannerPath_terminal_rightEnd
    (x : ConcretePakSide.Word) (c : ScannerCapacity x) :
    ((rawCapacityScannerPath x c).states
      ⟨capacityTerminalIndex x c + 1, by
        have := capacityTerminalIndex_lt x c
        omega⟩).centre = .rightEnd := by
  have ht := capacityTerminalIndex_lt x c
  simp [rawCapacityScannerPath,
    PakScannerTerminal.terminalScannerState,
    PakScannerTerminal.terminalTailState,
    PakScannerTerminal.terminalDataCell, ht]

/-- The occurrence-labelled reverse scanner fibre.  Its two guards are read
from the same physical path; the equality theorem proves they contain no
extra path multiplicity. -/
structure CapacityTerminalScannerPath (x : ConcretePakSide.Word) where
  capacity : ScannerCapacity x
  path : ScannerPath ((PakSideScanner.sideScannerBits x).length + 2)
  terminal_mode :
    (path.states ⟨capacityTerminalIndex x capacity, by
      have := capacityTerminalIndex_lt x capacity
      omega⟩).mode = .high
  terminal_rightEnd :
    (path.states ⟨capacityTerminalIndex x capacity + 1, by
      have := capacityTerminalIndex_lt x capacity
      omega⟩).centre = .rightEnd

def capacityToTerminalScannerPath (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) : CapacityTerminalScannerPath x where
  capacity := c
  path := rawCapacityScannerPath x c
  terminal_mode := rawCapacityScannerPath_terminal_mode x c
  terminal_rightEnd := rawCapacityScannerPath_terminal_rightEnd x c

def terminalScannerPathToCapacity (x : ConcretePakSide.Word) :
    CapacityTerminalScannerPath x → ScannerCapacity x :=
  fun P => P.capacity

theorem CapacityTerminalScannerPath.path_eq_raw
    {x : ConcretePakSide.Word} (P : CapacityTerminalScannerPath x) :
    P.path = rawCapacityScannerPath x P.capacity :=
  scannerPath_eq_rawCapacityScannerPath_of_terminal x P.capacity P.path
    P.terminal_mode P.terminal_rightEnd

def scannerCapacityTerminalEquiv (x : ConcretePakSide.Word) :
    ScannerCapacity x ≃ CapacityTerminalScannerPath x where
  toFun := capacityToTerminalScannerPath x
  invFun := terminalScannerPathToCapacity x
  left_inv := by intro c; rfl
  right_inv := by
    intro P
    cases P with
    | mk capacity path hmode hright =>
        have hp : path = rawCapacityScannerPath x capacity :=
          scannerPath_eq_rawCapacityScannerPath_of_terminal x capacity path
            hmode hright
        subst path
        rfl

noncomputable instance capacityTerminalScannerPathFintype
    (x : ConcretePakSide.Word) : Fintype (CapacityTerminalScannerPath x) :=
  Fintype.ofEquiv (ScannerCapacity x) (scannerCapacityTerminalEquiv x)

theorem card_capacityTerminalScannerPath (x : ConcretePakSide.Word) :
    Fintype.card (CapacityTerminalScannerPath x) = scannerCapacityCount x := by
  rw [← Fintype.card_congr (scannerCapacityTerminalEquiv x)]
  simp [ScannerCapacity]

private theorem rawCapacityScannerPath_ne_of_lt (x : ConcretePakSide.Word)
    (c d : ScannerCapacity x) (hcd : c.1 < d.1) :
    rawCapacityScannerPath x c ≠ rawCapacityScannerPath x d := by
  intro hpath
  let k := capacityTerminalIndex x c + 1
  have hk : k < (PakSideScanner.sideScannerBits x).length + 2 + 1 := by
    have hc := capacityTerminalIndex_lt x c
    omega
  have hstate := congrArg
    (fun P : ScannerPath ((PakSideScanner.sideScannerBits x).length + 2) =>
      (P.states ⟨k, hk⟩).centre) hpath
  have hterminal :
      ((rawCapacityScannerPath x c).states ⟨k, hk⟩).centre =
        ConcretePakScanner.Buffer.rightEnd := by
    have ht := capacityTerminalIndex_lt x c
    have hnotle : ¬ k ≤ capacityTerminalIndex x c := by unfold k; omega
    have hkle : k ≤ (PakSideScanner.sideScannerBits x).length := by
      unfold k
      omega
    simp [rawCapacityScannerPath, k,
      PakScannerTerminal.terminalScannerState,
      PakScannerTerminal.terminalTailState,
      PakScannerTerminal.terminalDataCell, hnotle, hkle]
  have hbefore : capacityTerminalIndex x c < capacityTerminalIndex x d := by
    unfold capacityTerminalIndex
    omega
  have hkBefore : k ≤ capacityTerminalIndex x d := by unfold k; omega
  have hdata :
      ((rawCapacityScannerPath x d).states ⟨k, hk⟩).centre =
        PakScannerPath.dataCell (PakSideScanner.sideScannerBits x)
          (capacityTerminalIndex x c) := by
    simp [rawCapacityScannerPath, k,
      PakScannerTerminal.terminalScannerState, hkBefore,
      PakScannerPath.midState]
  rw [hterminal, hdata] at hstate
  exact dataCell_ne_rightEnd _ _ hstate.symm

theorem rawCapacityScannerPath_injective (x : ConcretePakSide.Word) :
    Function.Injective (rawCapacityScannerPath x) := by
  intro c d hpath
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hcd | hdc
  · exact rawCapacityScannerPath_ne_of_lt x c d hcd hpath
  · exact rawCapacityScannerPath_ne_of_lt x d c hdc hpath.symm

theorem capacityScannerPath_injective (x : ConcretePakSide.Word) :
    Function.Injective (capacityScannerPath x) :=
  (Equiv.cast
    (congrArg ScannerPath (PakSideScanner.sideScannerHeight x))).injective.comp
      (rawCapacityScannerPath_injective x)

abbrev AllCapacityScannerPaths (x : ConcretePakSide.Word) :=
  Set.range (capacityScannerPath x)

noncomputable def scannerCapacityEquiv (x : ConcretePakSide.Word) :
    ScannerCapacity x ≃ AllCapacityScannerPaths x :=
  Equiv.ofInjective (capacityScannerPath x) (capacityScannerPath_injective x)

noncomputable instance allCapacityScannerPathsFintype
    (x : ConcretePakSide.Word) : Fintype (AllCapacityScannerPaths x) :=
  Fintype.ofEquiv (ScannerCapacity x) (scannerCapacityEquiv x)

theorem card_allCapacityScannerPaths (x : ConcretePakSide.Word) :
    Fintype.card (AllCapacityScannerPaths x) = scannerCapacityCount x := by
  rw [← Fintype.card_congr (scannerCapacityEquiv x)]
  simp [ScannerCapacity]

/-! ## Honest sum-over-capacities interface -/

/-- Sum the raw accepting contribution over every capacity at or above a
proved minimum.  The offset presentation is executable and avoids a hidden
claim that all capacities have the same accepting language. -/
def capacityWeightedCount (x : ConcretePakSide.Word) (minConsumed : ℕ)
    (rawCount : ℕ → ℕ) : ℕ :=
  ∑ d ∈ Finset.range (scannerCapacityCount x - minConsumed),
    rawCount (minConsumed + d)

theorem capacityWeightedCount_eq_mul_of_stable
    (x : ConcretePakSide.Word) (minConsumed common : ℕ)
    (rawCount : ℕ → ℕ)
    (hstable : ∀ c, minConsumed ≤ c →
      c < scannerCapacityCount x → rawCount c = common) :
    capacityWeightedCount x minConsumed rawCount =
      (scannerCapacityCount x - minConsumed) * common := by
  unfold capacityWeightedCount
  calc
    (∑ d ∈ Finset.range (scannerCapacityCount x - minConsumed),
        rawCount (minConsumed + d)) =
        ∑ _d ∈ Finset.range (scannerCapacityCount x - minConsumed), common := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mem_range] at hd
      rw [hstable (minConsumed + d) (by omega) (by omega)]
    _ = (scannerCapacityCount x - minConsumed) * common := by
      simp

/-- Splitting at a semantic stabilization threshold records the only honest
general alternative to a single multiplicative factor: finitely many small
capacity corrections plus a constant tail. -/
theorem capacityWeightedCount_split_stable_tail
    (x : ConcretePakSide.Word) (minConsumed stableAt common : ℕ)
    (rawCount : ℕ → ℕ)
    (hmin : minConsumed ≤ stableAt)
    (hbound : stableAt ≤ scannerCapacityCount x)
    (hstable : ∀ c, stableAt ≤ c →
      c < scannerCapacityCount x → rawCount c = common) :
    capacityWeightedCount x minConsumed rawCount =
      (∑ d ∈ Finset.range (stableAt - minConsumed),
          rawCount (minConsumed + d)) +
        (scannerCapacityCount x - stableAt) * common := by
  unfold capacityWeightedCount
  have hsplit : scannerCapacityCount x - minConsumed =
      (stableAt - minConsumed) +
        (scannerCapacityCount x - stableAt) := by omega
  rw [hsplit, Finset.sum_range_add]
  congr 1
  calc
    (∑ x_1 ∈ Finset.range (scannerCapacityCount x - stableAt),
        rawCount (minConsumed + ((stableAt - minConsumed) + x_1))) =
        ∑ _d ∈ Finset.range (scannerCapacityCount x - stableAt), common := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mem_range] at hd
      rw [hstable (minConsumed + ((stableAt - minConsumed) + d))
        (by omega) (by omega)]
    _ = (scannerCapacityCount x - stableAt) * common := by simp

end PakFixedPolyomino.PakSlotOneScannerMultiplicity
