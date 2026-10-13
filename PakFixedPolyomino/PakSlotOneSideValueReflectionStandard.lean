import PakFixedPolyomino.PakSlotOneCopierOriginBarrierStandard
import PakFixedPolyomino.PakSlotOneSideIdentificationStandard
import PakFixedPolyomino.PakSlotOneSideValueReflection

/-! # Slot-one side-value reflection

This file starts after the parser/copying converse has proved that the
optional physical `rightEnd` is genuinely present.  It packages the exact
scanner word and its terminal coordinate for the subsequent ripple-bit
identification.
-/

namespace PakFixedPolyomino.PakSlotOneSideValueReflectionStandard

open MStarConcreteAlphabet MStarOuterProgram MStarParserExecution
open MStarCopierMicrocode

open PakSlotOneSideValueReflection

/-- The complete time-one scanner word has one actual terminator.  This is a
zero-parameter consequence of a slot-one full frame, not an added terminal
premise. -/
theorem slotOne_cells_terminal_shape {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    ∃ x : ConcretePakSide.Word, ∃ remaining : List CoreTape, ∃ hashes : ℕ,
      (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        inputCells zero one work (ConcretePakSide.encodedWord x) ++
          [Tape.core work, Tape.core work] ++
          remaining.map Tape.core ++ [rightEnd] ++
          List.replicate hashes Tape.hash := by
  rcases PakSlotOneCopierOriginBarrierStandard.slotOne_hasRightEnd F with
    ⟨x, rawTail, source, external, remaining, hashes, fuel, out,
      hprefix, hexternal, htail, hsource, hrun⟩
  refine ⟨x, remaining, hashes, ?_⟩
  rw [hprefix, htail, hexternal]
  simp [MStarParserOrderedLength.OrderedScannerTail, List.append_assoc,
    rightEnd]

/-- The terminal coordinate is strictly inside the trimmed scanner word. -/
theorem terminalIndex_lt {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word) (remaining : List CoreTape) (hashes : ℕ)
    (hshape : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        inputCells zero one work (ConcretePakSide.encodedWord x) ++
          [Tape.core work, Tape.core work] ++
          remaining.map Tape.core ++ [rightEnd] ++
          List.replicate hashes Tape.hash) :
    terminalIndex x remaining < n - 1 := by
  have hlen := congrArg List.length hshape
  have hwindow :
      ((PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right).length = n - 1 := by
    rw [PakScannerRawShapeStandard.slotOneTrimmedZipper_cells_eq_scannerBufferPrefix F]
    rw [PakScannerRawShape.scannerBufferPrefix_eq_ofFn]
    simp
  rw [hwindow] at hlen
  simp [inputCells] at hlen
  unfold terminalIndex
  rw [ConcretePakSide.encodedWord_length]
  omega

/-- Reading the recovered terminal coordinate from the actual time-one word
returns the concrete copier terminator. -/
theorem getD_terminalIndex {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word) (remaining : List CoreTape) (hashes : ℕ)
    (hshape : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        inputCells zero one work (ConcretePakSide.encodedWord x) ++
          [Tape.core work, Tape.core work] ++
          remaining.map Tape.core ++ [rightEnd] ++
          List.replicate hashes Tape.hash) :
    ((PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
      (PakSlotOneParserDecode.slotOneTrimmedZipper F).right).getD
        (terminalIndex x remaining) (Tape.core zero) = rightEnd := by
  rw [hshape]
  let pre := inputCells zero one work (ConcretePakSide.encodedWord x) ++
    [Tape.core work, Tape.core work] ++ remaining.map Tape.core
  have hpre : pre.length = terminalIndex x remaining := by
    simp [pre, terminalIndex, inputCells]
    omega
  have hdecomp :
      inputCells zero one work (ConcretePakSide.encodedWord x) ++
          [Tape.core work, Tape.core work] ++ remaining.map Tape.core ++
          [rightEnd] ++ List.replicate hashes Tape.hash =
        pre ++ rightEnd :: List.replicate hashes Tape.hash := by
    simp [pre, List.append_assoc]
  rw [hdecomp]
  change (pre ++ rightEnd :: List.replicate hashes Tape.hash).getD
    (terminalIndex x remaining) (Tape.core zero) = rightEnd
  rw [List.getD_append_right]
  · simp [hpre]
  · omega

/-- Every cell after the encoded bits and strictly before the recovered
terminator is an ordinary core letter. -/
theorem getD_before_terminal_core {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word) (remaining : List CoreTape) (hashes k : ℕ)
    (hshape : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        inputCells zero one work (ConcretePakSide.encodedWord x) ++
          [Tape.core work, Tape.core work] ++
          remaining.map Tape.core ++ [rightEnd] ++
          List.replicate hashes Tape.hash)
    (hlow : (ConcretePakSide.encodedWord x).length ≤ k)
    (hhigh : k < terminalIndex x remaining) :
    ∃ a : CoreTape,
      ((PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right).getD k
          (Tape.core zero) = Tape.core a := by
  have hshape' :
      (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        encodedBitCells x ++ (postEncodedCore remaining).map Tape.core ++
          rightEnd :: List.replicate hashes Tape.hash := by
    rw [hshape]
    simp [encodedBitCells, postEncodedCore, inputCells, List.map_append,
      List.append_assoc]
  have hshape'' :
      (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        encodedBitCells x ++
          ((postEncodedCore remaining).map Tape.core ++
            rightEnd :: List.replicate hashes Tape.hash) := by
    simpa [List.append_assoc] using hshape'
  rw [hshape'']
  have hbitsLen : (encodedBitCells x).length =
      (ConcretePakSide.encodedWord x).length := by
    simp [encodedBitCells]
  rw [List.getD_append_right]
  · have hrel : k - (encodedBitCells x).length <
        ((postEncodedCore remaining).map Tape.core).length := by
      simp [postEncodedCore, terminalIndex, hbitsLen] at hhigh ⊢
      omega
    rw [List.getD_append _ _ _ _ hrel]
    let i : Fin (postEncodedCore remaining).length :=
      ⟨k - (encodedBitCells x).length, by simpa using hrel⟩
    refine ⟨(postEncodedCore remaining).get i, ?_⟩
    rw [List.getD_eq_get _ _
      ⟨k - (encodedBitCells x).length, hrel⟩]
    simp [i]
  · simpa [hbitsLen] using hlow

/-- At the recovered terminal coordinate the ripple bit is false and the
scanner enters its literal mid/tail state. -/
theorem terminal_edge_false_and_tail {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word) (remaining : List CoreTape) (hashes : ℕ)
    (hshape : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        inputCells zero one work (ConcretePakSide.encodedWord x) ++
          [Tape.core work, Tape.core work] ++
          remaining.map Tape.core ++ [rightEnd] ++
          List.replicate hashes Tape.hash) :
    n.testBit (terminalIndex x remaining) = false ∧
      let t := (PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1).states
        ⟨terminalIndex x remaining + 1, by
          have hlt := terminalIndex_lt F x remaining hashes hshape
          omega⟩
      t.phase = .mid ∧ t.mode = .tail := by
  let k := terminalIndex x remaining
  have hk := terminalIndex_lt F x remaining hashes hshape
  let P := PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1
  have hletter : PakScannerRawShape.scannerTapeLetter
      (P.states ⟨k + 1, by omega⟩).centre = rightEnd := by
    rw [← PakSlotOneSideIdentificationStandard.slotOneTrimmedZipper_getD_eq_scannerTapeLetter
      F k hk]
    exact getD_terminalIndex F x remaining hashes hshape
  have hcentre : (P.states ⟨k + 1, by omega⟩).centre =
      ConcretePakScanner.Buffer.rightEnd :=
    (PakSlotOneSideIdentification.scannerTapeLetter_rightEnd_iff _).mp hletter
  have hlegal := P.legal (⟨k, by omega⟩ : Fin n)
  rcases PakSlotOneSideIdentification.legalScan_to_rightEnd
      (P.states ⟨k, by omega⟩) (P.states ⟨k + 1, by omega⟩)
      (n.testBit k) (by simpa using hlegal) hcentre with
    ⟨hbit, _, hphase, hmode⟩
  exact ⟨by simpa [k] using hbit, by simpa [P, k] using And.intro hphase hmode⟩

/-- All ripple bits from the parser's work delimiter up to (but excluding)
the recovered terminator are zero; throughout this interval the scanner stays
in the high mid-mode. -/
theorem core_interval_false_midHigh {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word) (remaining : List CoreTape) (hashes : ℕ)
    (hshape : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        inputCells zero one work (ConcretePakSide.encodedWord x) ++
          [Tape.core work, Tape.core work] ++
          remaining.map Tape.core ++ [rightEnd] ++
          List.replicate hashes Tape.hash) :
    ∀ (d : ℕ)
      (hbound : (ConcretePakSide.encodedWord x).length + d <
        terminalIndex x remaining),
      n.testBit ((ConcretePakSide.encodedWord x).length + d) = false ∧
        let s :=
          (PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1).states
            ⟨(ConcretePakSide.encodedWord x).length + d + 1, by
              have ht := terminalIndex_lt F x remaining hashes hshape
              have := hbound
              omega⟩
        s.phase = .mid ∧ s.mode = .high := by
  let L := (ConcretePakSide.encodedWord x).length
  let P := PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1
  have hprefix :
      (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        inputCells zero one work (ConcretePakSide.encodedWord x) ++
          ([Tape.core work, Tape.core work] ++ remaining.map Tape.core ++
            [rightEnd] ++ List.replicate hashes Tape.hash) := by
    simpa [List.append_assoc] using hshape
  have hbase := PakSlotOneSideIdentificationStandard.slotOne_workDelimiter_enters_midHigh
    F x _ hprefix
  intro d
  induction d with
  | zero =>
      intro _
      exact ⟨by simpa [L] using hbase.1,
        by simpa [P, L] using hbase.2⟩
  | succ d ih =>
      intro hbound
      have hprev := ih (by omega)
      let k := L + d + 1
      have ht := terminalIndex_lt F x remaining hashes hshape
      have hkWindow : k < n - 1 := by omega
      rcases getD_before_terminal_core F x remaining hashes k hshape
          (by simp [k, L]; omega)
          (by simpa [k, L, Nat.add_assoc] using hbound) with
        ⟨a, hcell⟩
      have hletter : PakScannerRawShape.scannerTapeLetter
          (P.states ⟨k + 1, by omega⟩).centre = Tape.core a := by
        calc
          _ = ((PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
              (PakSlotOneParserDecode.slotOneTrimmedZipper F).right).getD k
                (Tape.core zero) :=
            (PakSlotOneSideIdentificationStandard.slotOneTrimmedZipper_getD_eq_scannerTapeLetter
              F k hkWindow).symm
          _ = Tape.core a := hcell
      have hstage :=
        PakSlotOneSideIdentification.scannerTapeLetter_core_forces_stage_core
          _ a hletter
      have hlegal := P.legal (⟨k, by omega⟩ : Fin n)
      have hsource : (P.states ⟨k, by omega⟩).phase = .mid ∧
          (P.states ⟨k, by omega⟩).mode = .high := by
        simpa [k, L, Nat.add_assoc] using hprev.2
      rcases PakSlotOneSideIdentification.legalScan_midHigh_to_core
          (P.states ⟨k, by omega⟩) (P.states ⟨k + 1, by omega⟩)
          (n.testBit k) hsource.1 hsource.2 (by simpa using hlegal) hstage with
        ⟨hbit, hphase, hmode, _⟩
      exact ⟨by simpa [k, L, Nat.add_assoc] using hbit,
        by simpa [P, k, L, Nat.add_assoc] using And.intro hphase hmode⟩

theorem legalScan_from_top_phase_cap
    (s t : ConcretePakScanner.State) (b : Bool)
    (hphase : s.phase = .top)
    (hlegal : ConcretePakScanner.LegalScan s t b) :
    t.phase = .cap := by
  rcases hlegal with ⟨clause, hclause⟩
  cases clause <;>
    simp [ConcretePakScanner.LegalClause, hphase] at hclause ⊢ <;>
    simp_all

/-- A top scanner state can occur only at the penultimate path state: its
successor is cap, which has no outgoing legal edge. -/
theorem ScannerPath.phase_ne_top_before_last {n : ℕ}
    (P : PakScannerBaselineAutomaton.ScannerPath n) (j : ℕ)
    (hj : j + 1 < n) : (P.states ⟨j, by omega⟩).phase ≠ .top := by
  intro htop
  have hlegal₀ := P.legal (⟨j, by omega⟩ : Fin n)
  have hcap : (P.states ⟨j + 1, by omega⟩).phase = .cap :=
    legalScan_from_top_phase_cap
      (P.states ⟨j, by omega⟩) (P.states ⟨j + 1, by omega⟩)
      (n.testBit j) htop (by simpa using hlegal₀)
  have hlegal₁ := P.legal (⟨j + 1, by omega⟩ : Fin n)
  exact PakScannerKernelTerminalFacts.no_clause_from_cap
    (P.states ⟨j + 1, by omega⟩) (P.states ⟨j + 2, by omega⟩)
    (n.testBit (j + 1)) hcap (by simpa using hlegal₁)

/-- From the recovered terminator through every remaining interior edge, all
ripple bits are false.  The successor state is either still mid/tail or the
single penultimate top state. -/
theorem tail_interval_false {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word) (remaining : List CoreTape) (hashes : ℕ)
    (hshape : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        inputCells zero one work (ConcretePakSide.encodedWord x) ++
          [Tape.core work, Tape.core work] ++
          remaining.map Tape.core ++ [rightEnd] ++
          List.replicate hashes Tape.hash) :
    ∀ (d : ℕ) (hbound : terminalIndex x remaining + d < n - 1),
      n.testBit (terminalIndex x remaining + d) = false ∧
        let s :=
          (PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1).states
            ⟨terminalIndex x remaining + d + 1, by omega⟩
        (s.phase = .mid ∧ s.mode = .tail) ∨ s.phase = .top := by
  let T := terminalIndex x remaining
  let P := PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1
  have hterminal := terminal_edge_false_and_tail F x remaining hashes hshape
  intro d
  induction d with
  | zero =>
      intro _
      exact ⟨by simpa [T] using hterminal.1,
        Or.inl (by simpa [P, T] using hterminal.2)⟩
  | succ d ih =>
      intro hbound
      have hprev := ih (by omega)
      let k := T + d + 1
      have hsource : (P.states ⟨k, by omega⟩).phase = .mid ∧
          (P.states ⟨k, by omega⟩).mode = .tail := by
        rcases hprev.2 with htail | htop
        · simpa [k, T, Nat.add_assoc] using htail
        · have hne := ScannerPath.phase_ne_top_before_last P k (by omega)
          exact (hne (by simpa [k, T, Nat.add_assoc] using htop)).elim
      have hlegal := P.legal (⟨k, by omega⟩ : Fin n)
      rcases PakSlotOneSideIdentification.legalScan_from_midTail
          (P.states ⟨k, by omega⟩) (P.states ⟨k + 1, by omega⟩)
          (n.testBit k) hsource.1 hsource.2 (by simpa using hlegal) with
        ⟨hbit, hnext⟩
      refine ⟨by simpa [k, T, Nat.add_assoc] using hbit, ?_⟩
      rcases hnext with htail | htop
      · exact Or.inl (by
          simpa [P, k, T, Nat.add_assoc] using And.intro htail.1 htail.2.1)
      · exact Or.inr (by simpa [P, k, T, Nat.add_assoc] using htop)

theorem sideValue_testBit_false_of_encoded_length_le
    (x : ConcretePakSide.Word) (k : ℕ)
    (hk : (ConcretePakSide.encodedWord x).length ≤ k) :
    (ConcretePakSide.sideValue x).testBit k = false := by
  rw [PakSideRipple.sideValue_testBit]
  unfold PakSideRipple.sideDigit ConcretePakSide.littleDigits
  change decide ((((ConcretePakSide.encodedWord x).reverse.map Bool.toNat).getD
    k (Bool.toNat false)) = 1) = false
  rw [List.getD_map]
  have hword : (ConcretePakSide.encodedWord x).reverse.getD k false = false := by
    apply List.getD_eq_default
    simpa only [List.length_reverse] using hk
  rw [hword]
  rfl

/-- The actual side length and the encoded side value have identical binary
digits. -/
theorem testBit_eq_sideValue {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (x : ConcretePakSide.Word) (remaining : List CoreTape) (hashes k : ℕ)
    (hshape : (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
          (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
        inputCells zero one work (ConcretePakSide.encodedWord x) ++
          [Tape.core work, Tape.core work] ++
          remaining.map Tape.core ++ [rightEnd] ++
          List.replicate hashes Tape.hash) :
    n.testBit k = (ConcretePakSide.sideValue x).testBit k := by
  by_cases hlow : k < (ConcretePakSide.encodedWord x).length
  · have hprefix :
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
            (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
          inputCells zero one work (ConcretePakSide.encodedWord x) ++
            ([Tape.core work, Tape.core work] ++ remaining.map Tape.core ++
              [rightEnd] ++ List.replicate hashes Tape.hash) := by
      simpa [List.append_assoc] using hshape
    exact PakSlotOneSideIdentificationStandard.slotOne_testBit_eq_sideValue_of_lt_encodedWord
      F x _ hprefix k hlow
  · have hencLe : (ConcretePakSide.encodedWord x).length ≤ k :=
      Nat.le_of_not_gt hlow
    have hside := sideValue_testBit_false_of_encoded_length_le x k hencLe
    rw [hside]
    have ht := terminalIndex_lt F x remaining hashes hshape
    have hnFive : 5 ≤ n := by
      unfold terminalIndex at ht
      rw [ConcretePakSide.encodedWord_length] at ht
      omega
    by_cases hkN : k < n
    · by_cases hkInterior : k < n - 1
      · by_cases hkTerminal : k < terminalIndex x remaining
        · let d := k - (ConcretePakSide.encodedWord x).length
          have hsum : (ConcretePakSide.encodedWord x).length + d = k :=
            Nat.add_sub_of_le hencLe
          have hcore := core_interval_false_midHigh F x remaining hashes hshape
            d (by omega)
          rw [← hsum]
          exact hcore.1
        · have htermLe : terminalIndex x remaining ≤ k :=
            Nat.le_of_not_gt hkTerminal
          let d := k - terminalIndex x remaining
          have hsum : terminalIndex x remaining + d = k :=
            Nat.add_sub_of_le htermLe
          have htail := tail_interval_false F x remaining hashes hshape d (by
            omega)
          rw [← hsum]
          exact htail.1
      · have hkEq : k = n - 1 := by omega
        rw [hkEq]
        exact ConcretePakSide.omitted_bit_sub_one hnFive
    · have hnle : n ≤ k := Nat.le_of_not_gt hkN
      apply Nat.testBit_eq_false_of_lt
      exact n.lt_two_pow_self.trans_le
        (Nat.pow_le_pow_right (by decide) hnle)

/-- Every slot-one full frame recovers a word whose encoded side value is the
actual square side. -/
theorem slotOne_prefix_forces_sideValue {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    ∃ x : ConcretePakSide.Word, n = ConcretePakSide.sideValue x := by
  rcases slotOne_cells_terminal_shape F with ⟨x, remaining, hashes, hshape⟩
  refine ⟨x, Nat.eq_of_testBit_eq ?_⟩
  intro k
  exact testBit_eq_sideValue F x remaining hashes k hshape

end PakFixedPolyomino.PakSlotOneSideValueReflectionStandard
