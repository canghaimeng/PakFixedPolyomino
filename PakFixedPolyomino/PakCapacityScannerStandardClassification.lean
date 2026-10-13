import PakFixedPolyomino.PakSlotOneScannerMultiplicity
import PakFixedPolyomino.PakScannerKernelTerminalFacts
import PakFixedPolyomino.PakScannerKernelTransitionFields

/-! Kernel-only reverse classification at an actual terminal. The ALL
scanner path is unchanged. The high-mode and rightEnd facts are explicit
local hypotheses, to be extracted separately from physical full frames. -/
namespace PakFixedPolyomino.PakCapacityScannerStandardClassification
open ConcretePakScanner PakScannerBaselineAutomaton
open PakSlotOneScannerMultiplicity

theorem ScannerPath.phase_ne_top_before_last {n : ℕ}
    (P : ScannerPath n) (j : ℕ) (hj : j + 1 < n) :
    (P.states ⟨j, by omega⟩).phase ≠ .top := by
  intro htop
  have hlegal₀ := P.legal (⟨j, by omega⟩ : Fin n)
  have hcap : (P.states ⟨j + 1, by omega⟩).phase = .cap :=
    PakSlotOneSideValueReflection.legalScan_from_top_phase_cap _ _ _ htop
      (by simpa using hlegal₀)
  have hlegal₁ := P.legal (⟨j + 1, by omega⟩ : Fin n)
  exact PakScannerKernelTerminalFacts.no_clause_from_cap _ _ _ hcap
    (by simpa using hlegal₁)

private theorem scannerPath_eq_of_states {n : ℕ} (P Q : ScannerPath n)
    (h : P.states = Q.states) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

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
      have hbad := PakScannerKernelTerminalFacts.no_clause_to_bot
        (P.states ⟨k - 1, by omega⟩) (P.states ⟨k, by omega⟩)
        (n.testBit (k - 1)) hphase
      apply False.elim
      apply hbad
      simpa only [prev, hpredIndex] using hprev
  | mid => rfl
  | top =>
      exact (ScannerPath.phase_ne_top_before_last
        P k hklast hphase).elim
  | cap =>
      have hbad := PakScannerKernelTerminalFacts.no_clause_from_cap
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
  exact PakScannerKernelTransitionFields.legalScan_terminal_target_fields s t b hlegal hsphase hsmode htphase htcentre

private theorem legalScan_tail_target_fields
    (s t : ConcretePakScanner.State) (b : Bool)
    (hlegal : ConcretePakScanner.LegalScan s t b)
    (hsphase : s.phase = .mid) (hsmode : s.mode = .tail)
    (htphase : t.phase = .mid) :
    b = false ∧ t.left = s.centre ∧ t.centre = .hash ∧
      t.lookahead = .lh0 ∧ t.mode = .tail := by
  exact PakScannerKernelTransitionFields.legalScan_tail_target_fields s t b hlegal hsphase hsmode htphase

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
  exact PakScannerKernelTransitionFields.legalScan_preTop_target_fields s t b hlegal hsphase hsmode htphase

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
    (PakScannerKernelTerminalFacts.legal_to_cap_is_top hlastLegal' (by
      rw [hcap]
      rfl)).2.1
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

end PakFixedPolyomino.PakCapacityScannerStandardClassification
