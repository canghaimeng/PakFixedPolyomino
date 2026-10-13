import PakFixedPolyomino.PakScannerBaselineAutomaton

/-! Structural kernel proofs for literal scanner transition fields. These
replace finite compiler-trust facts in the reverse terminal classification,
without changing the scanner's six clauses or any actual labelled path. -/
namespace PakFixedPolyomino.PakScannerKernelTransitionFields
open ConcretePakScanner

theorem legalScan_terminal_target_fields
    (s t : State) (b : Bool) (hlegal : LegalScan s t b)
    (hsphase : s.phase = .mid) (hsmode : s.mode = .high)
    (htphase : t.phase = .mid) (htcentre : t.centre = .rightEnd) :
    b = false ∧ t.left = s.centre ∧ t.lookahead = .lh0 ∧ t.mode = .tail := by
  rcases hlegal with ⟨clause, hc⟩
  rcases t with ⟨tp, tl, tc, ta, tm⟩
  cases tm <;> cases b <;> cases clause <;>
    simp_all [LegalClause, Shift, newMid, modeOut]

theorem legalScan_tail_target_fields
    (s t : State) (b : Bool) (hlegal : LegalScan s t b)
    (hsphase : s.phase = .mid) (hsmode : s.mode = .tail)
    (htphase : t.phase = .mid) :
    b = false ∧ t.left = s.centre ∧ t.centre = .hash ∧
      t.lookahead = .lh0 ∧ t.mode = .tail := by
  rcases hlegal with ⟨clause, hc⟩
  rcases t with ⟨tp, tl, tc, ta, tm⟩
  cases tm <;> cases b <;> cases clause <;>
    simp_all [LegalClause, Shift, newMid, modeOut]

theorem legalScan_preTop_target_fields
    (s t : State) (b : Bool) (hlegal : LegalScan s t b)
    (hsphase : s.phase = .mid) (hsmode : s.mode = .tail)
    (htphase : t.phase = .top) :
    b = false ∧ t.left = s.centre ∧ t.centre = .hash ∧
      t.lookahead = .lh1 ∧ t.mode = .high := by
  rcases hlegal with ⟨clause, hc⟩
  cases clause <;> simp_all [LegalClause, Shift]

theorem legalScan_from_bottom_target_isHead
    (t : State) (b : Bool)
    (hlegal : LegalScan PakCouplingGenerated.scannerBottom t b) :
    PakScannerBaselineAutomaton.isHeadBuffer t.centre = true := by
  rcases hlegal with ⟨clause, hc⟩
  cases clause <;> simp_all [LegalClause, PakCouplingGenerated.scannerBottom]
  cases b <;> rfl

/-- Joint actual finite transition fields, with no external certificate. -/
def scanner_kernel_transition_fields_spec : Prop :=
  (∀ s t : State, ∀ b : Bool, LegalScan s t b →
    s.phase = .mid → s.mode = .high → t.phase = .mid →
    t.centre = .rightEnd →
    b = false ∧ t.left = s.centre ∧ t.lookahead = .lh0 ∧ t.mode = .tail) ∧
  (∀ s t : State, ∀ b : Bool, LegalScan s t b →
    s.phase = .mid → s.mode = .tail → t.phase = .mid →
    b = false ∧ t.left = s.centre ∧ t.centre = .hash ∧
      t.lookahead = .lh0 ∧ t.mode = .tail) ∧
  (∀ s t : State, ∀ b : Bool, LegalScan s t b →
    s.phase = .mid → s.mode = .tail → t.phase = .top →
    b = false ∧ t.left = s.centre ∧ t.centre = .hash ∧
      t.lookahead = .lh1 ∧ t.mode = .high) ∧
  (∀ t : State, ∀ b : Bool, LegalScan PakCouplingGenerated.scannerBottom t b →
    PakScannerBaselineAutomaton.isHeadBuffer t.centre = true)

theorem scanner_kernel_transition_fields_spec_holds :
    scanner_kernel_transition_fields_spec :=
  ⟨legalScan_terminal_target_fields, legalScan_tail_target_fields,
    legalScan_preTop_target_fields, legalScan_from_bottom_target_isHead⟩

end PakFixedPolyomino.PakScannerKernelTransitionFields
