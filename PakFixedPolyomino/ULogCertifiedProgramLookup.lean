import PakFixedPolyomino.ULogSemanticRuleSelection

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

structure RuleScanCertificate (slot : Bool) (current actual : ℕ)
    (programToHead runtime : List Tape) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) : Prop where
  actual_valid : actual < 3
  read_valid : r.read < 3
  source_corridor : SourceCompareCorridorSafe
    (cursorRuleCorridor r rs programToHead (readHeadNat actual) runtime)
  read_boundary_free : ∀ x ∈
    cursorRuleCorridor r rs programToHead (readHeadNat actual) runtime,
      x ≠ ulogCore readBoundary
  read_scan : ReadCorridorSafe (cursorReadScanPath r rs programToHead)
  read_restore : MismatchRestorePathSafe
    (readMismatchRestorePath r.source r.read
      (cursorReadScanPath r rs programToHead))
  slot_scan : ReadCorridorSafe
    (codeTape (!slot) :: encodedActionPath r.action.write
      r.action.target r.action.move (cursorMatchedMovePath rs programToHead))
  slot_restore : MismatchRestorePathSafe
    (slotMismatchRestorePath r.source r.read)
  program_restore : RestoreMismatchIdentity programToHead

theorem RuleScanCertificate.toMismatch
    {slot : Bool} {current actual : ℕ} {programToHead runtime : List Tape}
    {r : ULogBytecode.RuleCode} {rs : List ULogBytecode.RuleCode}
    (cert : RuleScanCertificate slot current actual programToHead runtime r rs)
    (hmismatch : ¬ RuleMatchesCursor slot current actual r) :
    RuleMismatchCertificate slot current actual programToHead runtime r rs :=
  { mismatch := hmismatch
    actual_valid := cert.actual_valid
    read_valid := cert.read_valid
    source_corridor := cert.source_corridor
    read_boundary_free := cert.read_boundary_free
    read_scan := cert.read_scan
    read_restore := cert.read_restore
    slot_scan := cert.slot_scan
    slot_restore := cert.slot_restore
    program_restore := cert.program_restore }

inductive CertifiedProgramScan (slot : Bool) (current actual : ℕ)
    (programToHead runtime : List Tape) :
    List ULogBytecode.RuleCode → Prop
  | nil : CertifiedProgramScan slot current actual programToHead runtime []
  | cons (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
      (head : RuleScanCertificate slot current actual programToHead runtime
        r rs)
      (tail : CertifiedProgramScan slot current actual programToHead runtime
        rs) :
      CertifiedProgramScan slot current actual programToHead runtime (r :: rs)

theorem certifiedProgramScan_lookup_some
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime : List Tape)
    {rules : List ULogBytecode.RuleCode}
    (cert : CertifiedProgramScan slot current actual programToHead runtime
      rules)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule rules current actual slot =
      some action) :
    ∃ skip r rs,
      rules = skip ++ r :: rs ∧
        MismatchCertificateList slot current actual programToHead runtime
          skip (r :: rs) ∧
        RuleScanCertificate slot current actual programToHead runtime r rs ∧
        RuleMatchesCursor slot current actual r ∧ r.action = action := by
  induction cert with
  | nil => simp [ULogBytecode.lookupRule] at hlookup
  | cons x xs head tail ih =>
      by_cases hm : RuleMatchesCursor slot current actual x
      · have hbool : ULogBytecode.ruleMatches current actual slot x = true :=
          (ruleMatches_eq_true_iff slot current actual x).2 hm
        have haction : x.action = action := by
          simpa [ULogBytecode.lookupRule, List.find?, hbool] using hlookup
        exact ⟨[], x, xs, by simp,
          MismatchCertificateList.nil (x :: xs), head, hm, haction⟩
      · have hbool : ULogBytecode.ruleMatches current actual slot x = false := by
          cases he : ULogBytecode.ruleMatches current actual slot x
          · rfl
          · exact (hm ((ruleMatches_eq_true_iff slot current actual x).1
              he)).elim
        have htail : ULogBytecode.lookupRule xs current actual slot =
            some action := by
          simpa [ULogBytecode.lookupRule, List.find?, hbool] using hlookup
        obtain ⟨skip, r, rs, heq, hprefix, hrscan, hrmatch, hra⟩ :=
          ih htail
        subst xs
        exact ⟨x :: skip, r, rs, by simp,
          MismatchCertificateList.cons x skip (r :: rs)
            (head.toMismatch hm) hprefix,
          hrscan, hrmatch, hra⟩

theorem certifiedProgramScan_lookup_none
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime : List Tape)
    {rules : List ULogBytecode.RuleCode}
    (cert : CertifiedProgramScan slot current actual programToHead runtime
      rules)
    (hrules : rules ≠ [])
    (hlookup : ULogBytecode.lookupRule rules current actual slot = none) :
    ∃ skip last,
      rules = skip ++ [last] ∧
        NoMatchCertificate slot current actual programToHead runtime
          skip last := by
  have hall := (lookupRule_none_iff_all_mismatch rules current actual slot).1
    hlookup
  induction cert with
  | nil => exact (hrules rfl).elim
  | cons x xs head tail ih =>
      have hx : ¬ RuleMatchesCursor slot current actual x :=
        hall x (by simp)
      cases xs with
      | nil =>
          exact ⟨[], x, by simp,
            { mismatches := MismatchCertificateList.nil [x]
              lastMismatch := head.toMismatch hx }⟩
      | cons y ys =>
          have htailLookup : ULogBytecode.lookupRule (y :: ys) current actual
              slot = none :=
            (lookupRule_none_iff_all_mismatch (y :: ys) current actual slot).2
              (fun r hr => hall r (by simp [hr]))
          obtain ⟨skip, last, heq, hnomatch⟩ :=
            ih (by simp) htailLookup
              (fun r hr => hall r (by simp [hr]))
          rw [heq] at head
          exact ⟨x :: skip, last, by simp [heq],
            { mismatches := MismatchCertificateList.cons x skip [last]
                (head.toMismatch hx) hnomatch.mismatches
              lastMismatch := hnomatch.lastMismatch }⟩

end PakFixedPolyomino.ULogBootstrapExecution
