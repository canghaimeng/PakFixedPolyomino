import PakFixedPolyomino.ULogClockedNoMatchRejection

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem ruleMatches_eq_true_iff (slot : Bool) (current actual : ℕ)
    (r : ULogBytecode.RuleCode) :
    ULogBytecode.ruleMatches current actual slot r = true ↔
      RuleMatchesCursor slot current actual r := by
  simp [ULogBytecode.ruleMatches, RuleMatchesCursor]

theorem lookupRule_some_first_split
    (rules : List ULogBytecode.RuleCode) (current actual : ℕ)
    (slot : Bool) (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule rules current actual slot =
      some action) :
    ∃ skip r rs,
      rules = skip ++ r :: rs ∧
        (∀ s ∈ skip, ¬ RuleMatchesCursor slot current actual s) ∧
          RuleMatchesCursor slot current actual r ∧ r.action = action := by
  induction rules with
  | nil => simp [ULogBytecode.lookupRule] at hlookup
  | cons x xs ih =>
      by_cases hm : RuleMatchesCursor slot current actual x
      · have hbool : ULogBytecode.ruleMatches current actual slot x = true :=
          (ruleMatches_eq_true_iff slot current actual x).2 hm
        have haction : x.action = action := by
          simpa [ULogBytecode.lookupRule, List.find?, hbool] using hlookup
        exact ⟨[], x, xs, by simp, by simp, hm, haction⟩
      · have hbool : ULogBytecode.ruleMatches current actual slot x = false := by
          cases he : ULogBytecode.ruleMatches current actual slot x
          · rfl
          · exact (hm ((ruleMatches_eq_true_iff slot current actual x).1
              he)).elim
        have htail : ULogBytecode.lookupRule xs current actual slot =
            some action := by
          simpa [ULogBytecode.lookupRule, List.find?, hbool] using hlookup
        obtain ⟨skip, r, rs, heq, hskip, hr, ha⟩ := ih htail
        exact ⟨x :: skip, r, rs, by simp [heq], by
          intro s hs
          rcases List.mem_cons.mp hs with rfl | hs
          · exact hm
          · exact hskip s hs,
          hr, ha⟩

theorem lookupRule_none_iff_all_mismatch
    (rules : List ULogBytecode.RuleCode) (current actual : ℕ)
    (slot : Bool) :
    ULogBytecode.lookupRule rules current actual slot = none ↔
      ∀ r ∈ rules, ¬ RuleMatchesCursor slot current actual r := by
  induction rules with
  | nil => simp [ULogBytecode.lookupRule]
  | cons r rs ih =>
      by_cases hm : RuleMatchesCursor slot current actual r
      · have hbool : ULogBytecode.ruleMatches current actual slot r = true :=
          (ruleMatches_eq_true_iff slot current actual r).2 hm
        simp [ULogBytecode.lookupRule, List.find?, hbool, hm]
      · have hbool : ULogBytecode.ruleMatches current actual slot r = false := by
          cases he : ULogBytecode.ruleMatches current actual slot r
          · rfl
          · exact (hm ((ruleMatches_eq_true_iff slot current actual r).1
              he)).elim
        rw [show ULogBytecode.lookupRule (r :: rs) current actual slot =
          ULogBytecode.lookupRule rs current actual slot by
            simp [ULogBytecode.lookupRule, List.find?, hbool]]
        rw [ih]
        simp [hm]

theorem stepSlot_some_firstRule
    {slot : Bool} {c c' : ULogSemantics.Config}
    (hstep : ULogSemantics.stepSlot slot c = some c') :
    ∃ skip r rs,
      c.program = skip ++ r :: rs ∧
        (∀ s ∈ skip,
          ¬ RuleMatchesCursor slot c.state c.focus s) ∧
        RuleMatchesCursor slot c.state c.focus r ∧
        ULogSemantics.applyAction c r.action = c' := by
  rcases ULogSemantics.stepSlot_some_rule hstep with
    ⟨-, action, hlookup, haction⟩
  obtain ⟨skip, r, rs, heq, hskip, hmatch, hr⟩ :=
    lookupRule_some_first_split c.program c.state c.focus slot action
      hlookup
  subst action
  exact ⟨skip, r, rs, heq, hskip, hmatch, haction⟩

end PakFixedPolyomino.ULogBootstrapExecution
