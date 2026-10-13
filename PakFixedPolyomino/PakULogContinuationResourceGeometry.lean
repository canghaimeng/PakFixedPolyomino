import PakFixedPolyomino.PakULogCycleResourceBound

/-! # Derived target geometry for positive interpreter continuation

A capacity reserve is an upper bound, not evidence that an action is
nonterminal. The target lower bound below comes from actual semantic
nonhalting. Its radius upper bound comes from the physical encoded action
corridor, not the source-state coordinate. These facts repair precise missing
conditions in the preserved excluded continuation proof; they do not supply
its remaining tail execution, global resources or original counting theorem.
-/

namespace PakFixedPolyomino.PakULogContinuationResourceGeometry

open ULogAlphabet ULogControl ULogProgram ULogBootstrapExecution
open PakULogCycleResourceBound

/-- Actual nonhalting after an action is exactly the positive target condition. -/
theorem nonhalting_action_target (c : ULogSemantics.Config)
    (action : ULogBytecode.ActionCode)
    (hhalt : ULogSemantics.halted (ULogSemantics.applyAction c action) = false) :
    2 ≤ action.target := by
  by_contra hlower
  have ht : action.target < 2 := by omega
  have hh := (halted_applyAction_iff_target_lt_two c action).mpr ht
  rw [hh] at hhalt
  cases hhalt

theorem action_target_of_next (c next : ULogSemantics.Config)
    (action : ULogBytecode.ActionCode)
    (hnext : ULogSemantics.applyAction c action = next)
    (hhalt : ULogSemantics.halted next = false) : 2 ≤ action.target :=
  nonhalting_action_target c action (hnext ▸ hhalt)

/-- The actual unary target field is physically present in this corridor. -/
theorem target_le_encodedActionPath (write target : ℕ) (move : OneTapeTableau.Move)
    (path : List Tape) :
    target ≤ (encodedActionPath write target move path).length := by
  simp [encodedActionPath, ULogBytecode.encodeNatField]
  omega

theorem matched_radius_target_le {R : ℕ}
    {r : ULogBytecode.RuleCode} {rs : List ULogBytecode.RuleCode}
    {programToHead runtime : List Tape}
    (radius : MatchedTargetZeroWithinRadius R r rs programToHead runtime) :
    r.action.target ≤ R :=
  (target_le_encodedActionPath r.action.write r.action.target r.action.move
    (cursorMatchedMovePath rs programToHead)).trans radius.read_corridor_le

theorem canonical_target_le (current actual : ℕ)
    (passed skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (programToHead runtime : List Tape) :
    r.action.target ≤ canonicalMismatchBudget current actual passed skip (r :: rs)
      programToHead runtime :=
  matched_radius_target_le (matchedTargetZeroWithin_canonicalBudget current actual passed skip r rs
    programToHead runtime)

/-- A matched instruction's target fits the actual physical frame radius;
no capacity or source<=radius substitution is needed. -/
theorem matched_target_le_frameRadius {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix)
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode)
    (heq : frame.config.program = skip ++ r :: rs) :
    r.action.target ≤ semanticFrameCursorRadius input frame := by
  have ht := canonical_target_le frame.config.state frame.config.focus [] skip r rs
    (cursorDynamicProgramToHead input (frame.config.leftRev.map payloadNat))
    (clockCellsAfter (frame.config.right.map payloadNat) frame.clockZeros frame.runtime)
  exact ht.trans_eq (canonicalMismatchBudget_eq_frameCursorRadius frame skip r rs heq)

/-- Both disputed bounds are derived at the real caller's nonhalting next
configuration. The selected rule equality preserves its actual target. -/
theorem matched_continuation_target_bounds {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (next : ULogSemantics.Config)
    (action : ULogBytecode.ActionCode)
    (hnext : ULogSemantics.applyAction frame.config action = next)
    (hhalt : ULogSemantics.halted next = false)
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode)
    (heq : frame.config.program = skip ++ r :: rs)
    (hrule : r.action = action) :
    2 ≤ r.action.target ∧ r.action.target ≤ semanticFrameCursorRadius input frame := by
  refine ⟨?_, matched_target_le_frameRadius frame skip r rs heq⟩
  rw [hrule]
  exact action_target_of_next frame.config next action hnext hhalt

end PakFixedPolyomino.PakULogContinuationResourceGeometry
