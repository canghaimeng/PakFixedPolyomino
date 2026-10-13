import PakFixedPolyomino.ULogAutomaticSemanticLookupCycle

/-! Exact correspondence between semantic `stepSlot` and concrete cycle outcomes. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem stepSlot_eq_lookup_map (slot : Bool)
    (c : ULogSemantics.Config) (hhalt : ULogSemantics.halted c = false) :
    ULogSemantics.stepSlot slot c =
      (ULogBytecode.lookupRule c.program c.state c.focus slot).map
        (ULogSemantics.applyAction c) := by
  simp [ULogSemantics.stepSlot, hhalt]

theorem semanticCycleOutcome_of_step_none
    (c : ULogSemantics.Config) (slot : Bool)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape)
    (hhalt : ULogSemantics.halted c = false)
    (hstep : ULogSemantics.stepSlot slot c = none) :
    semanticCycleOutcome c slot input clockZeros capacity runtime outer
      suffix = .rejected := by
  have hmap := stepSlot_eq_lookup_map slot c hhalt
  rw [hstep] at hmap
  cases hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot with
  | none => simp [semanticCycleOutcome, hlookup]
  | some action => simp [hlookup] at hmap

theorem semanticCycleOutcome_of_step_some
    (c c' : ULogSemantics.Config) (slot : Bool)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape)
    (hhalt : ULogSemantics.halted c = false)
    (hstep : ULogSemantics.stepSlot slot c = some c') :
    ∃ action,
      ULogBytecode.lookupRule c.program c.state c.focus slot = some action ∧
        c' = ULogSemantics.applyAction c action ∧
        semanticCycleOutcome c slot input clockZeros capacity runtime outer
            suffix =
          semanticCycleEncoding input
            (clockCellsAfter (c'.right.map payloadNat) clockZeros runtime)
            (semanticCapacityAfter c action capacity)
            (semanticOuterAfter c action outer) suffix c' := by
  have hmap := stepSlot_eq_lookup_map slot c hhalt
  rw [hstep] at hmap
  cases hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot with
  | none => simp [hlookup] at hmap
  | some action =>
      have hc' : c' = ULogSemantics.applyAction c action := by
        simpa [hlookup] using hmap
      refine ⟨action, by simpa [hlookup], hc', ?_⟩
      subst c'
      simp [semanticCycleOutcome, hlookup]

end PakFixedPolyomino.ULogBootstrapExecution
