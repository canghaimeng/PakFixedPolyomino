import PakFixedPolyomino.ULogSemanticCycleSpec
import PakFixedPolyomino.ULogAutomaticSemanticHalt

/-! A successful semantic slot step automatically yields a coupled concrete cycle. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem automaticCoupledCycleStep
    (c c' : ULogSemantics.Config) (slot : Bool)
    (hhalt : ULogSemantics.halted c = false)
    (hstep : ULogSemantics.stepSlot slot c = some c')
    (hnext : ULogSemantics.halted c' = false)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (hstateCapacity : c.state ≤ capacity)
    (hcapacity : ∀ action,
      ULogBytecode.lookupRule c.program c.state c.focus slot = some action →
        SemanticCapacityReady c action capacity)
    (houter : ∀ action,
      ULogBytecode.lookupRule c.program c.state c.focus slot = some action →
        SemanticOuterReady c action outer) :
    ∃ action,
      ULogBytecode.lookupRule c.program c.state c.focus slot = some action ∧
        c' = ULogSemantics.applyAction c action ∧
        CoupledCycleStep slot c c'
          (semanticCycleEncoding input
            (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
            capacity outer suffix c)
          (semanticCycleEncoding input
            (clockCellsAfter (c'.right.map payloadNat) clockZeros runtime)
            (semanticCapacityAfter c action capacity)
            (semanticOuterAfter c action outer) suffix c') := by
  obtain ⟨action, hlookup, hc', houtcome⟩ :=
    semanticCycleOutcome_of_step_some c c' slot input clockZeros capacity
      runtime outer suffix hhalt hstep
  have hconcrete := branchedCycle_semanticLookupSome c slot action hlookup
    input clockZeros capacity runtime outer suffix hruntime hfocus hreads
    hwrites hstateCapacity (hcapacity action hlookup) (by
      rw [hc'] at hnext
      have hnot : ¬ ULogSemantics.halted
          (ULogSemantics.applyAction c action) = true := by
        intro htrue
        rw [htrue] at hnext
        contradiction
      have hnlt : ¬ action.target < 2 := fun ht =>
        hnot ((halted_applyAction_iff_target_lt_two c action).mpr ht)
      omega) (houter action hlookup)
  refine ⟨action, hlookup, hc', ⟨hstep, ?_⟩⟩
  simpa [hc'] using hconcrete

structure ClockReframe (right : List Tape) (after : List Tape) where
  zeros : ℕ
  runtime : List Tape
  runtime_passive : PassivePath runtime
  eq_before : clockCellsBefore right zeros runtime = after

theorem clockReframe_align
    {c : ULogSemantics.Config} {input : List Bool}
    {capacity : ℕ} {outer suffix after : List Tape}
    (frame : ClockReframe (c.right.map payloadNat) after) :
    semanticCycleEncoding input after capacity outer suffix c =
      semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) frame.zeros frame.runtime)
        capacity outer suffix c := by
  rw [frame.eq_before]

end PakFixedPolyomino.ULogBootstrapExecution
