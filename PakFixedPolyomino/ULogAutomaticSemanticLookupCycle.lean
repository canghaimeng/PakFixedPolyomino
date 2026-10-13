import PakFixedPolyomino.ULogAutomaticSemanticCycle

/-! Unified successful/no-rule semantic lookup outcome for one concrete cycle. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def semanticCycleOutcome (c : ULogSemantics.Config) (slot : Bool)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) : Result :=
  match ULogBytecode.lookupRule c.program c.state c.focus slot with
  | none => .rejected
  | some action =>
      semanticCycleEncoding input
        (clockCellsAfter
          ((ULogSemantics.applyAction c action).right.map payloadNat)
          clockZeros runtime)
        (semanticCapacityAfter c action capacity)
        (semanticOuterAfter c action outer) suffix
        (ULogSemantics.applyAction c action)

theorem branchedCycle_semanticLookup
    (c : ULogSemantics.Config) (slot : Bool)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3) (hrules : c.program ≠ [])
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (hstateCapacity : c.state ≤ capacity)
    (hcapacity : ∀ action,
      ULogBytecode.lookupRule c.program c.state c.focus slot = some action →
        SemanticCapacityReady c action capacity)
    (htargets : ∀ action,
      ULogBytecode.lookupRule c.program c.state c.focus slot = some action →
        2 ≤ action.target)
    (houter : ∀ action,
      ULogBytecode.lookupRule c.program c.state c.focus slot = some action →
        SemanticOuterReady c action outer) :
    BranchedReaches slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (semanticCycleOutcome c slot input clockZeros capacity runtime outer
        suffix) := by
  cases hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot with
  | none =>
      have h := branchedCycle_semanticNoRule c slot input clockZeros capacity
        runtime outer suffix hruntime hfocus hrules hreads hlookup
      simpa [semanticCycleOutcome, hlookup] using h
  | some action =>
      have h := branchedCycle_semanticLookupSome c slot action hlookup input
        clockZeros capacity runtime outer suffix hruntime hfocus hreads
        hwrites hstateCapacity (hcapacity action hlookup)
        (htargets action hlookup)
        (houter action hlookup)
      simpa [semanticCycleOutcome, hlookup] using h

end PakFixedPolyomino.ULogBootstrapExecution
