import PakFixedPolyomino.ULogAutomaticSemanticRightBoundary

/-! Unified automatic one-cycle semantic refinement across every move/boundary case. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def semanticCapacityAfter (c : ULogSemantics.Config)
    (action : ULogBytecode.ActionCode) (capacity : ℕ) : ℕ :=
  match action.move, c.right with
  | .right, [] => capacity - 1
  | _, _ => capacity

def semanticOuterAfter (c : ULogSemantics.Config)
    (action : ULogBytecode.ActionCode) (outer : List Tape) : List Tape :=
  match action.move, c.leftRev with
  | .left, [] => outer.tail
  | _, _ => outer

def SemanticCapacityReady (c : ULogSemantics.Config)
    (action : ULogBytecode.ActionCode) (capacity : ℕ) : Prop :=
  match action.move, c.right with
  | .right, [] => action.target < capacity
  | _, _ => action.target ≤ capacity

def SemanticOuterReady (c : ULogSemantics.Config)
    (action : ULogBytecode.ActionCode) (outer : List Tape) : Prop :=
  match action.move, c.leftRev with
  | .left, [] => ∃ tail, outer = MStarConcreteAlphabet.work :: tail
  | _, _ => True

theorem branchedCycle_semanticLookupSome
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (hstateCapacity : c.state ≤ capacity)
    (hcapacity : SemanticCapacityReady c action capacity)
    (htargetLower : 2 ≤ action.target)
    (houter : SemanticOuterReady c action outer) :
    BranchedReaches slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (semanticCycleEncoding input
        (clockCellsAfter
          ((ULogSemantics.applyAction c action).right.map payloadNat)
          clockZeros runtime)
        (semanticCapacityAfter c action capacity)
        (semanticOuterAfter c action outer) suffix
        (ULogSemantics.applyAction c action)) := by
  cases hmove : action.move with
  | stay =>
      have htarget : action.target ≤ capacity := by
        simpa [SemanticCapacityReady, hmove] using hcapacity
      have h := branchedCycle_semanticLookupSome_stay c slot action hlookup
        input clockZeros capacity runtime outer suffix hruntime hfocus hreads
        hwrites hstateCapacity htarget htargetLower hmove
      simpa [semanticCapacityAfter, semanticOuterAfter, hmove,
        ULogSemantics.applyAction] using h
  | right =>
      cases hright : c.right with
      | nil =>
          have htarget : action.target < capacity := by
            simpa [SemanticCapacityReady, hmove, hright] using hcapacity
          have h := branchedCycle_semanticRightBoundary c slot action hlookup
            hright input clockZeros capacity runtime outer suffix hruntime
            hfocus hreads hwrites hstateCapacity htarget htargetLower hmove
          simpa [semanticCapacityAfter, semanticOuterAfter, hmove, hright,
            ULogSemantics.applyAction] using h
      | cons next rightTail =>
          have htarget : action.target ≤ capacity := by
            simpa [SemanticCapacityReady, hmove, hright] using hcapacity
          have h := branchedCycle_semanticRightInternal c slot action hlookup
            next rightTail hright input clockZeros capacity runtime outer
            suffix hruntime hfocus hreads hwrites hstateCapacity htarget htargetLower hmove
          simpa [semanticCapacityAfter, semanticOuterAfter, hmove, hright,
            ULogSemantics.applyAction] using h
  | left =>
      cases hleft : c.leftRev with
      | nil =>
          obtain ⟨outerTail, houterEq⟩ :
              ∃ tail, outer = MStarConcreteAlphabet.work :: tail := by
            simpa [SemanticOuterReady, hmove, hleft] using houter
          have htarget : action.target ≤ capacity := by
            simpa [SemanticCapacityReady, hmove] using hcapacity
          have h := branchedCycle_semanticLeftBoundary c slot action hlookup
            hleft input clockZeros capacity runtime outerTail suffix hruntime
            hfocus hreads hwrites hstateCapacity htarget htargetLower hmove
          subst outer
          simpa [semanticCapacityAfter, semanticOuterAfter, hmove, hleft,
            ULogSemantics.applyAction] using h
      | cons next leftTail =>
          have htarget : action.target ≤ capacity := by
            simpa [SemanticCapacityReady, hmove] using hcapacity
          have h := branchedCycle_semanticLeftInternal c slot action hlookup
            next leftTail hleft input clockZeros capacity runtime outer suffix
            hruntime hfocus hreads hwrites hstateCapacity htarget htargetLower hmove
          simpa [semanticCapacityAfter, semanticOuterAfter, hmove, hleft,
            ULogSemantics.applyAction] using h

end PakFixedPolyomino.ULogBootstrapExecution
