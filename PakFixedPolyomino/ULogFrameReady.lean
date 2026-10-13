import PakFixedPolyomino.ULogClockReframing
import PakFixedPolyomino.ULogSemanticInitialization

/-! Uniform semantic bounds imply the concrete cycle-frame readiness invariant. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem FrameReady.ofUniformBounds
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix)
    (hruntime : PassivePath frame.runtime)
    (hfocus : frame.config.focus < 3)
    (hprogram : frame.config.program ≠ [])
    (hreads : ∀ r ∈ frame.config.program, r.read < 3)
    (hwrites : ∀ r ∈ frame.config.program, r.action.write < 3)
    (hstate : frame.config.state ≤ frame.capacity)
    (htargets : ∀ r ∈ frame.config.program,
      r.action.target < frame.capacity)
    (hleftBoundary : frame.config.leftRev = [] →
      ∃ tail, frame.outer = MStarConcreteAlphabet.work :: tail) :
    FrameReady frame := by
  refine
    { runtime_passive := hruntime
      focus_lt_three := hfocus
      program_nonempty := hprogram
      reads_lt_three := hreads
      writes_lt_three := hwrites
      state_le_capacity := hstate
      capacity_ready := ?_
      outer_ready := ?_ }
  · intro slot action hlookup
    obtain ⟨r, hr, _, _, _, haction⟩ :=
      ULogBytecode.lookupRule_some_mem hlookup
    have htarget : action.target < frame.capacity := by
      rw [← haction]
      exact htargets r hr
    unfold SemanticCapacityReady
    cases hm : action.move with
    | stay => omega
    | left => omega
    | right =>
        cases frame.config.right with
        | nil => simpa [hm] using htarget
        | cons x xs =>
            simpa [hm] using (Nat.le_of_lt htarget)
  · intro slot action hlookup
    unfold SemanticOuterReady
    cases hm : action.move with
    | stay => trivial
    | right => trivial
    | left =>
        cases hl : frame.config.leftRev with
        | nil => exact hleftBoundary hl
        | cons x xs => trivial

def programTargetBound : List ULogBytecode.RuleCode → ℕ
  | [] => 0
  | r :: rs => max r.action.target (programTargetBound rs)

theorem actionTarget_le_programTargetBound
    {rules : List ULogBytecode.RuleCode} {r : ULogBytecode.RuleCode}
    (hr : r ∈ rules) : r.action.target ≤ programTargetBound rules := by
  induction rules with
  | nil => simp at hr
  | cons head rules ih =>
      rcases List.mem_cons.mp hr with rfl | hr
      · exact Nat.le_max_left _ _
      · exact (ih hr).trans (Nat.le_max_right _ _)

/-- A canonical initial unary-state capacity.  Additional runtime reserve can
be added later for boundary motion, but this base already dominates every
program target and the fixed semantic start state. -/
def initialStateCapacity (rules : List ULogBytecode.RuleCode) : ℕ :=
  max 2 (programTargetBound rules + 1)

theorem initialStateCapacity_ge_two (rules : List ULogBytecode.RuleCode) :
    2 ≤ initialStateCapacity rules := Nat.le_max_left _ _

theorem actionTarget_lt_initialStateCapacity
    {rules : List ULogBytecode.RuleCode} {r : ULogBytecode.RuleCode}
    (hr : r ∈ rules) : r.action.target < initialStateCapacity rules := by
  have hle := actionTarget_le_programTargetBound hr
  unfold initialStateCapacity
  omega

/-- The exact semantic cycle frame produced by the bootstrap theorem when one
outer work cell is reserved for a possible first left-boundary move. -/
def bootstrapSemanticFrame
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (capacity : ℕ) (outerTail : List Tape) :
    SemanticCycleFrame input ([] : List Tape) where
  config := ULogSemantics.startFrom rules input
  clockZeros := padding.length
  runtime := [ulogCore clockSep]
  capacity := capacity
  outer := MStarConcreteAlphabet.work :: outerTail

theorem bootstrapSemanticFrame_encode
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (capacity : ℕ) (outerTail : List Tape) :
    (bootstrapSemanticFrame rules input padding capacity outerTail).encode =
      semanticCycleEncoding input
        (clockCellsBefore
          ((ULogSemantics.startFrom rules input).right.map payloadNat)
          padding.length [ulogCore clockSep])
        capacity (MStarConcreteAlphabet.work :: outerTail) []
        (ULogSemantics.startFrom rules input) := rfl

theorem bootstrapSemanticFrame_ready
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (capacity : ℕ) (outerTail : List Tape)
    (hprogram : rules ≠ []) (hcapacity : 2 ≤ capacity)
    (hreads : ∀ r ∈ rules, r.read < 3)
    (hwrites : ∀ r ∈ rules, r.action.write < 3)
    (htargets : ∀ r ∈ rules, r.action.target < capacity) :
    FrameReady (bootstrapSemanticFrame rules input padding capacity outerTail) := by
  apply FrameReady.ofUniformBounds
  · intro cell hcell
    simp only [bootstrapSemanticFrame, List.mem_singleton] at hcell
    subst cell
    constructor <;> native_decide
  · cases input with
    | nil =>
        simp [bootstrapSemanticFrame, ULogSemantics.startFrom,
          ULogSemantics.initialTape, ULogSemantics.blankCode]
    | cons b bs =>
        cases b <;>
          simp [bootstrapSemanticFrame, ULogSemantics.startFrom,
            ULogSemantics.initialTape, ULogSemantics.bitCode]
  · simpa [bootstrapSemanticFrame, ULogSemantics.startFrom] using hprogram
  · simpa [bootstrapSemanticFrame, ULogSemantics.startFrom] using hreads
  · simpa [bootstrapSemanticFrame, ULogSemantics.startFrom] using hwrites
  · simpa [bootstrapSemanticFrame, ULogSemantics.startFrom,
      ULogSemantics.startCode] using hcapacity
  · simpa [bootstrapSemanticFrame, ULogSemantics.startFrom] using htargets
  · intro _
    exact ⟨outerTail, rfl⟩

theorem bootstrapSemanticFrame_ready_canonicalCapacity
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (outerTail : List Tape) (hprogram : rules ≠ [])
    (hreads : ∀ r ∈ rules, r.read < 3)
    (hwrites : ∀ r ∈ rules, r.action.write < 3) :
    FrameReady
      (bootstrapSemanticFrame rules input padding
        (initialStateCapacity rules) outerTail) := by
  exact bootstrapSemanticFrame_ready rules input padding
    (initialStateCapacity rules) outerTail hprogram
    (initialStateCapacity_ge_two rules) hreads hwrites
    (fun r hr => actionTarget_lt_initialStateCapacity hr)

theorem reaches_bootstrap_frame
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (capacity : ℕ) (outerTail : List Tape) :
    Reaches
      (.running .start
        ⟨outerTail, MStarConcreteAlphabet.work,
          MStarConcreteAlphabet.work ::
            (ULogBytecode.encodeProgram rules ++
              ULogBytecode.encodePayload input padding).map bitTape ++
                MStarConcreteAlphabet.work ::
                  payloadRuntimeWorkspace input
                    (List.replicate (capacity - 2)
                      MStarConcreteAlphabet.work)⟩)
      (bootstrapSemanticFrame rules input padding capacity outerTail).encode := by
  have h := reaches_bootstrap_semanticStart_capacity 1 capacity rules input
    padding outerTail []
  simpa [bootstrapSemanticFrame, SemanticCycleFrame.encode,
    List.append_assoc] using h

end PakFixedPolyomino.ULogBootstrapExecution
