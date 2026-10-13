import PakFixedPolyomino.ULogConcreteMachine
import PakFixedPolyomino.ULogSemanticSlotTrace
import PakFixedPolyomino.ULogAutomaticSemanticHalt

/-! Canonical concrete accepting traces for labelled semantic accepting words.

The concrete interpreter may accept *during* the final labelled cycle: target
state zero reaches `.accepted` rather than another cycle-boundary encoding.
Consequently the refinement below is outcome-valued, rather than incorrectly
requiring every semantic step to end at an encoding of its successor. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

/-- A labelled concrete run followed, if necessary, by ordinary unlabelled
microsteps to a concrete accepting terminal. -/
def ConcreteAcceptingSlotTrace (start : Result) (slots : List Bool) : Prop :=
  ∃ cycleFinish, ConcreteBranchedRun start slots cycleFinish ∧
    ∃ finish, Reaches cycleFinish finish ∧
      concreteHalted finish = true ∧ concreteAccepting finish = true

/-- The semantic accepting words with a fixed time budget. -/
def SemanticAcceptingWords (t : ℕ) (c : ULogSemantics.Config) : Type :=
  { w : List Bool // w ∈ acceptingSlotWords t c }

/-- The resources that determine one semantic cycle-boundary encoding. -/
structure SemanticCycleFrame (input : List Bool) (suffix : List ULogProgram.Tape) where
  config : ULogSemantics.Config
  clockZeros : ℕ
  runtime : List ULogProgram.Tape
  capacity : ℕ
  outer : List ULogProgram.Tape

def SemanticCycleFrame.encode
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (frame : SemanticCycleFrame input suffix) : Result :=
  semanticCycleEncoding input
    (clockCellsBefore (frame.config.right.map payloadNat)
      frame.clockZeros frame.runtime)
    frame.capacity frame.outer suffix frame.config

/-- Reframing the post-cycle clock block as the next cycle's before-clock
block supplies the resources for a continuing semantic successor. -/
def SemanticCycleFrame.reframeNext
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (frame : SemanticCycleFrame input suffix) (action : ULogBytecode.ActionCode)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    SemanticCycleFrame input suffix where
  config := ULogSemantics.applyAction frame.config action
  clockZeros := reframe.zeros
  runtime := reframe.runtime
  capacity := semanticCapacityAfter frame.config action frame.capacity
  outer := semanticOuterAfter frame.config action frame.outer

/-- The local invariant required to apply the concrete complete-cycle theorem.
It is attached to a trace node rather than asserted for every resource frame. -/
structure FrameReady {input : List Bool} {suffix : List ULogProgram.Tape}
    (frame : SemanticCycleFrame input suffix) : Prop where
  runtime_passive : PassivePath frame.runtime
  focus_lt_three : frame.config.focus < 3
  program_nonempty : frame.config.program ≠ []
  reads_lt_three : ∀ r ∈ frame.config.program, r.read < 3
  writes_lt_three : ∀ r ∈ frame.config.program, r.action.write < 3
  state_le_capacity : frame.config.state ≤ frame.capacity
  capacity_ready : ∀ slot action,
    ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action →
      SemanticCapacityReady frame.config action frame.capacity
  outer_ready : ∀ slot action,
    ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action →
      SemanticOuterReady frame.config action frame.outer

theorem FrameReady.semanticConcreteCycleSpec
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (frame : SemanticCycleFrame input suffix) (ready : FrameReady frame)
    (slot : Bool) :
    SemanticConcreteCycleSpec frame.config slot input frame.clockZeros
      frame.capacity frame.runtime frame.outer suffix := by
  exact branchedCycle_semanticComplete frame.config slot input frame.clockZeros
    frame.capacity frame.runtime frame.outer suffix ready.runtime_passive
    ready.focus_lt_three ready.program_nonempty ready.reads_lt_three
    ready.writes_lt_three ready.state_le_capacity
    (fun action hlookup => ready.capacity_ready slot action hlookup)
    (fun action hlookup => ready.outer_ready slot action hlookup)

/-- At an accepting semantic cycle boundary the implementation must dispatch
by ordinary concrete microsteps to a concrete accepting terminal. -/
def FrameAcceptingTerminal
    {input : List Bool} {suffix : List ULogProgram.Tape} : Prop :=
  ∀ frame : SemanticCycleFrame input suffix,
    FrameReady frame → ULogSemantics.halted frame.config = true →
      ULogSemantics.accepting frame.config = true →
        ∃ finish, Reaches frame.encode finish ∧ concreteAccepting finish = true

/-- The nonterminal branch of a resource-indexed concrete cycle realization.
The accepting branch is supplied directly by `SemanticConcreteCycleSpec`; a
rejecting halted successor cannot occur in an accepting trace; and this
interface supplies an action, `ClockReframe`, and readiness certificate for a
continuing successor. -/
def ResourceContinuationRefinement
    {input : List Bool} {suffix : List ULogProgram.Tape} : Prop :=
  ∀ (frame : SemanticCycleFrame input suffix) (slot : Bool)
      (ready : FrameReady frame) (c' : ULogSemantics.Config),
    ULogSemantics.stepSlot slot frame.config = some c' →
      ULogSemantics.accepting c' = false →
      ULogSemantics.halted c' = false →
        ∃ (action : ULogBytecode.ActionCode)
        (hlookup : ULogBytecode.lookupRule frame.config.program
          frame.config.state frame.config.focus slot = some action)
        (haction : ULogSemantics.applyAction frame.config action = c')
        (reframe : ClockReframe
          ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
          (clockCellsAfter
            ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
            frame.clockZeros frame.runtime)),
        FrameReady (frame.reframeNext action reframe) ∧
        BranchedReaches slot frame.encode
          (frame.reframeNext action reframe).encode

/-- The genuinely external part of multi-cycle composition is now only a
resource schedule: it chooses a clock reframing and proves readiness of the
next frame.  The concrete branch itself is derived from
`branchedCycle_semanticLookupSome`. -/
def ResourceFrameSchedule
    {input : List Bool} {suffix : List ULogProgram.Tape} : Prop :=
  ∀ (frame : SemanticCycleFrame input suffix) (slot : Bool)
      (ready : FrameReady frame) (c' : ULogSemantics.Config),
    ULogSemantics.stepSlot slot frame.config = some c' →
      ULogSemantics.accepting c' = false →
      ULogSemantics.halted c' = false →
        ∃ (action : ULogBytecode.ActionCode)
        (hlookup : ULogBytecode.lookupRule frame.config.program
          frame.config.state frame.config.focus slot = some action)
        (haction : ULogSemantics.applyAction frame.config action = c')
        (reframe : ClockReframe
          ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
          (clockCellsAfter
            ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
            frame.clockZeros frame.runtime)),
        FrameReady (frame.reframeNext action reframe)

theorem ResourceFrameSchedule.toContinuation
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (schedule : ResourceFrameSchedule (input := input) (suffix := suffix)) :
    ResourceContinuationRefinement (input := input) (suffix := suffix) := by
  intro frame slot ready c' hstep haccept hhalt
  obtain ⟨action, hlookup, haction, reframe, hnextReady⟩ :=
    schedule frame slot ready c' hstep haccept hhalt
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro htrue
      have : ULogSemantics.halted c' = true := by simpa [haction] using htrue
      rw [this] at hhalt
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  have hbranch := branchedCycle_semanticLookupSome frame.config slot action
    hlookup input frame.clockZeros frame.capacity frame.runtime frame.outer
    suffix ready.runtime_passive ready.focus_lt_three ready.reads_lt_three
    ready.writes_lt_three ready.state_le_capacity
    (ready.capacity_ready slot action hlookup) htargetLower
    (ready.outer_ready slot action hlookup)
  have halign := clockReframe_align
    (c := ULogSemantics.applyAction frame.config action)
    (input := input)
    (capacity := semanticCapacityAfter frame.config action frame.capacity)
    (outer := semanticOuterAfter frame.config action frame.outer)
    (suffix := suffix) reframe
  refine ⟨action, hlookup, haction, reframe, hnextReady, ?_⟩
  rw [halign] at hbranch
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext] using
    hbranch

/-- The certified, canonical concrete image: its first field records that a
word is semantic, avoiding an unsupported claim about arbitrary junk runs. -/
def CanonicalConcreteAcceptingWords
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (t : ℕ) (frame : SemanticCycleFrame input suffix) : Type :=
  { w : List Bool // w ∈ acceptingSlotWords t frame.config ∧
    ConcreteAcceptingSlotTrace frame.encode w }

/-- The direct-terminal interface is impossible for a semantic cycle encoding:
such encodings are always running cycle-boundary configurations. -/
def DirectAcceptingTerminalEncoding
    (encode : ULogSemantics.Config → Result) : Prop :=
  ∀ ⦃c : ULogSemantics.Config⦄,
    ULogSemantics.halted c = true →
      ULogSemantics.accepting c = true → concreteAccepting (encode c) = true

theorem semanticCycleEncoding_not_concreteAccepting
    (input : List Bool) (clockCells : List ULogProgram.Tape) (capacity : ℕ)
    (outer suffix : List ULogProgram.Tape) (c : ULogSemantics.Config) :
    concreteAccepting
      (semanticCycleEncoding input clockCells capacity outer suffix c) = false := by
  rfl

theorem semanticCycleEncoding_not_directAcceptingTerminalEncoding
    (input : List Bool) (clockCells : List ULogProgram.Tape) (capacity : ℕ)
    (outer suffix : List ULogProgram.Tape) :
    ¬ DirectAcceptingTerminalEncoding
      (semanticCycleEncoding input clockCells capacity outer suffix) := by
  intro hdirect
  let c : ULogSemantics.Config :=
    ⟨[], ULogSemantics.acceptCode, [], ULogSemantics.blankCode, []⟩
  have hhalt : ULogSemantics.halted c = true := by
    simp [c, ULogSemantics.halted, ULogSemantics.acceptCode]
  have haccept : ULogSemantics.accepting c = true := by
    simp [c, ULogSemantics.accepting, ULogSemantics.acceptCode]
  have hconcrete := hdirect hhalt haccept
  simpa [c, concreteAccepting, semanticCycleEncoding] using hconcrete

theorem AcceptingSlotTrace.word_eq_nil_of_halted
    {t : ℕ} {c : ULogSemantics.Config} {w : List Bool}
    (htrace : AcceptingSlotTrace t c w)
    (hhalt : ULogSemantics.halted c = true) : w = [] := by
  cases t with
  | zero => exact htrace.1
  | succ t =>
      rcases htrace with hterminal | ⟨slot, c', rest, hw, hnotHalted, _, _⟩
      · exact hterminal.1
      · simp [hhalt] at hnotHalted

theorem AcceptingSlotTrace.false_of_halted_not_accepting
    {t : ℕ} {c : ULogSemantics.Config} {w : List Bool}
    (htrace : AcceptingSlotTrace t c w)
    (hhalt : ULogSemantics.halted c = true)
    (hnotAccept : ULogSemantics.accepting c = false) : False := by
  cases t with
  | zero => simpa [hnotAccept] using htrace.2.2
  | succ t =>
      rcases htrace with hterminal | ⟨slot, c', rest, hw, hnotHalted, _, _⟩
      · simpa [hnotAccept] using hterminal.2.2
      · simp [hhalt] at hnotHalted

/-- `SemanticConcreteCycleSpec` exposes the target-zero branch needed by an
outcome-valued refinement: an accepting semantic successor is directly
concretely accepted, not encoded as a further cycle boundary. -/
theorem semanticConcreteCycleSpec_accepting_outcome
    (c c' : ULogSemantics.Config) (slot : Bool)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List ULogProgram.Tape)
    (hcycle : SemanticConcreteCycleSpec c slot input clockZeros capacity
      runtime outer suffix)
    (hstep : ULogSemantics.stepSlot slot c = some c')
    (haccept : ULogSemantics.accepting c' = true) :
    ∃ z, BranchedReaches slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (.accepted z) := by
  obtain ⟨_, action, hlookup, haction⟩ :=
    ULogSemantics.stepSlot_some_rule hstep
  have hacceptAction :
      ULogSemantics.accepting (ULogSemantics.applyAction c action) = true := by
    simpa [haction] using haccept
  have htarget : action.target = 0 :=
    (accepting_applyAction_iff_target_zero c action).mp hacceptAction
  simpa [SemanticConcreteCycleSpec, hlookup, htarget] using hcycle

theorem acceptingSlotTrace_has_resource_concrete_accepting_trace
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (refineStep : ResourceContinuationRefinement (input := input) (suffix := suffix))
    (terminal : FrameAcceptingTerminal (input := input) (suffix := suffix))
    {t : ℕ} {frame : SemanticCycleFrame input suffix} {w : List Bool}
    (ready : FrameReady frame)
    (htrace : AcceptingSlotTrace t frame.config w) :
    ConcreteAcceptingSlotTrace frame.encode w := by
  induction t generalizing frame w with
  | zero =>
      rcases htrace with ⟨hw, hhalt, haccept⟩
      subst w
      obtain ⟨finish, hdispatch, hconcreteAccept⟩ :=
        terminal frame ready hhalt haccept
      exact ⟨frame.encode, .nil _, finish, hdispatch,
        concreteAccepting_halted hconcreteAccept, hconcreteAccept⟩
  | succ t ih =>
      rcases htrace with hterminal |
        ⟨slot, c', rest, hw, hnotHalted, hstep, htail⟩
      · rcases hterminal with ⟨hw, hhalt, haccept⟩
        subst w
        obtain ⟨finish, hdispatch, hconcreteAccept⟩ :=
          terminal frame ready hhalt haccept
        exact ⟨frame.encode, .nil _, finish, hdispatch,
          concreteAccepting_halted hconcreteAccept, hconcreteAccept⟩
      · subst w
        by_cases haccept : ULogSemantics.accepting c' = true
        · have hrest : rest = [] :=
            htail.word_eq_nil_of_halted
              (ULogSemantics.accepting_halted haccept)
          subst rest
          obtain ⟨z, hbranch⟩ := semanticConcreteCycleSpec_accepting_outcome
            frame.config c' slot input frame.clockZeros frame.capacity
            frame.runtime frame.outer suffix
            (ready.semanticConcreteCycleSpec frame slot) hstep haccept
          exact ⟨.accepted z,
            .cons frame.encode (.accepted z) (.accepted z) slot [] hbranch
              (.nil _),
            .accepted z, reaches_refl _, rfl, rfl⟩
        · by_cases hhalt : ULogSemantics.halted c' = true
          · have hacceptFalse : ULogSemantics.accepting c' = false := by
              cases hvalue : ULogSemantics.accepting c' <;> simp_all
            exact (htail.false_of_halted_not_accepting hhalt hacceptFalse).elim
          · have hacceptFalse : ULogSemantics.accepting c' = false := by
              cases hvalue : ULogSemantics.accepting c' <;> simp_all
            have hhaltFalse : ULogSemantics.halted c' = false := by
              cases hvalue : ULogSemantics.halted c' <;> simp_all
            obtain ⟨action, _, haction, reframe, hnextReady, hbranch⟩ :=
              refineStep frame slot ready c' hstep hacceptFalse hhaltFalse
            have htail' : AcceptingSlotTrace t
                (frame.reframeNext action reframe).config rest := by
              change AcceptingSlotTrace t
                (ULogSemantics.applyAction frame.config action) rest
              rw [haction]
              exact htail
            obtain ⟨cycleFinish, hrun, finish, hdispatch, hhalt, haccept'⟩ :=
              ih hnextReady htail'
            exact ⟨cycleFinish,
              .cons frame.encode (frame.reframeNext action reframe).encode
                cycleFinish slot rest hbranch hrun,
              finish, hdispatch, hhalt, haccept'⟩

theorem acceptingSlotWord_has_resource_concrete_accepting_trace
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (refineStep : ResourceContinuationRefinement (input := input) (suffix := suffix))
    (terminal : FrameAcceptingTerminal (input := input) (suffix := suffix))
    {t : ℕ} {frame : SemanticCycleFrame input suffix} {w : List Bool}
    (ready : FrameReady frame)
    (hw : w ∈ acceptingSlotWords t frame.config) :
    ConcreteAcceptingSlotTrace frame.encode w := by
  exact acceptingSlotTrace_has_resource_concrete_accepting_trace refineStep
    terminal ready ((mem_acceptingSlotWords_iff t frame.config w).mp hw)

/-- From a non-halting cycle frame, an accepting trace never uses the empty
halted branch: it must end in a target-zero cycle, which is concretely
accepted by `SemanticConcreteCycleSpec`. -/
theorem acceptingSlotTrace_has_resource_concrete_accepting_trace_of_not_halted
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (refineStep : ResourceContinuationRefinement (input := input) (suffix := suffix))
    {t : ℕ} {frame : SemanticCycleFrame input suffix} {w : List Bool}
    (ready : FrameReady frame)
    (hstart : ULogSemantics.halted frame.config = false)
    (htrace : AcceptingSlotTrace t frame.config w) :
    ConcreteAcceptingSlotTrace frame.encode w := by
  induction t generalizing frame w with
  | zero =>
      rcases htrace with ⟨hw, hhalt, haccept⟩
      simp [hstart] at hhalt
  | succ t ih =>
      rcases htrace with hterminal |
        ⟨slot, c', rest, hw, hnotHalted, hstep, htail⟩
      · rcases hterminal with ⟨hw, hhalt, haccept⟩
        simp [hstart] at hhalt
      · subst w
        by_cases haccept : ULogSemantics.accepting c' = true
        · have hrest : rest = [] :=
            htail.word_eq_nil_of_halted
              (ULogSemantics.accepting_halted haccept)
          subst rest
          obtain ⟨z, hbranch⟩ := semanticConcreteCycleSpec_accepting_outcome
            frame.config c' slot input frame.clockZeros frame.capacity
            frame.runtime frame.outer suffix
            (ready.semanticConcreteCycleSpec frame slot) hstep haccept
          exact ⟨.accepted z,
            .cons frame.encode (.accepted z) (.accepted z) slot [] hbranch
              (.nil _),
            .accepted z, reaches_refl _, rfl, rfl⟩
        · by_cases hhalt : ULogSemantics.halted c' = true
          · have hacceptFalse : ULogSemantics.accepting c' = false := by
              cases hvalue : ULogSemantics.accepting c' <;> simp_all
            exact (htail.false_of_halted_not_accepting hhalt hacceptFalse).elim
          · have hacceptFalse : ULogSemantics.accepting c' = false := by
              cases hvalue : ULogSemantics.accepting c' <;> simp_all
            have hhaltFalse : ULogSemantics.halted c' = false := by
              cases hvalue : ULogSemantics.halted c' <;> simp_all
            obtain ⟨action, _, haction, reframe, hnextReady, hbranch⟩ :=
              refineStep frame slot ready c' hstep hacceptFalse hhaltFalse
            have htail' : AcceptingSlotTrace t
                (frame.reframeNext action reframe).config rest := by
              change AcceptingSlotTrace t
                (ULogSemantics.applyAction frame.config action) rest
              rw [haction]
              exact htail
            have hnextStart :
                ULogSemantics.halted
                  (frame.reframeNext action reframe).config = false := by
              change ULogSemantics.halted
                (ULogSemantics.applyAction frame.config action) = false
              rw [haction]
              exact hhaltFalse
            obtain ⟨cycleFinish, hrun, finish, hdispatch, hhalt', haccept'⟩ :=
              ih hnextReady hnextStart htail'
            exact ⟨cycleFinish,
              .cons frame.encode (frame.reframeNext action reframe).encode
                cycleFinish slot rest hbranch hrun,
              finish, hdispatch, hhalt', haccept'⟩

theorem acceptingSlotWord_has_resource_concrete_accepting_trace_of_not_halted
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (refineStep : ResourceContinuationRefinement (input := input) (suffix := suffix))
    {t : ℕ} {frame : SemanticCycleFrame input suffix} {w : List Bool}
    (ready : FrameReady frame)
    (hstart : ULogSemantics.halted frame.config = false)
    (hw : w ∈ acceptingSlotWords t frame.config) :
    ConcreteAcceptingSlotTrace frame.encode w := by
  exact acceptingSlotTrace_has_resource_concrete_accepting_trace_of_not_halted
    refineStep ready hstart ((mem_acceptingSlotWords_iff t frame.config w).mp hw)

/-- The canonical, label-preserving concrete realization of semantic accepting
words.  Its codomain is certified semantic image, not the unrestricted class
of all microstep-reachability witnesses. -/
def semanticToCanonicalConcreteAccepting
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (t : ℕ) (frame : SemanticCycleFrame input suffix)
    (refineStep : ResourceContinuationRefinement (input := input) (suffix := suffix))
    (terminal : FrameAcceptingTerminal (input := input) (suffix := suffix))
    (ready : FrameReady frame) :
    SemanticAcceptingWords t frame.config →
      CanonicalConcreteAcceptingWords t frame :=
  fun w => ⟨w.1, w.2,
    acceptingSlotWord_has_resource_concrete_accepting_trace refineStep terminal ready
      w.2⟩

/-- The terminal-dispatch-free canonical map for a non-halting start frame. -/
def nonhaltingSemanticToCanonicalConcreteAccepting
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (t : ℕ) (frame : SemanticCycleFrame input suffix)
    (refineStep : ResourceContinuationRefinement (input := input) (suffix := suffix))
    (ready : FrameReady frame)
    (hstart : ULogSemantics.halted frame.config = false) :
    SemanticAcceptingWords t frame.config →
      CanonicalConcreteAcceptingWords t frame :=
  fun w => ⟨w.1, w.2,
    acceptingSlotWord_has_resource_concrete_accepting_trace_of_not_halted
      refineStep ready hstart w.2⟩

theorem nonhaltingSemanticToCanonicalConcreteAccepting_apply_val
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (t : ℕ) (frame : SemanticCycleFrame input suffix)
    (refineStep : ResourceContinuationRefinement (input := input) (suffix := suffix))
    (ready : FrameReady frame)
    (hstart : ULogSemantics.halted frame.config = false)
    (w : SemanticAcceptingWords t frame.config) :
    (nonhaltingSemanticToCanonicalConcreteAccepting t frame refineStep ready hstart w).1 =
      w.1 := rfl

theorem nonhaltingSemanticToCanonicalConcreteAccepting_injective
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (t : ℕ) (frame : SemanticCycleFrame input suffix)
    (refineStep : ResourceContinuationRefinement (input := input) (suffix := suffix))
    (ready : FrameReady frame)
    (hstart : ULogSemantics.halted frame.config = false) :
    Function.Injective
      (nonhaltingSemanticToCanonicalConcreteAccepting t frame refineStep ready
        hstart) := by
  intro x y hxy
  apply Subtype.ext
  simpa only [nonhaltingSemanticToCanonicalConcreteAccepting_apply_val] using
    congrArg (fun q : CanonicalConcreteAcceptingWords t frame => q.1) hxy

theorem semanticToCanonicalConcreteAccepting_apply_val
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (t : ℕ) (frame : SemanticCycleFrame input suffix)
    (refineStep : ResourceContinuationRefinement (input := input) (suffix := suffix))
    (terminal : FrameAcceptingTerminal (input := input) (suffix := suffix))
    (ready : FrameReady frame)
    (w : SemanticAcceptingWords t frame.config) :
    (semanticToCanonicalConcreteAccepting t frame refineStep terminal ready w).1 =
      w.1 := rfl

theorem semanticToCanonicalConcreteAccepting_injective
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (t : ℕ) (frame : SemanticCycleFrame input suffix)
    (refineStep : ResourceContinuationRefinement (input := input) (suffix := suffix))
    (terminal : FrameAcceptingTerminal (input := input) (suffix := suffix))
    (ready : FrameReady frame) :
    Function.Injective
      (semanticToCanonicalConcreteAccepting t frame refineStep terminal ready) := by
  intro x y hxy
  apply Subtype.ext
  simpa only [semanticToCanonicalConcreteAccepting_apply_val] using
    congrArg (fun q : CanonicalConcreteAcceptingWords t frame => q.1) hxy

/-- The exact bijection available without a no-spurious-run theorem: semantic
accepting words and their explicitly certified canonical concrete image. -/
def semanticCanonicalConcreteAcceptingEquiv
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (t : ℕ) (frame : SemanticCycleFrame input suffix)
    (refineStep : ResourceContinuationRefinement (input := input) (suffix := suffix))
    (terminal : FrameAcceptingTerminal (input := input) (suffix := suffix))
    (ready : FrameReady frame) :
    SemanticAcceptingWords t frame.config ≃
      CanonicalConcreteAcceptingWords t frame where
  toFun := semanticToCanonicalConcreteAccepting t frame refineStep terminal ready
  invFun := fun w => ⟨w.1, w.2.1⟩
  left_inv := by
    intro w
    apply Subtype.ext
    exact semanticToCanonicalConcreteAccepting_apply_val t frame refineStep
      terminal ready w
  right_inv := by
    intro w
    apply Subtype.ext
    exact semanticToCanonicalConcreteAccepting_apply_val t frame refineStep
      terminal ready ⟨w.1, w.2.1⟩

theorem semanticCanonicalConcreteAcceptingEquiv_apply_val
    {input : List Bool} {suffix : List ULogProgram.Tape}
    (t : ℕ) (frame : SemanticCycleFrame input suffix)
    (refineStep : ResourceContinuationRefinement (input := input) (suffix := suffix))
    (terminal : FrameAcceptingTerminal (input := input) (suffix := suffix))
    (ready : FrameReady frame)
    (w : SemanticAcceptingWords t frame.config) :
    (semanticCanonicalConcreteAcceptingEquiv t frame refineStep terminal ready w).1 =
      w.1 := rfl

end PakFixedPolyomino.ULogBootstrapExecution
