import PakFixedPolyomino.ULogConcreteNoSpurious

/-! Literal first-hit physical cycles from exactly their local FrameReady
requirements. No global per-tick capacity/outer reserve or remaining-cycle
count is assumed. A positive post-clock reframe remains explicit; the final
constructor obtains it internally from the actual decoded clock. Existing
audited source declarations are preserved. Physical time/ALL frames remain
separate obligations. -/

namespace PakFixedPolyomino.ULogActiveExactCycles
open ULogBootstrapExecution ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def ActivePositiveCycleCore {input : List Bool} {suffix : List Tape} : Type :=
  ∀ (frame : SemanticCycleFrame input suffix) (slot : Bool)
      (next : ULogSemantics.Config),
    FrameReady frame → PassivePath frame.runtime →
    ∀ (action : ULogBytecode.ActionCode),
      ULogBytecode.lookupRule frame.config.program frame.config.state frame.config.focus slot = some action →
      ULogSemantics.applyAction frame.config action = next →
      ULogSemantics.halted next = false →
      ∀ (reframe : ClockReframe
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        (clockCellsAfter ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
          frame.clockZeros frame.runtime)),
        ExactConcreteCycle slot frame.encode (frame.reframeNext action reframe).encode

noncomputable def exactPositiveCycleCore_stayAtMost
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (nextConfig : ULogSemantics.Config)
    (ready : FrameReady frame)
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = nextConfig)
    (hhalt : ULogSemantics.halted nextConfig = false)
    (extra : ℕ) (hstate : frame.config.state = action.target + extra)
    (hmove : action.move = .stay)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro hterminal
      rw [haction, hhalt] at hterminal
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  let hcycle := Classical.choice
    (exactCycle_semanticLookupSome_stayAtMost
      frame.config slot action hlookup input frame.clockZeros frame.capacity
      frame.runtime frame.outer suffix hruntime ready.focus_lt_three
      ready.reads_lt_three ready.writes_lt_three extra hstate
      ready.state_le_capacity htargetLower hmove)
  have hreframe := reframe.eq_before
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
    semanticCapacityAfter, semanticOuterAfter, hmove, hreframe]
    using hcycle

/-- The state-growth stay branch of the positive exact-cycle core. -/
noncomputable def exactPositiveCycleCore_stayAtLeast
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (nextConfig : ULogSemantics.Config)
    (ready : FrameReady frame)
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = nextConfig)
    (hhalt : ULogSemantics.halted nextConfig = false)
    (growth : ℕ) (htarget : action.target = frame.config.state + growth)
    (hmove : action.move = .stay)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro hterminal
      rw [haction, hhalt] at hterminal
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  have hcapacityReady :=
    ready.capacity_ready slot action hlookup
  have hcapacity : action.target ≤ frame.capacity := by
    simpa [SemanticCapacityReady, hmove] using hcapacityReady
  let hcycle := Classical.choice
    (exactCycle_semanticLookupSome_stayAtLeast
      frame.config slot action hlookup input frame.clockZeros frame.capacity
      frame.runtime frame.outer suffix hruntime ready.focus_lt_three
      ready.reads_lt_three ready.writes_lt_three growth htarget
      hcapacity htargetLower hmove)
  have hreframe := reframe.eq_before
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
    semanticCapacityAfter, semanticOuterAfter, hmove, hreframe]
    using hcycle

/-- The state-growth/internal-left branch of the positive exact-cycle core.
The nonempty left tape supplies the physical endpoint moved under the head;
the provided positive-clock reframe identifies the literal post-cycle clock
with the next resource frame. -/
noncomputable def exactPositiveCycleCore_leftInternalAtLeast
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (nextConfig : ULogSemantics.Config)
    (ready : FrameReady frame)
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = nextConfig)
    (hhalt : ULogSemantics.halted nextConfig = false)
    (next : ℕ) (leftTail : List ℕ)
    (hleft : frame.config.leftRev = next :: leftTail)
    (growth : ℕ) (htarget : action.target = frame.config.state + growth)
    (hmove : action.move = .left)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro hterminal
      rw [haction, hhalt] at hterminal
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  have hcapacityReady :=
    ready.capacity_ready slot action hlookup
  have hcapacity : action.target ≤ frame.capacity := by
    simpa [SemanticCapacityReady, hmove, hleft] using hcapacityReady
  let hcycle := Classical.choice
    (exactCycle_semanticLookupSome_leftInternalAtLeast
      frame.config slot action hlookup next leftTail hleft input
      frame.clockZeros frame.capacity frame.runtime frame.outer suffix hruntime
      ready.focus_lt_three ready.reads_lt_three
      ready.writes_lt_three growth htarget hcapacity htargetLower hmove)
  have hreframe := reframe.eq_before
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
    semanticCapacityAfter, semanticOuterAfter, hmove, hleft, hreframe]
    using hcycle

/-- The shrinking/equal-target internal-left branch of the positive exact
cycle core.  Moving the physical left endpoint under the head preserves the
capacity, and released state cells remain available as workspace. -/
noncomputable def exactPositiveCycleCore_leftInternalAtMost
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (nextConfig : ULogSemantics.Config)
    (ready : FrameReady frame)
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = nextConfig)
    (hhalt : ULogSemantics.halted nextConfig = false)
    (next : ℕ) (leftTail : List ℕ)
    (hleft : frame.config.leftRev = next :: leftTail)
    (extra : ℕ) (hstate : frame.config.state = action.target + extra)
    (hmove : action.move = .left)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro hterminal
      rw [haction, hhalt] at hterminal
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  let hcycle := Classical.choice
    (exactCycle_semanticLookupSome_leftInternalAtMost
      frame.config slot action hlookup next leftTail hleft input
      frame.clockZeros frame.capacity frame.runtime frame.outer suffix hruntime
      ready.focus_lt_three ready.reads_lt_three
      ready.writes_lt_three extra hstate ready.state_le_capacity
      htargetLower hmove)
  have hreframe := reframe.eq_before
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
    semanticCapacityAfter, semanticOuterAfter, hmove, hleft, hreframe]
    using hcycle

/-- The shrinking/equal-target internal-right branch of the positive exact
cycle core.  The nonempty right tape supplies the cell moved under the head,
while the released state cells stay inside the unchanged capacity. -/
noncomputable def exactPositiveCycleCore_rightInternalAtMost
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (nextConfig : ULogSemantics.Config)
    (ready : FrameReady frame)
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = nextConfig)
    (hhalt : ULogSemantics.halted nextConfig = false)
    (next : ℕ) (rightTail : List ℕ)
    (hright : frame.config.right = next :: rightTail)
    (extra : ℕ) (hstate : frame.config.state = action.target + extra)
    (hmove : action.move = .right)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro hterminal
      rw [haction, hhalt] at hterminal
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  let hcycle := Classical.choice
    (exactCycle_semanticLookupSome_rightInternalAtMost
      frame.config slot action hlookup next rightTail hright input
      frame.clockZeros frame.capacity frame.runtime frame.outer suffix hruntime
      ready.focus_lt_three ready.reads_lt_three
      ready.writes_lt_three extra hstate ready.state_le_capacity
      htargetLower hmove)
  have hreframe := reframe.eq_before
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
    semanticCapacityAfter, semanticOuterAfter, hmove, hright, hreframe]
    using hcycle

/-- The state-growth/internal-right branch of the positive exact-cycle core.
It consumes the current passive runtime explicitly and uses nonhalting of the
semantic successor to exclude the concrete target-zero/target-one terminal
dispatches. -/
noncomputable def exactPositiveCycleCore_rightInternalAtLeast
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (nextConfig : ULogSemantics.Config)
    (ready : FrameReady frame)
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = nextConfig)
    (hhalt : ULogSemantics.halted nextConfig = false)
    (next : ℕ) (rightTail : List ℕ)
    (hright : frame.config.right = next :: rightTail)
    (growth : ℕ) (htarget : action.target = frame.config.state + growth)
    (hmove : action.move = .right)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro hterminal
      rw [haction, hhalt] at hterminal
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  have hcapacityReady :=
    ready.capacity_ready slot action hlookup
  have hcapacity : action.target ≤ frame.capacity := by
    simpa [SemanticCapacityReady, hmove, hright] using hcapacityReady
  let hcycle := Classical.choice
    (exactCycle_semanticLookupSome_rightInternalAtLeast
      frame.config slot action hlookup next rightTail hright input
      frame.clockZeros frame.capacity frame.runtime frame.outer suffix hruntime
      ready.focus_lt_three ready.reads_lt_three
      ready.writes_lt_three growth htarget hcapacity htargetLower hmove)
  have hreframe := reframe.eq_before
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
    semanticCapacityAfter, semanticOuterAfter, hmove, hright, hreframe]
    using hcycle

/-- The strictly shrinking/right-boundary branch of the positive exact-cycle
core.  One released state cell is consumed by the boundary extension, so the
semantic capacity drops by one. -/
noncomputable def exactPositiveCycleCore_rightBoundaryAtMost
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (nextConfig : ULogSemantics.Config)
    (ready : FrameReady frame)
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = nextConfig)
    (hhalt : ULogSemantics.halted nextConfig = false)
    (hright : frame.config.right = [])
    (extra : ℕ)
    (hstate : frame.config.state = action.target + (extra + 1))
    (hmove : action.move = .right)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro hterminal
      rw [haction, hhalt] at hterminal
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  have hcapacityReady :=
    ready.capacity_ready slot action hlookup
  have hcapacity : action.target < frame.capacity := by
    simpa [SemanticCapacityReady, hmove, hright] using hcapacityReady
  let hcycle := Classical.choice
    (exactCycle_semanticLookupSome_rightBoundaryAtMost
      frame.config slot action hlookup hright input frame.clockZeros
      frame.capacity frame.runtime frame.outer suffix hruntime
      ready.focus_lt_three ready.reads_lt_three
      ready.writes_lt_three extra hstate ready.state_le_capacity
      htargetLower hmove)
  have hreframeNil :
      clockCellsBefore [] reframe.zeros reframe.runtime =
        clockCellsAfter [] frame.clockZeros frame.runtime := by
    simpa [ULogSemantics.applyAction, hmove, hright] using reframe.eq_before
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
    semanticCapacityAfter, semanticOuterAfter, ULogSemantics.applyAction,
    hmove, hright, hreframeNil]
    using hcycle

/-- The state-growth/right-boundary branch of the positive exact-cycle core.
The resource invariant supplies the strict target bound needed after the
boundary shift consumes one capacity cell, and the supplied clock reframe
identifies the literal post-cycle clock with the next semantic frame. -/
noncomputable def exactPositiveCycleCore_rightBoundaryAtLeast
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (nextConfig : ULogSemantics.Config)
    (ready : FrameReady frame)
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = nextConfig)
    (hhalt : ULogSemantics.halted nextConfig = false)
    (hright : frame.config.right = [])
    (growth : ℕ) (htarget : action.target = frame.config.state + growth)
    (hmove : action.move = .right)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro hterminal
      rw [haction, hhalt] at hterminal
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  have hcapacityReady :=
    ready.capacity_ready slot action hlookup
  have hcapacity : action.target < frame.capacity := by
    simpa [SemanticCapacityReady, hmove, hright] using hcapacityReady
  let hcycle := Classical.choice
    (exactCycle_semanticLookupSome_rightBoundaryAtLeast
      frame.config slot action hlookup hright input frame.clockZeros
      frame.capacity frame.runtime frame.outer suffix hruntime
      ready.focus_lt_three ready.reads_lt_three
      ready.writes_lt_three growth htarget hcapacity htargetLower hmove)
  have hreframeNil :
      clockCellsBefore [] reframe.zeros reframe.runtime =
        clockCellsAfter [] frame.clockZeros frame.runtime := by
    simpa [ULogSemantics.applyAction, hmove, hright] using reframe.eq_before
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
    semanticCapacityAfter, semanticOuterAfter, ULogSemantics.applyAction,
    hmove, hright, hreframeNil]
    using hcycle

/-- The strictly shrinking/left-boundary branch of the positive exact-cycle
core.  `SemanticOuterReady` supplies the physical leading `work` cell consumed
by the boundary extension, while released state cells keep the semantic
capacity unchanged. -/
noncomputable def exactPositiveCycleCore_leftBoundaryAtMost
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (nextConfig : ULogSemantics.Config)
    (ready : FrameReady frame)
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = nextConfig)
    (hhalt : ULogSemantics.halted nextConfig = false)
    (hleft : frame.config.leftRev = [])
    (extra : ℕ)
    (hstate : frame.config.state = action.target + (extra + 1))
    (hmove : action.move = .left)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro hterminal
      rw [haction, hhalt] at hterminal
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  have houterReady := ready.outer_ready slot action hlookup
  have hex : ∃ tail,
      frame.outer = MStarConcreteAlphabet.work :: tail := by
    simpa [SemanticOuterReady, hmove, hleft] using houterReady
  let outerTail := Classical.choose hex
  have houter : frame.outer = MStarConcreteAlphabet.work :: outerTail :=
    Classical.choose_spec hex
  let hcycle := Classical.choice
    (exactCycle_semanticLookupSome_leftBoundaryAtMost
      frame.config slot action hlookup hleft input frame.clockZeros
      frame.capacity frame.runtime outerTail suffix hruntime
      ready.focus_lt_three ready.reads_lt_three
      ready.writes_lt_three extra hstate ready.state_le_capacity
      htargetLower hmove)
  have hreframe := reframe.eq_before
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
    semanticCapacityAfter, semanticOuterAfter, hmove, hleft, houter, hreframe]
    using hcycle

/-- The state-growth/left-boundary branch of the positive exact-cycle core.
`SemanticOuterReady` supplies the physical leading `work` cell consumed by
the boundary extension; unlike a right-boundary extension, the semantic
capacity is unchanged. -/
noncomputable def exactPositiveCycleCore_leftBoundaryAtLeast
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (nextConfig : ULogSemantics.Config)
    (ready : FrameReady frame)
    (hruntime : PassivePath frame.runtime)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (haction : ULogSemantics.applyAction frame.config action = nextConfig)
    (hhalt : ULogSemantics.halted nextConfig = false)
    (hleft : frame.config.leftRev = [])
    (growth : ℕ) (htarget : action.target = frame.config.state + growth)
    (hmove : action.move = .left)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    ExactConcreteCycle slot frame.encode
      (frame.reframeNext action reframe).encode := by
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro hterminal
      rw [haction, hhalt] at hterminal
      contradiction
    have hnlt : ¬ action.target < 2 := fun ht =>
      hnot ((halted_applyAction_iff_target_lt_two frame.config action).mpr ht)
    omega
  have hcapacityReady := ready.capacity_ready slot action hlookup
  have hcapacity : action.target ≤ frame.capacity := by
    simpa [SemanticCapacityReady, hmove] using hcapacityReady
  have houterReady := ready.outer_ready slot action hlookup
  have hex : ∃ tail,
      frame.outer = MStarConcreteAlphabet.work :: tail := by
    simpa [SemanticOuterReady, hmove, hleft] using houterReady
  let outerTail := Classical.choose hex
  have houter : frame.outer = MStarConcreteAlphabet.work :: outerTail :=
    Classical.choose_spec hex
  let hcycle := Classical.choice
    (exactCycle_semanticLookupSome_leftBoundaryAtLeast
      frame.config slot action hlookup hleft input frame.clockZeros
      frame.capacity frame.runtime outerTail suffix hruntime
      ready.focus_lt_three ready.reads_lt_three
      ready.writes_lt_three growth htarget hcapacity htargetLower hmove)
  have hreframe := reframe.eq_before
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext,
    semanticCapacityAfter, semanticOuterAfter, hmove, hleft, houter, hreframe]
    using hcycle

/-- Total concrete dispatch for a positive nonhalting semantic cycle.  A
strictly smaller target uses the corresponding `AtMost` realization, while
an equal or larger target uses `AtLeast`; moving branches are further split
according to whether the tape in the direction of travel is empty. -/
noncomputable def concreteExactPositiveCycleCore
    {input : List Bool} {suffix : List Tape} :
    ActivePositiveCycleCore (input := input) (suffix := suffix) := by
  intro frame slot nextConfig ready hruntime action hlookup haction
    hhalt reframe
  cases hmove : action.move with
  | stay =>
      by_cases htarget : action.target < frame.config.state
      · let extra := frame.config.state - action.target - 1
        have hstate :
            frame.config.state = action.target + (extra + 1) := by
          dsimp [extra]
          omega
        exact exactPositiveCycleCore_stayAtMost frame slot nextConfig ready hruntime action hlookup haction hhalt (extra + 1) hstate
          hmove reframe
      · let growth := action.target - frame.config.state
        have htargetEq :
            action.target = frame.config.state + growth := by
          dsimp [growth]
          omega
        exact exactPositiveCycleCore_stayAtLeast frame slot nextConfig ready hruntime action hlookup haction hhalt growth htargetEq
          hmove reframe
  | right =>
      cases hright : frame.config.right with
      | nil =>
          by_cases htarget : action.target < frame.config.state
          · let extra := frame.config.state - action.target - 1
            have hstate :
                frame.config.state = action.target + (extra + 1) := by
              dsimp [extra]
              omega
            exact exactPositiveCycleCore_rightBoundaryAtMost frame slot
              nextConfig ready hruntime action hlookup haction hhalt
              hright extra hstate hmove reframe
          · let growth := action.target - frame.config.state
            have htargetEq :
                action.target = frame.config.state + growth := by
              dsimp [growth]
              omega
            exact exactPositiveCycleCore_rightBoundaryAtLeast frame slot
              nextConfig ready hruntime action hlookup haction hhalt
              hright growth htargetEq hmove reframe
      | cons next rightTail =>
          by_cases htarget : action.target < frame.config.state
          · let extra := frame.config.state - action.target - 1
            have hstate :
                frame.config.state = action.target + (extra + 1) := by
              dsimp [extra]
              omega
            exact exactPositiveCycleCore_rightInternalAtMost frame slot
              nextConfig ready hruntime action hlookup haction hhalt
              next rightTail hright (extra + 1) hstate hmove reframe
          · let growth := action.target - frame.config.state
            have htargetEq :
                action.target = frame.config.state + growth := by
              dsimp [growth]
              omega
            exact exactPositiveCycleCore_rightInternalAtLeast frame slot
              nextConfig ready hruntime action hlookup haction hhalt
              next rightTail hright growth htargetEq hmove reframe
  | left =>
      cases hleft : frame.config.leftRev with
      | nil =>
          by_cases htarget : action.target < frame.config.state
          · let extra := frame.config.state - action.target - 1
            have hstate :
                frame.config.state = action.target + (extra + 1) := by
              dsimp [extra]
              omega
            exact exactPositiveCycleCore_leftBoundaryAtMost frame slot
              nextConfig ready hruntime action hlookup haction hhalt
              hleft extra hstate hmove reframe
          · let growth := action.target - frame.config.state
            have htargetEq :
                action.target = frame.config.state + growth := by
              dsimp [growth]
              omega
            exact exactPositiveCycleCore_leftBoundaryAtLeast frame slot
              nextConfig ready hruntime action hlookup haction hhalt
              hleft growth htargetEq hmove reframe
      | cons next leftTail =>
          by_cases htarget : action.target < frame.config.state
          · let extra := frame.config.state - action.target - 1
            have hstate :
                frame.config.state = action.target + (extra + 1) := by
              dsimp [extra]
              omega
            exact exactPositiveCycleCore_leftInternalAtMost frame slot
              nextConfig ready hruntime action hlookup haction hhalt
              next leftTail hleft (extra + 1) hstate hmove reframe
          · let growth := action.target - frame.config.state
            have htargetEq :
                action.target = frame.config.state + growth := by
              dsimp [growth]
              omega
            exact exactPositiveCycleCore_leftInternalAtLeast frame slot
              nextConfig ready hruntime action hlookup haction hhalt
              next leftTail hleft growth htargetEq hmove reframe


noncomputable def positive_continuation
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (next : ULogSemantics.Config) (budget : Nat) (ready : FrameReady frame)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some budget)
    (hbudget : 1 < budget)
    (hstep : ULogSemantics.stepSlot slot frame.config = some next)
    (hhalt : ULogSemantics.halted next = false) :
    ExactPositiveResourceContinuation frame slot next (budget - 1) := by
  let actionWitness := Classical.indefiniteDescription _
    (ULogSemantics.stepSlot_some_rule hstep).2
  let action := actionWitness.1
  have hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action := actionWitness.2.1
  have haction : ULogSemantics.applyAction frame.config action = next := actionWitness.2.2
  have hafter := decodeBinaryClock_after_eq_pred frame.clockZeros frame.runtime budget hclock
  let reframeWitness := Classical.indefiniteDescription _
    (exists_clockReframe_of_positive_binaryClock
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      frame.clockZeros frame.runtime ready.runtime_passive
      (budget - 1) hafter (by omega))
  let reframe := reframeWitness.1
  exact
    { action := action
      reframe := reframe
      lookup := hlookup
      action_eq := haction
      clock_decoded := reframeWitness.2
      exact_cycle := concreteExactPositiveCycleCore frame slot next ready
        ready.runtime_passive action hlookup haction hhalt reframe }

end PakFixedPolyomino.ULogActiveExactCycles
