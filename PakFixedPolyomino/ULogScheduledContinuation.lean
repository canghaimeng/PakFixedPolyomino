import PakFixedPolyomino.ULogFrameReady

/-! Trace-indexed continuation from the initialized binary clock.

This file avoids a global resource claim over arbitrary frames.  It constructs
each continuing concrete step from the clock value carried by that frame and
an explicit non-clock preservation obligation.  The latter can be discharged
from uniform program bounds plus the genuinely dynamic capacity/outer facts. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem decodeBinaryClock_before_positive
    (zeros : ℕ) (runtime : List Tape) (value : ℕ)
    (hdecode : decodeBinaryClock
      (List.replicate zeros (ulogCore clockZero) ++
        ulogCore clockOne :: runtime) = some value) :
    0 < value := by
  induction zeros generalizing value with
  | zero =>
      have honeSep : ulogCore clockOne ≠ ulogCore clockSep :=
        ULogTapeDecoding.ulog_symbol_ne (by decide)
      have honeZero : ulogCore clockOne ≠ ulogCore clockZero :=
        ULogTapeDecoding.ulog_symbol_ne (by decide)
      cases htail : decodeBinaryClock runtime with
      | none => simp [decodeBinaryClock, honeSep, honeZero, htail] at hdecode
      | some tailValue =>
          have : 1 + 2 * tailValue = value := by
            simpa [decodeBinaryClock, honeSep, honeZero, htail] using hdecode
          omega
  | succ zeros ih =>
      rw [List.replicate_succ] at hdecode
      have hzeroSep : ulogCore clockZero ≠ ulogCore clockSep :=
        ULogTapeDecoding.ulog_symbol_ne (by decide)
      cases htail : decodeBinaryClock
          (List.replicate zeros (ulogCore clockZero) ++
            ulogCore clockOne :: runtime) with
      | none => simp [decodeBinaryClock, hzeroSep, htail] at hdecode
      | some tailValue =>
          have hvalue : 2 * tailValue = value := by
            simpa [decodeBinaryClock, hzeroSep, htail] using hdecode
          have := ih tailValue htail
          omega

/-- The concrete clock rewrite really is subtraction by one, for every
canonical before-clock split (not merely for the initial power of two). -/
theorem decodeBinaryClock_after_eq_pred
    (zeros : ℕ) (runtime : List Tape) (value : ℕ)
    (hdecode : decodeBinaryClock
      (List.replicate zeros (ulogCore clockZero) ++
        ulogCore clockOne :: runtime) = some value) :
    decodeBinaryClock
      (List.replicate zeros (ulogCore clockOne) ++
        ulogCore clockZero :: runtime) = some (value - 1) := by
  induction zeros generalizing value with
  | zero =>
      have honeSep : ulogCore clockOne ≠ ulogCore clockSep :=
        ULogTapeDecoding.ulog_symbol_ne (by decide)
      have honeZero : ulogCore clockOne ≠ ulogCore clockZero :=
        ULogTapeDecoding.ulog_symbol_ne (by decide)
      have hzeroSep : ulogCore clockZero ≠ ulogCore clockSep :=
        ULogTapeDecoding.ulog_symbol_ne (by decide)
      cases htail : decodeBinaryClock runtime with
      | none => simp [decodeBinaryClock, honeSep, honeZero, htail] at hdecode
      | some tailValue =>
          have hvalue : 1 + 2 * tailValue = value := by
            simpa [decodeBinaryClock, honeSep, honeZero, htail] using hdecode
          simp [decodeBinaryClock, hzeroSep, htail]
          omega
  | succ zeros ih =>
      rw [List.replicate_succ] at hdecode ⊢
      have hzeroSep : ulogCore clockZero ≠ ulogCore clockSep :=
        ULogTapeDecoding.ulog_symbol_ne (by decide)
      have honeSep : ulogCore clockOne ≠ ulogCore clockSep :=
        ULogTapeDecoding.ulog_symbol_ne (by decide)
      have honeZero : ulogCore clockOne ≠ ulogCore clockZero :=
        ULogTapeDecoding.ulog_symbol_ne (by decide)
      cases htail : decodeBinaryClock
          (List.replicate zeros (ulogCore clockZero) ++
            ulogCore clockOne :: runtime) with
      | none => simp [decodeBinaryClock, hzeroSep, htail] at hdecode
      | some tailValue =>
          have hvalue : 2 * tailValue = value := by
            simpa [decodeBinaryClock, hzeroSep, htail] using hdecode
          have htailPositive := decodeBinaryClock_before_positive zeros runtime
            tailValue htail
          have hafter := ih tailValue htail
          have hhead :
              decodeBinaryClock
                (ulogCore clockOne ::
                  (List.replicate zeros (ulogCore clockOne) ++
                    ulogCore clockZero :: runtime)) =
                (decodeBinaryClock
                  (List.replicate zeros (ulogCore clockOne) ++
                    ulogCore clockZero :: runtime)).map
                    (fun n => 1 + 2 * n) := by
            simp [decodeBinaryClock, honeSep, honeZero]
          change decodeBinaryClock
              (ulogCore clockOne ::
                (List.replicate zeros (ulogCore clockOne) ++
                  ulogCore clockZero :: runtime)) = some (value - 1)
          rw [hhead, hafter]
          simp
          omega

@[simp] theorem applyAction_program_eq
    (c : ULogSemantics.Config) (action : ULogBytecode.ActionCode) :
    (ULogSemantics.applyAction c action).program = c.program := by
  cases hm : action.move with
  | stay => simp [ULogSemantics.applyAction, hm]
  | right => cases hr : c.right <;> simp [ULogSemantics.applyAction, hm, hr]
  | left => cases hl : c.leftRev <;> simp [ULogSemantics.applyAction, hm, hl]

/-- Uniform program facts are preserved automatically.  Only the dynamically
changing focus, capacity reserve, and left-boundary outer reserve remain as
explicit obligations. -/
theorem nextNonClockReady_of_uniformProgramBounds
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (hprogram : frame.config.program ≠ [])
    (hreads : ∀ r ∈ frame.config.program, r.read < 3)
    (hwrites : ∀ r ∈ frame.config.program, r.action.write < 3)
    (hfocusNext : (ULogSemantics.applyAction frame.config action).focus < 3)
    (htargetsNext : ∀ r ∈ frame.config.program,
      r.action.target < semanticCapacityAfter frame.config action frame.capacity)
    (hleftBoundaryNext :
      (ULogSemantics.applyAction frame.config action).leftRev = [] →
        ∃ tail, semanticOuterAfter frame.config action frame.outer =
          MStarConcreteAlphabet.work :: tail) :
    NextNonClockReady frame action := by
  unfold NextNonClockReady
  refine
    { focus_lt_three := hfocusNext
      program_nonempty := ?_
      reads_lt_three := ?_
      writes_lt_three := ?_
      state_le_capacity := ?_
      capacity_ready := ?_
      outer_ready := ?_ }
  · simpa using hprogram
  · intro r hr
    exact hreads r (by simpa using hr)
  · intro r hr
    exact hwrites r (by simpa using hr)
  · obtain ⟨r, hr, _, _, _, haction⟩ :=
      ULogBytecode.lookupRule_some_mem hlookup
    rw [applyAction_state]
    exact Nat.le_of_lt (by
      simpa only [haction] using htargetsNext r hr)
  · intro nextSlot nextAction hnextLookup
    obtain ⟨r, hr, _, _, _, haction⟩ :=
      ULogBytecode.lookupRule_some_mem hnextLookup
    have htarget : nextAction.target <
        semanticCapacityAfter frame.config action frame.capacity := by
      rw [← haction]
      exact htargetsNext r (by simpa using hr)
    unfold SemanticCapacityReady
    cases hm : nextAction.move with
    | stay => omega
    | left => omega
    | right =>
        cases (ULogSemantics.applyAction frame.config action).right with
        | nil => simpa [hm] using htarget
        | cons x xs => simpa [hm] using Nat.le_of_lt htarget
  · intro nextSlot nextAction hnextLookup
    unfold SemanticOuterReady
    cases hm : nextAction.move with
    | stay => trivial
    | right => trivial
    | left =>
        cases hl : (ULogSemantics.applyAction frame.config action).leftRev with
        | nil => exact hleftBoundaryNext hl
        | cons x xs => trivial

/-- Every semantic tape symbol is in the three-symbol data alphabet. -/
structure SemanticTapeSymbolsLtThree (c : ULogSemantics.Config) : Prop where
  focus : c.focus < 3
  left : ∀ x ∈ c.leftRev, x < 3
  right : ∀ x ∈ c.right, x < 3

theorem SemanticTapeSymbolsLtThree.applyAction
    (c : ULogSemantics.Config) (action : ULogBytecode.ActionCode)
    (bounded : SemanticTapeSymbolsLtThree c)
    (hwrite : action.write < 3) :
    SemanticTapeSymbolsLtThree (ULogSemantics.applyAction c action) := by
  cases hm : action.move with
  | stay =>
      exact
        { focus := by simpa [ULogSemantics.applyAction, hm] using hwrite
          left := by simpa [ULogSemantics.applyAction, hm] using bounded.left
          right := by simpa [ULogSemantics.applyAction, hm] using bounded.right }
  | right =>
      cases hr : c.right with
      | nil =>
          refine
            { focus := by
                simp [ULogSemantics.applyAction, hm, hr,
                  ULogSemantics.blankCode]
              left := ?_
              right := by simp [ULogSemantics.applyAction, hm, hr] }
          intro x hx
          simp [ULogSemantics.applyAction, hm, hr] at hx
          rcases hx with rfl | hx
          · exact hwrite
          · exact bounded.left x hx
      | cons y ys =>
          have hy : y < 3 := bounded.right y (by simp [hr])
          refine
            { focus := by simpa [ULogSemantics.applyAction, hm, hr] using hy
              left := ?_
              right := ?_ }
          · intro x hx
            simp [ULogSemantics.applyAction, hm, hr] at hx
            rcases hx with rfl | hx
            · exact hwrite
            · exact bounded.left x hx
          · intro x hx
            have hxys : x ∈ ys := by
              simpa [ULogSemantics.applyAction, hm, hr] using hx
            apply bounded.right x
            rw [hr]
            exact List.mem_cons_of_mem y hxys
  | left =>
      cases hl : c.leftRev with
      | nil =>
          refine
            { focus := by
                simp [ULogSemantics.applyAction, hm, hl,
                  ULogSemantics.blankCode]
              left := by simp [ULogSemantics.applyAction, hm, hl]
              right := ?_ }
          intro x hx
          simp [ULogSemantics.applyAction, hm, hl] at hx
          rcases hx with rfl | hx
          · exact hwrite
          · exact bounded.right x hx
      | cons y ys =>
          have hy : y < 3 := bounded.left y (by simp [hl])
          refine
            { focus := by simpa [ULogSemantics.applyAction, hm, hl] using hy
              left := ?_
              right := ?_ }
          · intro x hx
            have hxys : x ∈ ys := by
              simpa [ULogSemantics.applyAction, hm, hl] using hx
            apply bounded.left x
            rw [hl]
            exact List.mem_cons_of_mem y hxys
          · intro x hx
            simp [ULogSemantics.applyAction, hm, hl] at hx
            rcases hx with rfl | hx
            · exact hwrite
            · exact bounded.right x hx

/-- Capacity and outer reserves indexed by the number of semantic cycles
still available.  The extra outer cell is exactly what `FrameReady` needs at
a possible left boundary. -/
structure FrameResourceInvariant
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (steps : ℕ) : Prop where
  tape_bounded : SemanticTapeSymbolsLtThree frame.config
  program_nonempty : frame.config.program ≠ []
  reads_lt_three : ∀ r ∈ frame.config.program, r.read < 3
  writes_lt_three : ∀ r ∈ frame.config.program, r.action.write < 3
  state_le_capacity : frame.config.state ≤ frame.capacity
  target_capacity_reserve : ∀ r ∈ frame.config.program,
    r.action.target + steps < frame.capacity
  outer_work_reserve : ∃ tail,
    frame.outer =
      List.replicate (steps + 1) MStarConcreteAlphabet.work ++ tail

theorem FrameResourceInvariant.frameReady
    {input : List Bool} {suffix : List Tape}
    {frame : SemanticCycleFrame input suffix} {steps : ℕ}
    (resources : FrameResourceInvariant frame steps)
    (hruntime : PassivePath frame.runtime) : FrameReady frame := by
  apply FrameReady.ofUniformBounds frame hruntime resources.tape_bounded.focus
    resources.program_nonempty resources.reads_lt_three
    resources.writes_lt_three resources.state_le_capacity
  · intro r hr
    have := resources.target_capacity_reserve r hr
    omega
  · intro _
    obtain ⟨tail, houter⟩ := resources.outer_work_reserve
    refine ⟨List.replicate steps MStarConcreteAlphabet.work ++ tail, ?_⟩
    simpa [List.replicate_succ, List.append_assoc] using houter

theorem targetCapacityReserve_after
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix)
    (action : ULogBytecode.ActionCode) (steps : ℕ)
    (hreserve : ∀ r ∈ frame.config.program,
      r.action.target + (steps + 1) < frame.capacity) :
    ∀ r ∈ (ULogSemantics.applyAction frame.config action).program,
      r.action.target + steps <
        semanticCapacityAfter frame.config action frame.capacity := by
  intro r hr
  have hold := hreserve r (by simpa using hr)
  unfold semanticCapacityAfter
  cases hm : action.move with
  | stay => simpa [hm] using (show r.action.target + steps < frame.capacity by omega)
  | left => simpa [hm] using (show r.action.target + steps < frame.capacity by omega)
  | right =>
      cases hright : frame.config.right with
      | nil =>
          simp [hm, hright]
          omega
      | cons x xs =>
          simpa [hm, hright] using
            (show r.action.target + steps < frame.capacity by omega)

theorem outerWorkReserve_after
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix)
    (action : ULogBytecode.ActionCode) (steps : ℕ)
    (hreserve : ∃ tail,
      frame.outer = List.replicate (steps + 2)
        MStarConcreteAlphabet.work ++ tail) :
    ∃ tail,
      semanticOuterAfter frame.config action frame.outer =
        List.replicate (steps + 1) MStarConcreteAlphabet.work ++ tail := by
  obtain ⟨tail, houter⟩ := hreserve
  unfold semanticOuterAfter
  cases hm : action.move with
  | stay =>
      refine ⟨MStarConcreteAlphabet.work :: tail, ?_⟩
      simpa [hm, List.replicate_succ, List.append_assoc] using houter
  | right =>
      refine ⟨MStarConcreteAlphabet.work :: tail, ?_⟩
      simpa [hm, List.replicate_succ, List.append_assoc] using houter
  | left =>
      cases hleft : frame.config.leftRev with
      | nil =>
          refine ⟨tail, ?_⟩
          rw [houter]
          simp [hm, hleft, List.replicate_succ, List.append_assoc]
      | cons x xs =>
          refine ⟨MStarConcreteAlphabet.work :: tail, ?_⟩
          simpa [hm, hleft, List.replicate_succ, List.append_assoc] using houter

theorem FrameResourceInvariant.next
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix)
    (slot : Bool) (action : ULogBytecode.ActionCode) (steps : ℕ)
    (resources : FrameResourceInvariant frame (steps + 1))
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    FrameResourceInvariant (frame.reframeNext action reframe) steps := by
  obtain ⟨matched, hmatchedMem, _, _, _, hmatchedAction⟩ :=
    ULogBytecode.lookupRule_some_mem hlookup
  have hwrite : action.write < 3 := by
    rw [← hmatchedAction]
    exact resources.writes_lt_three matched hmatchedMem
  have htargets := targetCapacityReserve_after frame action steps
    resources.target_capacity_reserve
  have hactionCapacity : action.target <
      semanticCapacityAfter frame.config action frame.capacity := by
    have h := htargets matched (by simpa using hmatchedMem)
    rw [hmatchedAction] at h
    omega
  have houter : ∃ tail,
      semanticOuterAfter frame.config action frame.outer =
        List.replicate (steps + 1) MStarConcreteAlphabet.work ++ tail := by
    apply outerWorkReserve_after frame action steps
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      resources.outer_work_reserve
  refine
    { tape_bounded := ?_
      program_nonempty := ?_
      reads_lt_three := ?_
      writes_lt_three := ?_
      state_le_capacity := ?_
      target_capacity_reserve := ?_
      outer_work_reserve := ?_ }
  · simpa [SemanticCycleFrame.reframeNext] using
      SemanticTapeSymbolsLtThree.applyAction frame.config action
        resources.tape_bounded hwrite
  · simpa [SemanticCycleFrame.reframeNext] using resources.program_nonempty
  · intro r hr
    exact resources.reads_lt_three r (by
      simpa [SemanticCycleFrame.reframeNext] using hr)
  · intro r hr
    exact resources.writes_lt_three r (by
      simpa [SemanticCycleFrame.reframeNext] using hr)
  · change (ULogSemantics.applyAction frame.config action).state ≤
      semanticCapacityAfter frame.config action frame.capacity
    rw [applyAction_state]
    exact Nat.le_of_lt hactionCapacity
  · simpa [SemanticCycleFrame.reframeNext] using htargets
  · simpa [SemanticCycleFrame.reframeNext] using houter

theorem FrameResourceInvariant.nextNonClockReady
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix)
    (slot : Bool) (action : ULogBytecode.ActionCode) (steps : ℕ)
    (resources : FrameResourceInvariant frame (steps + 1))
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action) :
    NextNonClockReady frame action := by
  obtain ⟨matched, hmatchedMem, _, _, _, hmatchedAction⟩ :=
    ULogBytecode.lookupRule_some_mem hlookup
  have hwrite : action.write < 3 := by
    rw [← hmatchedAction]
    exact resources.writes_lt_three matched hmatchedMem
  have htape := SemanticTapeSymbolsLtThree.applyAction frame.config action
    resources.tape_bounded hwrite
  have htargetsReserve := targetCapacityReserve_after frame action steps
    resources.target_capacity_reserve
  apply nextNonClockReady_of_uniformProgramBounds frame slot action hlookup
    resources.program_nonempty resources.reads_lt_three
    resources.writes_lt_three htape.focus
  · intro r hr
    have h := htargetsReserve r (by simpa using hr)
    omega
  · intro hleft
    obtain ⟨tail, houter⟩ := outerWorkReserve_after frame action steps
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        resources.outer_work_reserve)
    refine ⟨List.replicate steps MStarConcreteAlphabet.work ++ tail, ?_⟩
    simpa [List.replicate_succ, List.append_assoc] using houter

/-- The result of one automatically clocked, nonterminal continuation step. -/
def ScheduledContinuationStep
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (next : ULogSemantics.Config) (nextBudget : ℕ) : Prop :=
  ∃ (action : ULogBytecode.ActionCode)
      (reframe : ClockReframe
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        (clockCellsAfter
          ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
          frame.clockZeros frame.runtime)),
    ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action ∧
    ULogSemantics.applyAction frame.config action = next ∧
    FrameReady (frame.reframeNext action reframe) ∧
    decodeBinaryClock
      (List.replicate reframe.zeros (ulogCore clockZero) ++
        ulogCore clockOne :: reframe.runtime) = some nextBudget ∧
    BranchedReaches slot frame.encode
      (frame.reframeNext action reframe).encode

theorem scheduledContinuationStep_of_positiveClock
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (next : ULogSemantics.Config) (ready : FrameReady frame)
    (hstep : ULogSemantics.stepSlot slot frame.config = some next)
    (hnextHalted : ULogSemantics.halted next = false)
    (budget : ℕ)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some budget)
    (hbudget : 1 < budget)
    (hnonClock : ∀ action,
      ULogBytecode.lookupRule frame.config.program frame.config.state
        frame.config.focus slot = some action →
      ULogSemantics.applyAction frame.config action = next →
      NextNonClockReady frame action) :
    ScheduledContinuationStep frame slot next (budget - 1) := by
  obtain ⟨_, action, hlookup, haction⟩ :=
    ULogSemantics.stepSlot_some_rule hstep
  have hafter := decodeBinaryClock_after_eq_pred frame.clockZeros
    frame.runtime budget hclock
  obtain ⟨reframe, hreframeDecode⟩ :=
    exists_clockReframe_of_positive_binaryClock
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      frame.clockZeros frame.runtime ready.runtime_passive (budget - 1)
      hafter (by omega)
  have hnextReady : FrameReady (frame.reframeNext action reframe) := by
    apply (frameReady_iff_runtime_and_nonClock
      (frame.reframeNext action reframe)).2
    refine ⟨reframe.runtime_passive, ?_⟩
    simpa [NextNonClockReady, SemanticCycleFrame.reframeNext] using
      hnonClock action hlookup haction
  have htargetLower : 2 ≤ action.target := by
    have hnot : ¬ ULogSemantics.halted
        (ULogSemantics.applyAction frame.config action) = true := by
      intro htrue
      have : ULogSemantics.halted next = true := by simpa [haction] using htrue
      rw [this] at hnextHalted
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
  rw [halign] at hbranch
  refine ⟨action, reframe, hlookup, haction, hnextReady, hreframeDecode, ?_⟩
  simpa [SemanticCycleFrame.encode, SemanticCycleFrame.reframeNext] using hbranch

theorem AcceptingSlotTrace.length_le_budget
    {t : ℕ} {c : ULogSemantics.Config} {word : List Bool}
    (trace : AcceptingSlotTrace t c word) : word.length ≤ t := by
  induction t generalizing c word with
  | zero => simpa [AcceptingSlotTrace] using congrArg List.length trace.1
  | succ t ih =>
      rcases trace with terminal | ⟨slot, next, rest, rfl, _, _, tail⟩
      · simp [terminal.1]
      · simp only [List.length_cons]
        exact Nat.succ_le_succ (ih tail)

theorem AcceptingSlotTrace.length_pos_of_not_halted
    {t : ℕ} {c : ULogSemantics.Config} {word : List Bool}
    (trace : AcceptingSlotTrace t c word)
    (hhalt : ULogSemantics.halted c = false) : 0 < word.length := by
  cases t with
  | zero => simp [AcceptingSlotTrace, hhalt] at trace
  | succ t =>
      rcases trace with terminal | ⟨slot, next, rest, rfl, _, _, tail⟩
      · simp [hhalt] at terminal
      · simp

/-- Trace-local preservation is the exact residual assumption: it mentions
neither a clock split nor a concrete run. -/
def TraceNonClockPreservation
    {input : List Bool} {suffix : List Tape} : Prop :=
  ∀ (frame : SemanticCycleFrame input suffix) (slot : Bool)
      (next : ULogSemantics.Config) (action : ULogBytecode.ActionCode),
    ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action →
    ULogSemantics.applyAction frame.config action = next →
    NextNonClockReady frame action

/-- A bounded accepting semantic trace has a canonical concrete realization.
All clock reframes and labelled concrete branches are constructed internally. -/
theorem acceptingSlotTrace_has_scheduled_concrete_trace
    {input : List Bool} {suffix : List Tape}
    (preserve : TraceNonClockPreservation
      (input := input) (suffix := suffix))
    {t : ℕ} {frame : SemanticCycleFrame input suffix} {word : List Bool}
    (ready : FrameReady frame)
    (hstart : ULogSemantics.halted frame.config = false)
    (trace : AcceptingSlotTrace t frame.config word)
    (budget : ℕ)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some budget)
    (hwordBudget : word.length ≤ budget) :
    ConcreteAcceptingSlotTrace frame.encode word := by
  induction t generalizing frame word budget with
  | zero => simp [AcceptingSlotTrace, hstart] at trace
  | succ t ih =>
      rcases trace with terminal |
        ⟨slot, next, rest, rfl, _, hstep, tailTrace⟩
      · simp [hstart] at terminal
      · by_cases haccept : ULogSemantics.accepting next = true
        · have hrest : rest = [] :=
            tailTrace.word_eq_nil_of_halted
              (ULogSemantics.accepting_halted haccept)
          subst rest
          obtain ⟨z, hbranch⟩ := semanticConcreteCycleSpec_accepting_outcome
            frame.config next slot input frame.clockZeros frame.capacity
            frame.runtime frame.outer suffix
            (ready.semanticConcreteCycleSpec frame slot) hstep haccept
          exact ⟨.accepted z,
            .cons frame.encode (.accepted z) (.accepted z) slot [] hbranch
              (.nil _),
            .accepted z, reaches_refl _, rfl, rfl⟩
        · by_cases hhalt : ULogSemantics.halted next = true
          · have hacceptFalse : ULogSemantics.accepting next = false := by
              cases h : ULogSemantics.accepting next <;> simp_all
            exact (tailTrace.false_of_halted_not_accepting hhalt
              hacceptFalse).elim
          · have hhaltFalse : ULogSemantics.halted next = false := by
              cases h : ULogSemantics.halted next <;> simp_all
            have hrestPositive : 0 < rest.length :=
              tailTrace.length_pos_of_not_halted hhaltFalse
            have hbudget : 1 < budget := by
              simp only [List.length_cons] at hwordBudget
              omega
            obtain ⟨action, reframe, _hlookup, haction, hnextReady,
                hnextClock, hconcreteBranch⟩ :=
              scheduledContinuationStep_of_positiveClock frame slot
              next ready hstep hhaltFalse budget hclock hbudget
              (fun candidate hcandidate hcandEq =>
                preserve frame slot next candidate hcandidate hcandEq)
            have tailTrace' : AcceptingSlotTrace t
                (frame.reframeNext action reframe).config rest := by
              change AcceptingSlotTrace t
                (ULogSemantics.applyAction frame.config action) rest
              rw [haction]
              exact tailTrace
            have hnextStart : ULogSemantics.halted
                (frame.reframeNext action reframe).config = false := by
              change ULogSemantics.halted
                (ULogSemantics.applyAction frame.config action) = false
              rw [haction]
              exact hhaltFalse
            have hrestBudget : rest.length ≤ budget - 1 := by
              simp only [List.length_cons] at hwordBudget
              omega
            obtain ⟨cycleFinish, run, finish, hdispatch, hhalted, haccepted⟩ :=
              ih hnextReady hnextStart tailTrace'
                (budget - 1) hnextClock hrestBudget
            exact ⟨cycleFinish,
              .cons frame.encode
                (frame.reframeNext action reframe).encode
                cycleFinish slot rest hconcreteBranch run,
              finish, hdispatch, hhalted, haccepted⟩

theorem ULogSemantics.startFrom_tapeSymbolsLtThree
    (rules : List ULogBytecode.RuleCode) (input : List Bool) :
    SemanticTapeSymbolsLtThree (ULogSemantics.startFrom rules input) := by
  cases input with
  | nil =>
      refine
        { focus := by
            simp [ULogSemantics.startFrom, ULogSemantics.initialTape,
              ULogSemantics.blankCode]
          left := by simp [ULogSemantics.startFrom]
          right := by
            simp [ULogSemantics.startFrom, ULogSemantics.initialTape] }
  | cons b bs =>
      refine
        { focus := ?_
          left := by simp [ULogSemantics.startFrom]
          right := ?_ }
      · cases b <;>
          simp [ULogSemantics.startFrom, ULogSemantics.initialTape,
            ULogSemantics.bitCode]
      · intro x hx
        have hxmap : x ∈ bs.map ULogSemantics.bitCode := by
          simpa [ULogSemantics.startFrom, ULogSemantics.initialTape] using hx
        rcases List.mem_map.mp hxmap with ⟨bit, _, rfl⟩
        cases bit <;> simp [ULogSemantics.bitCode]

theorem bootstrapSemanticFrame_resources
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (capacity steps : ℕ) (outerTail : List Tape)
    (hprogram : rules ≠ []) (hcapacity : 2 ≤ capacity)
    (hreads : ∀ r ∈ rules, r.read < 3)
    (hwrites : ∀ r ∈ rules, r.action.write < 3)
    (htargets : ∀ r ∈ rules, r.action.target + steps < capacity) :
    FrameResourceInvariant
      (bootstrapSemanticFrame rules input padding capacity
        (List.replicate steps MStarConcreteAlphabet.work ++ outerTail))
      steps := by
  refine
    { tape_bounded := ULogSemantics.startFrom_tapeSymbolsLtThree rules input
      program_nonempty := by
        simpa [bootstrapSemanticFrame, ULogSemantics.startFrom] using hprogram
      reads_lt_three := by
        simpa [bootstrapSemanticFrame, ULogSemantics.startFrom] using hreads
      writes_lt_three := by
        simpa [bootstrapSemanticFrame, ULogSemantics.startFrom] using hwrites
      state_le_capacity := by
        simpa [bootstrapSemanticFrame, ULogSemantics.startFrom,
          ULogSemantics.startCode] using hcapacity
      target_capacity_reserve := by
        simpa [bootstrapSemanticFrame, ULogSemantics.startFrom] using htargets
      outer_work_reserve := ?_ }
  refine ⟨outerTail, ?_⟩
  simp [bootstrapSemanticFrame, List.replicate_succ, List.append_assoc]

/-- The trace-indexed reserve invariant discharges all non-clock obligations;
the only budget premise is the actual decoded clock bound. -/
theorem acceptingSlotTrace_has_boundedResource_concrete_trace
    {input : List Bool} {suffix : List Tape}
    {t : ℕ} {frame : SemanticCycleFrame input suffix} {word : List Bool}
    (resources : FrameResourceInvariant frame t)
    (hruntime : PassivePath frame.runtime)
    (hstart : ULogSemantics.halted frame.config = false)
    (trace : AcceptingSlotTrace t frame.config word)
    (budget : ℕ)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some budget)
    (hwordBudget : word.length ≤ budget) :
    ConcreteAcceptingSlotTrace frame.encode word := by
  induction t generalizing frame word budget with
  | zero => simp [AcceptingSlotTrace, hstart] at trace
  | succ t ih =>
      have ready := resources.frameReady hruntime
      rcases trace with terminal |
        ⟨slot, next, rest, rfl, _, hstep, tailTrace⟩
      · simp [hstart] at terminal
      · by_cases haccept : ULogSemantics.accepting next = true
        · have hrest : rest = [] :=
            tailTrace.word_eq_nil_of_halted
              (ULogSemantics.accepting_halted haccept)
          subst rest
          obtain ⟨z, hbranch⟩ := semanticConcreteCycleSpec_accepting_outcome
            frame.config next slot input frame.clockZeros frame.capacity
            frame.runtime frame.outer suffix
            (ready.semanticConcreteCycleSpec frame slot) hstep haccept
          exact ⟨.accepted z,
            .cons frame.encode (.accepted z) (.accepted z) slot [] hbranch
              (.nil _),
            .accepted z, reaches_refl _, rfl, rfl⟩
        · by_cases hhalt : ULogSemantics.halted next = true
          · have hacceptFalse : ULogSemantics.accepting next = false := by
              cases h : ULogSemantics.accepting next <;> simp_all
            exact (tailTrace.false_of_halted_not_accepting hhalt
              hacceptFalse).elim
          · have hhaltFalse : ULogSemantics.halted next = false := by
              cases h : ULogSemantics.halted next <;> simp_all
            have hrestPositive : 0 < rest.length :=
              tailTrace.length_pos_of_not_halted hhaltFalse
            have hbudget : 1 < budget := by
              simp only [List.length_cons] at hwordBudget
              omega
            obtain ⟨action, reframe, hlookup, haction, hnextReady,
                hnextClock, hconcreteBranch⟩ :=
              scheduledContinuationStep_of_positiveClock frame slot next
                ready hstep hhaltFalse budget hclock hbudget
                (fun candidate hcandidate _ =>
                  resources.nextNonClockReady frame slot candidate t
                    hcandidate)
            have nextResources : FrameResourceInvariant
                (frame.reframeNext action reframe) t :=
              resources.next frame slot action t hlookup reframe
            have tailTrace' : AcceptingSlotTrace t
                (frame.reframeNext action reframe).config rest := by
              change AcceptingSlotTrace t
                (ULogSemantics.applyAction frame.config action) rest
              rw [haction]
              exact tailTrace
            have hnextStart : ULogSemantics.halted
                (frame.reframeNext action reframe).config = false := by
              change ULogSemantics.halted
                (ULogSemantics.applyAction frame.config action) = false
              rw [haction]
              exact hhaltFalse
            have hrestBudget : rest.length ≤ budget - 1 := by
              simp only [List.length_cons] at hwordBudget
              omega
            obtain ⟨cycleFinish, run, finish, hdispatch, hhalted, haccepted⟩ :=
              ih nextResources reframe.runtime_passive hnextStart tailTrace'
                (budget - 1) hnextClock hrestBudget
            exact ⟨cycleFinish,
              .cons frame.encode (frame.reframeNext action reframe).encode
                cycleFinish slot rest hconcreteBranch run,
              finish, hdispatch, hhalted, haccepted⟩

/-- The initialized power clock provides enough budget for every accepting
word of depth `t` when `t ≤ 2^padding.length`. -/
theorem bootstrap_acceptingWord_has_scheduled_concrete_trace
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (capacity : ℕ) (outerTail : List Tape)
    (hprogram : rules ≠ []) (hcapacity : 2 ≤ capacity)
    (hreads : ∀ r ∈ rules, r.read < 3)
    (hwrites : ∀ r ∈ rules, r.action.write < 3)
    (htargets : ∀ r ∈ rules, r.action.target < capacity)
    (preserve : TraceNonClockPreservation
      (input := input) (suffix := ([] : List Tape)))
    {t : ℕ} (ht : t ≤ 2 ^ padding.length) {word : List Bool}
    (hword : word ∈ acceptingSlotWords t
      (ULogSemantics.startFrom rules input)) :
    ConcreteAcceptingSlotTrace
      (bootstrapSemanticFrame rules input padding capacity outerTail).encode
      word := by
  let frame := bootstrapSemanticFrame rules input padding capacity outerTail
  have ready : FrameReady frame := bootstrapSemanticFrame_ready rules input
    padding capacity outerTail hprogram hcapacity hreads hwrites htargets
  have hstart : ULogSemantics.halted frame.config = false := by
    simp [frame, bootstrapSemanticFrame, ULogSemantics.startFrom,
      ULogSemantics.halted, ULogSemantics.startCode]
  have trace : AcceptingSlotTrace t frame.config word := by
    exact (mem_acceptingSlotWords_iff t frame.config word).mp
      (by simpa [frame, bootstrapSemanticFrame] using hword)
  apply acceptingSlotTrace_has_scheduled_concrete_trace preserve ready hstart
    trace (2 ^ padding.length)
  · simpa [frame, bootstrapSemanticFrame] using
      decodeBinaryClock_power padding.length []
  · exact le_trans trace.length_le_budget ht

/-- Fully discharged bootstrap specialization.  A capacity margin of `t`
and `t + 1` outer work cells are sufficient for every length-`t` accepting
trace; no continuation, clock-reframe, or concrete-branch oracle remains. -/
theorem bootstrap_acceptingWord_has_concrete_trace
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (capacity : ℕ) (outerTail : List Tape)
    (hprogram : rules ≠ []) (hcapacity : 2 ≤ capacity)
    (hreads : ∀ r ∈ rules, r.read < 3)
    (hwrites : ∀ r ∈ rules, r.action.write < 3)
    {t : ℕ}
    (htargets : ∀ r ∈ rules, r.action.target + t < capacity)
    (ht : t ≤ 2 ^ padding.length) {word : List Bool}
    (hword : word ∈ acceptingSlotWords t
      (ULogSemantics.startFrom rules input)) :
    ConcreteAcceptingSlotTrace
      (bootstrapSemanticFrame rules input padding capacity
        (List.replicate t MStarConcreteAlphabet.work ++ outerTail)).encode
      word := by
  let frame := bootstrapSemanticFrame rules input padding capacity
    (List.replicate t MStarConcreteAlphabet.work ++ outerTail)
  have resources : FrameResourceInvariant frame t := by
    exact bootstrapSemanticFrame_resources rules input padding capacity t
      outerTail hprogram hcapacity hreads hwrites htargets
  have hruntime : PassivePath frame.runtime := by
    intro cell hcell
    simp only [frame, bootstrapSemanticFrame, List.mem_singleton] at hcell
    subst cell
    constructor <;> native_decide
  have hstart : ULogSemantics.halted frame.config = false := by
    simp [frame, bootstrapSemanticFrame, ULogSemantics.startFrom,
      ULogSemantics.halted, ULogSemantics.startCode]
  have trace : AcceptingSlotTrace t frame.config word := by
    exact (mem_acceptingSlotWords_iff t frame.config word).mp
      (by simpa [frame, bootstrapSemanticFrame] using hword)
  apply acceptingSlotTrace_has_boundedResource_concrete_trace resources
    hruntime hstart trace (2 ^ padding.length)
  · simpa [frame, bootstrapSemanticFrame] using
      decodeBinaryClock_power padding.length []
  · exact le_trans trace.length_le_budget ht

/-- The fully instantiated certified concrete image of the semantic accepting
words for a bootstrap frame with the required outer reserve. -/
def BootstrapCertifiedConcreteAcceptingWords
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (capacity : ℕ) (outerTail : List Tape) (t : ℕ) : Type :=
  { word : List Bool //
    word ∈ acceptingSlotWords t (ULogSemantics.startFrom rules input) ∧
    ConcreteAcceptingSlotTrace
      (bootstrapSemanticFrame rules input padding capacity
        (List.replicate t MStarConcreteAlphabet.work ++ outerTail)).encode
      word }

/-- The canonical concrete realization map for the fully reserved bootstrap
frame.  It has no continuation or terminal-dispatch parameter. -/
def bootstrapSemanticToCertifiedConcrete
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (capacity : ℕ) (outerTail : List Tape) (t : ℕ)
    (hprogram : rules ≠ []) (hcapacity : 2 ≤ capacity)
    (hreads : ∀ r ∈ rules, r.read < 3)
    (hwrites : ∀ r ∈ rules, r.action.write < 3)
    (htargets : ∀ r ∈ rules, r.action.target + t < capacity)
    (ht : t ≤ 2 ^ padding.length) :
    SemanticAcceptingWords t (ULogSemantics.startFrom rules input) →
      BootstrapCertifiedConcreteAcceptingWords rules input padding capacity
        outerTail t :=
  fun word => ⟨word.1, word.2,
    bootstrap_acceptingWord_has_concrete_trace rules input padding capacity
      outerTail hprogram hcapacity hreads hwrites htargets ht word.2⟩

theorem bootstrapSemanticToCertifiedConcrete_apply_val
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (capacity : ℕ) (outerTail : List Tape) (t : ℕ)
    (hprogram : rules ≠ []) (hcapacity : 2 ≤ capacity)
    (hreads : ∀ r ∈ rules, r.read < 3)
    (hwrites : ∀ r ∈ rules, r.action.write < 3)
    (htargets : ∀ r ∈ rules, r.action.target + t < capacity)
    (ht : t ≤ 2 ^ padding.length)
    (word : SemanticAcceptingWords t
      (ULogSemantics.startFrom rules input)) :
    (bootstrapSemanticToCertifiedConcrete rules input padding capacity
      outerTail t hprogram hcapacity hreads hwrites htargets ht word).1 =
      word.1 := rfl

theorem bootstrapSemanticToCertifiedConcrete_injective
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (capacity : ℕ) (outerTail : List Tape) (t : ℕ)
    (hprogram : rules ≠ []) (hcapacity : 2 ≤ capacity)
    (hreads : ∀ r ∈ rules, r.read < 3)
    (hwrites : ∀ r ∈ rules, r.action.write < 3)
    (htargets : ∀ r ∈ rules, r.action.target + t < capacity)
    (ht : t ≤ 2 ^ padding.length) :
    Function.Injective
      (bootstrapSemanticToCertifiedConcrete rules input padding capacity
        outerTail t hprogram hcapacity hreads hwrites htargets ht) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg
    (fun q : BootstrapCertifiedConcreteAcceptingWords rules input padding
      capacity outerTail t => q.1) hxy

/-- Semantic accepting words are equivalent to their fully certified concrete
bootstrap image. -/
def bootstrapCertifiedConcreteAcceptingEquiv
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (capacity : ℕ) (outerTail : List Tape) (t : ℕ)
    (hprogram : rules ≠ []) (hcapacity : 2 ≤ capacity)
    (hreads : ∀ r ∈ rules, r.read < 3)
    (hwrites : ∀ r ∈ rules, r.action.write < 3)
    (htargets : ∀ r ∈ rules, r.action.target + t < capacity)
    (ht : t ≤ 2 ^ padding.length) :
    SemanticAcceptingWords t (ULogSemantics.startFrom rules input) ≃
      BootstrapCertifiedConcreteAcceptingWords rules input padding capacity
        outerTail t where
  toFun := bootstrapSemanticToCertifiedConcrete rules input padding capacity
    outerTail t hprogram hcapacity hreads hwrites htargets ht
  invFun := fun word => ⟨word.1, word.2.1⟩
  left_inv := by intro word; rfl
  right_inv := by intro word; apply Subtype.ext; rfl

/-- A finite presentation of semantic accepting words by the finset attached
to the duplicate-free enumerating list. -/
def semanticAcceptingWordsFinsetEquiv
    (t : ℕ) (c : ULogSemantics.Config) :
    SemanticAcceptingWords t c ≃
      {word : List Bool // word ∈ (acceptingSlotWords t c).toFinset} where
  toFun := fun word => ⟨word.1, List.mem_toFinset.mpr word.2⟩
  invFun := fun word => ⟨word.1, List.mem_toFinset.mp word.2⟩
  left_inv := by intro word; rfl
  right_inv := by intro word; rfl

noncomputable def semanticAcceptingWordsFintype
    (t : ℕ) (c : ULogSemantics.Config) :
    Fintype (SemanticAcceptingWords t c) :=
  Fintype.ofEquiv
    {word : List Bool // word ∈ (acceptingSlotWords t c).toFinset}
    (semanticAcceptingWordsFinsetEquiv t c).symm

noncomputable def bootstrapCertifiedConcreteAcceptingFintype
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (capacity : ℕ) (outerTail : List Tape) (t : ℕ)
    (hprogram : rules ≠ []) (hcapacity : 2 ≤ capacity)
    (hreads : ∀ r ∈ rules, r.read < 3)
    (hwrites : ∀ r ∈ rules, r.action.write < 3)
    (htargets : ∀ r ∈ rules, r.action.target + t < capacity)
    (ht : t ≤ 2 ^ padding.length) :
    Fintype (BootstrapCertifiedConcreteAcceptingWords rules input padding
      capacity outerTail t) := by
  letI : Fintype
      (SemanticAcceptingWords t (ULogSemantics.startFrom rules input)) :=
    semanticAcceptingWordsFintype t (ULogSemantics.startFrom rules input)
  exact Fintype.ofEquiv
    (SemanticAcceptingWords t (ULogSemantics.startFrom rules input))
    (bootstrapCertifiedConcreteAcceptingEquiv rules input padding capacity
      outerTail t hprogram hcapacity hreads hwrites htargets ht)

theorem card_semanticAcceptingWords
    (t : ℕ) (c : ULogSemantics.Config) :
    @Fintype.card (SemanticAcceptingWords t c)
      (semanticAcceptingWordsFintype t c) =
      ULogSemantics.machine.acceptingPaths t c := by
  letI : Fintype (SemanticAcceptingWords t c) :=
    semanticAcceptingWordsFintype t c
  calc
    Fintype.card (SemanticAcceptingWords t c) =
        Fintype.card
          {word : List Bool // word ∈ (acceptingSlotWords t c).toFinset} :=
      Fintype.card_congr (semanticAcceptingWordsFinsetEquiv t c)
    _ = (acceptingSlotWords t c).toFinset.card :=
      Fintype.card_coe (acceptingSlotWords t c).toFinset
    _ = ULogSemantics.machine.acceptingPaths t c :=
      card_acceptingSlotWords t c

/-- The certified concrete bootstrap image has exactly the semantic accepting
path count. -/
theorem card_bootstrapCertifiedConcreteAcceptingWords
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (capacity : ℕ) (outerTail : List Tape) (t : ℕ)
    (hprogram : rules ≠ []) (hcapacity : 2 ≤ capacity)
    (hreads : ∀ r ∈ rules, r.read < 3)
    (hwrites : ∀ r ∈ rules, r.action.write < 3)
    (htargets : ∀ r ∈ rules, r.action.target + t < capacity)
    (ht : t ≤ 2 ^ padding.length) :
    @Fintype.card
      (BootstrapCertifiedConcreteAcceptingWords rules input padding capacity
        outerTail t)
      (bootstrapCertifiedConcreteAcceptingFintype rules input padding capacity
        outerTail t hprogram hcapacity hreads hwrites htargets ht) =
      ULogSemantics.machine.acceptingPaths t
        (ULogSemantics.startFrom rules input) := by
  letI : Fintype
      (BootstrapCertifiedConcreteAcceptingWords rules input padding capacity
        outerTail t) :=
    bootstrapCertifiedConcreteAcceptingFintype rules input padding capacity
      outerTail t hprogram hcapacity hreads hwrites htargets ht
  letI : Fintype
      (SemanticAcceptingWords t (ULogSemantics.startFrom rules input)) :=
    semanticAcceptingWordsFintype t (ULogSemantics.startFrom rules input)
  calc
    Fintype.card
        (BootstrapCertifiedConcreteAcceptingWords rules input padding capacity
          outerTail t) =
        Fintype.card
          (SemanticAcceptingWords t (ULogSemantics.startFrom rules input)) :=
      Fintype.card_congr
        (bootstrapCertifiedConcreteAcceptingEquiv rules input padding capacity
          outerTail t hprogram hcapacity hreads hwrites htargets ht).symm
    _ = ULogSemantics.machine.acceptingPaths t
        (ULogSemantics.startFrom rules input) :=
      card_semanticAcceptingWords t (ULogSemantics.startFrom rules input)

end PakFixedPolyomino.ULogBootstrapExecution
