import PakFixedPolyomino.ULogConcreteAcceptingBijection

/-! Exact clock reframing and explicitly scheduled resource preservation.

After one concrete cycle the least-significant zero block of the clock has
been decremented: `0^k 1` becomes `1^k 0`.  A positive decoded remainder has
another first `1`; splitting at that bit gives precisely the `ClockReframe`
required by the next cycle.  The clock argument is independent of the other
frame invariants, so the latter are recorded as an explicit per-step schedule
rather than asserted as an unsupported global preservation theorem. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

/-- Every positively decoded little-endian binary clock word has a first
`clockOne`, preceded only by `clockZero` cells. -/
theorem decodeBinaryClock_positive_split
    (cells : List Tape) (remaining : ℕ)
    (hdecode : decodeBinaryClock cells = some remaining)
    (hpositive : 0 < remaining) :
    ∃ zeros runtime,
      cells = List.replicate zeros (ulogCore clockZero) ++
        ulogCore clockOne :: runtime := by
  induction cells generalizing remaining with
  | nil => simp [decodeBinaryClock] at hdecode
  | cons cell cells ih =>
      by_cases hsep : cell = ulogCore clockSep
      · have hzero : remaining = 0 := by
          simpa [decodeBinaryClock, hsep] using hdecode.symm
        omega
      · by_cases hzero : cell = ulogCore clockZero
        · subst cell
          have hzeroSep :
              ulogCore clockZero ≠ ulogCore clockSep :=
            ULogTapeDecoding.ulog_symbol_ne (by decide)
          cases htail : decodeBinaryClock cells with
          | none =>
              simp [decodeBinaryClock, hzeroSep, htail] at hdecode
          | some tailValue =>
              have hvalue : 2 * tailValue = remaining := by
                simpa [decodeBinaryClock, hzeroSep, htail] using hdecode
              have htailPositive : 0 < tailValue := by omega
              obtain ⟨zeros, runtime, hsplit⟩ :=
                ih tailValue htail htailPositive
              refine ⟨zeros + 1, runtime, ?_⟩
              rw [hsplit]
              simp [List.replicate_succ, List.append_assoc]
        · by_cases hone : cell = ulogCore clockOne
          · refine ⟨0, cells, ?_⟩
            subst cell
            simp
          · simp [decodeBinaryClock, hsep, hzero, hone] at hdecode

/-- The decremented clock suffix is passive whenever its old runtime suffix
was passive. -/
theorem clockAfterSuffix_passive (zeros : ℕ) (runtime : List Tape)
    (hruntime : PassivePath runtime) :
    PassivePath
      (List.replicate zeros (ulogCore clockOne) ++
        ulogCore clockZero :: runtime) := by
  apply passivePath_append
  · intro cell hcell
    have heq : cell = ulogCore clockOne :=
      (by simpa only [List.mem_replicate] using hcell :
        zeros ≠ 0 ∧ cell = ulogCore clockOne).2
    rw [heq]
    exact passiveCell_clockOne
  · intro cell hcell
    rcases List.mem_cons.mp hcell with rfl | hcell
    · exact passiveCell_clockZero
    · exact hruntime cell hcell

/-- A positive value of the post-cycle binary clock supplies an exact next
cycle `ClockReframe`.  The returned equality also records that reframing does
not change the decoded remaining budget. -/
theorem exists_clockReframe_of_positive_binaryClock
    (right : List Tape) (clockZeros : ℕ) (runtime : List Tape)
    (hruntime : PassivePath runtime) (remaining : ℕ)
    (hdecode :
      decodeBinaryClock
        (List.replicate clockZeros (ulogCore clockOne) ++
          ulogCore clockZero :: runtime) = some remaining)
    (hpositive : 0 < remaining) :
    ∃ reframe : ClockReframe right
        (clockCellsAfter right clockZeros runtime),
      decodeBinaryClock
        (List.replicate reframe.zeros (ulogCore clockZero) ++
          ulogCore clockOne :: reframe.runtime) = some remaining := by
  let afterSuffix :=
    List.replicate clockZeros (ulogCore clockOne) ++
      ulogCore clockZero :: runtime
  obtain ⟨zeros, nextRuntime, hsplit⟩ :=
    decodeBinaryClock_positive_split afterSuffix remaining hdecode hpositive
  have hafterPassive : PassivePath afterSuffix :=
    clockAfterSuffix_passive clockZeros runtime hruntime
  have hnextPassive : PassivePath nextRuntime := by
    intro cell hcell
    apply hafterPassive cell
    rw [hsplit]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hcell)
  let reframe : ClockReframe right
      (clockCellsAfter right clockZeros runtime) :=
    { zeros := zeros
      runtime := nextRuntime
      runtime_passive := hnextPassive
      eq_before := by
        unfold clockCellsBefore clockCellsAfter
        simpa only [List.append_assoc] using
          congrArg (fun suffix => right ++ suffix) hsplit.symm }
  refine ⟨reframe, ?_⟩
  change decodeBinaryClock
      (List.replicate zeros (ulogCore clockZero) ++
        ulogCore clockOne :: nextRuntime) = some remaining
  rw [← hsplit]
  exact hdecode

/-- Specialization to the binary clock installed by bootstrap.  Its first
post-cycle value is exactly `2^k - 1`. -/
theorem initializedBinaryClock_after_reframe
    (right : List Tape) (k : ℕ) (hpositive : 0 < 2 ^ k - 1) :
    ∃ reframe : ClockReframe right
        (clockCellsAfter right k [ulogCore clockSep]),
      decodeBinaryClock
        (List.replicate reframe.zeros (ulogCore clockZero) ++
          ulogCore clockOne :: reframe.runtime) = some (2 ^ k - 1) := by
  apply exists_clockReframe_of_positive_binaryClock right k
    [ulogCore clockSep]
  · intro cell hcell
    simp only [List.mem_singleton] at hcell
    subst cell
    constructor <;> native_decide
  · simpa only using decodeBinaryClock_power_pred k []
  · exact hpositive

/-- Exactly the part of `FrameReady` which is independent of the clock
runtime.  In particular this exposes capacity and outer-tape obligations
instead of pretending that they follow from clock arithmetic. -/
structure NonClockFrameReady
    (config : ULogSemantics.Config) (capacity : ℕ)
    (outer : List Tape) : Prop where
  focus_lt_three : config.focus < 3
  program_nonempty : config.program ≠ []
  reads_lt_three : ∀ r ∈ config.program, r.read < 3
  writes_lt_three : ∀ r ∈ config.program, r.action.write < 3
  state_le_capacity : config.state ≤ capacity
  capacity_ready : ∀ slot action,
    ULogBytecode.lookupRule config.program config.state config.focus slot =
      some action →
    SemanticCapacityReady config action capacity
  outer_ready : ∀ slot action,
    ULogBytecode.lookupRule config.program config.state config.focus slot =
      some action →
    SemanticOuterReady config action outer

theorem frameReady_iff_runtime_and_nonClock
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) :
    FrameReady frame ↔
      PassivePath frame.runtime ∧
        NonClockFrameReady frame.config frame.capacity frame.outer := by
  constructor
  · intro ready
    exact ⟨ready.runtime_passive,
      { focus_lt_three := ready.focus_lt_three
        program_nonempty := ready.program_nonempty
        reads_lt_three := ready.reads_lt_three
        writes_lt_three := ready.writes_lt_three
        state_le_capacity := ready.state_le_capacity
        capacity_ready := ready.capacity_ready
        outer_ready := ready.outer_ready }⟩
  · rintro ⟨hruntime, ready⟩
    exact
      { runtime_passive := hruntime
        focus_lt_three := ready.focus_lt_three
        program_nonempty := ready.program_nonempty
        reads_lt_three := ready.reads_lt_three
        writes_lt_three := ready.writes_lt_three
        state_le_capacity := ready.state_le_capacity
        capacity_ready := ready.capacity_ready
        outer_ready := ready.outer_ready }

/-- The exact non-clock obligation for continuing after `action`. -/
def NextNonClockReady
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix)
    (action : ULogBytecode.ActionCode) : Prop :=
  NonClockFrameReady
    (ULogSemantics.applyAction frame.config action)
    (semanticCapacityAfter frame.config action frame.capacity)
    (semanticOuterAfter frame.config action frame.outer)

/-- A single scheduled continuation step: semantic rule identification,
positive remaining binary clock, and the exact non-clock readiness facts. -/
structure ScheduledFrameReady
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (next : ULogSemantics.Config) : Type where
  action : ULogBytecode.ActionCode
  lookup : ULogBytecode.lookupRule frame.config.program frame.config.state
    frame.config.focus slot = some action
  action_eq : ULogSemantics.applyAction frame.config action = next
  remaining : ℕ
  clock_decoded :
    decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockOne) ++
        ulogCore clockZero :: frame.runtime) = some remaining
  clock_positive : 0 < remaining
  next_nonClock : NextNonClockReady frame action

/-- A schedule supplies only the facts that genuinely vary from step to step.
The semantic step and nonterminal hypotheses are kept in the interface so it
can directly discharge `ResourceFrameSchedule`. -/
def ScheduledResourceFrames
    {input : List Bool} {suffix : List Tape} : Type :=
  ∀ (frame : SemanticCycleFrame input suffix) (slot : Bool)
      (_ready : FrameReady frame) (next : ULogSemantics.Config),
    ULogSemantics.stepSlot slot frame.config = some next →
      ULogSemantics.accepting next = false →
      ULogSemantics.halted next = false →
      ScheduledFrameReady frame slot next

theorem ScheduledResourceFrames.toResourceFrameSchedule
    {input : List Bool} {suffix : List Tape}
    (scheduled : ScheduledResourceFrames
      (input := input) (suffix := suffix)) :
    ResourceFrameSchedule (input := input) (suffix := suffix) := by
  intro frame slot ready next hstep haccept hhalt
  let cert := scheduled frame slot ready next hstep haccept hhalt
  obtain ⟨reframe, _⟩ := exists_clockReframe_of_positive_binaryClock
    ((ULogSemantics.applyAction frame.config cert.action).right.map payloadNat)
    frame.clockZeros frame.runtime ready.runtime_passive cert.remaining
    cert.clock_decoded cert.clock_positive
  refine ⟨cert.action, cert.lookup, cert.action_eq, reframe, ?_⟩
  apply (frameReady_iff_runtime_and_nonClock
    (frame.reframeNext cert.action reframe)).2
  refine ⟨reframe.runtime_passive, ?_⟩
  simpa [NextNonClockReady, SemanticCycleFrame.reframeNext] using
    cert.next_nonClock

/-- The scheduled certificate therefore yields the complete concrete
continuation relation, including the labelled concrete cycle. -/
theorem ScheduledResourceFrames.toContinuation
    {input : List Bool} {suffix : List Tape}
    (scheduled : ScheduledResourceFrames
      (input := input) (suffix := suffix)) :
    ResourceContinuationRefinement (input := input) (suffix := suffix) :=
  (scheduled.toResourceFrameSchedule).toContinuation

end PakFixedPolyomino.ULogBootstrapExecution
