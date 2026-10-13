import PakFixedPolyomino.ULogFiniteTapeActiveMicroInverse
import PakFixedPolyomino.ULogFiniteTapeBoundedGrowthReadiness
import PakFixedPolyomino.ULogActiveExactTargetOne

/-! Generic physical reflection for genuinely labelled nondeterministic
finite programs. All-prefix resource/length bounds are explicit intermediate
premises; concrete source interfaces must prove them internally. The raw
micro-path itself carries only its literal edges and physical labels. -/

namespace PakFixedPolyomino.ULogFiniteTapeNondeterministicMicroInverse
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open ULogFiniteTapePhysicalResourceLedger ULogFiniteTapeBoundedGrowthReadiness
open ULogFiniteTapeDeterministicFrameReadiness ULogBootstrapExecution
open ULogAlphabet ULogProgram ULogActiveExactCycles ULogConcreteSlotMicroExpansion
open ULogConcreteMicroPathSplitting
open MStarParserExecution (Zipper)
open FiniteOneTapeSemantics (moveHead)

variable {ns : Nat}

def AllReachableReady (p : BoundedProgram ns 3) (head : Int)
    (z : BoundedConfig ns 3) (C : Nat) (outer : List Tape) : Prop :=
  ∀ w hf out Cf outerf,
    resourceRun p 2 w head z C outer = some (hf, out, Cf, outerf) →
    boundedHalted out = false → NonClockFrameReady (liftConfig p out) Cf outerf

def AllRunLengthBound (p : BoundedProgram ns 3) (head : Int)
    (z : BoundedConfig ns 3) (B : Nat) : Prop :=
  ∀ w hf out, run p 2 w head z = some (hf, out) → w.length ≤ B

def frameChoice {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) : Result :=
  .running .chooseSlot
    ⟨dynamicRuleReturnPath (frame.config.leftRev.map payloadNat) frame.config.program input ++
        ulogCore pcMark :: frame.outer,
      readHeadNat frame.config.focus,
      clockCellsAfter (frame.config.right.map payloadNat) frame.clockZeros frame.runtime ++
        stateWorkspace frame.capacity frame.config.state suffix⟩

noncomputable def frame_first_choice {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (focus : frame.config.focus < 3) :
    FirstValidZeroHit IsConcreteChoice frame.encode (frameChoice frame) := by
  have head : choiceHead (readHeadNat frame.config.focus) = true := by
    interval_cases frame.config.focus <;> decide
  simpa only [SemanticCycleFrame.encode, semanticCycleEncoding, frameChoice,
    stateWorkspace, clockCellsBefore, clockCellsAfter, List.append_assoc, List.cons_append] using
    clockDecrementCells_firstChoice (readHeadNat frame.config.focus) head frame.clockZeros
      (frame.config.right.map payloadNat) (payloadNatList_safe frame.config.right)
      (dynamicRuleReturnPath (frame.config.leftRev.map payloadNat) frame.config.program input ++
        ulogCore pcMark :: frame.outer)
      (frame.runtime ++ stateWorkspace frame.capacity frame.config.state suffix)

theorem split_frame_choice {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (focus : frame.config.focus < 3)
    (labels : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath frame.encode labels (.accepted tape)) :
    ∃ slot rest,
      labels = List.replicate (frame_first_choice frame focus).steps 0 ++
        ULogBytecode.slotIndex slot :: rest ∧
      ConcreteMicroPath (frameChoice frame) (ULogBytecode.slotIndex slot :: rest)
        (.accepted tape) := by
  obtain ⟨rest, word, atChoice⟩ := zero_prefix_of_micro_accepting
    (frame_first_choice frame focus).valid (frame_first_choice frame focus).before raw
  cases rest with
  | nil =>
      have last := microPath_nil_finish atChoice
      simp [frameChoice] at last
  | cons label rest =>
      fin_cases label
      · exact ⟨false, rest, word, atChoice⟩
      · exact ⟨true, rest, word, atChoice⟩

theorem split_selected_frame_cycle {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (focus : frame.config.focus < 3)
    {slot : Bool} {finish : Result} (cycle : ExactConcreteCycle slot frame.encode finish)
    (labels : List (Fin 2)) (rest : List (Fin 2)) (tape : Zipper Tape)
    (word : labels = List.replicate (frame_first_choice frame focus).steps 0 ++
      ULogBytecode.slotIndex slot :: rest)
    (raw : ConcreteMicroPath (frameChoice frame) (ULogBytecode.slotIndex slot :: rest)
      (.accepted tape)) :
    ∃ tail, labels = cycleWord cycle ++ tail ∧
      ConcreteMicroPath finish tail (.accepted tape) := by
  have choice := cycle.choicePrefix.finish_unique (frame_first_choice frame focus)
  have selected : ConcreteMicroPath cycle.choice (ULogBytecode.slotIndex slot :: rest)
      (.accepted tape) := by simpa only [choice] using raw
  obtain ⟨tail, suffixWord, after⟩ := split_after_cycle_selection cycle selected
  refine ⟨tail, ?_, after⟩
  have steps := cycle.choicePrefix.steps_eq (frame_first_choice frame focus)
  rw [word, suffixWord]
  simp only [cycleWord, steps, List.append_assoc, List.cons_append]

theorem child_reachable_ready (p : BoundedProgram ns 3) (head : Int)
    (z : BoundedConfig ns 3) (C : Nat) (outer : List Tape)
    (all : AllReachableReady p head z C outer) (slot : Bool) (a : BoundedAction ns 3)
    (halt : boundedHalted z = false) (rule : p.rule z.state z.focus slot = some a) :
    AllReachableReady p (moveHead a.move head) (applyBounded 2 z a)
      (semanticCapacityAfter (liftConfig p z) (actionCode a) C)
      (semanticOuterAfter (liftConfig p z) (actionCode a) outer) := by
  intro w hf out Cf outerf path halted
  apply all (slot :: w) hf out Cf outerf _ halted
  simpa only [resourceRun, halt, Bool.false_eq_true, ↓reduceIte, rule] using path

theorem child_length_bound (p : BoundedProgram ns 3) (head : Int)
    (z : BoundedConfig ns 3) (B : Nat)
    (all : AllRunLengthBound p head z B) (slot : Bool) (a : BoundedAction ns 3)
    (halt : boundedHalted z = false) (rule : p.rule z.state z.focus slot = some a) :
    0 < B ∧ AllRunLengthBound p (moveHead a.move head) (applyBounded 2 z a) (B - 1) := by
  have one : run p 2 [slot] head z =
      some (moveHead a.move head, applyBounded 2 z a) := by
    simp [ULogFiniteTapeZipperRun.run, halt, rule]
  have bound := all _ _ _ one
  refine ⟨by simp only [List.length_cons, List.length_nil] at bound; omega, ?_⟩
  intro w hf out path
  have parent : run p 2 (slot :: w) head z = some (hf, out) := by
    simpa only [ULogFiniteTapeZipperRun.run, halt, Bool.false_eq_true, ↓reduceIte, rule] using path
  have bound := all _ _ _ parent
  simp only [List.length_cons] at bound
  omega

theorem every_accepting_micro_path_reflects {input : List Bool} {suffix : List Tape}
    (p : BoundedProgram ns 3) (B : Nat) (head : Int) (z : BoundedConfig ns 3)
    (C : Nat) (outer : List Tape)
    (reachable : AllReachableReady p head z C outer)
    (lengths : AllRunLengthBound p head z B)
    (halt : boundedHalted z = false)
    (frame : SemanticCycleFrame input suffix)
    (hconfig : frame.config = liftConfig p z)
    (hcapacity : frame.capacity = C) (houter : frame.outer = outer)
    (runtime : PassivePath frame.runtime) (budget : Nat)
    (clock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some budget)
    (slack : B < budget) (labels : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath frame.encode labels (.accepted tape)) :
    ∃ w hf out, ULogFiniteTapeZipperRun.run p 2 w head z = some (hf, out) ∧
      out.state.val = 0 ∧ SlotMicroExpansion frame.encode w labels (.accepted tape) := by
  induction B using Nat.strong_induction_on generalizing head z C outer frame budget labels with
  | h B ih =>
    have localReady := reachable [] head z C outer rfl halt
    have ready : FrameReady frame :=
      (frameReady_iff_runtime_and_nonClock frame).2
        ⟨runtime, by simpa only [hconfig, hcapacity, houter] using localReady⟩
    obtain ⟨slot, rest, word, selected⟩ := split_frame_choice frame ready.focus_lt_three labels tape raw
    cases rule : p.rule z.state z.focus slot with
    | none =>
      have lookup : ULogBytecode.lookupRule frame.config.program frame.config.state
          frame.config.focus slot = none := by
        rw [hconfig]
        change ULogBytecode.lookupRule (compile p) z.state.val z.focus.val slot = none
        rw [lookup_compile, rule]
        rfl
      obtain ⟨canonical⟩ := ULogActiveExactNoRule.branchedCycle_semanticNoRule_exact_nonempty
        frame.config slot input frame.clockZeros frame.capacity frame.runtime frame.outer suffix
        runtime ready.focus_lt_three ready.program_nonempty ready.reads_lt_three lookup
      have cycle : ExactConcreteCycle slot frame.encode .rejected := by
        simpa only [SemanticCycleFrame.encode] using canonical
      obtain ⟨tail, _, after⟩ := split_selected_frame_cycle frame ready.focus_lt_three cycle
        labels rest tape word selected
      have ended := microPath_halted_start after (by rfl)
      cases ended.2
    | some a =>
      obtain ⟨positive, childLength⟩ := child_length_bound p head z B lengths slot a halt rule
      have lookup : ULogBytecode.lookupRule frame.config.program frame.config.state
          frame.config.focus slot = some (actionCode a) := by
        rw [hconfig]
        change ULogBytecode.lookupRule (compile p) z.state.val z.focus.val slot = _
        rw [lookup_compile, rule]
        rfl
      have step : ULogSemantics.stepSlot slot frame.config =
          some (liftConfig p (applyBounded 2 z a)) := by
        rw [hconfig]
        simpa [boundedStepSlot, halt, rule] using
          (stepSlot_liftConfig p (2 : Fin 3) rfl slot z)
      have action : ULogSemantics.applyAction frame.config (actionCode a) =
          liftConfig p (applyBounded 2 z a) := by
        rw [hconfig]
        exact (liftConfig_applyBounded p 2 rfl z a).symm
      by_cases accepted : (applyBounded 2 z a).state.val = 0
      · have accepts : ULogSemantics.accepting (liftConfig p (applyBounded 2 z a)) = true := by
          simp [ULogSemantics.accepting, ULogSemantics.acceptCode, liftConfig, accepted]
        let witness := exactAcceptingCycleRefinement frame slot ready
          (liftConfig p (applyBounded 2 z a)) step accepts
        obtain ⟨tail, labelsWord, after⟩ := split_selected_frame_cycle frame ready.focus_lt_three
          witness.exact_cycle labels rest tape word selected
        have ended := microPath_halted_start after (by rfl)
        have expansion : SlotMicroExpansion (.accepted witness.tape) [] tail (.accepted tape) := by
          rw [ended.1, ended.2]
          exact .nil _
        refine ⟨[slot], moveHead a.move head, applyBounded 2 z a, ?_, accepted, ?_⟩
        · simp [ULogFiniteTapeZipperRun.run, halt, rule]
        · rw [labelsWord]
          exact .cons frame.encode (.accepted witness.tape) (.accepted tape) slot [] tail
            witness.exact_cycle expansion
      · by_cases rejected : (applyBounded 2 z a).state.val = 1
        · have target : (actionCode a).target = 1 := by
            change a.target.val = 1
            cases hm : a.move <;> cases hl : z.leftRev <;> cases hr : z.right <;>
              simpa only [applyBounded, hm, hl, hr] using rejected
          have capacity : 1 ≤ frame.capacity := by
            have h := semanticCapacityReady_target_le frame.config (actionCode a) frame.capacity
              (ready.capacity_ready slot (actionCode a) lookup)
            rw [target] at h
            exact h
          obtain ⟨canonical⟩ := ULogActiveExactTargetOne.branchedCycle_semanticTargetOne_exact_nonempty
            frame.config slot (actionCode a) lookup target input frame.clockZeros frame.capacity
            frame.runtime frame.outer suffix runtime ready.focus_lt_three ready.reads_lt_three
            ready.writes_lt_three ready.state_le_capacity capacity
          have cycle : ExactConcreteCycle slot frame.encode .rejected := by
            simpa only [SemanticCycleFrame.encode] using canonical
          obtain ⟨tail, _, after⟩ := split_selected_frame_cycle frame ready.focus_lt_three cycle
            labels rest tape word selected
          have ended := microPath_halted_start after (by rfl)
          cases ended.2
        · have nextHalt : boundedHalted (applyBounded 2 z a) = false := by
            simp only [boundedHalted, decide_eq_false_iff_not]
            omega
          have semHalt : ULogSemantics.halted (liftConfig p (applyBounded 2 z a)) = false := by
            simpa [ULogSemantics.halted, liftConfig, boundedHalted] using nextHalt
          obtain ⟨actual, reframe, actualLookup, _, decoded, cycle⟩ :=
            positive_continuation frame slot (liftConfig p (applyBounded 2 z a)) budget ready
              clock (by omega) step semHalt
          have eq : actual = actionCode a := Option.some.inj (actualLookup.symm.trans lookup)
          subst actual
          obtain ⟨tail, labelsWord, after⟩ := split_selected_frame_cycle frame ready.focus_lt_three
            cycle labels rest tape word selected
          have hc : (frame.reframeNext (actionCode a) reframe).config =
              liftConfig p (applyBounded 2 z a) := action
          have hC : (frame.reframeNext (actionCode a) reframe).capacity =
              semanticCapacityAfter (liftConfig p z) (actionCode a) C := by
            simp only [SemanticCycleFrame.reframeNext, hconfig, hcapacity]
          have ho : (frame.reframeNext (actionCode a) reframe).outer =
              semanticOuterAfter (liftConfig p z) (actionCode a) outer := by
            simp only [SemanticCycleFrame.reframeNext, hconfig, houter]
          obtain ⟨w, hf, out, path, accepts, expansion⟩ := ih (B - 1) (by omega)
            (moveHead a.move head) (applyBounded 2 z a) _ _
            (child_reachable_ready p head z C outer reachable slot a halt rule)
            childLength nextHalt (frame.reframeNext (actionCode a) reframe) hc hC ho
            reframe.runtime_passive (budget - 1) decoded (by omega) tail after
          refine ⟨slot :: w, hf, out, ?_, accepts, ?_⟩
          · simpa only [ULogFiniteTapeZipperRun.run, halt, Bool.false_eq_true, ↓reduceIte, rule] using path
          · rw [labelsWord]
            exact .cons frame.encode (frame.reframeNext (actionCode a) reframe).encode
              (.accepted tape) slot w tail cycle expansion

end PakFixedPolyomino.ULogFiniteTapeNondeterministicMicroInverse
