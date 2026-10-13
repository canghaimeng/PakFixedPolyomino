import PakFixedPolyomino.ULogFiniteTapeSelectedRawBranch
import PakFixedPolyomino.ULogSelectedExactPositiveCycles

/-! Reflection of ALL literal accepting physical words at arbitrary capacity.
The physical word has only actual edges and labels. Its selected capacity
ledger is derived here; neither a large-capacity premise nor readiness of
the alternative slot is supplied. Logical length/outer bounds are explicit
generic premises, supplied internally by the concrete whole scanner. -/
namespace PakFixedPolyomino.ULogFiniteTapeSelectedMicroInverse
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapePhysicalResourceLedger
open ULogFiniteTapeAllCapacityOuterReadiness ULogFiniteTapeSelectedCapacityBridge
open ULogFiniteTapeCapacityReadiness ULogFiniteTapeSelectedRawBranch
open ULogFiniteTapeNondeterministicMicroInverse ULogBootstrapExecution
open ULogSemanticFrameSelectedRightCapacity ULogSelectedExactTerminalCycles
open ULogSelectedExactPositiveCycles ULogConcreteSlotMicroExpansion
open ULogConcreteMicroPathSplitting ULogAlphabet ULogProgram
open FiniteOneTapeSemantics (moveHead)
open MStarParserExecution (Zipper)
variable {ns : Nat}

theorem every_accepting_micro_path_reflects_selected {input : List Bool}
    (p : BoundedProgram ns 3) (hp : compile p ≠ []) (B : Nat)
    (head : Int) (z : BoundedConfig ns 3) (C : Nat) (outer : List Tape)
    (outerReady : AllReachableOuterReady p head z C outer)
    (lengths : AllRunLengthBound p head z B) (halt : boundedHalted z = false)
    (current : z.state.val ≤ C)
    (frame : SemanticCycleFrame input ([] : List Tape))
    (hconfig : frame.config = liftConfig p z)
    (hcapacity : frame.capacity = C) (houter : frame.outer = outer)
    (runtime : PassivePath frame.runtime) (budget : Nat)
    (clock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some budget)
    (slack : B < budget) (labels : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath frame.encode labels (.accepted tape)) :
    ∃ w hf out, run p 2 w head z = some (hf, out) ∧ out.state.val = 0 ∧
      CapacityReadyRun p 2 w head z C ∧
      SlotMicroExpansion frame.encode w labels (.accepted tape) := by
  induction B using Nat.strong_induction_on generalizing head z C outer frame budget labels with
  | h B ih =>
    have focus : frame.config.focus < 3 := by rw [hconfig]; exact z.focus.isLt
    have reads : ∀ r ∈ frame.config.program, r.read < 3 := by
      intro r member
      exact (compile_rule_bounded p (by simpa only [hconfig, liftConfig] using member)).2.1
    have writes : ∀ r ∈ frame.config.program, r.action.write < 3 := by
      intro r member
      exact (compile_rule_bounded p (by simpa only [hconfig, liftConfig] using member)).2.2.1
    have stateCapacity : frame.config.state ≤ frame.capacity := by
      simpa only [hconfig, liftConfig, hcapacity] using current
    have twoCapacity : 2 ≤ C := by
      have active := halt
      simp only [boundedHalted, decide_eq_false_iff_not] at active
      omega
    obtain ⟨slot, rest, a, word, selected, rule, lookup⟩ :=
      first_selected_raw_branch p hp z frame hconfig runtime labels tape raw
    obtain ⟨positive, childLength⟩ := child_length_bound p head z B lengths slot a halt rule
    have step : ULogSemantics.stepSlot slot frame.config =
        some (liftConfig p (applyBounded 2 z a)) := by
      rw [hconfig]
      simpa [boundedStepSlot, halt, rule] using
        (stepSlot_liftConfig p (2 : Fin 3) rfl slot z)
    have action : ULogSemantics.applyAction frame.config (actionCode a) =
        liftConfig p (applyBounded 2 z a) := by
      rw [hconfig]
      exact (liftConfig_applyBounded p 2 rfl z a).symm
    by_cases accepted : a.target.val = 0
    · obtain ⟨witness⟩ := selected_accepting_cycle_nonempty frame slot focus reads writes
        runtime stateCapacity (actionCode a) lookup accepted
      obtain ⟨tail, labelsWord, after⟩ := split_selected_frame_cycle frame focus
        witness.exact_cycle labels rest tape word selected
      have ended := microPath_halted_start after (by rfl)
      have expansion : SlotMicroExpansion (.accepted witness.tape) [] tail (.accepted tape) := by
        rw [ended.1, ended.2]
        exact .nil _
      have capacity := target_zero_capacity_ready p z a C halt current accepted
      refine ⟨[slot], moveHead a.move head, applyBounded 2 z a, ?_, ?_, ?_, ?_⟩
      · simp [ULogFiniteTapeZipperRun.run, halt, rule]
      · simpa only [apply_state] using accepted
      · exact .cons halt rule current capacity (.nil (selected_capacity_next_state p z a C capacity))
      · rw [labelsWord]
        exact .cons frame.encode (.accepted witness.tape) (.accepted tape) slot [] tail
          witness.exact_cycle expansion
    · by_cases rejected : a.target.val = 1
      · exact (selected_target_one_no_accepting_tail frame slot focus reads writes runtime
          stateCapacity (by rw [hcapacity]; omega) (actionCode a) lookup rejected
          rest tape selected).elim
      · have nonhalting : 2 ≤ a.target.val := by omega
        have nextHalt : boundedHalted (applyBounded 2 z a) = false := by
          simp only [boundedHalted, apply_state, decide_eq_false_iff_not]
          omega
        have semHalt : ULogSemantics.halted (liftConfig p (applyBounded 2 z a)) = false := by
          simpa [ULogSemantics.halted, liftConfig, boundedHalted] using nextHalt
        have capacity := selected_nonhalting_raw_capacity p z C frame hconfig hcapacity
          runtime current slot a lookup nonhalting rest tape selected
        have localOuter := outerReady [] head z C outer rfl halt slot (actionCode a)
          (by simpa only [hconfig, liftConfig] using lookup)
        have ready : SelectedFrameReady frame slot :=
          { runtime_passive := runtime
            focus_lt_three := focus
            program_nonempty := by simpa only [hconfig, liftConfig] using hp
            reads_lt_three := reads
            writes_lt_three := writes
            state_le_capacity := stateCapacity
            capacity_ready := by
              intro actual matched
              have same := Option.some.inj (matched.symm.trans lookup)
              subst actual
              simpa only [hconfig, hcapacity] using capacity
            outer_ready := by
              intro actual matched
              have same := Option.some.inj (matched.symm.trans lookup)
              subst actual
              simpa only [hconfig, houter] using localOuter }
        obtain ⟨actual, reframe, actualLookup, _, decoded, cycle⟩ :=
          selected_positive_continuation frame slot (liftConfig p (applyBounded 2 z a))
            budget ready clock (by omega) step semHalt
        have same : actual = actionCode a := Option.some.inj (actualLookup.symm.trans lookup)
        subst actual
        obtain ⟨tail, labelsWord, after⟩ := split_selected_frame_cycle frame focus
          cycle labels rest tape word selected
        have hc : (frame.reframeNext (actionCode a) reframe).config =
            liftConfig p (applyBounded 2 z a) := action
        have hC : (frame.reframeNext (actionCode a) reframe).capacity =
            semanticCapacityAfter (liftConfig p z) (actionCode a) C := by
          simp only [SemanticCycleFrame.reframeNext, hconfig, hcapacity]
        have ho : (frame.reframeNext (actionCode a) reframe).outer =
            semanticOuterAfter (liftConfig p z) (actionCode a) outer := by
          simp only [SemanticCycleFrame.reframeNext, hconfig, houter]
        obtain ⟨w, hf, out, path, accepts, selectedReady, expansion⟩ := ih (B - 1) (by omega)
          (moveHead a.move head) (applyBounded 2 z a) _ _
          (child_outer_ready p head z C outer outerReady slot a halt rule) childLength nextHalt
          (selected_capacity_next_state p z a C capacity)
          (frame.reframeNext (actionCode a) reframe) hc hC ho reframe.runtime_passive
          (budget - 1) decoded (by omega) tail after
        refine ⟨slot :: w, hf, out, ?_, accepts, .cons halt rule current capacity selectedReady, ?_⟩
        · simpa only [ULogFiniteTapeZipperRun.run, halt, Bool.false_eq_true, ↓reduceIte, rule] using path
        · rw [labelsWord]
          exact .cons frame.encode (frame.reframeNext (actionCode a) reframe).encode
            (.accepted tape) slot w tail cycle expansion

end PakFixedPolyomino.ULogFiniteTapeSelectedMicroInverse
