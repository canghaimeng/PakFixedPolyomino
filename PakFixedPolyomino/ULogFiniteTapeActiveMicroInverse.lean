import PakFixedPolyomino.ULogConcreteSlotMicroExpansion
import PakFixedPolyomino.ULogFiniteTapeActiveExactTrace
import PakFixedPolyomino.ULogActiveExactNoRule

/-! ALL arbitrary accepting physical micro-paths from a ready finite-program
frame expand into its actual full slot word. The raw path contains only its
actual local edges and physical labels. Its expansion is a proved conclusion;
no canonical-image or semantic membership condition restricts the raw path. -/

namespace PakFixedPolyomino.ULogFiniteTapeActiveMicroInverse
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeDeterministicFrameReadiness ULogBootstrapExecution
open ULogAlphabet ULogProgram ULogActiveExactCycles ULogConcreteSlotMicroExpansion
open MStarParserExecution (Zipper)
open FiniteOneTapeSemantics (moveHead)

variable {ns : Nat}

theorem every_accepting_micro_path_expands {input : List Bool} {suffix : List Tape}
    (p : BoundedProgram ns 3) (hp : FalseOnly p) (w : List Bool) (head hf : Int)
    (z zf : BoundedConfig ns 3) (C : Nat) (outer : List Tape)
    (active : ActiveReadyRun p w head z C outer)
    (hrun : run p 2 w head z = some (hf, zf))
    (hfinal : zf.state.val = 0) (hstart : boundedHalted z = false)
    (frame : SemanticCycleFrame input suffix)
    (hconfig : frame.config = liftConfig p z)
    (hcapacity : frame.capacity = C) (houter : frame.outer = outer)
    (runtime : PassivePath frame.runtime) (budget : Nat)
    (hclock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some budget)
    (hbudget : w.length ≤ budget)
    (labels : List (Fin 2)) (tape : Zipper Tape)
    (raw : ConcreteMicroPath frame.encode labels (.accepted tape)) :
    SlotMicroExpansion frame.encode w labels (.accepted tape) := by
  induction w generalizing head z C outer frame budget labels with
  | nil =>
      have hz : z = zf := congrArg Prod.snd (Option.some.inj hrun)
      have hh := halted_of_state0 (z := z) (by rw [hz]; exact hfinal)
      rw [hstart] at hh
      contradiction
  | cons slot rest ih =>
      cases active with
      | @cons _ _ _ _ a _ _ halt rule ready tailReady =>
          have hslot := (lookup_actual_action p hp z slot a rule).1
          subst slot
          have htail : run p 2 rest (moveHead a.move head) (applyBounded 2 z a) =
              some (hf, zf) := by
            simpa only [ULogFiniteTapeZipperRun.run, halt, Bool.false_eq_true, ↓reduceIte, rule] using hrun
          have hstep : ULogSemantics.stepSlot false frame.config =
              some (liftConfig p (applyBounded 2 z a)) := by
            rw [hconfig]
            simpa [boundedStepSlot, halt, rule] using
              (stepSlot_liftConfig p (2 : Fin 3) rfl false z)
          have hready : FrameReady frame := by
            apply (frameReady_iff_runtime_and_nonClock frame).2
            exact ⟨runtime, by simpa [hconfig, hcapacity, houter] using ready⟩
          have hnone : ULogBytecode.lookupRule frame.config.program frame.config.state
              frame.config.focus true = none := by
            rw [hconfig]
            change ULogBytecode.lookupRule (compile p) z.state.val z.focus.val true = none
            rw [lookup_compile, hp z.state z.focus]
            rfl
          obtain ⟨rejectCycle⟩ := ULogActiveExactNoRule.branchedCycle_semanticNoRule_exact_nonempty
            frame.config true input frame.clockZeros frame.capacity frame.runtime frame.outer suffix
            runtime hready.focus_lt_three hready.program_nonempty hready.reads_lt_three hnone
          have reject : ExactConcreteCycle true frame.encode .rejected := by
            simpa only [SemanticCycleFrame.encode] using rejectCycle
          by_cases ha : (applyBounded 2 z a).state.val = 0
          · have hrest : rest = [] := by
              cases rest with
              | nil => rfl
              | cons b bs =>
                  rw [zipperSlotRun_halted_cons (2 : Fin 3) p (halted_of_state0 ha)] at htail
                  contradiction
            subst rest
            have hs : ULogSemantics.accepting (liftConfig p (applyBounded 2 z a)) = true := by
              simp [ULogSemantics.accepting, ULogSemantics.acceptCode, liftConfig, ha]
            let witness := exactAcceptingCycleRefinement frame false hready
              (liftConfig p (applyBounded 2 z a)) hstep hs
            obtain ⟨rawTail, word, after⟩ := rejecting_alternative_forces_split witness.exact_cycle reject raw
            have ended := ULogConcreteMicroPathSplitting.microPath_halted_start after (by rfl)
            have tailExpansion : SlotMicroExpansion (.accepted witness.tape) [] rawTail (.accepted tape) := by
              rw [ended.1, ended.2]
              exact .nil _
            rw [word]
            exact .cons frame.encode (.accepted witness.tape) (.accepted tape) false [] rawTail
              witness.exact_cycle tailExpansion
          · have hne : rest ≠ [] := by
              intro hn
              subst rest
              have hz : applyBounded 2 z a = zf := congrArg Prod.snd (Option.some.inj htail)
              exact ha (by rw [hz]; exact hfinal)
            have hnextHalt : boundedHalted (applyBounded 2 z a) = false := by
              cases hh : boundedHalted (applyBounded 2 z a) with
              | false => rfl
              | true =>
                  cases rest with
                  | nil => exact (hne rfl).elim
                  | cons b bs =>
                      rw [zipperSlotRun_halted_cons (2 : Fin 3) p hh] at htail
                      contradiction
            have hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
                frame.config.focus false = some (actionCode a) := by
              rw [hconfig]
              change ULogBytecode.lookupRule (compile p) z.state.val z.focus.val false = _
              rw [lookup_compile, rule]
              rfl
            have haction : ULogSemantics.applyAction frame.config (actionCode a) =
                liftConfig p (applyBounded 2 z a) := by
              rw [hconfig]
              exact (liftConfig_applyBounded p 2 rfl z a).symm
            have hnextSemHalt : ULogSemantics.halted (liftConfig p (applyBounded 2 z a)) = false := by
              simpa [ULogSemantics.halted, liftConfig, boundedHalted] using hnextHalt
            have hpositive : 1 < budget := by
              have hl : 0 < rest.length := by cases rest <;> simp_all
              simp only [List.length_cons] at hbudget
              omega
            obtain ⟨action, reframe, lookup, _, decoded, exactCycle⟩ :=
              positive_continuation frame false (liftConfig p (applyBounded 2 z a))
                budget hready hclock hpositive hstep hnextSemHalt
            have he : action = actionCode a := Option.some.inj (lookup.symm.trans hlookup)
            subst action
            obtain ⟨rawTail, word, after⟩ := rejecting_alternative_forces_split exactCycle reject raw
            have hc : (frame.reframeNext (actionCode a) reframe).config =
                liftConfig p (applyBounded 2 z a) := haction
            have hC : (frame.reframeNext (actionCode a) reframe).capacity =
                semanticCapacityAfter (liftConfig p z) (actionCode a) C := by
              simp [SemanticCycleFrame.reframeNext, hconfig, hcapacity]
            have ho : (frame.reframeNext (actionCode a) reframe).outer =
                semanticOuterAfter (liftConfig p z) (actionCode a) outer := by
              simp [SemanticCycleFrame.reframeNext, hconfig, houter]
            have expansion := ih (moveHead a.move head) (applyBounded 2 z a) _ _ tailReady htail hnextHalt
              (frame.reframeNext (actionCode a) reframe) hc hC ho reframe.runtime_passive
              (budget - 1) decoded (by simp only [List.length_cons] at hbudget; omega) rawTail after
            rw [word]
            exact .cons frame.encode (frame.reframeNext (actionCode a) reframe).encode
              (.accepted tape) false rest rawTail exactCycle expansion

end PakFixedPolyomino.ULogFiniteTapeActiveMicroInverse
