import PakFixedPolyomino.ULogFiniteTapeDeterministicFrameReadiness
import PakFixedPolyomino.ULogActiveExactCycles
import PakFixedPolyomino.ULogLocalTimeAllCycles

/-! Actual active-node resources realize literal FIRST-HIT physical
accepting traces. No global per-tick capacity/outer reserve and no canonical
image membership is present in the concrete trace predicate. All labelled
finite-program words are retained. Source-specific initial runs/resources are
supplied by independently proved input modules; physical bootstrap/raw converse,
physical time and ALL full-frame count remain separate. -/

namespace PakFixedPolyomino.ULogFiniteTapeActiveBoundedTrace

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeDeterministicFrameReadiness ULogBootstrapExecution
open ULogAlphabet ULogProgram ULogActiveExactCycles
open FiniteOneTapeSemantics (moveHead)
open PakULogTraceResourceBound PakULogCycleResourceBound

variable {ns : Nat}

theorem active_head_ready {p : BoundedProgram ns 3} {slot : Bool} {rest : List Bool}
    {head : Int} {z : BoundedConfig ns 3} {C : Nat} {outer : List Tape}
    (h : ActiveReadyRun p (slot :: rest) head z C outer) :
    NonClockFrameReady (liftConfig p z) C outer := by
  cases h with
  | cons _ _ ready _ => exact ready

theorem accepting_run_bounded {input : List Bool} {suffix : List Tape}
    (p : BoundedProgram ns 3) (w : List Bool) (head hf : Int)
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
    (side : ConcretePakSide.Word) (elapsed : Nat)
    (global : GlobalCopiedEnvelope side frame elapsed)
    (hword : elapsed + w.length ≤ PakOuterULogBridge.copiedCoreRadius side) :
    ExactConcreteAcceptingBoundedFuel
      (globalCyclePolynomial (PakOuterULogBridge.copiedCoreRadius side)) frame.encode w := by
  induction w generalizing head z C outer frame budget elapsed with
  | nil =>
      have he := Option.some.inj hrun
      have hz : z = zf := congrArg Prod.snd he
      have hh := halted_of_state0 (z := z) (by rw [hz]; exact hfinal)
      rw [hstart] at hh
      contradiction
  | cons slot rest ih =>
      cases active with
      | @cons _ _ _ _ a _ _ halt rule ready tail =>
          have htail : run p 2 rest (moveHead a.move head) (applyBounded 2 z a) =
              some (hf, zf) := by
            simpa only [ULogFiniteTapeZipperRun.run, halt, Bool.false_eq_true, ↓reduceIte, rule] using hrun
          have hstep : ULogSemantics.stepSlot slot frame.config =
              some (liftConfig p (applyBounded 2 z a)) := by
            rw [hconfig]
            simpa [boundedStepSlot, halt, rule] using
              (stepSlot_liftConfig p (2 : Fin 3) rfl slot z)
          have hready : FrameReady frame := by
            apply (frameReady_iff_runtime_and_nonClock frame).2
            exact ⟨runtime, by simpa [hconfig, hcapacity, houter] using ready⟩
          by_cases ha : (applyBounded 2 z a).state.val = 0
          · have hrest : rest = [] := by
              cases rest with
              | nil => rfl
              | cons b bs =>
                  rw [zipperSlotRun_halted_cons (2 : Fin 3) p (halted_of_state0 ha)] at htail
                  contradiction
            subst rest
            have haccept : ULogSemantics.accepting (liftConfig p (applyBounded 2 z a)) = true := by
              simp [ULogSemantics.accepting, ULogSemantics.acceptCode, liftConfig, ha]
            let witness := exactAcceptingCycleRefinement frame slot hready
              (liftConfig p (applyBounded 2 z a)) hstep haccept
            have bound := exactAcceptingCycle_le_globalCyclePolynomial frame elapsed global
              slot (liftConfig p (applyBounded 2 z a)) hready hstep haccept
            exact ⟨.accepted witness.tape,
              .cons frame.encode (.accepted witness.tape) (.accepted witness.tape)
                slot [] witness.exact_cycle (.nil _),
              witness.exact_cycle.choicePrefix.steps + 1 + witness.exact_cycle.cycleSuffix.steps + 0,
              rfl, .cons _ _ _ _ _ witness.exact_cycle (.nil _) 0 bound (.nil _)⟩
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
                frame.config.focus slot = some (actionCode a) := by
              rw [hconfig]
              change ULogBytecode.lookupRule (compile p) z.state.val z.focus.val slot = _
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
            obtain ⟨action, reframe, lookup, action_eq, decoded, cycle⟩ :=
              positive_continuation frame slot (liftConfig p (applyBounded 2 z a))
                budget hready hclock hpositive hstep hnextSemHalt
            have he : action = actionCode a := Option.some.inj (lookup.symm.trans hlookup)
            subst action
            have hc : (frame.reframeNext (actionCode a) reframe).config =
                liftConfig p (applyBounded 2 z a) := haction
            have hC : (frame.reframeNext (actionCode a) reframe).capacity =
                semanticCapacityAfter (liftConfig p z) (actionCode a) C := by
              simp [SemanticCycleFrame.reframeNext, hconfig, hcapacity]
            have ho : (frame.reframeNext (actionCode a) reframe).outer =
                semanticOuterAfter (liftConfig p z) (actionCode a) outer := by
              simp [SemanticCycleFrame.reframeNext, hconfig, houter]
            have afterGlobal := global.next (actionCode a) reframe (by
              simp only [List.length_cons] at hword
              omega)
            have radius := global.cursorRadius_le slot (actionCode a) hlookup hready.focus_lt_three
            have bound := ULogLocalTimeAllCycles.nonhalting_complete_cycle_bound_of_radius_le
              frame slot hready runtime (actionCode a) hlookup
              (by rw [haction]; exact hnextSemHalt) reframe cycle
              (64 * PakOuterULogBridge.copiedCoreRadius side) radius
            obtain ⟨cycleFinish, physical, fuel, haccept, tailBound⟩ :=
              ih (moveHead a.move head) (applyBounded 2 z a) _ _ tail htail hnextHalt
                (frame.reframeNext (actionCode a) reframe) hc hC ho
                reframe.runtime_passive (budget - 1) decoded (by
                  simp only [List.length_cons] at hbudget
                  omega) (elapsed + 1) afterGlobal (by
                  simp only [List.length_cons] at hword
                  omega)
            exact ⟨cycleFinish,
              .cons frame.encode (frame.reframeNext (actionCode a) reframe).encode
                cycleFinish slot rest cycle physical,
              cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps + fuel,
              haccept, .cons _ _ _ _ _ cycle physical fuel bound tailBound⟩

end PakFixedPolyomino.ULogFiniteTapeActiveBoundedTrace
