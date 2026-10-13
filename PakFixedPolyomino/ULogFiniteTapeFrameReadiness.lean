import PakFixedPolyomino.ULogFiniteTapeCapacityReadiness
import PakFixedPolyomino.ULogScheduledContinuation

/-! Literal non-clock frame readiness along every successful ternary run.
The reserve is charged only at actual left/right boundary extensions.
One additional outer cell and one state-capacity cell give uniform local
readiness even at the final node. Clock execution and physical time are
separate obligations. -/

namespace PakFixedPolyomino.ULogFiniteTapeFrameReadiness

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open ULogFiniteTapePhysicalResourceLedger ULogBootstrapExecution
open FiniteOneTapeSemantics (moveHead)

variable {ns : Nat}

theorem lift_nonClock_ready (p : BoundedProgram ns 3) (z : BoundedConfig ns 3)
    (C : Nat) (outer : List ULogProgram.Tape)
    (hp : compile p ≠ []) (hc : ns ≤ C)
    (ho : ∃ tail, outer = MStarConcreteAlphabet.work :: tail) :
    NonClockFrameReady (liftConfig p z) C outer := by
  refine
    { focus_lt_three := z.focus.isLt
      program_nonempty := hp
      reads_lt_three := ?_
      writes_lt_three := ?_
      state_le_capacity := ?_
      capacity_ready := ?_
      outer_ready := ?_ }
  · intro r hr
    exact (compile_rule_bounded p hr).2.1
  · intro r hr
    exact (compile_rule_bounded p hr).2.2.1
  · change z.state.val ≤ C
    have hz := z.state.isLt
    omega
  · intro slot action hlookup
    obtain ⟨r, hr, _, _, _, haction⟩ := ULogBytecode.lookupRule_some_mem hlookup
    have ht : action.target < ns := by
      rw [← haction]
      exact (compile_rule_bounded p hr).2.2.2
    have htC : action.target < C := lt_of_lt_of_le ht hc
    unfold SemanticCapacityReady
    cases hm : action.move <;> cases hz : (liftConfig p z).right <;>
      simp [hm, hz] <;> omega
  · intro slot action hlookup
    unfold SemanticOuterReady
    cases hm : action.move <;> cases hz : (liftConfig p z).leftRev <;>
      simp [hm, hz]
    exact ho

inductive NonClockReadyRun (p : BoundedProgram ns 3) :
    List Bool → Int → BoundedConfig ns 3 → Nat → List ULogProgram.Tape → Prop
  | nil {head : Int} {z : BoundedConfig ns 3} {C : Nat} {outer : List ULogProgram.Tape}
      (ready : NonClockFrameReady (liftConfig p z) C outer) :
      NonClockReadyRun p [] head z C outer
  | cons {slot : Bool} {rest : List Bool} {head : Int}
      {z : BoundedConfig ns 3} {a : BoundedAction ns 3}
      {C : Nat} {outer : List ULogProgram.Tape}
      (halt : boundedHalted z = false)
      (rule : p.rule z.state z.focus slot = some a)
      (ready : NonClockFrameReady (liftConfig p z) C outer)
      (tail : NonClockReadyRun p rest (moveHead a.move head) (applyBounded 2 z a)
        (semanticCapacityAfter (liftConfig p z) (actionCode a) C)
        (semanticOuterAfter (liftConfig p z) (actionCode a) outer)) :
      NonClockReadyRun p (slot :: rest) head z C outer

theorem drop_outer_reserve (charge remaining : Nat) (tail : List ULogProgram.Tape) :
    (List.replicate (charge + remaining + 1) MStarConcreteAlphabet.work ++ tail).drop charge =
      List.replicate (remaining + 1) MStarConcreteAlphabet.work ++ tail := by
  rw [show charge + remaining + 1 = charge + (remaining + 1) by omega,
    List.replicate_add, List.append_assoc]
  simp

theorem actual_nonClock_ready {p : BoundedProgram ns 3}
    {w : List Bool} {head hf : Int} {z zf : BoundedConfig ns 3} {lg rg : Nat}
    (h : GrowthRun p 2 w head z hf zf lg rg)
    (hp : compile p ≠ []) (C : Nat) (tail : List ULogProgram.Tape)
    (hc : rg + ns ≤ C) :
    NonClockReadyRun p w head z C
      (List.replicate (lg + 1) MStarConcreteAlphabet.work ++ tail) := by
  induction h generalizing C tail with
  | @nil head z =>
      apply NonClockReadyRun.nil
      exact lift_nonClock_ready p z C _ hp (by omega) ⟨tail, rfl⟩
  | @cons slot rest head hf z zf a lg rg halt rule run ih =>
      apply NonClockReadyRun.cons halt rule
      · apply lift_nonClock_ready p z C _ hp (by omega)
        refine ⟨List.replicate (leftCharge z a + lg) MStarConcreteAlphabet.work ++ tail, ?_⟩
        simp [List.replicate_succ, List.append_assoc]
      · rw [capacity_after_charge, outer_after_charge, drop_outer_reserve]
        exact ih _ tail (by omega)

theorem every_raw_nonClock_ready (p : BoundedProgram ns 3)
    (hp : compile p ≠ []) (w : List Bool) (head hf : Int) (z zf : BoundedConfig ns 3)
    (hr : run p 2 w head z = some (hf, zf)) :
    ∃ lg rg, GrowthRun p 2 w head z hf zf lg rg ∧
      ∀ C tail, rg + ns ≤ C → NonClockReadyRun p w head z C
        (List.replicate (lg + 1) MStarConcreteAlphabet.work ++ tail) := by
  obtain ⟨lg, rg, hg⟩ := every_actual_run p 2 w head hf z zf hr
  exact ⟨lg, rg, hg, actual_nonClock_ready hg hp⟩

theorem NonClockReadyRun.final_ready {p : BoundedProgram ns 3}
    {w : List Bool} {head hf : Int} {z zf : BoundedConfig ns 3}
    {C Cf : Nat} {outer outerf : List ULogProgram.Tape}
    (h : NonClockReadyRun p w head z C outer)
    (hr : resourceRun p 2 w head z C outer = some (hf, zf, Cf, outerf)) :
    NonClockFrameReady (liftConfig p zf) Cf outerf := by
  induction h generalizing hf zf Cf outerf with
  | nil ready =>
      simp only [resourceRun, Option.some.injEq, Prod.mk.injEq] at hr
      rcases hr with ⟨_, rfl, rfl, rfl⟩
      exact ready
  | cons halt rule ready tail ih =>
      apply ih
      simpa [resourceRun, halt, rule] using hr

theorem every_raw_resource_ready (p : BoundedProgram ns 3)
    (hp : compile p ≠ []) (w : List Bool) (head hf : Int) (z zf : BoundedConfig ns 3)
    (hr : run p 2 w head z = some (hf, zf)) :
    ∃ lg rg, GrowthRun p 2 w head z hf zf lg rg ∧
      ∀ C tail, rg + ns ≤ C →
        NonClockReadyRun p w head z C
          (List.replicate (lg + 1) MStarConcreteAlphabet.work ++ tail) ∧
        resourceRun p 2 w head z C
            (List.replicate (lg + 1) MStarConcreteAlphabet.work ++ tail) =
          some (hf, zf, C - rg,
            (List.replicate (lg + 1) MStarConcreteAlphabet.work ++ tail).drop lg) ∧
        NonClockFrameReady (liftConfig p zf) (C - rg)
          (MStarConcreteAlphabet.work :: tail) := by
  obtain ⟨lg, rg, hg⟩ := every_actual_run p 2 w head hf z zf hr
  refine ⟨lg, rg, hg, ?_⟩
  intro C tail hc
  have hready := actual_nonClock_ready hg hp C tail hc
  have hresource := actual_resource_run hg C
    (List.replicate (lg + 1) MStarConcreteAlphabet.work ++ tail)
  refine ⟨hready, hresource, ?_⟩
  have hfinal := hready.final_ready hresource
  have hdrop : (List.replicate (lg + 1) MStarConcreteAlphabet.work ++ tail).drop lg =
      MStarConcreteAlphabet.work :: tail := by
    simpa using drop_outer_reserve lg 0 tail
  simpa only [hdrop] using hfinal

theorem final_frame_ready {input : List Bool} {suffix : List ULogProgram.Tape}
    (frame : SemanticCycleFrame input suffix)
    (ready : NonClockFrameReady frame.config frame.capacity frame.outer)
    (runtime : PassivePath frame.runtime) : FrameReady frame :=
  (frameReady_iff_runtime_and_nonClock frame).mpr ⟨runtime, ready⟩

end PakFixedPolyomino.ULogFiniteTapeFrameReadiness
