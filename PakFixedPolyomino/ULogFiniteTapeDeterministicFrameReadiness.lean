import PakFixedPolyomino.ULogFiniteTapeFrameReadiness
import PakFixedPolyomino.ULogFiniteAlphabetDeterministicRuns

/-! Actual active-cycle readiness for false-slot deterministic ternary
programs. Only selected boundary extensions consume reserves. A terminal
node needs no next cycle, so no fictitious extra outer cell is reserved.
This does not prove a physical clock, time bound or minimum guard. -/

namespace PakFixedPolyomino.ULogFiniteTapeDeterministicFrameReadiness

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open ULogFiniteTapePhysicalResourceLedger ULogFiniteTapeCapacityReadiness
open ULogFiniteTapeFrameReadiness ULogFiniteAlphabetDeterministicRuns
open ULogBootstrapExecution
open FiniteOneTapeSemantics (moveHead)

variable {ns : Nat}

theorem lookup_actual_action (p : BoundedProgram ns 3) (hp : FalseOnly p)
    (z : BoundedConfig ns 3) (slot : Bool) (a : BoundedAction ns 3)
    (hr : p.rule z.state z.focus slot = some a) :
    slot = false ∧
      ULogBytecode.lookupRule (compile p) z.state.val z.focus.val false = some (actionCode a) ∧
      (∀ b action, ULogBytecode.lookupRule (compile p) z.state.val z.focus.val b =
        some action → action = actionCode a) := by
  cases slot with
  | true => rw [hp z.state z.focus] at hr; contradiction
  | false =>
      refine ⟨rfl, ?_, ?_⟩
      · rw [lookup_compile, hr]; rfl
      · intro b action hb
        cases b with
        | true => rw [lookup_compile, hp z.state z.focus] at hb; contradiction
        | false => rw [lookup_compile, hr] at hb; exact (Option.some.inj hb).symm

theorem active_nonClock_ready (p : BoundedProgram ns 3) (hp : FalseOnly p)
    (z : BoundedConfig ns 3) (slot : Bool) (a : BoundedAction ns 3)
    (hr : p.rule z.state z.focus slot = some a) (C rg lg : Nat)
    (tail : List ULogProgram.Tape)
    (hc : rightCharge z a + rg + (ns - 1) ≤ C) :
    NonClockFrameReady (liftConfig p z) C
      (List.replicate (leftCharge z a + lg) MStarConcreteAlphabet.work ++ tail) := by
  have ha := lookup_actual_action p hp z slot a hr
  have hs := step_capacity_ready p z a C rg hc
  obtain ⟨r, hmem, _, _, _, _⟩ := ULogBytecode.lookupRule_some_mem ha.2.1
  refine
    { focus_lt_three := z.focus.isLt
      program_nonempty := ?_
      reads_lt_three := ?_
      writes_lt_three := ?_
      state_le_capacity := hs.1
      capacity_ready := ?_
      outer_ready := ?_ }
  · change compile p ≠ []
    intro hn
    rw [hn] at hmem
    exact List.not_mem_nil hmem
  · intro r hr
    exact (compile_rule_bounded p hr).2.1
  · intro r hr
    exact (compile_rule_bounded p hr).2.2.1
  · intro b action hlookup
    rw [ha.2.2 b action hlookup]
    exact hs.2.1
  · intro b action hlookup
    rw [ha.2.2 b action hlookup]
    cases hm : a.move <;> cases hl : z.leftRev <;>
      simp [SemanticOuterReady, liftConfig, actionCode, leftCharge, hm, hl]
    refine ⟨List.replicate lg MStarConcreteAlphabet.work ++ tail, ?_⟩
    rw [show 1 + lg = lg + 1 by omega, List.replicate_succ]
    rfl

inductive ActiveReadyRun (p : BoundedProgram ns 3) :
    List Bool → Int → BoundedConfig ns 3 → Nat → List ULogProgram.Tape → Prop
  | nil (head : Int) (z : BoundedConfig ns 3) (C : Nat) (outer : List ULogProgram.Tape) :
      ActiveReadyRun p [] head z C outer
  | cons {slot : Bool} {rest : List Bool} {head : Int}
      {z : BoundedConfig ns 3} {a : BoundedAction ns 3}
      {C : Nat} {outer : List ULogProgram.Tape}
      (halt : boundedHalted z = false)
      (rule : p.rule z.state z.focus slot = some a)
      (ready : NonClockFrameReady (liftConfig p z) C outer)
      (tail : ActiveReadyRun p rest (moveHead a.move head) (applyBounded 2 z a)
        (semanticCapacityAfter (liftConfig p z) (actionCode a) C)
        (semanticOuterAfter (liftConfig p z) (actionCode a) outer)) :
      ActiveReadyRun p (slot :: rest) head z C outer

theorem drop_work_prefix (charge remaining : Nat) (tail : List ULogProgram.Tape) :
    (List.replicate (charge + remaining) MStarConcreteAlphabet.work ++ tail).drop charge =
      List.replicate remaining MStarConcreteAlphabet.work ++ tail := by
  rw [List.replicate_add, List.append_assoc]
  simp

theorem actual_active_ready {p : BoundedProgram ns 3}
    {w : List Bool} {head hf : Int} {z zf : BoundedConfig ns 3} {lg rg : Nat}
    (h : GrowthRun p 2 w head z hf zf lg rg) (hp : FalseOnly p)
    (C : Nat) (tail : List ULogProgram.Tape) (hc : rg + (ns - 1) ≤ C) :
    ActiveReadyRun p w head z C (List.replicate lg MStarConcreteAlphabet.work ++ tail) := by
  induction h generalizing C tail with
  | nil => exact ActiveReadyRun.nil _ _ _ _
  | @cons slot rest head hf z zf a lg rg halt rule run ih =>
      apply ActiveReadyRun.cons halt rule
      · exact active_nonClock_ready p hp z slot a rule C rg lg tail (by
          simpa [Nat.add_assoc] using hc)
      · rw [capacity_after_charge, outer_after_charge, drop_work_prefix]
        exact ih _ tail (by omega)

theorem every_raw_active_ready (p : BoundedProgram ns 3) (hp : FalseOnly p)
    (w : List Bool) (head hf : Int) (z zf : BoundedConfig ns 3)
    (hr : run p 2 w head z = some (hf, zf)) :
    ∃ lg rg, GrowthRun p 2 w head z hf zf lg rg ∧
      ∀ C tail, rg + (ns - 1) ≤ C →
        ActiveReadyRun p w head z C (List.replicate lg MStarConcreteAlphabet.work ++ tail) ∧
        resourceRun p 2 w head z C (List.replicate lg MStarConcreteAlphabet.work ++ tail) =
          some (hf, zf, C - rg, tail) := by
  obtain ⟨lg, rg, hg⟩ := every_actual_run p 2 w head hf z zf hr
  refine ⟨lg, rg, hg, ?_⟩
  intro C tail hc
  refine ⟨actual_active_ready hg hp C tail hc, ?_⟩
  have hresource := actual_resource_run hg C (List.replicate lg MStarConcreteAlphabet.work ++ tail)
  simpa using hresource

end PakFixedPolyomino.ULogFiniteTapeDeterministicFrameReadiness
