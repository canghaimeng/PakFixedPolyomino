import PakFixedPolyomino.ULogFiniteTapeDeterministicFrameReadiness

/-! Uniform bounds on EVERY successful prefix derive readiness at the
actual reachable nonhalting node, including both occupied slots. This
generic bridge exposes its growth-bound premise; concrete scanner modules
must derive it internally. It makes no physical inverse or time claim. -/

namespace PakFixedPolyomino.ULogFiniteTapeBoundedGrowthReadiness
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open ULogFiniteTapePhysicalResourceLedger ULogFiniteTapeCapacityReadiness
open ULogFiniteTapeDeterministicFrameReadiness ULogBootstrapExecution
open FiniteOneTapeSemantics (moveHead)

variable {ns nt : Nat}

theorem growth_append {p : BoundedProgram ns nt} {blank : Fin nt}
    {u v : List Bool} {h0 h1 h2 : Int} {z0 z1 z2 : BoundedConfig ns nt}
    {l1 r1 l2 r2 : Nat}
    (first : GrowthRun p blank u h0 z0 h1 z1 l1 r1)
    (last : GrowthRun p blank v h1 z1 h2 z2 l2 r2) :
    GrowthRun p blank (u ++ v) h0 z0 h2 z2 (l1 + l2) (r1 + r2) := by
  induction first with
  | nil => simpa using last
  | cons halt rule tail ih =>
      simpa only [List.cons_append, Nat.add_assoc] using
        GrowthRun.cons halt rule (ih last)

def AllGrowthBounded (p : BoundedProgram ns 3) (head : Int)
    (z : BoundedConfig ns 3) (L R : Nat) : Prop :=
  ∀ w hf out lg rg, GrowthRun p 2 w head z hf out lg rg → lg ≤ L ∧ rg ≤ R

theorem reachable_nonClock_ready (p : BoundedProgram ns 3)
    (hp : compile p ≠ []) (head : Int) (z : BoundedConfig ns 3) (L R : Nat)
    (bounds : AllGrowthBounded p head z L R)
    (w : List Bool) (hf : Int) (out : BoundedConfig ns 3) (lg rg : Nat)
    (path : GrowthRun p 2 w head z hf out lg rg)
    (halt : boundedHalted out = false)
    (C : Nat) (tail : List ULogProgram.Tape) (hc : R + (ns - 1) ≤ C) :
    NonClockFrameReady (liftConfig p out) (C - rg)
      ((List.replicate L MStarConcreteAlphabet.work ++ tail).drop lg) := by
  have past := bounds _ _ _ _ _ path
  have stateBound : out.state.val ≤ ns - 1 := by
    have h := out.state.isLt
    omega
  have extension : ∀ slot a, p.rule out.state out.focus slot = some a →
      lg + leftCharge out a ≤ L ∧ rg + rightCharge out a ≤ R := by
    intro slot a rule
    have next : GrowthRun p 2 [slot] hf out (moveHead a.move hf)
        (applyBounded 2 out a) (leftCharge out a) (rightCharge out a) := by
      simpa using GrowthRun.cons halt rule
        (GrowthRun.nil (moveHead a.move hf) (applyBounded 2 out a))
    exact bounds _ _ _ _ _ (growth_append path next)
  have lookup : ∀ slot action,
      ULogBytecode.lookupRule (compile p) out.state.val out.focus.val slot = some action →
      ∃ a, p.rule out.state out.focus slot = some a ∧ actionCode a = action := by
    intro slot action rule
    rw [lookup_compile] at rule
    exact Option.map_eq_some_iff.mp rule
  refine
    { focus_lt_three := out.focus.isLt
      program_nonempty := hp
      reads_lt_three := ?_
      writes_lt_three := ?_
      state_le_capacity := by change out.state.val ≤ C - rg; omega
      capacity_ready := ?_
      outer_ready := ?_ }
  · intro r hr
    exact (compile_rule_bounded p hr).2.1
  · intro r hr
    exact (compile_rule_bounded p hr).2.2.1
  · intro slot action rule
    obtain ⟨a, ha, rfl⟩ := lookup slot action rule
    have available := (extension slot a ha).2
    exact (step_capacity_ready p out a (C - rg) 0 (by omega)).2.1
  · intro slot action rule
    obtain ⟨a, ha, rfl⟩ := lookup slot action rule
    have available := (extension slot a ha).1
    have drop : (List.replicate L MStarConcreteAlphabet.work ++ tail).drop lg =
        List.replicate (L - lg) MStarConcreteAlphabet.work ++ tail := by
      conv_lhs => rw [show L = lg + (L - lg) by omega]
      exact drop_work_prefix lg (L - lg) tail
    cases hm : a.move <;> cases hl : out.leftRev <;>
      simp only [SemanticOuterReady, actionCode, liftConfig, hm, hl, List.map_cons]
    have positive : 0 < L - lg := by
      simp only [leftCharge, hm, hl] at available
      omega
    refine ⟨List.replicate (L - lg - 1) MStarConcreteAlphabet.work ++ tail, ?_⟩
    rw [drop, show L - lg = (L - lg - 1) + 1 by omega, List.replicate_succ]
    rfl

theorem every_reachable_resource_ready (p : BoundedProgram ns 3)
    (hp : compile p ≠ []) (head : Int) (z : BoundedConfig ns 3) (L R : Nat)
    (bounds : AllGrowthBounded p head z L R)
    (w : List Bool) (hf : Int) (out : BoundedConfig ns 3)
    (path : run p 2 w head z = some (hf, out))
    (halt : boundedHalted out = false)
    (C : Nat) (tail : List ULogProgram.Tape) (hc : R + (ns - 1) ≤ C) :
    ∃ lg rg, lg ≤ L ∧ rg ≤ R ∧
      resourceRun p 2 w head z C (List.replicate L MStarConcreteAlphabet.work ++ tail) =
        some (hf, out, C - rg,
          (List.replicate L MStarConcreteAlphabet.work ++ tail).drop lg) ∧
      NonClockFrameReady (liftConfig p out) (C - rg)
        ((List.replicate L MStarConcreteAlphabet.work ++ tail).drop lg) := by
  obtain ⟨lg, rg, growth⟩ := every_actual_run p 2 w head hf z out path
  have bound := bounds _ _ _ _ _ growth
  exact ⟨lg, rg, bound.1, bound.2, actual_resource_run growth C _,
    reachable_nonClock_ready p hp head z L R bounds w hf out lg rg growth halt C tail hc⟩

end PakFixedPolyomino.ULogFiniteTapeBoundedGrowthReadiness
