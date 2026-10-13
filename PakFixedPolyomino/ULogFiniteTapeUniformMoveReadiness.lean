import PakFixedPolyomino.ULogFiniteTapeDeterministicFrameReadiness

/-! Sharp active-frame reserves for labelled nondeterministic programs whose
occupied slots at a given state/read pair have the same head move. Targets
and writes may differ, and the two labels remain distinct. Actual extension
counts charge capacity and outer cells. No physical microtime is asserted. -/
namespace PakFixedPolyomino.ULogFiniteTapeUniformMoveReadiness
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open ULogFiniteTapePhysicalResourceLedger ULogFiniteTapeCapacityReadiness
open ULogFiniteTapeDeterministicFrameReadiness ULogBootstrapExecution
variable {ns : Nat}

def SameMoves (p : BoundedProgram ns 3) : Prop :=
  ∀ q read b c a d, p.rule q read b = some a → p.rule q read c = some d → a.move = d.move

theorem active_nonClock_ready (p : BoundedProgram ns 3) (hp : SameMoves p)
    (z : BoundedConfig ns 3) (slot : Bool) (a : BoundedAction ns 3)
    (hr : p.rule z.state z.focus slot = some a) (C rg lg : Nat)
    (tail : List ULogProgram.Tape)
    (hc : rightCharge z a + rg + (ns - 1) ≤ C) :
    NonClockFrameReady (liftConfig p z) C
      (List.replicate (leftCharge z a + lg) MStarConcreteAlphabet.work ++ tail) := by
  have hselected : ULogBytecode.lookupRule (compile p) z.state.val z.focus.val slot =
      some (actionCode a) := by rw [lookup_compile, hr]; rfl
  have hs := step_capacity_ready p z a C rg hc
  obtain ⟨r, hmem, _, _, _, _⟩ := ULogBytecode.lookupRule_some_mem hselected
  have actual : ∀ b action,
      ULogBytecode.lookupRule (compile p) z.state.val z.focus.val b = some action →
      ∃ d, p.rule z.state z.focus b = some d ∧ actionCode d = action ∧ d.move = a.move := by
    intro b action hb
    rw [lookup_compile] at hb
    obtain ⟨d, hd, he⟩ := Option.map_eq_some_iff.mp hb
    exact ⟨d, hd, he, hp _ _ _ _ _ _ hd hr⟩
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
  · intro b action hb
    obtain ⟨d, _, rfl, hm⟩ := actual b action hb
    have htarget : d.target.val ≤ ns - 1 := by have ht := d.target.isLt; omega
    cases ha : a.move <;> cases hz : z.right <;>
      simp [SemanticCapacityReady, actionCode, liftConfig, hm, ha, rightCharge, hz] at * <;> omega
  · intro b action hb
    obtain ⟨d, _, rfl, hm⟩ := actual b action hb
    cases ha : a.move <;> cases hl : z.leftRev <;>
      simp [SemanticOuterReady, liftConfig, actionCode, leftCharge, hm, ha, hl]
    refine ⟨List.replicate lg MStarConcreteAlphabet.work ++ tail, ?_⟩
    rw [show 1 + lg = lg + 1 by omega, List.replicate_succ]
    rfl

theorem actual_active_ready {p : BoundedProgram ns 3}
    {w : List Bool} {head hf : Int} {z zf : BoundedConfig ns 3} {lg rg : Nat}
    (h : GrowthRun p 2 w head z hf zf lg rg) (hp : SameMoves p)
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

theorem every_raw_active_ready (p : BoundedProgram ns 3) (hp : SameMoves p)
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
  simpa using actual_resource_run hg C (List.replicate lg MStarConcreteAlphabet.work ++ tail)

end PakFixedPolyomino.ULogFiniteTapeUniformMoveReadiness
