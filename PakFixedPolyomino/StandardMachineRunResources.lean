import PakFixedPolyomino.StandardNondeterministicMachine

/-! # Actual spatial bounds for standard one-tape runs

These follow from physical one-cell writes/moves. They apply to arbitrary
successful label lists and every operational prefix. No arithmetic-operation
bound is substituted for machine time, and no workspace certificate is a
premise of the source definition.
-/

namespace PakFixedPolyomino.StandardNondeterministicMachine

open FiniteOneTapeSemantics (moveHead writtenTape)

variable {ns nt branching : ℕ}

theorem step_geometry (M : Machine ns nt branching) (slot : Fin branching)
    (c out : Configuration ns nt) (hstep : step M slot c = some out) :
    c.head - 1 ≤ out.head ∧ out.head ≤ c.head + 1 ∧
      ∀ z : Int, z ≠ c.head → out.tape z = c.tape z := by
  cases hrule : M.rule c.state (c.tape c.head) slot with
  | none => simp [step, hrule] at hstep
  | some a =>
      have hout :
          { state := a.target, head := moveHead a.move c.head,
            tape := writtenTape c a.write } = out := by
        simpa [step, hrule] using hstep
      subst out
      refine ⟨?_, ?_, ?_⟩
      · cases a.move <;> simp [moveHead] <;> omega
      · cases a.move <;> simp [moveHead] <;> omega
      · intro z hne
        simp [writtenTape, Function.update, hne]

theorem run_geometry (M : Machine ns nt branching) (slots : List (Fin branching))
    (c out : Configuration ns nt) (hrun : run M slots c = some out) :
    c.head - (slots.length : Int) ≤ out.head ∧
      out.head ≤ c.head + (slots.length : Int) ∧
      ∀ z : Int,
        z < c.head - (slots.length : Int) ∨ c.head + (slots.length : Int) < z →
        out.tape z = c.tape z := by
  induction slots generalizing c with
  | nil =>
      have heq : c = out := Option.some.inj hrun
      subst out
      simp
  | cons slot slots ih =>
      cases hstep : step M slot c with
      | none => simp [run, hstep] at hrun
      | some middle =>
          have htail : run M slots middle = some out := by
            simpa [run, hstep] using hrun
          obtain ⟨hlo, hhi, htape⟩ := ih middle htail
          obtain ⟨hstepLo, hstepHi, hstepTape⟩ := step_geometry M slot c middle hstep
          refine ⟨?_, ?_, ?_⟩
          · simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
            omega
          · simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
            omega
          · intro z hz
            have houtside :
                z < middle.head - (slots.length : Int) ∨
                  middle.head + (slots.length : Int) < z := by
              simp only [List.length_cons, Int.natCast_add, Int.natCast_one] at hz
              rcases hz with hz | hz
              · left; omega
              · right; omega
            have hne : z ≠ c.head := by
              simp only [List.length_cons, Int.natCast_add, Int.natCast_one] at hz
              omega
            exact (htape z houtside).trans (hstepTape z hne)

/-- Every actual successful prefix stays in the physical time-radius. -/
theorem prefix_head_bound (M : Machine ns nt branching) (slots : List (Fin branching))
    (c out : Configuration ns nt) (k : ℕ)
    (hrun : run M (slots.take k) c = some out) :
    c.head - (k : Int) ≤ out.head ∧ out.head ≤ c.head + (k : Int) := by
  obtain ⟨hlo, hhi, _⟩ := run_geometry M (slots.take k) c out hrun
  have hlen : (slots.take k).length ≤ k := List.length_take_le _ _
  constructor <;> omega

/-- All initialized input and written cells lie inside a linear interval in
input length plus the actual number of physical transitions. -/
theorem initialized_run_exterior (M : Machine ns nt branching) (x : List Bool)
    (slots : List (Fin branching)) (out : Configuration ns nt)
    (hrun : run M slots (initial M x) = some out) (z : Int)
    (hz : z < -(slots.length : Int) ∨
      (x.length : Int) + (slots.length : Int) + 1 ≤ z) :
    out.tape z = M.blank := by
  have hgeometry := run_geometry M slots (initial M x) out hrun
  have htape : out.tape z = inputTape M x z := by
    apply hgeometry.2.2 z
    simp only [initial]
    rcases hz with hz | hz
    · left; omega
    · right; omega
  rw [htape]
  rcases hz with hz | hz
  · apply inputTape_neg M x z
    omega
  · apply inputTape_ge M x z
    omega

/-- Public acceptance scope for source counts and actual physical runs.
This supplies neither effective normalization nor source hardness. -/
theorem count_and_physical_resources (M : Machine ns nt branching)
    (x : List Bool) (bound : ℕ) (htime : RunsAtMost M x bound) :
    Nonempty (AcceptingCode M x bound ≃ AcceptingLeaf M x) ∧
    (∀ bound₁ bound₂, bound ≤ bound₁ → bound ≤ bound₂ →
      acceptingCount M x bound₁ = acceptingCount M x bound₂) ∧
    (∀ slots out, run M slots (initial M x) = some out →
      -(slots.length : Int) ≤ out.head ∧ out.head ≤ (slots.length : Int) ∧
      ∀ z : Int, z < -(slots.length : Int) ∨
        (x.length : Int) + (slots.length : Int) + 1 ≤ z →
        out.tape z = M.blank) := by
  refine ⟨⟨acceptingLeavesEquiv M x bound htime⟩, ?_, ?_⟩
  · exact fun b₁ b₂ h₁ h₂ => acceptingCount_eq_of_bounds M x bound b₁ b₂ htime h₁ h₂
  · intro slots out hrun
    have hg := run_geometry M slots (initial M x) out hrun
    refine ⟨?_, ?_, initialized_run_exterior M x slots out hrun⟩
    · simpa [initial] using hg.1
    · simpa [initial] using hg.2.1

end PakFixedPolyomino.StandardNondeterministicMachine
