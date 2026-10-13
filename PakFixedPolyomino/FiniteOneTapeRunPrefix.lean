import PakFixedPolyomino.FiniteOneTapeRunSlots

/-! # Forced prefixes of arbitrary successful histories

The compared raw execution is unrestricted. A deterministic prefix records
the actual occupied arrows and local uniqueness along that prefix only.
The scanner phase grammar must establish this condition before using the
converse to reconstruct an entire window cycle.
-/

namespace PakFixedPolyomino.FiniteOneTapeSemantics

open FiniteOneTapeProgram

variable {State Tape : Type*}
variable [Fintype State] [Fintype Tape]
variable [DecidableEq State] [DecidableEq Tape]

def ForcedPrefix (P : Program State Tape) (movable : Tape → Bool) :
    List (Arrow P) → Config State Tape → Prop
  | [], _ => True
  | a :: as, c => ∃ d,
      step P movable c a = some d ∧
      (∀ b e, step P movable c b = some e → b = a) ∧
      ForcedPrefix P movable as d

/-- A successful raw run at least as long as a locally forced prefix
begins with precisely that prefix, at its actual operational endpoint. -/
theorem forcedPrefix_split_successful_run
    (P : Program State Tape) (movable : Tape → Bool)
    (pre raw : List (Arrow P)) (c out : Config State Tape)
    (hforced : ForcedPrefix P movable pre c)
    (hrun : run P movable raw c = some out)
    (hlength : pre.length ≤ raw.length) :
    ∃ tail boundary,
      raw = pre ++ tail ∧
      run P movable pre c = some boundary ∧
      run P movable tail boundary = some out := by
  induction pre generalizing raw c out with
  | nil => exact ⟨raw, c, rfl, rfl, hrun⟩
  | cons a pre ih =>
      rcases hforced with ⟨d, hstep, hunique, htail⟩
      cases raw with
      | nil => simp at hlength
      | cons b raw =>
          cases hrawstep : step P movable c b with
          | none => simp [run, hrawstep] at hrun
          | some e =>
              have hba := hunique b e hrawstep
              subst b
              have hed := step_label_deterministic P movable c e d a hrawstep hstep
              subst e
              have hruntail : run P movable raw d = some out := by
                simpa [run, hstep] using hrun
              have htail_length : pre.length ≤ raw.length := by simpa using hlength
              obtain ⟨tail, boundary, heq, hprefix, hremaining⟩ :=
                ih raw d out htail hruntail htail_length
              refine ⟨tail, boundary, ?_, ?_, hremaining⟩
              · simp [heq]
              · simpa [run, hstep] using hprefix

theorem forcedPrefix_unique_successful_run
    (P : Program State Tape) (movable : Tape → Bool)
    (pre raw : List (Arrow P)) (c out : Config State Tape)
    (hforced : ForcedPrefix P movable pre c)
    (hrun : run P movable raw c = some out)
    (hlength : pre.length = raw.length) :
    raw = pre ∧ run P movable pre c = some out := by
  obtain ⟨tail, boundary, heq, hprefix, htail⟩ :=
    forcedPrefix_split_successful_run P movable pre raw c out
      hforced hrun (Nat.le_of_eq hlength)
  have hnil : tail = [] := by
    apply List.length_eq_zero_iff.mp
    have : raw.length = pre.length + tail.length := by simp [heq]
    omega
  subst tail
  simp only [List.append_nil] at heq
  exact ⟨heq, heq ▸ hrun⟩

end PakFixedPolyomino.FiniteOneTapeSemantics
