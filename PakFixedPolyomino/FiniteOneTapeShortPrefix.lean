import PakFixedPolyomino.FiniteOneTapeRunPrefix

/-! A locally forced phase cannot reach a state excluded from every source
in that phase before consuming the phase. The compared raw word is arbitrary. -/

namespace PakFixedPolyomino.FiniteOneTapeSemantics

open FiniteOneTapeProgram

variable {State Tape : Type*} [Fintype State] [Fintype Tape]
variable [DecidableEq State] [DecidableEq Tape]

theorem short_forced_prefix_excludes
    (P : Program State Tape) (movable : Tape → Bool) (excluded : State → Prop)
    (pre raw : List (Arrow P)) (c out : Config State Tape)
    (hforced : ForcedPrefix P movable pre c)
    (hsources : ∀ a ∈ pre, ¬ excluded (transition P a).sourceState)
    (hrun : run P movable raw c = some out)
    (hlen : raw.length < pre.length) : ¬ excluded out.state := by
  induction pre generalizing raw c out with
  | nil => simp at hlen
  | cons a pre ih =>
      rcases hforced with ⟨d, hstep, hunique, htail⟩
      cases raw with
      | nil =>
          have heq : c = out := Option.some.inj hrun
          have hsource := (step_some_forces_source P movable c d a hstep).1
          rw [← heq, hsource]
          exact hsources a (by simp)
      | cons b raw =>
          cases hb : step P movable c b with
          | none => simp [run, hb] at hrun
          | some e =>
              have hba := hunique b e hb
              subst b
              have hed := step_label_deterministic P movable c e d a hb hstep
              subst e
              apply ih raw d out htail
              · intro b hmem
                exact hsources b (List.mem_cons_of_mem a hmem)
              · simpa [run, hstep] using hrun
              · simpa using hlen

end PakFixedPolyomino.FiniteOneTapeSemantics
