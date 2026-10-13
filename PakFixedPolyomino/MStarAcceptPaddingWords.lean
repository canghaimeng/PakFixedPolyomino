import PakFixedPolyomino.PakFullFrameFirstBranch

/-! Actual stationary accept padding, with literal occupied-arrow identities.
This does not yet choose the first accepting prefix of an arbitrary history
or assert a frame/source count. -/
namespace PakFixedPolyomino.MStarAcceptPaddingWords
open PakMStarCouplingCorrectness PakFullFrameTableauReadback
open FiniteOneTapeProgram FiniteOneTapeSemantics

private theorem read_ne_hash (c : MStarConfig)
    (hm : MStarOuterProgram.movable (c.tape c.head) = true) :
    c.tape c.head ≠ MStarOuterProgram.Tape.hash := by
  intro h
  rw [h] at hm
  cases hm

def paddingArrow (c : MStarConfig)
    (hm : MStarOuterProgram.movable (c.tape c.head) = true) :
    MStarULogAssembly.Arrow :=
  ⟨((MStarOuterProgram.State.accept, c.tape c.head), 0), by
    have hrule := (MStarOuterProgram.accept_unique_stay MStarULogAssembly.data
      (read_ne_hash c hm)).1
    intro hnone
    rw [hrule] at hnone
    contradiction⟩

private theorem actionOf_eq_of_rule_eq
    (a : MStarULogAssembly.Arrow)
    (act : Action MStarULogAssembly.State MStarULogAssembly.Tape)
    (h : MStarULogAssembly.program.rule a.val.1.1 a.val.1.2 a.val.2 = some act) :
    actionOf MStarULogAssembly.program a = act := by
  unfold actionOf
  split
  · rename_i found hfound
    exact Option.some.inj (hfound.symm.trans h)
  · rename_i hnone
    exact (a.property hnone).elim

theorem padding_arrow_transition (c : MStarConfig)
    (hm : MStarOuterProgram.movable (c.tape c.head) = true) :
    transition MStarULogAssembly.program (paddingArrow c hm) =
      { sourceState := .accept, read := c.tape c.head,
        write := c.tape c.head, targetState := .accept, move := .stay } := by
  have ha : actionOf MStarULogAssembly.program (paddingArrow c hm) =
      { write := c.tape c.head, target := .accept, move := .stay } :=
    actionOf_eq_of_rule_eq _ _
      (MStarOuterProgram.accept_unique_stay MStarULogAssembly.data (read_ne_hash c hm)).1
  unfold transition
  rw [ha]
  rfl

theorem padding_arrow_step (c : MStarConfig) (hs : c.state = .accept)
    (hm : MStarOuterProgram.movable (c.tape c.head) = true) :
    step MStarULogAssembly.program MStarOuterProgram.movable c (paddingArrow c hm) =
      some c := by
  have hw : writtenTape c (c.tape c.head) = c.tape := by
    funext z
    by_cases hz : z = c.head <;> simp [writtenTape, Function.update, hz]
  unfold step
  rw [padding_arrow_transition]
  simp only [hs, ne_eq, not_true_eq_false, or_self, if_false, hw, moveHead, hm,
    Bool.true_eq, if_true]
  apply congrArg some
  cases c
  simp only at hs
  subst_vars
  rfl

theorem successful_accept_arrow_eq_padding (c d : MStarConfig)
    (hs : c.state = .accept)
    (hm : MStarOuterProgram.movable (c.tape c.head) = true)
    (a : MStarULogAssembly.Arrow)
    (ha : step MStarULogAssembly.program MStarOuterProgram.movable c a = some d) :
    a = paddingArrow c hm := by
  apply arrow_eq_of_successful_steps_same_slot c d c a (paddingArrow c hm) ha
    (padding_arrow_step c hs hm)
  exact accept_successful_arrow_slot_zero c d a hs ha

theorem padding_word_run (c : MStarConfig) (hs : c.state = .accept)
    (hm : MStarOuterProgram.movable (c.tape c.head) = true) (k : Nat) :
    run MStarULogAssembly.program MStarOuterProgram.movable
      (List.replicate k (paddingArrow c hm)) c = some c := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [List.replicate_succ, run_cons, padding_arrow_step c hs hm,
        Option.bind_some, ih]

theorem every_accept_word_is_padding (c d : MStarConfig) (hs : c.state = .accept)
    (hm : MStarOuterProgram.movable (c.tape c.head) = true)
    (labels : List MStarULogAssembly.Arrow)
    (hrun : run MStarULogAssembly.program MStarOuterProgram.movable labels c = some d) :
    d = c ∧ labels = List.replicate labels.length (paddingArrow c hm) := by
  induction labels generalizing d with
  | nil =>
      have heq : c = d := Option.some.inj hrun
      exact ⟨heq.symm, rfl⟩
  | cons a labels ih =>
      cases hstep : step MStarULogAssembly.program MStarOuterProgram.movable c a with
      | none => simp [run_cons, hstep] at hrun
      | some next =>
          have hnext := accept_successor_eq_self c next a hs hstep
          subst next
          have ha := successful_accept_arrow_eq_padding c c hs hm a hstep
          have htail : run MStarULogAssembly.program MStarOuterProgram.movable labels c =
              some d := by simpa [run_cons, hstep] using hrun
          have result := ih d htail
          refine ⟨result.1, ?_⟩
          rw [List.length_cons, List.replicate_succ, ha, result.2]
          simp only [List.length_replicate]

theorem step_finish_movable (c d : MStarConfig) (a : MStarULogAssembly.Arrow)
    (h : step MStarULogAssembly.program MStarOuterProgram.movable c a = some d) :
    MStarOuterProgram.movable (d.tape d.head) = true := by
  unfold step at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · rename_i hm
      have hd := Option.some.inj h
      subst d
      exact hm
    · simp at h

theorem nonempty_run_finish_movable (c d : MStarConfig)
    (labels : List MStarULogAssembly.Arrow) (hne : labels ≠ [])
    (hrun : run MStarULogAssembly.program MStarOuterProgram.movable labels c = some d) :
    MStarOuterProgram.movable (d.tape d.head) = true := by
  induction labels generalizing c d with
  | nil => exact (hne rfl).elim
  | cons a labels ih =>
      cases hstep : step MStarULogAssembly.program MStarOuterProgram.movable c a with
      | none => simp [run_cons, hstep] at hrun
      | some next =>
          have htail : run MStarULogAssembly.program MStarOuterProgram.movable labels next =
              some d := by simpa [run_cons, hstep] using hrun
          by_cases hempty : labels = []
          · subst labels
            have hd : next = d := Option.some.inj htail
            subst d
            exact step_finish_movable c next a hstep
          · exact ih next d hempty htail

end PakFixedPolyomino.MStarAcceptPaddingWords
