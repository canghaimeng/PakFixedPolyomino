import PakFixedPolyomino.FiniteOneTapeSemantics

/-! # Literal slot words determine successful one-tape histories

The source pair is recovered from the current configuration, rather than
stored in an assumed normal-form certificate. Distinct occupied slots remain
distinct paths even if they write the same symbol and reach the same state.
-/

namespace PakFixedPolyomino.FiniteOneTapeSemantics

open FiniteOneTapeProgram

variable {State Tape : Type*}
variable [Fintype State] [Fintype Tape]
variable [DecidableEq State] [DecidableEq Tape]

def arrowSlots (P : Program State Tape) (arrows : List (Arrow P)) : List (Fin 2) :=
  arrows.map fun a => a.1.2

theorem successful_arrows_eq_of_slot_eq
    (P : Program State Tape) (movable : Tape → Bool)
    (c d e : Config State Tape) (a b : Arrow P)
    (ha : step P movable c a = some d)
    (hb : step P movable c b = some e)
    (hslot : a.1.2 = b.1.2) : a = b := by
  have hsa := step_some_forces_source P movable c d a ha
  have hsb := step_some_forces_source P movable c e b hb
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · exact hsa.1.symm.trans hsb.1
    · exact hsa.2.symm.trans hsb.2
  · exact hslot

/-- No restriction to a chosen canonical image: both arrow lists are
arbitrary successful executions from the displayed starting configuration. -/
theorem successful_runs_eq_of_slots_eq
    (P : Program State Tape) (movable : Tape → Bool)
    (as bs : List (Arrow P)) (c d e : Config State Tape)
    (ha : run P movable as c = some d)
    (hb : run P movable bs c = some e)
    (hslots : arrowSlots P as = arrowSlots P bs) : as = bs ∧ d = e := by
  induction as generalizing bs c d e with
  | nil =>
      cases bs with
      | nil =>
          have hd : c = d := Option.some.inj ha
          have he : c = e := Option.some.inj hb
          exact ⟨rfl, hd.symm.trans he⟩
      | cons b bs => simp [arrowSlots] at hslots
  | cons a as ih =>
      cases bs with
      | nil => simp [arrowSlots] at hslots
      | cons b bs =>
          have hparts := List.cons.inj hslots
          cases hstepA : step P movable c a with
          | none => simp [run, hstepA] at ha
          | some cA =>
              cases hstepB : step P movable c b with
              | none => simp [run, hstepB] at hb
              | some cB =>
                  have hab := successful_arrows_eq_of_slot_eq P movable
                    c cA cB a b hstepA hstepB hparts.1
                  subst b
                  have hc := step_label_deterministic P movable c cA cB a
                    hstepA hstepB
                  subst cB
                  have htailA : run P movable as cA = some d := by
                    simpa [run, hstepA] using ha
                  have htailB : run P movable bs cA = some e := by
                    simpa [run, hstepA] using hb
                  rcases ih bs cA d e htailA htailB hparts.2 with ⟨hlist, hend⟩
                  exact ⟨congrArg (List.cons a) hlist, hend⟩

/-- The raw domain stores the actual arrow list and successful execution,
with no stored source choices or canonicality predicate. -/
abbrev SuccessfulRun (P : Program State Tape) (movable : Tape → Bool)
    (c : Config State Tape) :=
  {as : List (Arrow P) // ∃ out, run P movable as c = some out}

theorem successfulRun_slots_injective
    (P : Program State Tape) (movable : Tape → Bool) (c : Config State Tape) :
    Function.Injective (fun r : SuccessfulRun P movable c => arrowSlots P r.1) := by
  intro a b h
  rcases a.2 with ⟨d, hd⟩
  rcases b.2 with ⟨e, he⟩
  apply Subtype.ext
  exact (successful_runs_eq_of_slots_eq P movable a.1 b.1 c d e hd he h).1

end PakFixedPolyomino.FiniteOneTapeSemantics
