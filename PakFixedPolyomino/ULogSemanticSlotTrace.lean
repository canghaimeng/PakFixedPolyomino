import PakFixedPolyomino.ULogSemanticPathCount
import PakFixedPolyomino.ULogSemanticRunLift

/-! A logical (rather than list-recursive) presentation of accepting slot traces. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogSemantics

/-- A slot word is accepted when it either stops at an accepting halted
configuration, or spends one unit of budget on a legal slot step and then
continues from the resulting configuration.  The empty word is deliberately
allowed at every positive budget, since accepting paths stop as soon as they
halt. -/
def AcceptingSlotTrace : ℕ → ULogSemantics.Config → List Bool → Prop
  | 0, c, w =>
      w = [] ∧ ULogSemantics.halted c = true ∧ ULogSemantics.accepting c = true
  | t + 1, c, w =>
      (w = [] ∧ ULogSemantics.halted c = true ∧ ULogSemantics.accepting c = true) ∨
        ∃ slot c' rest,
          w = slot :: rest ∧
            ULogSemantics.halted c = false ∧
            ULogSemantics.stepSlot slot c = some c' ∧
            AcceptingSlotTrace t c' rest

theorem mem_acceptingSlotWords_iff (t : ℕ) (c : ULogSemantics.Config)
    (w : List Bool) :
    w ∈ acceptingSlotWords t c ↔ AcceptingSlotTrace t c w := by
  induction t generalizing c w with
  | zero =>
      simp [acceptingSlotWords, AcceptingSlotTrace,
        and_left_comm, and_comm, and_assoc]
  | succ t ih =>
      by_cases hh : ULogSemantics.halted c = true
      · by_cases ha : ULogSemantics.accepting c = true
        · simp [acceptingSlotWords, AcceptingSlotTrace, hh, ha]
        · have haf : ULogSemantics.accepting c = false := by
            cases h : ULogSemantics.accepting c <;> simp_all
          simp [acceptingSlotWords, AcceptingSlotTrace, hh, haf]
      · have hhf : ULogSemantics.halted c = false := by
          cases h : ULogSemantics.halted c <;> simp_all
        simp only [acceptingSlotWords, AcceptingSlotTrace, hh, hhf,
          Bool.false_eq_true, false_and, and_false, true_and, and_true,
          ↓reduceIte, List.mem_flatMap]
        constructor
        · rintro ⟨slot, hslot, hmem⟩
          cases hstep : ULogSemantics.stepSlot slot c with
          | none => simp [hstep] at hmem
          | some c' =>
              simp only [hstep, List.mem_map] at hmem
              rcases hmem with ⟨rest, hrest, rfl⟩
              exact Or.inr ⟨slot, c', rest, by simp, hstep,
                (ih (c := c') (w := rest)).mp hrest⟩
        · rintro (hfalse | ⟨slot, c', rest, hw, hstep, htail⟩)
          · exact hfalse.elim
          subst w
          refine ⟨slot, by simp, ?_⟩
          rw [hstep]
          exact List.mem_map.mpr ⟨rest, (ih (c := c') (w := rest)).mpr htail, rfl⟩

theorem nodup_acceptingSlotWords (t : ℕ) (c : ULogSemantics.Config) :
    (acceptingSlotWords t c).Nodup := by
  induction t generalizing c with
  | zero =>
      by_cases hh : ULogSemantics.halted c = true <;>
        by_cases ha : ULogSemantics.accepting c = true <;>
          simp [acceptingSlotWords, hh, ha]
  | succ t ih =>
      by_cases hh : ULogSemantics.halted c = true
      · by_cases ha : ULogSemantics.accepting c = true <;>
          simp [acceptingSlotWords, hh, ha]
      · have hhf : ULogSemantics.halted c = false := by
          cases h : ULogSemantics.halted c <;> simp_all
        cases hfalse : ULogSemantics.stepSlot false c with
        | none =>
            cases htrue : ULogSemantics.stepSlot true c with
            | none => simp [acceptingSlotWords, hh, hfalse, htrue]
            | some c₁ =>
                rw [show acceptingSlotWords (t + 1) c =
                    (acceptingSlotWords t c₁).map (true :: ·) by
                      simp [acceptingSlotWords, hh, hfalse, htrue]]
                exact (ih c₁).map (by
                  intro a b hab
                  simpa using hab)
        | some c₀ =>
            cases htrue : ULogSemantics.stepSlot true c with
            | none =>
                rw [show acceptingSlotWords (t + 1) c =
                    (acceptingSlotWords t c₀).map (false :: ·) by
                      simp [acceptingSlotWords, hh, hfalse, htrue]]
                exact (ih c₀).map (by
                  intro a b hab
                  simpa using hab)
            | some c₁ =>
                rw [show acceptingSlotWords (t + 1) c =
                    (acceptingSlotWords t c₀).map (false :: ·) ++
                      (acceptingSlotWords t c₁).map (true :: ·) by
                      simp [acceptingSlotWords, hh, hfalse, htrue]]
                apply List.Nodup.append
                · exact (ih c₀).map (by
                    intro a b hab
                    simpa using hab)
                · exact (ih c₁).map (by
                    intro a b hab
                    simpa using hab)
                · apply List.disjoint_left.mpr
                  intro x hx₀ hx₁
                  simp only [List.mem_map] at hx₀ hx₁
                  rcases hx₀ with ⟨a, _, hxa⟩
                  rcases hx₁ with ⟨b, _, hxb⟩
                  rw [← hxa] at hxb
                  cases hxb

theorem card_acceptingSlotWords (t : ℕ) (c : ULogSemantics.Config) :
    (acceptingSlotWords t c).toFinset.card =
      ULogSemantics.machine.acceptingPaths t c := by
  rw [List.toFinset_card_of_nodup (nodup_acceptingSlotWords t c)]
  exact length_acceptingSlotWords t c

theorem AcceptingSlotTrace.toSemanticSlotRun
    {t : ℕ} {c : ULogSemantics.Config} {w : List Bool}
    (htrace : AcceptingSlotTrace t c w) :
    ∃ finish, SemanticSlotRun c w finish ∧
      ULogSemantics.halted finish = true ∧
      ULogSemantics.accepting finish = true := by
  induction t generalizing c w with
  | zero =>
      rcases htrace with ⟨hw, hh, ha⟩
      subst w
      exact ⟨c, .nil c, hh, ha⟩
  | succ t ih =>
      rcases htrace with hhalt |
        ⟨slot, c', rest, hw, _hnotHalted, hstep, htail⟩
      · rcases hhalt with ⟨hw, hh, ha⟩
        subst w
        exact ⟨c, .nil c, hh, ha⟩
      · subst w
        obtain ⟨finish, hrun, hh, ha⟩ := ih htail
        exact ⟨finish, .cons c c' finish slot rest hstep hrun, hh, ha⟩

theorem acceptingSlotWords_concrete_refinement
    (encode : ULogSemantics.Config → Result)
    (refineStep : ∀ (c c' : ULogSemantics.Config) (slot : Bool),
      ULogSemantics.stepSlot slot c = some c' →
        BranchedReaches slot (encode c) (encode c'))
    {t : ℕ} {c : ULogSemantics.Config} {w : List Bool}
    (hw : w ∈ acceptingSlotWords t c) :
    ∃ finish,
      ULogSemantics.halted finish = true ∧
      ULogSemantics.accepting finish = true ∧
      ConcreteBranchedRun (encode c) w (encode finish) := by
  have htrace := (mem_acceptingSlotWords_iff t c w).mp hw
  obtain ⟨finish, hrun, hh, ha⟩ := htrace.toSemanticSlotRun
  exact ⟨finish, hh, ha,
    semanticSlotRun_has_concrete_refinement encode hrun refineStep⟩

end PakFixedPolyomino.ULogBootstrapExecution
