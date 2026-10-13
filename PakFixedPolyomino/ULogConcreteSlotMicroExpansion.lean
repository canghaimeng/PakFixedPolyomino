import PakFixedPolyomino.ULogConcreteMicroPathSplitting

/-! Preserve every physical label in first-hit slot-cycle expansion. The
expansion is derived from raw micro-paths by later inverse theorems, never
required as a certificate in the definition of a counted raw micro-path. -/

namespace PakFixedPolyomino.ULogConcreteSlotMicroExpansion
open ULogBootstrapExecution ULogProgram

def cycleWord {slot : Bool} {start finish : Result}
    (cycle : ExactConcreteCycle slot start finish) : List (Fin 2) :=
  List.replicate cycle.choicePrefix.steps 0 ++
    ULogBytecode.slotIndex slot :: List.replicate cycle.cycleSuffix.steps 0

theorem cycleWord_unique {slot : Bool} {start finish₁ finish₂ : Result}
    (a : ExactConcreteCycle slot start finish₁) (b : ExactConcreteCycle slot start finish₂) :
    cycleWord a = cycleWord b := by
  have prefixSteps := a.choicePrefix.steps_eq b.choicePrefix
  have branch := (a.decomposition_unique b).2.1
  let suffix : FirstValidZeroHit IsConcreteCycleStop a.branch finish₂ :=
    { steps := b.cycleSuffix.steps
      valid := by rw [branch]; exact b.cycleSuffix.valid
      hit := b.cycleSuffix.hit
      before := by rw [branch]; exact b.cycleSuffix.before }
  have steps := a.cycleSuffix.steps_eq suffix
  simpa only [cycleWord, prefixSteps] using
    congrArg (fun n => List.replicate b.choicePrefix.steps (0 : Fin 2) ++
      ULogBytecode.slotIndex slot :: List.replicate n 0) steps

inductive SlotMicroExpansion : Result → List Bool → List (Fin 2) → Result → Prop
  | nil (r : Result) : SlotMicroExpansion r [] [] r
  | cons (start middle finish : Result) (slot : Bool) (slots : List Bool)
      (rest : List (Fin 2)) (cycle : ExactConcreteCycle slot start middle)
      (tail : SlotMicroExpansion middle slots rest finish) :
      SlotMicroExpansion start (slot :: slots) (cycleWord cycle ++ rest) finish

theorem to_micro_path {start finish : Result} {slots : List Bool} {labels : List (Fin 2)}
    (expansion : SlotMicroExpansion start slots labels finish) :
    ConcreteMicroPath start labels finish := by
  induction expansion with
  | nil r => exact .nil r
  | cons start middle finish slot slots rest cycle tail ih =>
      exact cycle.toMicroPath.append ih

theorem to_slot_run {start finish : Result} {slots : List Bool} {labels : List (Fin 2)}
    (expansion : SlotMicroExpansion start slots labels finish) :
    ExactConcreteSlotRun start slots finish := by
  induction expansion with
  | nil r => exact .nil r
  | cons start middle finish slot slots rest cycle tail ih =>
      exact .cons start middle finish slot slots cycle ih

theorem exists_expansion {start finish : Result} {slots : List Bool}
    (run : ExactConcreteSlotRun start slots finish) :
    ∃ labels, SlotMicroExpansion start slots labels finish := by
  induction run with
  | nil r => exact ⟨[], .nil r⟩
  | cons start middle finish slot slots cycle tail ih =>
      obtain ⟨labels, expansion⟩ := ih
      exact ⟨cycleWord cycle ++ labels, .cons start middle finish slot slots labels cycle expansion⟩

theorem word_and_finish_unique {start finish₁ finish₂ : Result} {slots : List Bool}
    {labels₁ labels₂ : List (Fin 2)}
    (a : SlotMicroExpansion start slots labels₁ finish₁)
    (b : SlotMicroExpansion start slots labels₂ finish₂) :
    labels₁ = labels₂ ∧ finish₁ = finish₂ := by
  induction a generalizing finish₂ labels₂ with
  | nil r =>
      cases b
      exact ⟨rfl, rfl⟩
  | cons start middle finish slot slots rest cycle tail ih =>
      cases b with
      | cons _ middle₂ finish₂ _ _ rest₂ cycle₂ tail₂ =>
          have next := cycle.finish_unique cycle₂
          subst middle₂
          obtain ⟨word, last⟩ := ih tail₂
          exact ⟨by rw [cycleWord_unique cycle cycle₂, word], last⟩

theorem rejecting_alternative_forces_split {start finish : Result}
    (cycle : ExactConcreteCycle false start finish)
    (reject : ExactConcreteCycle true start .rejected)
    {tape : MStarParserExecution.Zipper Tape} {labels : List (Fin 2)}
    (raw : ConcreteMicroPath start labels (.accepted tape)) :
    ∃ tail, labels = cycleWord cycle ++ tail ∧ ConcreteMicroPath finish tail (.accepted tape) := by
  obtain ⟨rest, prefixWord, atChoice⟩ :=
    ULogConcreteMicroPathSplitting.split_at_cycle_choice cycle raw
  cases rest with
  | nil =>
      have choice := cycle.choicePrefix.hit
      rw [← ULogConcreteMicroPathSplitting.microPath_nil_finish atChoice] at choice
      simp [IsConcreteChoice] at choice
  | cons label rest =>
      fin_cases label
      · have selected : ConcreteMicroPath cycle.choice (ULogBytecode.slotIndex false :: rest)
            (.accepted tape) := by simpa [ULogBytecode.slotIndex] using atChoice
        obtain ⟨tail, suffixWord, last⟩ :=
          ULogConcreteMicroPathSplitting.split_after_cycle_selection cycle selected
        refine ⟨tail, ?_, last⟩
        rw [prefixWord, suffixWord]
        simp only [cycleWord, List.append_assoc, List.cons_append]
        rfl
      · have choiceEq := reject.choicePrefix.finish_unique cycle.choicePrefix
        have selected : ConcreteMicroPath reject.choice (ULogBytecode.slotIndex true :: rest)
            (.accepted tape) := by simpa [choiceEq, ULogBytecode.slotIndex] using atChoice
        exact (ULogConcreteMicroPathSplitting.rejected_cycle_no_accepting_selection reject selected).elim

end PakFixedPolyomino.ULogConcreteSlotMicroExpansion
