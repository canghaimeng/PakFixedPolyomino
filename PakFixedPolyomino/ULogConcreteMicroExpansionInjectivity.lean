import PakFixedPolyomino.ULogConcreteSlotMicroExpansion

/-! Literal micro-labels determine the entire slot word. In particular,
occupied branches with identical effects still have different micro-label
words. First-hit uniqueness supplies the common prefix and suffix lengths. -/

namespace PakFixedPolyomino.ULogConcreteMicroExpansionInjectivity
open ULogBootstrapExecution ULogProgram ULogConcreteSlotMicroExpansion

theorem slots_and_finish_unique {start finish₁ finish₂ : Result}
    {slots₁ slots₂ : List Bool} {labels₁ labels₂ : List (Fin 2)}
    (first : SlotMicroExpansion start slots₁ labels₁ finish₁)
    (last : SlotMicroExpansion start slots₂ labels₂ finish₂)
    (same : labels₁ = labels₂) : slots₁ = slots₂ ∧ finish₁ = finish₂ := by
  induction first generalizing slots₂ labels₂ finish₂ with
  | nil r =>
    cases last with
    | nil => exact ⟨rfl, rfl⟩
    | cons start middle finish slot slots rest cycle tail =>
      have length := congrArg List.length same
      simp only [cycleWord, List.length_append, List.length_replicate,
        List.length_cons, List.length_nil] at length
      omega
  | cons start middle finish slot slots rest cycle tail ih =>
    cases last with
    | nil =>
      have length := congrArg List.length same
      simp only [cycleWord, List.length_append, List.length_replicate,
        List.length_cons, List.length_nil] at length
      omega
    | cons _ middle₂ finish₂ slot₂ slots₂ rest₂ cycle₂ tail₂ =>
      have steps := cycle.choicePrefix.steps_eq cycle₂.choicePrefix
      have selected := congrArg (List.drop cycle.choicePrefix.steps) same
      have selected' :
          ULogBytecode.slotIndex slot :: (List.replicate cycle.cycleSuffix.steps 0 ++ rest) =
          ULogBytecode.slotIndex slot₂ :: (List.replicate cycle₂.cycleSuffix.steps 0 ++ rest₂) := by
        simpa [cycleWord, ← steps, List.append_assoc, List.cons_append] using selected
      have labels := (List.cons.inj selected').1
      have slotEq : slot = slot₂ := by
        cases slot <;> cases slot₂ <;> simp_all [ULogBytecode.slotIndex]
      subst slot₂
      have next := cycle.finish_unique cycle₂
      subst middle₂
      have word := cycleWord_unique cycle cycle₂
      rw [word] at same
      have restEq : rest = rest₂ := List.append_cancel_left same
      obtain ⟨slotsEq, finishEq⟩ := ih tail₂ restEq
      exact ⟨congrArg (List.cons slot) slotsEq, finishEq⟩

end PakFixedPolyomino.ULogConcreteMicroExpansionInjectivity
