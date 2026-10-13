import PakFixedPolyomino.ULogConcreteChoiceBarrier

/-! Split arbitrary label-preserving physical accepting micro-paths at the
actual first choice and next cycle stop. Raw paths need no semantic/image
certificate. Literal control flow proves that the suffix contains no other
choice, so its actual labels are forced to zero. -/

namespace PakFixedPolyomino.ULogConcreteMicroPathSplitting
open ULogBootstrapExecution ULogControl ULogProgram
open MStarParserExecution (Zipper)
open ULogConcreteChoiceBarrier

theorem microPath_nil_finish {start finish : Result}
    (path : ConcreteMicroPath start [] finish) : finish = start := by
  cases path
  rfl

theorem microPath_halted_start {start finish : Result} {labels : List (Fin 2)}
    (path : ConcreteMicroPath start labels finish) (halted : concreteHalted start = true) :
    labels = [] ∧ finish = start := by
  cases path with
  | nil => exact ⟨rfl, rfl⟩
  | cons start next finish label labels edge tail =>
      cases start <;> simp_all [concreteHalted, validStepAt]

theorem nonchoice_label_zero {start next : Result} {label : Fin 2}
    (edge : validStepAt label start = some next) (noChoice : ¬ IsConcreteChoice start) :
    label = 0 := by
  fin_cases label
  · rfl
  · cases start with
    | accepted z => simp [validStepAt] at edge
    | rejected => simp [validStepAt] at edge
    | stuck => simp [validStepAt] at edge
    | running q z =>
        have hq : q ≠ .chooseSlot := by
          intro he
          subst q
          exact noChoice trivial
        change validStepAt 1 (.running q z) = some next at edge
        rw [validStepAt_one_nonchoose q hq z] at edge
        contradiction

theorem zero_prefix_of_micro_accepting {n : Nat} {start middle : Result}
    {tape : Zipper Tape} {labels : List (Fin 2)}
    (valid : ValidZeroRun n start middle)
    (noChoice : ∀ m, m < n → ¬ IsConcreteChoice (run m start))
    (raw : ConcreteMicroPath start labels (.accepted tape)) :
    ∃ rest, labels = List.replicate n (0 : Fin 2) ++ rest ∧
      ConcreteMicroPath middle rest (.accepted tape) := by
  induction valid generalizing labels with
  | nil r => exact ⟨labels, rfl, raw⟩
  | cons start next middle n edge tail ih =>
      cases raw with
      | nil => simp [validStepAt] at edge
      | cons _ actualNext _ label rawrest observed remaining =>
          have hz := nonchoice_label_zero observed (noChoice 0 (by omega))
          subst label
          have he : actualNext = next := Option.some.inj (observed.symm.trans edge)
          subst actualNext
          have shifted : ∀ m, m < n → ¬ IsConcreteChoice (run m next) := by
            intro m hm hit
            apply noChoice (m + 1) (by omega)
            simpa only [ULogBootstrapExecution.run, validStepAt_zero_some_eq_oneStep edge] using hit
          obtain ⟨rest, word, last⟩ := ih shifted remaining
          refine ⟨rest, ?_, last⟩
          simp only [List.replicate_succ, List.cons_append, word]

theorem split_at_cycle_choice {slot : Bool} {start finish : Result}
    (cycle : ExactConcreteCycle slot start finish)
    {tape : Zipper Tape} {labels : List (Fin 2)}
    (raw : ConcreteMicroPath start labels (.accepted tape)) :
    ∃ rest, labels = List.replicate cycle.choicePrefix.steps (0 : Fin 2) ++ rest ∧
      ConcreteMicroPath cycle.choice rest (.accepted tape) :=
  zero_prefix_of_micro_accepting cycle.choicePrefix.valid cycle.choicePrefix.before raw

theorem split_after_cycle_selection {slot : Bool} {start finish : Result}
    (cycle : ExactConcreteCycle slot start finish)
    {tape : Zipper Tape} {rest : List (Fin 2)}
    (raw : ConcreteMicroPath cycle.choice (ULogBytecode.slotIndex slot :: rest) (.accepted tape)) :
    ∃ tail, rest = List.replicate cycle.cycleSuffix.steps (0 : Fin 2) ++ tail ∧
      ConcreteMicroPath finish tail (.accepted tape) := by
  cases raw with
  | cons _ actualNext _ _ _ edge remaining =>
      have he : actualNext = cycle.branch := Option.some.inj (edge.symm.trans cycle.selected)
      subst actualNext
      exact zero_prefix_of_micro_accepting cycle.cycleSuffix.valid
        (fun m hm => exact_cycle_suffix_no_choice cycle m (by omega)) remaining

theorem rejected_cycle_no_accepting_selection {slot : Bool} {start : Result}
    (cycle : ExactConcreteCycle slot start .rejected)
    {tape : Zipper Tape} {rest : List (Fin 2)}
    (raw : ConcreteMicroPath cycle.choice (ULogBytecode.slotIndex slot :: rest) (.accepted tape)) : False := by
  obtain ⟨tail, _, after⟩ := split_after_cycle_selection cycle raw
  have halted := microPath_halted_start after (by rfl)
  cases halted.2

end PakFixedPolyomino.ULogConcreteMicroPathSplitting
