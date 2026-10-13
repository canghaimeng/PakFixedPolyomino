import PakFixedPolyomino.ULogConcreteMicroPathSplitting

/-! ALL accepting physical words cross the actual first bootstrap boundary.
The premise is a genuine first-hit run, not a selected image of raw paths. -/

namespace PakFixedPolyomino.ULogBootstrapMicroPrefix
open ULogBootstrapExecution ULogConcreteChoiceBarrier ULogConcreteMicroPathSplitting
open MStarParserExecution (Zipper)
open ULogProgram

theorem zero_run_live_before {n : Nat} {start finish : Result}
    (valid : ValidZeroRun n start finish) (m : Nat) (hm : m < n) :
    concreteHalted (run m start) = false := by
  induction valid generalizing m with
  | nil => omega
  | cons start next finish n edge tail ih =>
      cases m with
      | zero => cases start <;> simp_all [run, validStepAt, concreteHalted]
      | succ m =>
          simpa only [run, validStepAt_zero_some_eq_oneStep edge] using ih m (by omega)

theorem first_boundary_choice_free {start finish : Result}
    (hit : FirstValidZeroHit IsConcreteCycleBoundary start finish)
    (outside : preChoiceResult start = false) :
    ∀ m, m < hit.steps → ¬ IsConcreteChoice (run m start) := by
  have noStop : ∀ m, m < hit.steps → ¬ IsConcreteCycleStop (run m start) := by
    intro m hm stop
    rcases stop with boundary | halted
    · exact hit.before m hm boundary
    · rw [zero_run_live_before hit.valid m hm] at halted
      contradiction
  have allOutside := outside_before_boundary hit.valid noStop outside
  intro m hm choice
  have current := allOutside m (by omega)
  cases h : run m start with
  | accepted z => simp [h, IsConcreteChoice] at choice
  | rejected => simp [h, IsConcreteChoice] at choice
  | stuck => simp [h, IsConcreteChoice] at choice
  | running q z =>
      have hq : q = .chooseSlot := by cases q <;> simp_all [h, IsConcreteChoice]
      simp [h, hq, preChoiceResult, preChoice] at current

theorem zero_run_micro_path {n : Nat} {start finish : Result}
    (valid : ValidZeroRun n start finish) :
    ConcreteMicroPath start (List.replicate n (0 : Fin 2)) finish := by
  induction valid with
  | nil r => exact .nil r
  | cons start next finish n edge tail ih =>
      simpa only [List.replicate_succ] using
        ConcreteMicroPath.cons start next finish 0 _ edge ih

theorem accepting_path_split_iff {start finish : Result}
    (hit : FirstValidZeroHit IsConcreteCycleBoundary start finish)
    (outside : preChoiceResult start = false)
    (labels : List (Fin 2)) (tape : Zipper Tape) :
    ConcreteMicroPath start labels (.accepted tape) ↔
      ∃ rest, labels = List.replicate hit.steps (0 : Fin 2) ++ rest ∧
        ConcreteMicroPath finish rest (.accepted tape) := by
  constructor
  · exact zero_prefix_of_micro_accepting hit.valid (first_boundary_choice_free hit outside)
  · rintro ⟨rest, word, tail⟩
    rw [word]
    exact (zero_run_micro_path hit.valid).append tail

end PakFixedPolyomino.ULogBootstrapMicroPrefix
