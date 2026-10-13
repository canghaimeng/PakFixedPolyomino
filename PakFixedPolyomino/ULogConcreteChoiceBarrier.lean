import PakFixedPolyomino.ULogConcreteNoSpurious

/-! Literal control-flow barrier for arbitrary physical micro-paths.
The only states immediately before a slot choice are the clock phases.
Every entry to those phases from outside crosses cycleStart. This is a
finite statement about the actual rule table, checked by the Lean kernel;
it does not assume semantic membership of an arbitrary tape or path. -/

namespace PakFixedPolyomino.ULogConcreteChoiceBarrier
open ULogBootstrapExecution ULogControl ULogProgram
open MStarParserExecution (Zipper applyAction)

def preChoice : State → Bool
  | .clockSeek | .clockConsume | .clockReturn | .chooseSlot => true
  | _ => false

def barrierTest (q : State) (x : Tape) (slot : Fin 2) : Bool :=
  match program.rule q x slot with
  | none => true
  | some a => if preChoice a.target then preChoice q || decide (q = .cycleStart) else true

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem literal_rule_barrier_test : ∀ (q : State) (x : Tape) (slot : Fin 2),
    barrierTest q x slot = true := by
  decide

theorem literal_rule_barrier :
    ∀ (q : State) (x : Tape) (slot : Fin 2),
      match program.rule q x slot with
      | none => True
      | some a => preChoice a.target = true → preChoice q = true ∨ q = .cycleStart := by
  intro q x slot
  have tested := literal_rule_barrier_test q x slot
  cases h : program.rule q x slot with
  | none => trivial
  | some a =>
      intro ht
      simpa [barrierTest, h, ht] using tested

def preChoiceResult : Result → Bool
  | .running q _ => preChoice q
  | _ => false

theorem step_outside_of_targets (q : State) (z : Zipper Tape) (slot : Fin 2)
    (next : Result) (edge : validStepAt slot (.running q z) = some next)
    (targets : ∀ a, program.rule q z.focus slot = some a → preChoice a.target = false) :
    preChoiceResult next = false := by
  cases hrule : program.rule q z.focus slot with
  | none => simp [validStepAt, hrule] at edge
  | some a =>
      have ht := targets a hrule
      rw [← validStepAt_some_eq_oneStepAt edge]
      cases ha : applyAction z a with
      | none => simp [oneStepAt, hrule, ha, preChoiceResult]
      | some za =>
          simp only [oneStepAt, hrule, ha]
          split_ifs <;> simp [preChoiceResult, ht]

theorem nonfront_step {start next : Result} {slot : Fin 2}
    (edge : validStepAt slot start = some next)
    (outside : preChoiceResult start = false)
    (boundary : ¬ IsConcreteCycleBoundary start) :
    preChoiceResult next = false := by
  cases start with
  | accepted z => simp [validStepAt] at edge
  | rejected => simp [validStepAt] at edge
  | stuck => simp [validStepAt] at edge
  | running q z =>
      apply step_outside_of_targets q z slot next edge
      intro a rule
      have table := literal_rule_barrier q z.focus slot
      rw [rule] at table
      cases h : preChoice a.target with
      | false => rfl
      | true =>
          rcases table h with hf | hb
          · have ho : preChoice q = false := outside
            rw [ho] at hf
            contradiction
          · subst q
            exact (boundary (by trivial)).elim

def selectedTest (x : Tape) (slot : Fin 2) : Bool :=
  match program.rule .chooseSlot x slot with
  | none => true
  | some a => !preChoice a.target

set_option maxRecDepth 4096 in
theorem literal_selected_test : ∀ (x : Tape) (slot : Fin 2),
    selectedTest x slot = true := by
  decide

theorem selected_branch_outside {choice next : Result} {slot : Fin 2}
    (choiceHead : IsConcreteChoice choice) (edge : validStepAt slot choice = some next) :
    preChoiceResult next = false := by
  cases choice with
  | accepted z => simp [IsConcreteChoice] at choiceHead
  | rejected => simp [IsConcreteChoice] at choiceHead
  | stuck => simp [IsConcreteChoice] at choiceHead
  | running q z =>
      have hq : q = .chooseSlot := by cases q <;> simp_all [IsConcreteChoice]
      subst q
      apply step_outside_of_targets _ z slot next edge
      intro a rule
      have tested := literal_selected_test z.focus slot
      simpa [selectedTest, rule] using tested

theorem outside_before_boundary {n : Nat} {start finish : Result}
    (valid : ValidZeroRun n start finish)
    (noStop : ∀ m, m < n → ¬ IsConcreteCycleStop (run m start))
    (outside : preChoiceResult start = false) :
    ∀ m, m ≤ n → preChoiceResult (run m start) = false := by
  induction valid with
  | nil r =>
      intro m hm
      have hm0 : m = 0 := by omega
      subst m
      exact outside
  | cons start next finish n edge tail ih =>
      have hbound : ¬ IsConcreteCycleBoundary start := by
        intro hb
        exact noStop 0 (by omega) (Or.inl hb)
      have nextOutside := nonfront_step edge outside hbound
      have nextNoStop : ∀ m, m < n → ¬ IsConcreteCycleStop (run m next) := by
        intro m hm hit
        apply noStop (m + 1) (by omega)
        simpa only [ULogBootstrapExecution.run, validStepAt_zero_some_eq_oneStep edge] using hit
      intro m hm
      cases m with
      | zero => exact outside
      | succ m =>
          simpa only [ULogBootstrapExecution.run, validStepAt_zero_some_eq_oneStep edge] using
            ih nextNoStop nextOutside m (by omega)

theorem exact_cycle_suffix_no_choice {slot : Bool} {start finish : Result}
    (cycle : ExactConcreteCycle slot start finish) :
    ∀ m, m ≤ cycle.cycleSuffix.steps → ¬ IsConcreteChoice (run m cycle.branch) := by
  have branchOutside := selected_branch_outside cycle.choicePrefix.hit cycle.selected
  have allOutside := outside_before_boundary cycle.cycleSuffix.valid
    cycle.cycleSuffix.before branchOutside
  intro m hm choice
  have current := allOutside m hm
  cases h : run m cycle.branch with
  | accepted z => simp [h, IsConcreteChoice] at choice
  | rejected => simp [h, IsConcreteChoice] at choice
  | stuck => simp [h, IsConcreteChoice] at choice
  | running q z =>
      have hq : q = .chooseSlot := by cases q <;> simp_all [h, IsConcreteChoice]
      simp [h, hq, preChoiceResult, preChoice] at current

end PakFixedPolyomino.ULogConcreteChoiceBarrier
