import PakFixedPolyomino.FiniteOneTapeRunSlots
import PakFixedPolyomino.ULogSourceOneHotPaddedMacro

/-! # Operational terminal-state restriction of a finite one-tape program

The new finite rule table removes outgoing rules at the chosen halting states.
Its arrow alphabet embeds into the original literal arrow alphabet. Actual
remaining transitions and full runs preserve their tape/head/configuration,
and every successful restricted run is an actual unrestricted run.
This changes the executable table; it does not rename an endpoint predicate
as a physical halting condition.
-/

namespace PakFixedPolyomino.FiniteOneTapeHaltingRestriction

open FiniteOneTapeProgram FiniteOneTapeSemantics

variable {State Tape : Type*}
variable [Fintype State] [Fintype Tape] [DecidableEq State] [DecidableEq Tape]

def terminalize (P : Program State Tape) (halted : State → Bool) : Program State Tape where
  rule q x slot := if halted q then none else P.rule q x slot

theorem restricted_source_not_halted (P : Program State Tape) (halted : State → Bool)
    (a : Arrow (terminalize P halted)) : halted a.1.1.1 = false := by
  cases h : halted a.1.1.1 with
  | false => rfl
  | true =>
      have ha := a.2
      simp [terminalize, h] at ha

def includeArrow (P : Program State Tape) (halted : State → Bool)
    (a : Arrow (terminalize P halted)) : Arrow P :=
  ⟨a.1, by simpa [terminalize, restricted_source_not_halted P halted a] using a.2⟩

theorem includeArrow_injective (P : Program State Tape) (halted : State → Bool) :
    Function.Injective (includeArrow P halted) := by
  intro a b h
  exact Subtype.ext (congrArg (fun x : Arrow P => x.1) h)

theorem actionOf_includeArrow (P : Program State Tape) (halted : State → Bool)
    (a : Arrow (terminalize P halted)) :
    actionOf P (includeArrow P halted a) = actionOf (terminalize P halted) a := by
  have hsource := restricted_source_not_halted P halted a
  cases hrule : P.rule a.1.1.1 a.1.1.2 a.1.2 with
  | none =>
      have ha := (includeArrow P halted a).2
      exact (ha hrule).elim
  | some act =>
      have hnew : (terminalize P halted).rule a.1.1.1 a.1.1.2 a.1.2 = some act := by
        simp [terminalize, hsource, hrule]
      exact (ULogSourceOneHotPaddedMacro.actionOf_eq_of_rule_eq P
        (includeArrow P halted a) act hrule).trans
          (ULogSourceOneHotPaddedMacro.actionOf_eq_of_rule_eq (terminalize P halted)
            a act hnew).symm

theorem transition_includeArrow (P : Program State Tape) (halted : State → Bool)
    (a : Arrow (terminalize P halted)) :
    transition P (includeArrow P halted a) = transition (terminalize P halted) a := by
  unfold transition
  rw [actionOf_includeArrow]
  rfl

theorem step_includeArrow (P : Program State Tape) (halted : State → Bool)
    (movable : Tape → Bool) (c : Config State Tape)
    (a : Arrow (terminalize P halted)) :
    step P movable c (includeArrow P halted a) =
      step (terminalize P halted) movable c a := by
  simp only [step, transition_includeArrow]

theorem run_includeArrows (P : Program State Tape) (halted : State → Bool)
    (movable : Tape → Bool) (word : List (Arrow (terminalize P halted)))
    (c : Config State Tape) :
    run P movable (word.map (includeArrow P halted)) c =
      run (terminalize P halted) movable word c := by
  induction word generalizing c with
  | nil => rfl
  | cons a word ih => simp only [List.map_cons, run_cons, step_includeArrow, ih]

theorem terminal_step_none (P : Program State Tape) (halted : State → Bool)
    (movable : Tape → Bool) (c : Config State Tape)
    (hc : halted c.state = true) (a : Arrow (terminalize P halted)) :
    step (terminalize P halted) movable c a = none := by
  have ha := restricted_source_not_halted P halted a
  have hne : c.state ≠ a.1.1.1 := by intro heq; rw [heq, ha] at hc; cases hc
  simp [step, transition, hne]

theorem terminal_run_nonempty_none (P : Program State Tape) (halted : State → Bool)
    (movable : Tape → Bool) (c : Config State Tape)
    (hc : halted c.state = true) (word : List (Arrow (terminalize P halted)))
    (hne : word ≠ []) : run (terminalize P halted) movable word c = none := by
  cases word with
  | nil => contradiction
  | cons a word => simp only [run_cons, terminal_step_none P halted movable c hc a,
      Option.bind_none]

def RemainingArrow (P : Program State Tape) (halted : State → Bool) :=
  {a : Arrow P // halted a.1.1.1 = false}

def arrowEquiv (P : Program State Tape) (halted : State → Bool) :
    Arrow (terminalize P halted) ≃ RemainingArrow P halted where
  toFun a := ⟨includeArrow P halted a, restricted_source_not_halted P halted a⟩
  invFun a := ⟨a.1.1, by simp [terminalize, a.2, a.1.2]⟩
  left_inv a := rfl
  right_inv a := rfl

def liftArrow (P : Program State Tape) (halted : State → Bool)
    (a : Arrow P) (ha : halted a.1.1.1 = false) : Arrow (terminalize P halted) :=
  ⟨a.1, by simpa [terminalize, ha] using a.2⟩

@[simp] theorem include_lift (P : Program State Tape) (halted : State → Bool)
    (a : Arrow P) (ha : halted a.1.1.1 = false) :
    includeArrow P halted (liftArrow P halted a ha) = a := rfl

def liftWord (P : Program State Tape) (halted : State → Bool) :
    (word : List (Arrow P)) →
      (∀ a ∈ word, halted a.1.1.1 = false) → List (Arrow (terminalize P halted))
  | [], _ => []
  | a :: word, h => liftArrow P halted a (h a (by simp)) ::
      liftWord P halted word (fun b hb => h b (by simp [hb]))

@[simp] theorem include_liftWord (P : Program State Tape) (halted : State → Bool)
    (word : List (Arrow P)) (h : ∀ a ∈ word, halted a.1.1.1 = false) :
    (liftWord P halted word h).map (includeArrow P halted) = word := by
  induction word with
  | nil => rfl
  | cons a word ih => simp only [liftWord, List.map_cons, include_lift, ih]

theorem run_liftWord (P : Program State Tape) (halted : State → Bool)
    (movable : Tape → Bool) (word : List (Arrow P))
    (h : ∀ a ∈ word, halted a.1.1.1 = false) (c : Config State Tape) :
    run (terminalize P halted) movable (liftWord P halted word h) c =
      run P movable word c := by
  rw [← run_includeArrows, include_liftWord]

end PakFixedPolyomino.FiniteOneTapeHaltingRestriction
