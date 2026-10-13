import PakFixedPolyomino.FiniteOneTapeProgram
import Mathlib.Tactic

/-!
# Operational semantics for finite one-tape programs

This supplies the labelled-arrow path semantics needed to state and prove the
M3/M4 refinement and the exact accepting-branch count.  A branch is a vector
of literal occupied rule slots, so coincident actions with distinct labels are
still counted separately.
-/

namespace PakFixedPolyomino.FiniteOneTapeSemantics

open OneTapeTableau FiniteOneTapeProgram

structure Config (State Tape : Type*) where
  state : State
  head : Int
  tape : Int → Tape

def moveHead : Move → Int → Int
  | .left, p => p - 1
  | .stay, p => p
  | .right, p => p + 1

def writtenTape {State Tape : Type*} [DecidableEq Int]
    (c : Config State Tape) (x : Tape) : Int → Tape :=
  Function.update c.tape c.head x

variable {State Tape : Type*}
variable [Fintype State] [Fintype Tape]
variable [DecidableEq State] [DecidableEq Tape]

/-- Execute one labelled arrow.  The post-write target cell must be movable;
this excludes entering a sentinel, including a stay that writes one. -/
def step (P : Program State Tape) (movable : Tape → Bool)
    (c : Config State Tape) (a : Arrow P) : Option (Config State Tape) :=
  let tr := transition P a
  if c.state ≠ tr.sourceState ∨ c.tape c.head ≠ tr.read then none
  else
    let tape' := writtenTape c tr.write
    let head' := moveHead tr.move c.head
    if movable (tape' head') then
      some { state := tr.targetState, head := head', tape := tape' }
    else none

theorem step_some_forces_source
    (P : Program State Tape) (movable : Tape → Bool)
    (c c' : Config State Tape) (a : Arrow P)
    (h : step P movable c a = some c') :
    c.state = (transition P a).sourceState ∧
      c.tape c.head = (transition P a).read := by
  unfold step at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i hgood
    push Not at hgood
    exact hgood

theorem step_some_state
    (P : Program State Tape) (movable : Tape → Bool)
    (c c' : Config State Tape) (a : Arrow P)
    (h : step P movable c a = some c') :
    c'.state = (transition P a).targetState := by
  unfold step at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · exact Option.some.inj h |>.symm ▸ rfl
    · simp at h

theorem step_label_deterministic
    (P : Program State Tape) (movable : Tape → Bool)
    (c c₁ c₂ : Config State Tape) (a : Arrow P)
    (h₁ : step P movable c a = some c₁)
    (h₂ : step P movable c a = some c₂) : c₁ = c₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

def run (P : Program State Tape) (movable : Tape → Bool) :
    List (Arrow P) → Config State Tape → Option (Config State Tape)
  | [], c => some c
  | a :: as, c => (step P movable c a).bind (run P movable as)

@[simp] theorem run_nil (P : Program State Tape) (movable : Tape → Bool)
    (c : Config State Tape) : run P movable [] c = some c := rfl

@[simp] theorem run_cons (P : Program State Tape) (movable : Tape → Bool)
    (a : Arrow P) (as : List (Arrow P)) (c : Config State Tape) :
    run P movable (a :: as) c =
      (step P movable c a).bind (run P movable as) := rfl

def branchResult (P : Program State Tape) (movable : Tape → Bool)
    {n : ℕ} (word : Fin n → Arrow P) (c : Config State Tape) :
    Option (Config State Tape) :=
  run P movable (List.ofFn word) c

abbrev AcceptingBranch (P : Program State Tape) (movable : Tape → Bool)
    (accept : State) (c : Config State Tape) (n : ℕ) :=
  {word : Fin n → Arrow P //
    ∃ out, branchResult P movable word c = some out ∧ out.state = accept}

noncomputable def acceptingCount (P : Program State Tape)
    (movable : Tape → Bool) (accept : State)
    (c : Config State Tape) (n : ℕ) : ℕ :=
  Fintype.card (AcceptingBranch P movable accept c n)

end PakFixedPolyomino.FiniteOneTapeSemantics
