import PakFixedPolyomino.ULogSourceOneHotPaddingArithmetic
import Mathlib.Tactic

/-!
# Constant-time wrapper for one-hot source microsteps

The base source macro reaches its next logical head after a relocation of
`0`, `nt`, or `2*nt` cells.  This finite wrapper intercepts the relocation
handoff and inserts the complementary number of deterministic stay ticks.
Consequently the relocation-plus-padding suffix has the same length for all
three source moves.  No new nondeterministic slot is introduced.
-/

namespace PakFixedPolyomino.ULogSourceOneHotPaddedStep

open OneTapeTableau FiniteOneTapeProgram ULogCompiler
open ULogSourceOneHotPhysicalStep
open ULogSourceOneHotPaddingArithmetic

abbrev Tape := Fin 3

variable {ns nt : ℕ}

inductive State (ns nt : ℕ) where
  | base : ULogSourceOneHotPhysicalStep.State ns nt → State ns nt
  /-- `i` is the relocation distance already paid.  Padding is used only when
  `i < 2*nt`, hence this counter has no state at `2*nt`. -/
  | padding : BoundedAction ns nt → Fin (2 * nt) → State ns nt
  deriving DecidableEq, Fintype, Repr

def liftAction (a : Action (ULogSourceOneHotPhysicalStep.State ns nt) Tape) :
    Action (State ns nt) Tape :=
  ⟨a.write, .base a.target, a.move⟩

def paddingAction (hnt : 0 < nt) (a : BoundedAction ns nt)
    (i : Fin (2 * nt)) (x : Tape) : Action (State ns nt) Tape :=
  if hlast : i.1 + 1 = 2 * nt then
    ⟨x, .base (.reading a.target (initialReaderState hnt)), .stay⟩
  else
    ⟨x, .padding a ⟨i.1 + 1, by omega⟩, .stay⟩

/-- Intercept precisely a completed relocation.  A left move has already paid
the full `2*nt` distance and enters the reader immediately; the other moves
enter the deterministic padding counter at their paid distance. -/
def baseMicroAction (hnt : 0 < nt) (logicalBlank : Fin nt) :
    ULogSourceOneHotPhysicalStep.State ns nt → Tape → Action (State ns nt) Tape
  | .relocate a i, x =>
      if hdone : relocationDistance a.move nt ≤ i.1 then
        if hfull : i.1 = 2 * nt then
          ⟨x, .base (.reading a.target (initialReaderState hnt)), .stay⟩
        else
          ⟨x, .padding a ⟨i.1, by omega⟩, .stay⟩
      else
        liftAction (microAction hnt logicalBlank (.relocate a i) x)
  | s, x => liftAction (microAction hnt logicalBlank s x)

def step (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt) :
    State ns nt → Tape → Fin 2 → Option (Action (State ns nt) Tape)
  | .base (.branch q read), x, slot =>
      ((ULogSourceOneHotPhysicalStep.program p hnt logicalBlank).rule
        (.branch q read) x slot).map liftAction
  | .base s, x, slot =>
      if slot = 0 then some (baseMicroAction hnt logicalBlank s x) else none
  | .padding a i, x, slot =>
      if slot = 0 then some (paddingAction hnt a i x) else none

def program (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt) :
    Program (State ns nt) Tape where
  rule := step p hnt logicalBlank

@[simp] theorem padding_slot_one_empty (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (logicalBlank : Fin nt) (a : BoundedAction ns nt)
    (i : Fin (2 * nt)) (x : Tape) :
    (program p hnt logicalBlank).rule (.padding a i) x 1 = none := by
  rfl

theorem base_nonbranch_slot_one_empty (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (logicalBlank : Fin nt)
    (s : ULogSourceOneHotPhysicalStep.State ns nt) (x : Tape)
    (hs : ∀ q read, s ≠ .branch q read) :
    (program p hnt logicalBlank).rule (.base s) x 1 = none := by
  cases s with
  | branch q read => exact False.elim (hs q read rfl)
  | reading q r => rfl
  | rewind q read slot a i => rfl
  | writing a i => rfl
  | relocate a i => rfl
  | accept => rfl
  | reject => rfl

theorem padded_branch_rule_exact (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (logicalBlank : Fin nt) (q : Fin ns) (read : Fin nt)
    (x : Tape) (slot : Fin 2) :
    (program p hnt logicalBlank).rule (.base (.branch q read)) x slot =
      ((ULogSourceOneHotPhysicalStep.program p hnt logicalBlank).rule
        (.branch q read) x slot).map liftAction := by
  rfl

theorem completed_relocation_target (hnt : 0 < nt) (logicalBlank : Fin nt)
    (a : BoundedAction ns nt) (i : Fin (2 * nt + 1)) (x : Tape)
    (hdone : relocationDistance a.move nt ≤ i.1) :
    (baseMicroAction hnt logicalBlank (.relocate a i) x).target =
      if hfull : i.1 = 2 * nt then
        .base (.reading a.target (initialReaderState hnt))
      else .padding a ⟨i.1, by omega⟩ := by
  by_cases hfull : i.1 = 2 * nt <;>
    simp [baseMicroAction, hdone, hfull,
      ULogSourceOneHotPhaseEndpoints.relocationDistance_le]

theorem padding_move (hnt : 0 < nt) (a : BoundedAction ns nt)
    (i : Fin (2 * nt)) (x : Tape) :
    (paddingAction hnt a i x).move = .stay := by
  by_cases hlast : i.1 + 1 = 2 * nt <;> simp [paddingAction, hlast]

end PakFixedPolyomino.ULogSourceOneHotPaddedStep
