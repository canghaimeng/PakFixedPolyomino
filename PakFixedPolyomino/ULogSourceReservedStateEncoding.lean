import PakFixedPolyomino.ULogCompiler
import Mathlib.Tactic

/-!
# Reserved halt-state encoding for source microprograms

The bounded-machine convention reserves numerical state `0` for acceptance
and `1` for rejection.  This small adapter lets later microprograms use an
arbitrary finite active-control type without relying on the unspecified order
chosen by `Fintype.equivFin` for those two distinguished states.
-/

namespace PakFixedPolyomino.ULogSourceReservedStateEncoding

open OneTapeTableau FiniteOneTapeProgram ULogCompiler

/-- Two distinguished halting states followed by arbitrary active control. -/
abbrev State (Active : Type*) := Fin 2 ⊕ Active

variable {Active Tape : Type*}
variable [Fintype Active] [DecidableEq Active]
variable [Fintype Tape] [DecidableEq Tape]

/-- A numerical state encoding whose first two values are definitionally the
accept/reject codes required by `boundedMachine`. -/
noncomputable def stateEquiv : State Active ≃ Fin (2 + Fintype.card Active) :=
  (Equiv.sumCongr (Equiv.refl (Fin 2)) (Fintype.equivFin Active)).trans
    finSumFinEquiv

@[simp] theorem stateEquiv_halt (q : Fin 2) :
    (stateEquiv (Active := Active) (Sum.inl q)).val = q.val := by
  simp [stateEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left]

@[simp] theorem stateEquiv_accept :
    (stateEquiv (Active := Active) (Sum.inl (0 : Fin 2))).val =
      ULogSemantics.acceptCode := by
  rfl

@[simp] theorem stateEquiv_reject :
    (stateEquiv (Active := Active) (Sum.inl (1 : Fin 2))).val = 1 := by
  rfl

@[simp] theorem stateEquiv_active_val (q : Active) :
    (stateEquiv (Active := Active) (Sum.inr q)).val =
      2 + (Fintype.equivFin Active q).val := by
  simp [stateEquiv, Equiv.trans_apply, finSumFinEquiv_apply_right]

theorem stateEquiv_active_not_halted (q : Active) :
    ¬ (stateEquiv (Active := Active) (Sum.inr q)).val < 2 := by
  rw [stateEquiv_active_val]
  omega

/-- Compile a finite physical microprogram while preserving the two reserved
halting-state codes. -/
noncomputable def compileProgram
    (eTape : Tape ≃ Fin 3) (p : Program (State Active) Tape) :
    BoundedProgram (2 + Fintype.card Active) 3 :=
  ofFiniteProgram (stateEquiv (Active := Active)) eTape p

@[simp] theorem compileProgram_rule
    (eTape : Tape ≃ Fin 3) (p : Program (State Active) Tape)
    (q : State Active) (read : Tape) (slot : Bool) :
    (compileProgram eTape p).rule
        (stateEquiv (Active := Active) q) (eTape read) slot =
      (p.rule q read (ULogBytecode.slotIndex slot)).map
        (ofFiniteAction (stateEquiv (Active := Active)) eTape) := by
  exact ofFiniteProgram_rule (stateEquiv (Active := Active)) eTape p q read slot

end PakFixedPolyomino.ULogSourceReservedStateEncoding
