import PakFixedPolyomino.ULogFreshEntry
import PakFixedPolyomino.ULogFiniteProgramZipperRunBridge

/-! ALL actual raw semantic prefixes through the forced fresh-entry recoding.
Exact total finite zipper diagram, old-tail inversion, forced false first slot,
and generic budget+1. Source scanner instantiation and compact loading remain
open. -/

namespace PakFixedPolyomino.ULogFreshEntryRunBridge

open ULogCompiler
open ULogFreshEntry
open ULogFiniteProgramZipperRunBridge
open FiniteOneTapeSemantics (moveHead)

variable {k : Nat}

theorem boundedHalted_insertConfig (z : BoundedConfig (2 + k) 3) :
    boundedHalted (insertConfig z) = boundedHalted z := by
  change decide ((insertState z.state).val < 2) = decide (z.state.val < 2)
  simp only [insertState_halted]

theorem program_insertConfig_rule (p : BoundedProgram (2 + k) 3)
    (qStart : Fin (2 + k)) (z : BoundedConfig (2 + k) 3) (slot : Bool) :
    (program p qStart).rule (insertConfig z).state (insertConfig z).focus slot =
      (p.rule z.state z.focus slot).map insertAction := by
  change (program p qStart).rule (insertState z.state) z.focus slot =
    (p.rule z.state z.focus slot).map insertAction
  exact program_old_rule p qStart z.state z.focus slot

theorem zipperSlotRun_insertConfig (p : BoundedProgram (2 + k) 3)
    (qStart : Fin (2 + k)) (slots : List Bool) (head : Int)
    (z : BoundedConfig (2 + k) 3) :
    zipperSlotRun (program p qStart) slots head (insertConfig z) =
      (zipperSlotRun p slots head z).map
        (fun hz => (hz.1, insertConfig hz.2)) := by
  induction slots generalizing head z with
  | nil => rfl
  | cons slot rest ih =>
      dsimp [zipperSlotRun]
      rw [boundedHalted_insertConfig]
      cases hc : boundedHalted z with
      | true => simp
      | false =>
          simp
          rw [program_insertConfig_rule]
          cases hr : p.rule z.state z.focus slot with
          | none => simp
          | some a =>
              simp
              have hmove : (insertAction a).move = a.move := rfl
              rw [hmove, insertConfig_applyBounded]
              exact ih (moveHead a.move head) (applyBounded (2 : Fin 3) z a)

theorem lift_insert_accept (p : BoundedProgram (2 + k) 3)
    (qStart : Fin (2 + k)) (z : BoundedConfig (2 + k) 3) :
    (liftConfig (program p qStart) (insertConfig z)).state = 0 ↔
      (liftConfig p z).state = 0 := by
  change (insertState z.state).val = 0 ↔ z.state.val = 0
  exact insertState_accepting z.state

/-- Inverse: every successful recoded semantic word is a successful old
semantic word of the same literal slots. -/
theorem semantic_success_of_insert (p : BoundedProgram (2 + k) 3)
    (qStart : Fin (2 + k)) (z : BoundedConfig (2 + k) 3)
    (slots : List Bool) (outNew : ULogSemantics.Config)
    (hsem : semanticRun (liftConfig (program p qStart) (insertConfig z))
      slots = some outNew) :
    ∃ outOld, semanticRun (liftConfig p z) slots = some outOld ∧
      (outNew.state = 0 ↔ outOld.state = 0) := by
  have hfresh :=
    zipperSlotRun_lift (program p qStart) slots (0 : Int) (insertConfig z)
  have hmap :
      ((zipperSlotRun p slots (0 : Int) z).map
        (fun hz => (hz.1, insertConfig hz.2))).map
          (fun hz => liftConfig (program p qStart) hz.2) = some outNew := by
    rw [← zipperSlotRun_insertConfig, hfresh, hsem]
  have hcomp :
      (zipperSlotRun p slots (0 : Int) z).map
        (fun hz => liftConfig (program p qStart) (insertConfig hz.2)) =
          some outNew := by
    simpa [Option.map_map] using hmap
  obtain ⟨hz, hzip, hlift⟩ := Option.map_eq_some_iff.mp hcomp
  have hold := zipperSlotRun_lift p slots (0 : Int) z
  refine ⟨liftConfig p hz.2, ?_, ?_⟩
  · simpa [hzip] using hold.symm
  · rw [← hlift]
    exact lift_insert_accept p qStart hz.2

theorem semanticRun_cons (c : ULogSemantics.Config) (slot : Bool)
    (rest : List Bool) :
    semanticRun c (slot :: rest) =
      (ULogSemantics.stepSlot slot c).bind (fun c' => semanticRun c' rest) :=
  rfl

theorem stepSlot_encodeInstance_entry (p : BoundedProgram (2 + k) 3)
    (qStart : Fin (2 + k)) (input : List Bool) (slot : Bool) :
    ULogSemantics.stepSlot slot
        (ULogSemantics.start (encodeInstance (program p qStart) input)) =
      if slot then none
      else some (liftConfig (program p qStart)
        (insertConfig (bootTarget qStart input))) := by
  rw [← liftConfig_boundedInitial (program p qStart) (entryState k)
    (0 : Fin 3) 1 2 rfl rfl rfl rfl]
  rw [stepSlot_liftConfig (program p qStart) (2 : Fin 3) blank2]
  rw [boundedStepSlot_entry]
  cases slot <;> rfl

theorem entry_first_slot (p : BoundedProgram (2 + k) 3)
    (qStart : Fin (2 + k)) (input : List Bool) (slot : Bool)
    (rest : List Bool) (out : ULogSemantics.Config)
    (hsem : semanticRun
      (ULogSemantics.start (encodeInstance (program p qStart) input))
      (slot :: rest) = some out) :
    slot = false ∧
      ∃ outOld, semanticRun
        (liftConfig p (bootTarget qStart input)) rest = some outOld := by
  have hstep := stepSlot_encodeInstance_entry p qStart input slot
  rw [semanticRun_cons, hstep] at hsem
  cases slot with
  | true => simp at hsem
  | false =>
      simp at hsem
      refine ⟨rfl, ?_⟩
      obtain ⟨outOld, hold, _⟩ :=
        semantic_success_of_insert p qStart (bootTarget qStart input)
          rest out hsem
      exact ⟨outOld, hold⟩

theorem all_entry_runs_length_le (p : BoundedProgram (2 + k) 3)
    (qStart : Fin (2 + k)) (input : List Bool) (budget : Nat)
    (hbound : ∀ slots out,
      semanticRun (liftConfig p (bootTarget qStart input)) slots = some out →
        slots.length ≤ budget)
    (slots : List Bool) (out : ULogSemantics.Config)
    (hsem : semanticRun
      (ULogSemantics.start (encodeInstance (program p qStart) input)) slots =
        some out) :
    slots.length ≤ budget + 1 := by
  cases slots with
  | nil => exact Nat.zero_le _
  | cons slot rest =>
      obtain ⟨_, outOld, htail⟩ :=
        entry_first_slot p qStart input slot rest out hsem
      have hrest := hbound rest outOld htail
      simp only [List.length_cons]
      omega

end PakFixedPolyomino.ULogFreshEntryRunBridge
