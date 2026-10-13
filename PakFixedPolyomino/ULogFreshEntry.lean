import PakFixedPolyomino.ULogCompiler

/-! A genuine forced startup transition for a three-letter bounded program.
The old terminal codes zero and one are preserved; old active codes are
shifted above the new entry code two. The transition writes back the input
letter and moves left onto the blank sentinel. It preserves literal slot
multiplicities and costs one transition, including an already accepting old
start. This module does not construct a compact scanner window. -/

namespace PakFixedPolyomino.ULogFreshEntry

open ULogCompiler OneTapeTableau

def insertState {k : Nat} (q : Fin (2 + k)) : Fin (3 + k) :=
  ⟨if q.val < 2 then q.val else q.val + 1, by split <;> omega⟩

def dropState {k : Nat} (q : Fin (3 + k)) (h : q.val ≠ 2) : Fin (2 + k) :=
  ⟨if q.val < 2 then q.val else q.val - 1, by split <;> omega⟩

@[simp] theorem insertState_ne_two {k : Nat} (q : Fin (2 + k)) :
    (insertState q).val ≠ 2 := by
  simp only [insertState]; split_ifs <;> omega

@[simp] theorem dropState_insertState {k : Nat} (q : Fin (2 + k)) :
    dropState (insertState q) (insertState_ne_two q) = q := by
  apply Fin.ext
  simp only [dropState, insertState]
  split_ifs <;> omega

@[simp] theorem insertState_halted {k : Nat} (q : Fin (2 + k)) :
    (insertState q).val < 2 ↔ q.val < 2 := by
  change (if q.val < 2 then q.val else q.val + 1) < 2 ↔ q.val < 2
  split_ifs <;> omega

@[simp] theorem insertState_accepting {k : Nat} (q : Fin (2 + k)) :
    (insertState q).val = 0 ↔ q.val = 0 := by
  change (if q.val < 2 then q.val else q.val + 1) = 0 ↔ q.val = 0
  split_ifs with h
  · rfl
  · constructor
    · intro he
      exact he.elim
    · intro he
      omega

def insertAction {k : Nat} (a : BoundedAction (2 + k) 3) :
    BoundedAction (3 + k) 3 := ⟨a.write, insertState a.target, a.move⟩

def insertConfig {k : Nat} (c : BoundedConfig (2 + k) 3) :
    BoundedConfig (3 + k) 3 :=
  ⟨insertState c.state, c.leftRev, c.focus, c.right⟩

def entryState (k : Nat) : Fin (3 + k) := ⟨2, by omega⟩

def program {k : Nat} (p : BoundedProgram (2 + k) 3)
    (qStart : Fin (2 + k)) : BoundedProgram (3 + k) 3 where
  rule q read slot :=
    if h : q.val = 2 then
      if slot then none else some ⟨read, insertState qStart, .left⟩
    else (p.rule (dropState q h) read slot).map insertAction

@[simp] theorem program_old_rule {k : Nat} (p : BoundedProgram (2 + k) 3)
    (qStart q : Fin (2 + k)) (read : Fin 3) (slot : Bool) :
    (program p qStart).rule (insertState q) read slot =
      (p.rule q read slot).map insertAction := by
  simp [program, insertState_ne_two]

@[simp] theorem program_entry_rule {k : Nat} (p : BoundedProgram (2 + k) 3)
    (qStart : Fin (2 + k)) (read : Fin 3) (slot : Bool) :
    (program p qStart).rule (entryState k) read slot =
      if slot then none else some ⟨read, insertState qStart, .left⟩ := by
  simp [program, entryState]

theorem insertConfig_applyBounded {k : Nat} (c : BoundedConfig (2 + k) 3)
    (a : BoundedAction (2 + k) 3) :
    applyBounded (2 : Fin 3) (insertConfig c) (insertAction a) =
      insertConfig (applyBounded (2 : Fin 3) c a) := by
  cases hm : a.move with
  | stay => simp [applyBounded, insertAction, insertConfig, hm]
  | left => cases hl : c.leftRev <;>
      simp [applyBounded, insertAction, insertConfig, hm, hl]
  | right => cases hr : c.right <;>
      simp [applyBounded, insertAction, insertConfig, hm, hr]

theorem boundedStepSlot_insertConfig {k : Nat}
    (p : BoundedProgram (2 + k) 3) (qStart : Fin (2 + k))
    (slot : Bool) (c : BoundedConfig (2 + k) 3) :
    boundedStepSlot (program p qStart) (2 : Fin 3) slot (insertConfig c) =
      (boundedStepSlot p (2 : Fin 3) slot c).map insertConfig := by
  have hh : boundedHalted (insertConfig c) = boundedHalted c := by
    change decide ((insertState c.state).val < 2) = decide (c.state.val < 2)
    simp only [insertState_halted]
  unfold boundedStepSlot
  rw [hh]
  cases hc : boundedHalted c <;> simp [hc]
  change ((program p qStart).rule (insertState c.state) c.focus slot).map
      (applyBounded (2 : Fin 3) (insertConfig c)) =
    (p.rule c.state c.focus slot).map (insertConfig ∘ applyBounded (2 : Fin 3) c)
  rw [program_old_rule]
  cases ha : p.rule c.state c.focus slot <;>
    simp [ha, insertConfig_applyBounded]

theorem boundedNext_insertConfig {k : Nat}
    (p : BoundedProgram (2 + k) 3) (qStart : Fin (2 + k))
    (c : BoundedConfig (2 + k) 3) :
    boundedNext (program p qStart) (2 : Fin 3) (insertConfig c) =
      (boundedNext p (2 : Fin 3) c).map insertConfig := by
  unfold boundedNext
  rw [boundedStepSlot_insertConfig, boundedStepSlot_insertConfig]
  cases boundedStepSlot p (2 : Fin 3) false c <;>
    cases boundedStepSlot p (2 : Fin 3) true c <;> rfl

theorem acceptingPaths_insertConfig {k : Nat}
    (p : BoundedProgram (2 + k) 3) (qStart : Fin (2 + k))
    (t : Nat) (c : BoundedConfig (2 + k) 3) :
    ULogSemantics.machine.acceptingPaths t
        (liftConfig (program p qStart) (insertConfig c)) =
      ULogSemantics.machine.acceptingPaths t (liftConfig p c) := by
  have hh (c : BoundedConfig (2 + k) 3) :
      ULogSemantics.halted (liftConfig (program p qStart) (insertConfig c)) =
        ULogSemantics.halted (liftConfig p c) := by
    change decide ((insertState c.state).val < 2) = decide (c.state.val < 2)
    simp only [insertState_halted]
  have ha (c : BoundedConfig (2 + k) 3) :
      ULogSemantics.accepting (liftConfig (program p qStart) (insertConfig c)) =
        ULogSemantics.accepting (liftConfig p c) := by
    change decide ((insertState c.state).val = 0) = decide (c.state.val = 0)
    simp only [insertState_accepting]
  induction t generalizing c with
  | zero =>
      change (if ULogSemantics.halted _ then
        if ULogSemantics.accepting _ then 1 else 0 else 0) =
        if ULogSemantics.halted _ then
          if ULogSemantics.accepting _ then 1 else 0 else 0
      rw [hh, ha]
  | succ t ih =>
      change (if ULogSemantics.halted _ then
        if ULogSemantics.accepting _ then 1 else 0 else
          ((ULogSemantics.next _).map
            (ULogSemantics.machine.acceptingPaths t)).sum) =
        if ULogSemantics.halted _ then
          if ULogSemantics.accepting _ then 1 else 0 else
            ((ULogSemantics.next _).map
              (ULogSemantics.machine.acceptingPaths t)).sum
      rw [hh, ha]
      cases hc : ULogSemantics.halted (liftConfig p c) <;> simp only [hc, if_true,
        if_false, Bool.false_eq_true]
      rw [next_liftConfig (program p qStart) (2 : Fin 3) rfl,
        next_liftConfig p (2 : Fin 3) rfl]
      rw [boundedNext_insertConfig]
      dsimp only [ULogSemantics.machine]
      simp only [List.map_map, Function.comp_def]
      apply congrArg List.sum
      apply List.map_congr_left
      intro d hd
      simpa only [ULogSemantics.machine] using ih d

/-- The sentinel is reached by a genuine left move. Empty input writes its
blank back as an explicit right cell, exactly as the executable semantics do. -/
def bootTarget {k : Nat} (qStart : Fin (2 + k)) : List Bool →
    BoundedConfig (2 + k) 3
  | [] => ⟨qStart, [], 2, [2]⟩
  | b :: bs => ⟨qStart, [], 2, (b :: bs).map (boundedBit 0 1)⟩

theorem boundedStepSlot_entry {k : Nat} (p : BoundedProgram (2 + k) 3)
    (qStart : Fin (2 + k)) (input : List Bool) (slot : Bool) :
    boundedStepSlot (program p qStart) (2 : Fin 3) slot
        (boundedInitial (entryState k) (0 : Fin 3) 1 2 input) =
      if slot then none else some (insertConfig (bootTarget qStart input)) := by
  cases input with
  | nil => cases slot <;>
      simp [boundedStepSlot, boundedInitial, boundedHalted, entryState,
        program, applyBounded, insertConfig, bootTarget]
  | cons b bs => cases slot <;> cases b <;>
      simp [boundedStepSlot, boundedInitial, boundedHalted, entryState,
        program, applyBounded, insertConfig, bootTarget, boundedBit]

theorem next_entry {k : Nat} (p : BoundedProgram (2 + k) 3)
    (qStart : Fin (2 + k)) (input : List Bool) :
    ULogSemantics.next (ULogSemantics.start
        (encodeInstance (program p qStart) input)) =
      [liftConfig (program p qStart) (insertConfig (bootTarget qStart input))] := by
  rw [← liftConfig_boundedInitial (program p qStart) (entryState k)
    (0 : Fin 3) 1 2 rfl rfl rfl rfl, next_liftConfig _ (2 : Fin 3) rfl]
  simp [boundedNext, boundedStepSlot_entry]

/-- A single additional physical semantic transition, followed by the same
actual accepting-path recursion. No restriction on the old start is made. -/
theorem acceptingPaths_entry {k : Nat} (p : BoundedProgram (2 + k) 3)
    (qStart : Fin (2 + k)) (input : List Bool) (t : Nat) :
    ULogSemantics.machine.acceptingPaths (t + 1)
        (ULogSemantics.start (encodeInstance (program p qStart) input)) =
      ULogSemantics.machine.acceptingPaths t
        (liftConfig p (bootTarget qStart input)) := by
  have hh : ULogSemantics.halted (ULogSemantics.start
      (encodeInstance (program p qStart) input)) = false := by
    rw [← liftConfig_boundedInitial (program p qStart) (entryState k)
      (0 : Fin 3) 1 2 rfl rfl rfl rfl]
    cases input <;>
      simp [ULogSemantics.halted, liftConfig, boundedInitial, entryState]
  rw [BinaryNondeterministicMachine.acceptingPaths_succ_nonhalt
    ULogSemantics.machine hh]
  change ((ULogSemantics.next _).map
    (ULogSemantics.machine.acceptingPaths t)).sum = _
  rw [next_entry]
  dsimp only [ULogSemantics.machine]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  simpa only [ULogSemantics.machine] using
    acceptingPaths_insertConfig p qStart t (bootTarget qStart input)

theorem accepting_start_preserved {k : Nat} (p : BoundedProgram (2 + k) 3)
    (qStart : Fin (2 + k)) (hstart : qStart.val = 0)
    (input : List Bool) (t : Nat) :
    ULogSemantics.machine.acceptingPaths (t + 1)
        (ULogSemantics.start (encodeInstance (program p qStart) input)) = 1 := by
  rw [acceptingPaths_entry]
  apply BinaryNondeterministicMachine.acceptingPaths_halt_accept
  · change ULogSemantics.halted (liftConfig p (bootTarget qStart input)) = true
    cases input <;> simp [ULogSemantics.halted, liftConfig, bootTarget, hstart]
  · change ULogSemantics.accepting (liftConfig p (bootTarget qStart input)) = true
    cases input <;> simp [ULogSemantics.accepting, ULogSemantics.acceptCode,
      liftConfig, bootTarget, hstart]

end PakFixedPolyomino.ULogFreshEntry
