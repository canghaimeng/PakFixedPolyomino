import PakFixedPolyomino.ULogSourceObliviousBytecode
import PakFixedPolyomino.ULogSourceObliviousHaltingLeaves
import PakFixedPolyomino.ULogSourceOneHotPaddedMacro

/-! Numerical finite-program ALL-run transport of the source scanner table.
The encoded table depends on the source machine, not the input or horizon.
Compact window loading and a fixed universal physical interpreter remain open. -/

namespace PakFixedPolyomino.ULogSourceObliviousBytecodeRunBridge

open FiniteOneTapeProgram (Program Arrow actionOf transition)
open FiniteOneTapeSemantics (Config step run writtenTape moveHead run_nil run_cons)
open ULogCompiler
open ULogSourceObliviousHaltingProgram
open ULogSourceObliviousBytecode
open ULogSourceObliviousHaltingLeaves
open ULogSourceObliviousScanProgram (State)
open ULogSourceObliviousInitialWindowExecution (initialWindowConfig)
open StandardNondeterministicMachine (Machine acceptingCount RunsAtMost AcceptingLeaf)
open StandardMachineWindowBridge (inputWindow)

variable {ns nt : Nat}

noncomputable def numericalProgram (M : Machine ns nt 2) :
    Program (Fin (2 + Fintype.card (Active M))) (Fin 3) :=
  toFiniteProgram (ULogSourceObliviousBytecode.boundedProgram M)

noncomputable def encodeConfig (M : Machine ns nt 2)
    (c : Config (State ns nt) (Fin 3)) :
    Config (Fin (2 + Fintype.card (Active M))) (Fin 3) :=
  { state := stateEquiv M c.state, head := c.head, tape := c.tape }

noncomputable def encodeActionFinite (M : Machine ns nt 2)
    (a : FiniteOneTapeProgram.Action (State ns nt) (Fin 3)) :
    FiniteOneTapeProgram.Action (Fin (2 + Fintype.card (Active M))) (Fin 3) :=
  ⟨a.write, stateEquiv M a.target, a.move⟩

theorem slotIndex_eq_of_eq_one (slot : Fin 2) :
    ULogBytecode.slotIndex (slot = 1) = slot := by
  fin_cases slot <;> rfl

theorem numerical_rule_source (M : Machine ns nt 2)
    (q : State ns nt) (read : Fin 3) (slot : Fin 2) :
    (numericalProgram M).rule (stateEquiv M q) read slot =
      ((haltProgram M).rule q read slot).map (encodeActionFinite M) := by
  have hbound :
      (ULogSourceObliviousBytecode.boundedProgram M).rule
          (stateEquiv M q) read (slot = 1) =
        ((haltProgram M).rule q read (ULogBytecode.slotIndex (slot = 1))).map
          (ofFiniteAction (stateEquiv M) (Equiv.refl (Fin 3))) := by
    simpa [ULogSourceObliviousBytecode.boundedProgram] using
      ofFiniteProgram_rule (stateEquiv M) (Equiv.refl (Fin 3))
        (haltProgram M) q read (slot = 1)
  change ((ULogSourceObliviousBytecode.boundedProgram M).rule
      (stateEquiv M q) read (slot = 1)).map
      (fun a => ⟨a.write, a.target, a.move⟩) =
    ((haltProgram M).rule q read slot).map (encodeActionFinite M)
  rw [hbound, slotIndex_eq_of_eq_one, Option.map_map]
  rfl

theorem numerical_rule (M : Machine ns nt 2)
    (q : Fin (2 + Fintype.card (Active M))) (read : Fin 3) (slot : Fin 2) :
    (numericalProgram M).rule q read slot =
      ((haltProgram M).rule ((stateEquiv M).symm q) read slot).map
        (encodeActionFinite M) := by
  simpa [Equiv.apply_symm_apply] using
    numerical_rule_source M ((stateEquiv M).symm q) read slot

noncomputable def arrowEquiv (M : Machine ns nt 2) :
    Arrow (haltProgram M) ≃ Arrow (numericalProgram M) where
  toFun a :=
    ⟨((stateEquiv M a.1.1.1, a.1.1.2), a.1.2), by
      intro hnone
      apply a.2
      have hrule := numerical_rule_source M a.1.1.1 a.1.1.2 a.1.2
      rw [hrule] at hnone
      exact Option.map_eq_none_iff.mp hnone⟩
  invFun a :=
    ⟨(((stateEquiv M).symm a.1.1.1, a.1.1.2), a.1.2), by
      intro hnone
      apply a.2
      rw [numerical_rule, hnone]
      rfl⟩
  left_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · exact Equiv.symm_apply_apply (stateEquiv M) _
      · rfl
    · rfl
  right_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · exact Equiv.apply_symm_apply (stateEquiv M) _
      · rfl
    · rfl

theorem arrowEquiv_val (M : Machine ns nt 2) (a : Arrow (haltProgram M)) :
    (arrowEquiv M a).1 = ((stateEquiv M a.1.1.1, a.1.1.2), a.1.2) := rfl

theorem actionOf_arrowEquiv (M : Machine ns nt 2) (a : Arrow (haltProgram M)) :
    actionOf (numericalProgram M) (arrowEquiv M a) =
      encodeActionFinite M (actionOf (haltProgram M) a) := by
  cases h : (haltProgram M).rule a.1.1.1 a.1.1.2 a.1.2 with
  | none => exact (a.2 h).elim
  | some act =>
      have hsrc :=
        ULogSourceOneHotPaddedMacro.actionOf_eq_of_rule_eq
          (haltProgram M) a act h
      have hnum :
          (numericalProgram M).rule (stateEquiv M a.1.1.1) a.1.1.2 a.1.2 =
            some (encodeActionFinite M act) := by
        rw [numerical_rule_source, h]
        rfl
      have htgt :=
        ULogSourceOneHotPaddedMacro.actionOf_eq_of_rule_eq
          (numericalProgram M) (arrowEquiv M a) (encodeActionFinite M act)
          (by simpa [arrowEquiv_val] using hnum)
      rw [htgt, hsrc]

theorem transition_arrowEquiv (M : Machine ns nt 2) (a : Arrow (haltProgram M)) :
    transition (numericalProgram M) (arrowEquiv M a) =
      { sourceState := stateEquiv M (transition (haltProgram M) a).sourceState
        read := (transition (haltProgram M) a).read
        write := (transition (haltProgram M) a).write
        targetState := stateEquiv M (transition (haltProgram M) a).targetState
        move := (transition (haltProgram M) a).move } := by
  unfold transition
  rw [actionOf_arrowEquiv]
  simp [encodeActionFinite, arrowEquiv_val]

@[simp] theorem encodeConfig_state (M : Machine ns nt 2)
    (c : Config (State ns nt) (Fin 3)) :
    (encodeConfig M c).state = stateEquiv M c.state := rfl

@[simp] theorem encodeConfig_head (M : Machine ns nt 2)
    (c : Config (State ns nt) (Fin 3)) :
    (encodeConfig M c).head = c.head := rfl

@[simp] theorem encodeConfig_tape (M : Machine ns nt 2)
    (c : Config (State ns nt) (Fin 3)) :
    (encodeConfig M c).tape = c.tape := rfl

theorem encodeConfig_accept (M : Machine ns nt 2)
    (c : Config (State ns nt) (Fin 3)) :
    (encodeConfig M c).state.val = 0 ↔ c.state = State.atLeft M.accept := by
  constructor
  · intro h
    have h0 : stateEquiv M c.state = stateEquiv M (State.atLeft M.accept) := by
      apply Fin.ext
      simpa [stateEquiv_accept] using h
    exact (stateEquiv M).injective h0
  · intro h
    simp [h, stateEquiv_accept]

theorem step_arrowEquiv (M : Machine ns nt 2) (movable : Fin 3 → Bool)
    (c : Config (State ns nt) (Fin 3)) (a : Arrow (haltProgram M)) :
    step (numericalProgram M) movable (encodeConfig M c) (arrowEquiv M a) =
      (step (haltProgram M) movable c a).map (encodeConfig M) := by
  unfold step
  have htr := transition_arrowEquiv M a
  have hiff :
      ((encodeConfig M c).state ≠
          (transition (numericalProgram M) (arrowEquiv M a)).sourceState ∨
        (encodeConfig M c).tape (encodeConfig M c).head ≠
          (transition (numericalProgram M) (arrowEquiv M a)).read) ↔
      (c.state ≠ (transition (haltProgram M) a).sourceState ∨
        c.tape c.head ≠ (transition (haltProgram M) a).read) := by
    rw [htr]
    simp [encodeConfig, Equiv.apply_eq_iff_eq]
  by_cases hbad :
      c.state ≠ (transition (haltProgram M) a).sourceState ∨
        c.tape c.head ≠ (transition (haltProgram M) a).read
  · rw [if_pos (hiff.mpr hbad), if_pos hbad]
    rfl
  · rw [if_neg (mt hiff.mp hbad), if_neg hbad]
    have hwrite :
        (transition (numericalProgram M) (arrowEquiv M a)).write =
          (transition (haltProgram M) a).write := by
      rw [htr]
    have hmove :
        (transition (numericalProgram M) (arrowEquiv M a)).move =
          (transition (haltProgram M) a).move := by
      rw [htr]
    have htgt :
        (transition (numericalProgram M) (arrowEquiv M a)).targetState =
          stateEquiv M (transition (haltProgram M) a).targetState := by
      rw [htr]
    have htape :
        writtenTape (encodeConfig M c)
            (transition (numericalProgram M) (arrowEquiv M a)).write =
          writtenTape c (transition (haltProgram M) a).write := by
      simp [writtenTape, hwrite]
    have hhead :
        moveHead (transition (numericalProgram M) (arrowEquiv M a)).move
            (encodeConfig M c).head =
          moveHead (transition (haltProgram M) a).move c.head := by
      simp [hmove]
    simp only [htape, hhead]
    by_cases hmov :
        movable (writtenTape c (transition (haltProgram M) a).write
          (moveHead (transition (haltProgram M) a).move c.head)) = true
    · rw [if_pos hmov, if_pos hmov]
      apply congrArg some
      simp [encodeConfig, htgt]
    · rw [if_neg hmov, if_neg hmov]
      rfl

theorem run_arrowEquiv (M : Machine ns nt 2) (movable : Fin 3 → Bool)
    (word : List (Arrow (haltProgram M))) (c : Config (State ns nt) (Fin 3)) :
    run (numericalProgram M) movable (word.map (arrowEquiv M)) (encodeConfig M c) =
      (run (haltProgram M) movable word c).map (encodeConfig M) := by
  induction word generalizing c with
  | nil => simp [run]
  | cons a word ih =>
      simp only [List.map_cons, run_cons]
      rw [step_arrowEquiv]
      cases step (haltProgram M) movable c a with
      | none => simp
      | some c' => simp [ih]

theorem arrowEquiv_word_length (M : Machine ns nt 2)
    (word : List (Arrow (haltProgram M))) :
    (word.map (arrowEquiv M)).length = word.length := by
  simp

theorem map_arrowEquiv_left (M : Machine ns nt 2)
    (word : List (Arrow (haltProgram M))) :
    (word.map (arrowEquiv M)).map (arrowEquiv M).symm = word := by
  induction word with
  | nil => rfl
  | cons a word ih => simp [ih, Equiv.symm_apply_apply]

theorem map_arrowEquiv_right (M : Machine ns nt 2)
    (word : List (Arrow (numericalProgram M))) :
    (word.map (arrowEquiv M).symm).map (arrowEquiv M) = word := by
  induction word with
  | nil => rfl
  | cons a word ih => simp [ih, Equiv.apply_symm_apply]

def AcceptingHaltLeavesAt (M : Machine ns nt 2)
    (c : Config (State ns nt) (Fin 3)) :=
  {word : List (Arrow (haltProgram M)) //
    ∃ out, run (haltProgram M) (fun _ => true) word c = some out ∧
      out.state = State.atLeft M.accept}

def AcceptingNumericalLeavesAt (M : Machine ns nt 2)
    (c : Config (State ns nt) (Fin 3)) :=
  {word : List (Arrow (numericalProgram M)) //
    ∃ out, run (numericalProgram M) (fun _ => true) word (encodeConfig M c) =
        some out ∧ out.state.val = 0}

noncomputable def acceptingLeavesAtEquiv (M : Machine ns nt 2)
    (c : Config (State ns nt) (Fin 3)) :
    AcceptingHaltLeavesAt M c ≃ AcceptingNumericalLeavesAt M c where
  toFun w :=
    ⟨w.1.map (arrowEquiv M), by
      obtain ⟨out, hrun, hacc⟩ := w.2
      refine ⟨encodeConfig M out, ?_, (encodeConfig_accept M out).mpr hacc⟩
      rw [run_arrowEquiv, hrun]
      rfl⟩
  invFun w :=
    ⟨w.1.map (arrowEquiv M).symm, by
      obtain ⟨outN, hrun, hacc⟩ := w.2
      have hrestore :
          w.1 =
            List.map (arrowEquiv M)
              (List.map (arrowEquiv M).symm w.1) :=
        (map_arrowEquiv_right M w.1).symm
      rw [hrestore, run_arrowEquiv] at hrun
      obtain ⟨out, hhalt, hout⟩ := Option.map_eq_some_iff.mp hrun
      refine ⟨out, hhalt, (encodeConfig_accept M out).mp ?_⟩
      simpa [hout] using hacc⟩
  left_inv w := Subtype.ext (map_arrowEquiv_left M w.1)
  right_inv w := Subtype.ext (map_arrowEquiv_right M w.1)

def AcceptingNumericalLeaves (M : Machine ns nt 2) (x : List Bool)
    (bound : Nat) (exterior : Int → Fin 3) :=
  AcceptingNumericalLeavesAt M
    (initialWindowConfig M.start (inputWindow M x bound) exterior)

noncomputable def numericalLeavesEquiv (M : Machine ns nt 2) (x : List Bool)
    (bound : Nat) (exterior : Int → Fin 3) :
    AcceptingHaltLeaves M x bound exterior ≃
      AcceptingNumericalLeaves M x bound exterior :=
  acceptingLeavesAtEquiv M
    (initialWindowConfig M.start (inputWindow M x bound) exterior)

theorem ordinary_leaf_count_numerical (M : Machine ns nt 2) (x : List Bool)
    (bound : Nat) (htime : RunsAtMost M x bound) (exterior : Int → Fin 3) :
    acceptingCount M x bound =
      Nat.card (AcceptingNumericalLeaves M x bound exterior) :=
  (all_physical_leaf_count M x bound htime exterior).trans
    (Nat.card_congr (numericalLeavesEquiv M x bound exterior))

noncomputable def ordinaryLeavesNumericalEquiv (M : Machine ns nt 2)
    (x : List Bool) (bound : Nat) (htime : RunsAtMost M x bound)
    (exterior : Int → Fin 3) :
    AcceptingLeaf M x ≃ AcceptingNumericalLeaves M x bound exterior :=
  (ordinaryLeavesEquiv M x bound htime exterior).trans
    (numericalLeavesEquiv M x bound exterior)

end PakFixedPolyomino.ULogSourceObliviousBytecodeRunBridge
