import PakFixedPolyomino.ULogSourceObliviousHaltingProgram
import PakFixedPolyomino.ULogSourceReservedStateEncoding

/-! Reserved-code bytecode for the actual source scanner's finite table.
The table depends on the source machine, not its input, horizon or window
length. This is a rule-level compiler; compact input loading and whole-run
transport into the fixed physical interpreter remain separate obligations. -/

namespace PakFixedPolyomino.ULogSourceObliviousBytecode

open FiniteOneTapeProgram ULogCompiler ULogSourceObliviousScanProgram
open ULogSourceObliviousHaltingProgram StandardNondeterministicMachine

variable {ns nt : ℕ}

abbrev ScannerState (ns nt : Nat) := ULogSourceObliviousScanProgram.State ns nt

/-- Keep every scanner state distinct, including the two rejecting forms.
Only the scanner rejection state receives numerical code one. The source
rejection state remains a distinct blocked state, with no outgoing rule. -/
def Active (M : Machine ns nt 2) :=
  {q : ScannerState ns nt // q ≠ .atLeft M.accept ∧ q ≠ .reject}

noncomputable instance (M : Machine ns nt 2) : Fintype (Active M) :=
  by
    classical
    dsimp [Active]
    infer_instance

noncomputable def toReserved (M : Machine ns nt 2) (q : ScannerState ns nt) :
    ULogSourceReservedStateEncoding.State (Active M) :=
  if ha : q = .atLeft M.accept then .inl 0
  else if hr : q = .reject then .inl 1
  else .inr ⟨q, ha, hr⟩

def fromReserved (M : Machine ns nt 2) :
    ULogSourceReservedStateEncoding.State (Active M) → ScannerState ns nt
  | .inl h => if h = 0 then .atLeft M.accept else .reject
  | .inr q => q.val

theorem from_to (M : Machine ns nt 2) (q : ScannerState ns nt) :
    fromReserved M (toReserved M q) = q := by
  classical
  unfold toReserved
  split_ifs with ha hr
  · simp [fromReserved, ha]
  · simp [fromReserved, hr]
  · rfl

theorem to_from (M : Machine ns nt 2)
    (q : ULogSourceReservedStateEncoding.State (Active M)) :
    toReserved M (fromReserved M q) = q := by
  classical
  cases q with
  | inl h =>
      fin_cases h <;> simp [fromReserved, toReserved]
  | inr q =>
      simp [fromReserved, toReserved, q.property.1, q.property.2]
      apply congrArg Sum.inr
      exact Subtype.ext rfl

noncomputable def reservedEquiv (M : Machine ns nt 2) :
    ScannerState ns nt ≃ ULogSourceReservedStateEncoding.State (Active M) where
  toFun := toReserved M
  invFun := fromReserved M
  left_inv := from_to M
  right_inv := to_from M

noncomputable def stateEquiv (M : Machine ns nt 2) :
    ScannerState ns nt ≃ Fin (2 + Fintype.card (Active M)) :=
  (reservedEquiv M).trans ULogSourceReservedStateEncoding.stateEquiv

@[simp] theorem stateEquiv_accept (M : Machine ns nt 2) :
    (stateEquiv M (.atLeft M.accept)).val = 0 := by
  classical
  simp [stateEquiv, reservedEquiv, toReserved]

@[simp] theorem stateEquiv_reject (M : Machine ns nt 2) :
    (stateEquiv M .reject).val = 1 := by
  classical
  simp [stateEquiv, reservedEquiv, toReserved]

/-- Numerical recoding uses the same three tape symbols and both actual
occupied slots. No time horizon or window length is an argument. -/
noncomputable def boundedProgram (M : Machine ns nt 2) :
    BoundedProgram (2 + Fintype.card (Active M)) 3 :=
  ofFiniteProgram (stateEquiv M) (Equiv.refl (Fin 3)) (haltProgram M)

noncomputable def bytecode (M : Machine ns nt 2) : ULogBytecode.ProgramCode :=
  compile (boundedProgram M)

noncomputable def encodeAction (M : Machine ns nt 2)
    (a : Action (ScannerState ns nt) (Fin 3)) : ULogBytecode.ActionCode :=
  actionCode (ofFiniteAction (stateEquiv M) (Equiv.refl (Fin 3)) a)

/-- Exact selected-rule transport into universal bytecode. Slot labels stay
literal even if two rules have the same action. -/
theorem lookup_bytecode (M : Machine ns nt 2) (q : ScannerState ns nt)
    (read : Fin 3) (slot : Bool) :
    ULogBytecode.lookupRule (bytecode M) (stateEquiv M q).val read.val slot =
      ((haltProgram M).rule q read (ULogBytecode.slotIndex slot)).map
        (encodeAction M) := by
  classical
  rw [bytecode, lookup_compile]
  rw [show (boundedProgram M).rule (stateEquiv M q) read slot =
    ((haltProgram M).rule q read (ULogBytecode.slotIndex slot)).map
      (ofFiniteAction (stateEquiv M) (Equiv.refl (Fin 3))) by
        exact ofFiniteProgram_rule (stateEquiv M) (Equiv.refl (Fin 3))
          (haltProgram M) q read slot]
  simp only [Option.map_map]
  rfl

theorem encodeAction_injective (M : Machine ns nt 2) :
    Function.Injective (encodeAction M) := by
  classical
  intro a b h
  cases a with
  | mk aw aq am =>
    cases b with
    | mk bw bt bm =>
      have hw : aw = bw := Fin.ext (congrArg ULogBytecode.ActionCode.write h)
      have ht : aq = bt := (stateEquiv M).injective
        (Fin.ext (congrArg ULogBytecode.ActionCode.target h))
      have hm : am = bm := congrArg ULogBytecode.ActionCode.move h
      subst bw; subst bt; subst bm
      rfl

/-- Every selected bytecode rule comes from the actual finite scanner rule;
there is no extra accepted-image assumption. -/
theorem lookup_bytecode_some_iff (M : Machine ns nt 2) (q : ScannerState ns nt)
    (read : Fin 3) (slot : Bool) (code : ULogBytecode.ActionCode) :
    ULogBytecode.lookupRule (bytecode M) (stateEquiv M q).val read.val slot = some code ↔
      ∃ a, (haltProgram M).rule q read (ULogBytecode.slotIndex slot) = some a ∧
        encodeAction M a = code := by
  rw [lookup_bytecode]
  exact Option.map_eq_some_iff

@[simp] theorem bytecode_accept_terminal (M : Machine ns nt 2)
    (read : Fin 3) (slot : Bool) :
    ULogBytecode.lookupRule (bytecode M) 0 read.val slot = none := by
  simpa only [stateEquiv_accept, haltProgram_accept_terminal, Option.map_none] using
    lookup_bytecode M (.atLeft M.accept) read slot

@[simp] theorem bytecode_reject_terminal (M : Machine ns nt 2)
    (read : Fin 3) (slot : Bool) :
    ULogBytecode.lookupRule (bytecode M) 1 read.val slot = none := by
  simpa only [stateEquiv_reject, haltProgram_reject_terminal, Option.map_none] using
    lookup_bytecode M .reject read slot

@[simp] theorem bytecode_source_reject_terminal (M : Machine ns nt 2)
    (read : Fin 3) (slot : Bool) :
    ULogBytecode.lookupRule (bytecode M) (stateEquiv M (.atLeft M.reject)).val
      read.val slot = none := by
  simpa only [haltProgram_source_reject_terminal, Option.map_none] using
    lookup_bytecode M (.atLeft M.reject) read slot

theorem bytecode_tape_bounds (M : Machine ns nt 2)
    {r : ULogBytecode.RuleCode} (hr : r ∈ bytecode M) :
    r.read < 3 ∧ r.action.write < 3 := by
  have h := compile_rule_bounded (boundedProgram M) hr
  exact ⟨h.2.1, h.2.2.1⟩

theorem bytecode_length_le (M : Machine ns nt 2) :
    (bytecode M).length ≤ 6 * (2 + Fintype.card (Active M)) := by
  have h := compile_length_le (boundedProgram M)
  dsimp [bytecode]
  nlinarith

end PakFixedPolyomino.ULogSourceObliviousBytecode
