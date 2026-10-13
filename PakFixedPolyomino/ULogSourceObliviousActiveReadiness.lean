import PakFixedPolyomino.ULogSourceObliviousAcceptingGrowth
import PakFixedPolyomino.ULogFiniteTapeUniformMoveReadiness
import PakFixedPolyomino.ULogFiniteTapeHeadTranslation

/-! Source scanner branching changes the selected action stored in control,
but both occupied branches physically stay. This internally supplies the
uniform-move property. Every accepting word therefore has active frame
readiness at the exact state-capacity bound and consumes no exterior cells.
No arbitrary physical trace reflection or physical microtime is asserted. -/
namespace PakFixedPolyomino.ULogSourceObliviousActiveReadiness
open StandardNondeterministicMachine StandardMachineWindowBridge
open ULogCompiler ULogSourceObliviousBytecode
open ULogSourceObliviousScanProgram ULogSourceObliviousHaltingProgram
open ULogSourceObliviousExteriorZipper ULogSourceObliviousAcceptingGrowth
open ULogFiniteTapeUniformMoveReadiness
open ULogFiniteTapeDeterministicFrameReadiness (ActiveReadyRun)
open ULogFiniteTapePhysicalResourceLedger (resourceRun actual_resource_run)
variable {ns nt : Nat}

theorem original_same_moves (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : State ns nt) (read : Fin 3) (b c : Fin 2)
    (a d : FiniteOneTapeProgram.Action (State ns nt) (Fin 3))
    (hb : (program p hnt blank).rule q read b = some a)
    (hc : (program p hnt blank).rule q read c = some d) : a.move = d.move := by
  classical
  by_cases hq : ∃ s r, q = .branch s r
  · obtain ⟨s, r, rfl⟩ := hq
    rw [branch_rule] at hb hc
    obtain ⟨a0, _, rfl⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨d0, _, rfl⟩ := Option.map_eq_some_iff.mp hc
    rfl
  · have hn : ∀ s r, q ≠ .branch s r := fun s r h => hq ⟨s, r, h⟩
    have slot_zero : ∀ slot act, (program p hnt blank).rule q read slot = some act → slot = 0 := by
      intro slot act hh
      fin_cases slot
      · rfl
      · have hh' : (program p hnt blank).rule q read 1 = some act := by simpa using hh
        rw [nonbranch_slot_one_empty p hnt blank q read hn] at hh'
        contradiction
    rw [slot_zero b a hb] at hb
    rw [slot_zero c d hc] at hc
    exact congrArg FiniteOneTapeProgram.Action.move (Option.some.inj (hb.symm.trans hc))

theorem halt_same_moves (M : Machine ns nt 2) (q : State ns nt) (read : Fin 3)
    (b c : Fin 2) (a d : FiniteOneTapeProgram.Action (State ns nt) (Fin 3))
    (hb : (haltProgram M).rule q read b = some a)
    (hc : (haltProgram M).rule q read c = some d) : a.move = d.move := by
  cases hh : halted M q with
  | true => simp [haltProgram, FiniteOneTapeHaltingRestriction.terminalize, hh] at hb
  | false =>
      apply original_same_moves (StandardMachineZipperBridge.toBounded M)
        (Nat.zero_lt_of_lt M.blank.isLt) M.blank q read b c a d
      · simpa [haltProgram, FiniteOneTapeHaltingRestriction.terminalize, hh] using hb
      · simpa [haltProgram, FiniteOneTapeHaltingRestriction.terminalize, hh] using hc

theorem scanner_same_moves (M : Machine ns nt 2) :
    SameMoves (ULogSourceObliviousBytecode.boundedProgram M) := by
  intro q read b c a d hb hc
  change ((haltProgram M).rule ((stateEquiv M).symm q) read (ULogBytecode.slotIndex b)).map
    (ofFiniteAction (stateEquiv M) (Equiv.refl (Fin 3))) = some a at hb
  change ((haltProgram M).rule ((stateEquiv M).symm q) read (ULogBytecode.slotIndex c)).map
    (ofFiniteAction (stateEquiv M) (Equiv.refl (Fin 3))) = some d at hc
  obtain ⟨a0, ha0, rfl⟩ := Option.map_eq_some_iff.mp hb
  obtain ⟨d0, hd0, rfl⟩ := Option.map_eq_some_iff.mp hc
  exact halt_same_moves M _ _ _ _ a0 d0 ha0 hd0

theorem accepting_active_ready (M : Machine ns nt 2) (x : List Bool)
    (bound : Nat) (ht : RunsAtMost M x bound) (left suffix : List (Fin 3))
    (slots : List Bool) (hf : Int)
    (out : BoundedConfig (2 + Fintype.card (ULogSourceObliviousBytecode.Active M)) 3)
    (hw : ULogFiniteTapeZipperRun.run (ULogSourceObliviousBytecode.boundedProgram M) 2 slots 0
      (zipper M (inputWindow M x bound) left suffix) = some (hf, out))
    (ha : out.state.val = 0) (C : Nat) (outer : List ULogProgram.Tape)
    (hC : 1 + Fintype.card (ULogSourceObliviousBytecode.Active M) ≤ C) :
    ActiveReadyRun (ULogSourceObliviousBytecode.boundedProgram M) slots 0
      (zipper M (inputWindow M x bound) left suffix) C outer ∧
    resourceRun (ULogSourceObliviousBytecode.boundedProgram M) 2 slots 0
      (zipper M (inputWindow M x bound) left suffix) C outer = some (hf, out, C, outer) := by
  have growth := accepting_zero_growth M x bound ht left suffix slots hf out hw ha
  constructor
  · simpa using actual_active_ready growth (scanner_same_moves M) C outer (by omega)
  · simpa using actual_resource_run growth C outer

theorem accepting_zero_growth_at (M : Machine ns nt 2) (x : List Bool)
    (bound : Nat) (ht : RunsAtMost M x bound) (left suffix : List (Fin 3))
    (slots : List Bool) (H hf : Int)
    (out : BoundedConfig (2 + Fintype.card (ULogSourceObliviousBytecode.Active M)) 3)
    (hw : ULogFiniteTapeZipperRun.run (ULogSourceObliviousBytecode.boundedProgram M) 2 slots H
      (zipper M (inputWindow M x bound) left suffix) = some (hf, out))
    (ha : out.state.val = 0) :
    ULogFiniteTapeGrowthLedger.GrowthRun (ULogSourceObliviousBytecode.boundedProgram M) 2 slots H
      (zipper M (inputWindow M x bound) left suffix) hf out 0 0 := by
  obtain ⟨hf0, hzero, hhead⟩ := ULogFiniteTapeHeadTranslation.run_from_zero _ 2 slots H hf _ out hw
  have growth := accepting_zero_growth M x bound ht left suffix slots hf0 out hzero ha
  simpa only [zero_add, hhead] using ULogFiniteTapeHeadTranslation.growth_add growth H

theorem accepting_active_ready_at (M : Machine ns nt 2) (x : List Bool)
    (bound : Nat) (ht : RunsAtMost M x bound) (left suffix : List (Fin 3))
    (slots : List Bool) (H hf : Int)
    (out : BoundedConfig (2 + Fintype.card (ULogSourceObliviousBytecode.Active M)) 3)
    (hw : ULogFiniteTapeZipperRun.run (ULogSourceObliviousBytecode.boundedProgram M) 2 slots H
      (zipper M (inputWindow M x bound) left suffix) = some (hf, out))
    (ha : out.state.val = 0) (C : Nat) (outer : List ULogProgram.Tape)
    (hC : 1 + Fintype.card (ULogSourceObliviousBytecode.Active M) ≤ C) :
    ActiveReadyRun (ULogSourceObliviousBytecode.boundedProgram M) slots H
      (zipper M (inputWindow M x bound) left suffix) C outer ∧
    resourceRun (ULogSourceObliviousBytecode.boundedProgram M) 2 slots H
      (zipper M (inputWindow M x bound) left suffix) C outer = some (hf, out, C, outer) := by
  have growth := accepting_zero_growth_at M x bound ht left suffix slots H hf out hw ha
  exact ⟨by simpa using actual_active_ready growth (scanner_same_moves M) C outer (by omega),
    by simpa using actual_resource_run growth C outer⟩

theorem scanner_active_resource_spec (M : Machine ns nt 2) (x : List Bool)
    (bound : Nat) (ht : RunsAtMost M x bound) (left suffix : List (Fin 3)) :
    SameMoves (ULogSourceObliviousBytecode.boundedProgram M) ∧
    ∀ slots H hf out, ULogFiniteTapeZipperRun.run (ULogSourceObliviousBytecode.boundedProgram M)
      2 slots H (zipper M (inputWindow M x bound) left suffix) = some (hf, out) →
      out.state.val = 0 →
      ULogFiniteTapeGrowthLedger.GrowthRun (ULogSourceObliviousBytecode.boundedProgram M) 2 slots H
        (zipper M (inputWindow M x bound) left suffix) hf out 0 0 ∧
      ∀ C outer, 1 + Fintype.card (ULogSourceObliviousBytecode.Active M) ≤ C →
        ActiveReadyRun (ULogSourceObliviousBytecode.boundedProgram M) slots H
          (zipper M (inputWindow M x bound) left suffix) C outer ∧
        resourceRun (ULogSourceObliviousBytecode.boundedProgram M) 2 slots H
          (zipper M (inputWindow M x bound) left suffix) C outer = some (hf, out, C, outer) :=
  ⟨scanner_same_moves M, fun slots H hf out hw ha =>
    ⟨accepting_zero_growth_at M x bound ht left suffix slots H hf out hw ha,
      accepting_active_ready_at M x bound ht left suffix slots H hf out hw ha⟩⟩

end PakFixedPolyomino.ULogSourceObliviousActiveReadiness
