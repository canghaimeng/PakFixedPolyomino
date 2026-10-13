import PakFixedPolyomino.ULogFreshEntryRunBridge
import PakFixedPolyomino.ULogTernaryGeneratedMarginSourceClock

/-! The existing fresh entry makes a real LEFT move. Advance onto the next
allocated cell first, so that this move returns to the scanner's delimiter.
The arbitrary finite exterior is retained. No scanner code is assumed to be
entry2, and the actual entry costs one tick. -/
namespace PakFixedPolyomino.ULogFreshEntryExteriorBoot
open ULogCompiler ULogFreshEntry ULogFiniteProgramZipperRunBridge
variable {k : Nat}

def initial (z : BoundedConfig (2 + k) 3) : BoundedConfig (3 + k) 3 :=
  applyBounded 2 ⟨entryState k, z.leftRev, z.focus, z.right⟩
    ⟨z.focus, entryState k, .right⟩

theorem initial_live (z : BoundedConfig (2 + k) 3) :
    boundedHalted (initial z) = false := by
  cases h : z.right <;> simp [initial, applyBounded, h, boundedHalted, entryState]

theorem stepSlot_initial (p : BoundedProgram (2 + k) 3)
    (z : BoundedConfig (2 + k) 3) (hr : z.right ≠ []) (slot : Bool) :
    boundedStepSlot (program p z.state) 2 slot (initial z) =
      if slot then none else some (insertConfig z) := by
  cases h : z.right with
  | nil => exact (hr h).elim
  | cons a rest =>
      cases slot <;>
        simp [boundedStepSlot, initial, applyBounded, h, boundedHalted,
          entryState, program, insertConfig]

theorem next_initial (p : BoundedProgram (2 + k) 3)
    (z : BoundedConfig (2 + k) 3) (hr : z.right ≠ []) :
    ULogSemantics.next (liftConfig (program p z.state) (initial z)) =
      [liftConfig (program p z.state) (insertConfig z)] := by
  rw [next_liftConfig _ (2 : Fin 3) rfl]
  simp [boundedNext, stepSlot_initial p z hr]

theorem cutoff_succ (p : BoundedProgram (2 + k) 3)
    (z : BoundedConfig (2 + k) 3) (hr : z.right ≠ []) (T : Nat) :
    ULogSemantics.machine.acceptingPaths (T + 1)
      (liftConfig (program p z.state) (initial z)) =
        ULogSemantics.machine.acceptingPaths T (liftConfig p z) := by
  have hh : ULogSemantics.halted (liftConfig (program p z.state) (initial z)) = false :=
    initial_live z
  rw [BinaryNondeterministicMachine.acceptingPaths_succ_nonhalt ULogSemantics.machine hh]
  change ((ULogSemantics.next _).map (ULogSemantics.machine.acceptingPaths T)).sum = _
  rw [next_initial p z hr]
  dsimp only [ULogSemantics.machine]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  simpa only [ULogSemantics.machine] using acceptingPaths_insertConfig p z.state T z

theorem every_raw_length (p : BoundedProgram (2 + k) 3)
    (z : BoundedConfig (2 + k) 3) (hr : z.right ≠ []) (Q : Nat)
    (hbound : ∀ w out, semanticRun (liftConfig p z) w = some out → w.length ≤ Q)
    (w : List Bool) (out : ULogSemantics.Config)
    (hw : semanticRun (liftConfig (program p z.state) (initial z)) w = some out) :
    w.length ≤ Q + 1 := by
  cases w with
  | nil => exact Nat.zero_le _
  | cons slot rest =>
      have hs := stepSlot_liftConfig (program p z.state) (2 : Fin 3) rfl slot (initial z)
      rw [stepSlot_initial p z hr] at hs
      unfold semanticRun at hw
      rw [hs] at hw
      cases slot with
      | true => simp at hw
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.bind_some] at hw
          obtain ⟨outOld, hold, _⟩ := ULogFreshEntryRunBridge.semantic_success_of_insert
            p z.state z rest out hw
          have hl := hbound rest outOld hold
          simp only [List.length_cons]; omega

theorem scanner_right_nonempty {ns nt : Nat}
    (M : StandardNondeterministicMachine.Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (left suffix : List (Fin 3)) :
    (ULogTernaryGeneratedMarginSourceCounts.scannerInitial M p x left suffix).right ≠ [] := by
  simp [ULogTernaryGeneratedMarginSourceCounts.scannerInitial]

theorem scanner_cutoff_count {ns nt : Nat}
    (M : StandardNondeterministicMachine.Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (htime : StandardNondeterministicMachine.RunsAtMost M x (2 ^ p.eval x.length))
    (left suffix : List (Fin 3)) (T : Nat)
    (hT : 14 * (ULogTernaryGeneratedMarginSourceClock.reserve nt p x) ^ 2 ≤ T) :
    StandardNondeterministicMachine.acceptingCount M x (2 ^ p.eval x.length) =
      ULogSemantics.machine.acceptingPaths (T + 1)
        (liftConfig (program (ULogSourceObliviousBytecode.boundedProgram M)
          (ULogTernaryGeneratedMarginSourceCounts.scannerInitial M p x left suffix).state)
          (initial (ULogTernaryGeneratedMarginSourceCounts.scannerInitial M p x left suffix))) := by
  rw [cutoff_succ _ _ (scanner_right_nonempty M p x left suffix)]
  exact ULogTernaryGeneratedMarginSourceClock.large_cutoff_count M p x htime left suffix T hT

theorem scanner_all_raw_length {ns nt : Nat}
    (M : StandardNondeterministicMachine.Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (htime : StandardNondeterministicMachine.RunsAtMost M x (2 ^ p.eval x.length))
    (left suffix : List (Fin 3)) (w : List Bool) (out : ULogSemantics.Config)
    (hw : semanticRun
      (liftConfig (program (ULogSourceObliviousBytecode.boundedProgram M)
        (ULogTernaryGeneratedMarginSourceCounts.scannerInitial M p x left suffix).state)
        (initial (ULogTernaryGeneratedMarginSourceCounts.scannerInitial M p x left suffix))) w = some out) :
    w.length ≤ 14 * (ULogTernaryGeneratedMarginSourceClock.reserve nt p x) ^ 2 + 1 :=
  every_raw_length _ _ (scanner_right_nonempty M p x left suffix) _
    (ULogTernaryGeneratedMarginSourceClock.every_raw_scanner_length M p x htime left suffix) w out hw

theorem actual_left_tick (p : BoundedProgram (2 + k) 3)
    (z : BoundedConfig (2 + k) 3) (hr : z.right ≠ []) (H : Int) :
    ULogFiniteTapeZipperRun.run (program p z.state) 2 [false] (H + 1) (initial z) =
      some (H, insertConfig z) := by
  cases h : z.right with
  | nil => exact (hr h).elim
  | cons a rest =>
      simp [ULogFiniteTapeZipperRun.run, initial, applyBounded, h, boundedHalted,
        entryState, program, insertConfig, FiniteOneTapeSemantics.moveHead]

theorem exterior_scanner_boot_spec {ns nt : Nat}
    (M : StandardNondeterministicMachine.Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (htime : StandardNondeterministicMachine.RunsAtMost M x (2 ^ p.eval x.length))
    (left suffix : List (Fin 3)) :
    (∀ H, ULogFiniteTapeZipperRun.run
      (program (ULogSourceObliviousBytecode.boundedProgram M)
        (ULogTernaryGeneratedMarginSourceCounts.scannerInitial M p x left suffix).state)
      2 [false] (H + 1)
      (initial (ULogTernaryGeneratedMarginSourceCounts.scannerInitial M p x left suffix)) =
      some (H, insertConfig (ULogTernaryGeneratedMarginSourceCounts.scannerInitial M p x left suffix))) ∧
    (∀ w out, semanticRun
      (liftConfig (program (ULogSourceObliviousBytecode.boundedProgram M)
        (ULogTernaryGeneratedMarginSourceCounts.scannerInitial M p x left suffix).state)
        (initial (ULogTernaryGeneratedMarginSourceCounts.scannerInitial M p x left suffix))) w = some out →
        w.length ≤ 14 * (ULogTernaryGeneratedMarginSourceClock.reserve nt p x) ^ 2 + 1) ∧
    (∀ T, 14 * (ULogTernaryGeneratedMarginSourceClock.reserve nt p x) ^ 2 ≤ T →
      StandardNondeterministicMachine.acceptingCount M x (2 ^ p.eval x.length) =
        ULogSemantics.machine.acceptingPaths (T + 1)
          (liftConfig (program (ULogSourceObliviousBytecode.boundedProgram M)
            (ULogTernaryGeneratedMarginSourceCounts.scannerInitial M p x left suffix).state)
            (initial (ULogTernaryGeneratedMarginSourceCounts.scannerInitial M p x left suffix)))) :=
  ⟨actual_left_tick _ _ (scanner_right_nonempty M p x left suffix),
    scanner_all_raw_length M p x htime left suffix, scanner_cutoff_count M p x htime left suffix⟩

end PakFixedPolyomino.ULogFreshEntryExteriorBoot
