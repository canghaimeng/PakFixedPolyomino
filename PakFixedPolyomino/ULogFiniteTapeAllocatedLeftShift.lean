import PakFixedPolyomino.ULogFiniteTapeAllocatedRightShift
import PakFixedPolyomino.ULogFiniteTapeReflection

/-! Actual leftward movement through allocated ternary cells, obtained by
literal reflection of the checked rightward controller. No extra tick or
cell, and no loss of raw labels. -/
namespace PakFixedPolyomino.ULogFiniteTapeAllocatedLeftShift
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open ULogFiniteTapeReflection (reflectConfig config_involutive cellCount_reflect)

abbrev stateCount := ULogFiniteTapeAllocatedRightShift.stateCount

def program (distance : Nat) : BoundedProgram (stateCount distance) 3 :=
  ULogFiniteTapeReflection.program (ULogFiniteTapeAllocatedRightShift.program distance)

def initial (distance : Nat) (left xs target : List (Fin 3)) :
    BoundedConfig (stateCount distance) 3 :=
  reflectConfig (ULogFiniteTapeAllocatedRightShift.initial distance left xs target)

def final (distance : Nat) (left xs target : List (Fin 3)) :
    BoundedConfig (stateCount distance) 3 :=
  reflectConfig (ULogFiniteTapeAllocatedRightShift.final distance left xs target)

theorem program_falseOnly (distance : Nat) :
    ULogFiniteAlphabetDeterministicRuns.FalseOnly (program distance) :=
  ULogFiniteTapeReflection.program_falseOnly _
    (ULogFiniteTapeAllocatedRightShift.program_falseOnly distance)

theorem final_accepts (distance : Nat) (left xs target : List (Fin 3)) :
    (final distance left xs target).state.val = 0 :=
  ULogFiniteTapeAllocatedRightShift.final_accepts distance left xs target

theorem actual_run (distance : Nat) (left xs target : List (Fin 3))
    (hlen : xs.length = distance) (hne : target ≠ []) (H : Int) :
    run (program distance) 2 (List.replicate distance false) H
      (initial distance left xs target) =
        some (H - (distance : Int), final distance left xs target) := by
  have reflected := ULogFiniteTapeReflection.run_reflect
    (ULogFiniteTapeAllocatedRightShift.program distance) (2 : Fin 3)
    (List.replicate distance false) (-H)
    (ULogFiniteTapeAllocatedRightShift.initial distance left xs target)
  rw [ULogFiniteTapeAllocatedRightShift.actual_run distance left xs target hlen hne (-H)] at reflected
  simpa [program, initial, final, sub_eq_add_neg, add_comm] using reflected

theorem raw_inverse (distance : Nat) (left xs target : List (Fin 3))
    (H hf : Int) (w : List Bool) (out : BoundedConfig (stateCount distance) 3)
    (raw : run (program distance) 2 w H (initial distance left xs target) = some (hf, out)) :
    run (ULogFiniteTapeAllocatedRightShift.program distance) 2 w (-H)
      (ULogFiniteTapeAllocatedRightShift.initial distance left xs target) =
        some (-hf, reflectConfig out) := by
  have h := (ULogFiniteTapeReflection.every_raw_inverse
    (ULogFiniteTapeAllocatedRightShift.program distance) (2 : Fin 3) w H hf
    (initial distance left xs target) out).1 raw
  simpa only [initial, config_involutive] using h

theorem occupied_initial (distance : Nat) (left xs target : List (Fin 3))
    (hlen : xs.length = distance) (hne : target ≠ []) :
    cellCount (initial distance left xs target) = left.length + distance + target.length := by
  simpa only [initial, cellCount_reflect] using
    ULogFiniteTapeAllocatedRightShift.occupied_initial distance left xs target hlen hne

theorem every_raw (distance : Nat) (left xs target : List (Fin 3))
    (hlen : xs.length = distance) (hne : target ≠ []) (H hf : Int)
    (w : List Bool) (out : BoundedConfig (stateCount distance) 3)
    (raw : run (program distance) 2 w H (initial distance left xs target) = some (hf, out)) :
    w = List.replicate w.length false ∧ w.length ≤ distance ∧
      hf = H - (w.length : Int) ∧ H - (distance : Int) ≤ hf ∧ hf ≤ H ∧
      cellCount out = left.length + distance + target.length := by
  have after := raw_inverse distance left xs target H hf w out raw
  have bounds := ULogFiniteTapeAllocatedRightShift.every_raw distance left xs target hlen hne
    (-H) (-hf) w (reflectConfig out) after
  have growth := ULogFiniteTapeAllocatedRightShift.every_raw_no_growth distance left xs target
    hlen hne (-H) (-hf) w (reflectConfig out) after
  have cells : cellCount out = left.length + distance + target.length := by
    simpa only [cellCount_reflect, Nat.add_zero,
      ULogFiniteTapeAllocatedRightShift.occupied_initial distance left xs target hlen hne]
      using growth.exact_ledger.2.2.1
  refine ⟨bounds.1, bounds.2.1, ?_, ?_, ?_, cells⟩ <;> omega

theorem every_raw_no_growth (distance : Nat) (left xs target : List (Fin 3))
    (hlen : xs.length = distance) (hne : target ≠ []) (H hf : Int)
    (w : List Bool) (out : BoundedConfig (stateCount distance) 3)
    (raw : run (program distance) 2 w H (initial distance left xs target) = some (hf, out)) :
    GrowthRun (program distance) 2 w H (initial distance left xs target) hf out 0 0 := by
  obtain ⟨lg, rg, growth⟩ := every_actual_run (program distance) 2 w H hf _ out raw
  have ledger := growth.exact_ledger
  have cells := (every_raw distance left xs target hlen hne H hf w out raw).2.2.2.2.2
  have before := occupied_initial distance left xs target hlen hne
  have hl : lg = 0 := by omega
  have hr : rg = 0 := by omega
  simpa only [hl, hr] using growth

theorem every_accepting_word (distance : Nat) (left xs target : List (Fin 3))
    (hlen : xs.length = distance) (hne : target ≠ []) (H hf : Int)
    (w : List Bool) (out : BoundedConfig (stateCount distance) 3)
    (raw : run (program distance) 2 w H (initial distance left xs target) = some (hf, out))
    (accepts : out.state.val = 0) :
    w = List.replicate distance false ∧ hf = H - (distance : Int) ∧
      out = final distance left xs target := by
  have after := raw_inverse distance left xs target H hf w out raw
  have h := ULogFiniteTapeAllocatedRightShift.every_accepting_word distance left xs target
    hlen hne (-H) (-hf) w (reflectConfig out) after accepts
  refine ⟨h.1, by omega, ?_⟩
  have endpoint := congrArg reflectConfig h.2.2
  simpa only [config_involutive, final] using endpoint

theorem all_cutoff_counts (distance : Nat) (left xs target : List (Fin 3))
    (hlen : xs.length = distance) (hne : target ≠ []) (H : Int) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T
      (liftConfig (program distance) (initial distance left xs target)) =
        if distance ≤ T then 1 else 0 :=
  ULogFiniteAlphabetDeterministicRuns.acceptingPaths_threshold (2 : Fin 3) (by decide)
    (program distance) (program_falseOnly distance) distance H
    (initial distance left xs target) (final distance left xs target) (H - (distance : Int))
    (actual_run distance left xs target hlen hne H) (final_accepts distance left xs target) T

theorem allocated_left_shift_spec (distance : Nat) (left xs target : List (Fin 3))
    (hlen : xs.length = distance) (hne : target ≠ []) (H : Int) :
    (run (program distance) 2 (List.replicate distance false) H
      (initial distance left xs target) =
        some (H - (distance : Int), final distance left xs target)) ∧
    (∀ w hf out, run (program distance) 2 w H (initial distance left xs target) = some (hf, out) →
      w = List.replicate w.length false ∧ w.length ≤ distance ∧
      hf = H - (w.length : Int) ∧ H - (distance : Int) ≤ hf ∧ hf ≤ H ∧
      cellCount out = left.length + distance + target.length ∧
      GrowthRun (program distance) 2 w H (initial distance left xs target) hf out 0 0) ∧
    (∀ w hf out, run (program distance) 2 w H (initial distance left xs target) = some (hf, out) →
      out.state.val = 0 → w = List.replicate distance false ∧
        hf = H - (distance : Int) ∧ out = final distance left xs target) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T
      (liftConfig (program distance) (initial distance left xs target)) =
        if distance ≤ T then 1 else 0) := by
  refine ⟨actual_run distance left xs target hlen hne H, ?_,
    (fun w hf out => every_accepting_word distance left xs target hlen hne H hf w out),
    all_cutoff_counts distance left xs target hlen hne H⟩
  intro w hf out raw
  have bounds := every_raw distance left xs target hlen hne H hf w out raw
  exact ⟨bounds.1, bounds.2.1, bounds.2.2.1, bounds.2.2.2.1, bounds.2.2.2.2.1,
    bounds.2.2.2.2.2, every_raw_no_growth distance left xs target hlen hne H hf w out raw⟩

end PakFixedPolyomino.ULogFiniteTapeAllocatedLeftShift
