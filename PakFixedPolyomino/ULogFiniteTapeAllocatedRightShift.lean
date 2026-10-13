import PakFixedPolyomino.ULogTernaryCountedSourceDelimiter
import PakFixedPolyomino.ULogFiniteAlphabetDeterministicRuns
import PakFixedPolyomino.ULogFiniteTapeGrowthLedger
import PakFixedPolyomino.ULogTernaryOneHotBlockWriter

/-! An actual finite ternary controller moves a fixed number of cells right,
preserving every traversed letter. It is intended for moving between loader
blocks. Every raw labelled run is covered; no allocation is hidden. -/
namespace PakFixedPolyomino.ULogFiniteTapeAllocatedRightShift
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger
open ULogTernaryCountedSourceDelimiter (fromCells fromCells_state)
open FiniteOneTapeSemantics (moveHead)

def stateCount (distance : Nat) := distance + 2

instance (distance : Nat) : NeZero (stateCount distance) :=
  ⟨by unfold stateCount; omega⟩

def remaining (distance r : Nat) (hr : r ≤ distance) : Fin (stateCount distance) :=
  if r = 0 then 0 else ⟨r + 1, by unfold stateCount; omega⟩

def program (distance : Nat) : BoundedProgram (stateCount distance) 3 where
  rule state read slot :=
    if slot then none else if halt : state.val < 2 then none else
      some ⟨read, if state.val = 2 then 0 else
        ⟨state.val - 1, by have h := state.isLt; omega⟩, .right⟩

theorem program_falseOnly (distance : Nat) : FalseOnly (program distance) := by
  intro state read
  simp [program]

theorem remaining_zero (distance : Nat) : remaining distance 0 (Nat.zero_le _) = 0 := rfl

theorem rule_remaining (distance r : Nat) (hr : r + 1 ≤ distance) (read : Fin 3) :
    (program distance).rule (remaining distance (r + 1) hr) read false =
      some ⟨read, remaining distance r (by omega), .right⟩ := by
  cases r with
  | zero => simp [program, remaining]
  | succ r =>
      have h : r + 1 + 1 + 1 ≠ 2 := by omega
      simp [program, remaining, h]

theorem sweep (distance r : Nat) (hr : r ≤ distance) (xs target left : List (Fin 3))
    (hxs : xs.length ≤ r) (hne : target ≠ []) (H : Int) :
    run (program distance) 2 (List.replicate xs.length false) H
      (fromCells (remaining distance r hr) left (xs ++ target)) =
        some (H + (xs.length : Int),
          fromCells (remaining distance (r - xs.length) (by omega))
            (xs.reverse ++ left) target) := by
  induction xs generalizing r H left with
  | nil => simp [run]
  | cons a xs ih =>
      obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by simp only [List.length_cons] at hxs; omega⟩
      simp only [List.length_cons, List.replicate_succ]
      simp only [Nat.add_sub_add_right]
      simp only [run, List.cons_append, fromCells]
      rw [rule_remaining distance k hr a]
      have hxne : xs ++ target ≠ [] := by
        intro bad
        have len := congrArg List.length bad
        have zero : target.length = 0 := by
          simp only [List.length_append, List.length_nil] at len
          omega
        exact hne (by simpa using zero)
      cases ht : xs ++ target with
      | nil => exact False.elim (hxne ht)
      | cons b rest =>
          have ih' := ih k (by omega) (a :: left) (by simp only [List.length_cons] at hxs; omega)
            (H + 1)
          rw [ht] at ih'
          simpa [applyBounded, moveHead, fromCells, boundedHalted, remaining, List.reverse_cons,
            List.append_assoc, Nat.add_sub_add_right, Int.natCast_add,
            Int.natCast_one, add_assoc, add_comm, add_left_comm] using ih'

def initial (distance : Nat) (left xs target : List (Fin 3)) :
    BoundedConfig (stateCount distance) 3 :=
  fromCells (remaining distance distance le_rfl) left (xs ++ target)

def final (distance : Nat) (left xs target : List (Fin 3)) :
    BoundedConfig (stateCount distance) 3 := fromCells 0 (xs.reverse ++ left) target

theorem actual_run (distance : Nat) (left xs target : List (Fin 3))
    (hlen : xs.length = distance) (hne : target ≠ []) (H : Int) :
    run (program distance) 2 (List.replicate distance false) H
      (initial distance left xs target) =
        some (H + (distance : Int), final distance left xs target) := by
  simpa [initial, final, hlen, remaining] using
    sweep distance distance le_rfl xs target left (by omega) hne H

theorem final_accepts (distance : Nat) (left xs target : List (Fin 3)) :
    (final distance left xs target).state.val = 0 := by
  simp [final, fromCells_state]

theorem rule_move (distance : Nat) (state : Fin (stateCount distance))
    (read : Fin 3) (slot : Bool) (a : BoundedAction (stateCount distance) 3)
    (given : (program distance).rule state read slot = some a) : a.move = .right := by
  cases slot with
  | true => simp [program] at given
  | false =>
      by_cases halt : state.val < 2
      · simp only [program, Bool.false_eq_true, ↓reduceIte, halt] at given
        cases given
      · simp only [program, Bool.false_eq_true, ↓reduceIte, halt] at given
        cases Option.some.inj given
        rfl

theorem raw_head (distance : Nat) (w : List Bool) (H hf : Int)
    (z out : BoundedConfig (stateCount distance) 3)
    (raw : run (program distance) 2 w H z = some (hf, out)) :
    hf = H + (w.length : Int) := by
  induction w generalizing H z with
  | nil => simpa [run] using (congrArg (Option.map Prod.fst) raw).symm
  | cons slot rest ih =>
      cases hh : boundedHalted z with
      | true => simp [run, hh] at raw
      | false =>
          cases ha : (program distance).rule z.state z.focus slot with
          | none => simp [run, hh, ha] at raw
          | some a =>
              have after : run (program distance) 2 rest (moveHead a.move H)
                  (applyBounded 2 z a) = some (hf, out) := by
                simpa [run, hh, ha] using raw
              have h := ih _ _ after
              have hm := rule_move distance z.state z.focus slot a ha
              simp only [hm, moveHead] at h
              simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
              omega

theorem every_raw (distance : Nat) (left xs target : List (Fin 3))
    (hlen : xs.length = distance) (hne : target ≠ []) (H hf : Int)
    (w : List Bool) (out : BoundedConfig (stateCount distance) 3)
    (raw : run (program distance) 2 w H (initial distance left xs target) = some (hf, out)) :
    w = List.replicate w.length false ∧ w.length ≤ distance ∧
      hf = H + (w.length : Int) ∧ H ≤ hf ∧ hf ≤ H + (distance : Int) := by
  have hw := successful_zipper_is_false (2 : Fin 3) (program distance)
    (program_falseOnly distance) raw
  have hb := successful_zipper_length_le (2 : Fin 3) (program distance)
    (program_falseOnly distance) distance H (initial distance left xs target)
    (final distance left xs target) (H + (distance : Int))
    (actual_run distance left xs target hlen hne H) (final_accepts distance left xs target) raw
  have hh := raw_head distance w H hf _ out raw
  refine ⟨hw, hb, hh, ?_, ?_⟩ <;> omega

theorem occupied_initial (distance : Nat) (left xs target : List (Fin 3))
    (hlen : xs.length = distance) (hne : target ≠ []) :
    cellCount (initial distance left xs target) = left.length + distance + target.length := by
  have both : xs ++ target ≠ [] := by
    intro bad
    have len := congrArg List.length bad
    have zero : target.length = 0 := by simp only [List.length_append, List.length_nil] at len; omega
    exact hne (by simpa using zero)
  simpa [initial, hlen, add_assoc] using
    ULogTernaryOneHotBlockWriter.cellCount_of_cells _ left (xs ++ target) both

theorem occupied_final (distance : Nat) (left xs target : List (Fin 3))
    (hlen : xs.length = distance) (hne : target ≠ []) :
    cellCount (final distance left xs target) = left.length + distance + target.length := by
  simpa [final, hlen, add_comm, add_left_comm, add_assoc] using
    ULogTernaryOneHotBlockWriter.cellCount_of_cells (0 : Fin (stateCount distance))
      (xs.reverse ++ left) target hne

theorem every_raw_no_growth (distance : Nat) (left xs target : List (Fin 3))
    (hlen : xs.length = distance) (hne : target ≠ []) (H hf : Int)
    (w : List Bool) (out : BoundedConfig (stateCount distance) 3)
    (raw : run (program distance) 2 w H (initial distance left xs target) = some (hf, out)) :
    GrowthRun (program distance) 2 w H (initial distance left xs target) hf out 0 0 := by
  have bounds := every_raw distance left xs target hlen hne H hf w out raw
  obtain ⟨lg, rg, full⟩ := every_actual_run (program distance) 2
    (List.replicate distance false) H (H + (distance : Int))
    (initial distance left xs target) (final distance left xs target)
    (actual_run distance left xs target hlen hne H)
  have ledger := full.exact_ledger
  have before := occupied_initial distance left xs target hlen hne
  have after := occupied_final distance left xs target hlen hne
  have hl : lg = 0 := by omega
  have hr : rg = 0 := by omega
  have whole : GrowthRun (program distance) 2
      (w ++ List.replicate (distance - w.length) false) H
      (initial distance left xs target) (H + (distance : Int))
      (final distance left xs target) 0 0 := by
    have split := ULogTernaryOneHotBlockWriter.replicate_split distance w.length bounds.2.1
    rw [bounds.1]
    simp only [List.length_replicate]
    rw [← split]
    simpa only [hl, hr] using full
  obtain ⟨lp, rp, prefixRun⟩ := every_actual_run (program distance) 2 w H hf
    (initial distance left xs target) out raw
  have small := ULogTernaryOneHotBlockWriter.growth_append_le whole prefixRun
  have hpl : lp = 0 := by omega
  have hpr : rp = 0 := by omega
  simpa only [hpl, hpr] using prefixRun

theorem every_accepting_word (distance : Nat) (left xs target : List (Fin 3))
    (hlen : xs.length = distance) (hne : target ≠ []) (H hf : Int)
    (w : List Bool) (out : BoundedConfig (stateCount distance) 3)
    (raw : run (program distance) 2 w H (initial distance left xs target) = some (hf, out))
    (accepts : out.state.val = 0) :
    w = List.replicate distance false ∧ hf = H + (distance : Int) ∧
      out = final distance left xs target :=
  accepting_zipper_word_eq (2 : Fin 3) (program distance) (program_falseOnly distance)
    distance H (initial distance left xs target) (final distance left xs target)
    (H + (distance : Int)) (actual_run distance left xs target hlen hne H)
    (final_accepts distance left xs target) raw accepts

theorem all_cutoff_counts (distance : Nat) (left xs target : List (Fin 3))
    (hlen : xs.length = distance) (hne : target ≠ []) (H : Int) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T
      (liftConfig (program distance) (initial distance left xs target)) =
        if distance ≤ T then 1 else 0 :=
  acceptingPaths_threshold (2 : Fin 3) (by decide) (program distance)
    (program_falseOnly distance) distance H (initial distance left xs target)
    (final distance left xs target) (H + (distance : Int))
    (actual_run distance left xs target hlen hne H) (final_accepts distance left xs target) T

theorem allocated_right_shift_spec (distance : Nat) (left xs target : List (Fin 3))
    (hlen : xs.length = distance) (hne : target ≠ []) (H : Int) :
    (run (program distance) 2 (List.replicate distance false) H
      (initial distance left xs target) =
        some (H + (distance : Int), final distance left xs target)) ∧
    (∀ w hf out, run (program distance) 2 w H (initial distance left xs target) = some (hf, out) →
      w = List.replicate w.length false ∧ w.length ≤ distance ∧
      hf = H + (w.length : Int) ∧ H ≤ hf ∧ hf ≤ H + (distance : Int) ∧
      cellCount out = left.length + distance + target.length ∧
      GrowthRun (program distance) 2 w H (initial distance left xs target) hf out 0 0) ∧
    (∀ w hf out, run (program distance) 2 w H (initial distance left xs target) = some (hf, out) →
      out.state.val = 0 → w = List.replicate distance false ∧
        hf = H + (distance : Int) ∧ out = final distance left xs target) ∧
    (∀ T, ULogSemantics.machine.acceptingPaths T
      (liftConfig (program distance) (initial distance left xs target)) =
        if distance ≤ T then 1 else 0) := by
  refine ⟨actual_run distance left xs target hlen hne H, ?_,
    (fun w hf out => every_accepting_word distance left xs target hlen hne H hf w out),
    all_cutoff_counts distance left xs target hlen hne H⟩
  intro w hf out raw
  have bounds := every_raw distance left xs target hlen hne H hf w out raw
  have growth := every_raw_no_growth distance left xs target hlen hne H hf w out raw
  have cells : cellCount out = left.length + distance + target.length := by
    simpa only [Nat.add_zero, occupied_initial distance left xs target hlen hne] using
      growth.exact_ledger.2.2.1
  exact ⟨bounds.1, bounds.2.1, bounds.2.2.1, bounds.2.2.2.1, bounds.2.2.2.2, cells, growth⟩

end PakFixedPolyomino.ULogFiniteTapeAllocatedRightShift
