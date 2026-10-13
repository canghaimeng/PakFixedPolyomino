import PakFixedPolyomino.ULogSourceObliviousLRWindowExecution

/-! # Unrestricted raw-run inverse of the complete LR window

The unique mark derives every flag update in the forward window module.
Local cell forcedness then composes through its actual intermediate runs.
The compared raw list contains no image or source-choice certificate.
-/

namespace PakFixedPolyomino.ULogSourceObliviousLRWindowInverse

open FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceOneHotReader (tapeOfBit)
open ULogSourceObliviousWindow ULogSourceObliviousScanProgram
open ULogSourceObliviousScanExecution ULogSourceObliviousUpdateExecution
open ULogSourceObliviousRunPrefix ULogSourceObliviousReturnInverse
open ULogSourceObliviousLRCellExecution ULogSourceObliviousLRWindowExecution

variable {ns nt : ℕ}

theorem lr_take_cells_nonbranch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (exterior : Int → Phys) (k : ℕ) (hk : k ≤ w.cells.length) :
    NonbranchPrefix p hnt blank (lrInteriorArrowsTake p hnt blank a w hright k hk)
      (lrStart a w exterior) := by
  induction k with
  | zero => simp [lrInteriorArrowsTake, NonbranchPrefix]
  | succ k ih =>
      have hlt : k < w.cells.length := by omega
      have hle : k ≤ w.cells.length := Nat.le_of_lt hlt
      rw [lrInteriorArrowsTake_succ p hnt blank a w hright k hlt]
      apply nonbranchPrefix_append p hnt blank _ _ _
        (lrMid w a hright exterior k hle) (ih hle)
        (lr_take_cells p hnt blank a w hright exterior k hle)
      let kk : Fin w.cells.length := ⟨k, hlt⟩
      unfold lrCellArrows
      exact cell_nonbranchPrefix p hnt blank a (lrArmed w a k)
        (tapeOfBit (decide (k = w.head.val)))
        (tapeOfBit (decide (k = (lrWindow w a hright).head.val)))
        (lrArmed w a (k + 1)) (tapeOfBit_ne_blank _)
        (updateLR_window_cell w a hright kk) (cellBits w kk)
        (cellBits_length w kk) (cellBits_valid w kk)
        (lrMid w a hright exterior k hle) (by simp [lrMid])
        (lrMid_read_flag w a hright exterior kk)
        (lrMid_read_bits w a hright exterior kk)

theorem lr_window_nonbranch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (exterior : Int → Phys) :
    NonbranchPrefix p hnt blank (lrWindowArrows p hnt blank a w hright)
      (lrStart a w exterior) := by
  rw [lrWindowArrows]
  let middle : ScanCfg ns nt :=
    { state := .updateLRFlag a false
      head := (windowWidth w + 1 : Int)
      tape := windowTape (lrWindow w a hright) exterior }
  apply nonbranchPrefix_append p hnt blank _ _ _ middle
    (lr_take_cells_nonbranch p hnt blank a w hright exterior w.cells.length le_rfl)
    (lr_interior_run p hnt blank a w hright exterior)
  refine ⟨?_, _, updateLRFlagRightBoundaryArrow_step p hnt blank a middle rfl ?_, trivial⟩
  · intro q read
    simp [middle]
  · simpa [middle, lrWindow_windowWidth w a hright] using
      windowTape_right (lrWindow w a hright) exterior

/-- Every successful raw list of the complete pass length has exactly its
literal arrows and the explicit intermediate LogicalWindow endpoint. -/
theorem lr_window_raw_unique (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (exterior : Int → Phys) (raw : List (ScanArrow p hnt blank))
    (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw (lrStart a w exterior) = some out)
    (hlen : raw.length = windowWidth w + 1) :
    raw = lrWindowArrows p hnt blank a w hright ∧
      out = { state := .skipRL a false ⟨nt - 1, by omega⟩
              head := (windowWidth w : Int)
              tape := windowTape (lrWindow w a hright) exterior } := by
  have hforced := nonbranchPrefix_forced p hnt blank _ _
    (lr_window_nonbranch p hnt blank a w hright exterior)
  obtain ⟨heq, hprefix⟩ := forcedPrefix_unique_successful_run (program p hnt blank)
    (fun _ => true) _ raw _ out hforced hrun
    (by rw [lrWindowArrows_length, hlen])
  refine ⟨heq, ?_⟩
  rw [lr_window_run p hnt blank a w hright exterior] at hprefix
  exact (Option.some.inj hprefix).symm

/-- A longer unrestricted raw history has the same whole pass as prefix. -/
theorem lr_window_raw_prefix (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (exterior : Int → Phys) (raw : List (ScanArrow p hnt blank))
    (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw (lrStart a w exterior) = some out)
    (hlen : windowWidth w + 1 ≤ raw.length) :
    ∃ tail, raw = lrWindowArrows p hnt blank a w hright ++ tail ∧
      run (program p hnt blank) (fun _ => true) tail
        { state := .skipRL a false ⟨nt - 1, by omega⟩
          head := (windowWidth w : Int)
          tape := windowTape (lrWindow w a hright) exterior } = some out := by
  obtain ⟨tail, middle, heq, hpre, htail⟩ := nonbranchPrefix_split_successful_run
    p hnt blank _ raw _ out (lr_window_nonbranch p hnt blank a w hright exterior)
    hrun (by simpa [lrWindowArrows_length] using hlen)
  rw [lr_window_run p hnt blank a w hright exterior] at hpre
  have hm := Option.some.inj hpre
  subst middle
  exact ⟨tail, heq, htail⟩

end PakFixedPolyomino.ULogSourceObliviousLRWindowInverse
