import PakFixedPolyomino.ULogSourceObliviousRLWindowExecution

/-! # Unrestricted raw-run inverse of the complete reverse window

Each reverse cell is nonbranching on the actual derived intermediate tape.
The compared history is an arbitrary successful raw arrow list.
-/

namespace PakFixedPolyomino.ULogSourceObliviousRLWindowInverse

open FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceOneHotReader (tapeOfBit)
open ULogSourceObliviousWindow ULogSourceObliviousScanProgram
open ULogSourceObliviousScanExecution ULogSourceObliviousUpdateExecution
open ULogSourceObliviousRunPrefix ULogSourceObliviousReturnInverse
open ULogSourceObliviousRLCellExecution ULogSourceObliviousRLWindowExecution
open ULogSourceObliviousLRWindowExecution

variable {ns nt : ℕ}

theorem rl_take_cells_nonbranch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (exterior : Int → Phys) (r : ℕ) (hr : r ≤ u.cells.length) :
    NonbranchPrefix p hnt blank (rlInteriorArrowsTake p hnt blank a u hleft r hr)
      (rlStart hnt a u exterior) := by
  induction r with
  | zero => simp [rlInteriorArrowsTake, NonbranchPrefix]
  | succ r ih =>
      have hlt : r < u.cells.length := by omega
      have hle : r ≤ u.cells.length := Nat.le_of_lt hlt
      rw [rlInteriorArrowsTake_succ p hnt blank a u hleft r hlt]
      apply nonbranchPrefix_append p hnt blank _ _ _
        (rlMid hnt u a hleft exterior r hle) (ih hle)
        (rl_take_cells p hnt blank a u hleft exterior r hle)
      let k : Fin u.cells.length := ⟨u.cells.length - 1 - r, by omega⟩
      unfold rlCellArrows
      exact cell_nonbranchPrefix p hnt blank a (rlArmed u a k.val)
        (tapeOfBit (decide (k.val = u.head.val)))
        (tapeOfBit (decide (k.val = (rlWindow u a hleft).head.val)))
        (decide (a.move = .left ∧ k.val = u.head.val))
        (updateRL_window_cell u a hleft k) (cellBits u k)
        (cellBits_length u k) (cellBits_valid u k) (cellBits_ne_blank u k)
        (rlMid hnt u a hleft exterior r hle)
        (by simp [rlMid, k, rlCarry_eq_rlArmed u a r hlt])
        ((2 + k.val * (nt + 1) : ℕ) : Int)
        (by
          simp only [rlMid]
          have hidx : u.cells.length - r = k.val + 1 := by
            change u.cells.length - r = u.cells.length - 1 - r + 1
            omega
          rw [hidx]
          exact (rl_base_head nt k.val).symm)
        (by intro i; simpa [k] using rlMid_read_bits hnt u a hleft exterior r hlt i)
        (by
          have hf := rlMid_read_flag hnt u a hleft exterior r hlt
          have hc := (rl_base_flag nt k.val).symm
          simpa [k, hc] using hf)

theorem rl_window_nonbranch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val) (exterior : Int → Phys) :
    NonbranchPrefix p hnt blank (rlWindowArrows p hnt blank a u hleft)
      (rlStart hnt a u exterior) := by
  rw [rlWindowArrows]
  let middle : ScanCfg ns nt :=
    { state := .skipRL a false ⟨nt - 1, by omega⟩
      head := 0
      tape := windowTape (rlWindow u a hleft) exterior }
  apply nonbranchPrefix_append p hnt blank _ _ _ middle
    (rl_take_cells_nonbranch p hnt blank a u hleft exterior u.cells.length le_rfl)
    (rl_interior_run p hnt blank a u hleft exterior)
  refine ⟨?_, _, skipRLLeftBoundaryArrow_step p hnt blank a middle rfl ?_, trivial⟩
  · intro q read
    simp [middle]
  · exact windowTape_left (rlWindow u a hleft) exterior

theorem rl_window_raw_unique (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val) (exterior : Int → Phys)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw (rlStart hnt a u exterior) = some out)
    (hlen : raw.length = windowWidth u + 1) :
    raw = rlWindowArrows p hnt blank a u hleft ∧
      out = { state := .atLeft a.target, head := 0
              tape := windowTape (rlWindow u a hleft) exterior } := by
  have hforced := nonbranchPrefix_forced p hnt blank _ _
    (rl_window_nonbranch p hnt blank a u hleft exterior)
  obtain ⟨heq, hprefix⟩ := forcedPrefix_unique_successful_run (program p hnt blank)
    (fun _ => true) _ raw _ out hforced hrun
    (by rw [rlWindowArrows_length, hlen])
  refine ⟨heq, ?_⟩
  rw [rl_window_run p hnt blank a u hleft exterior] at hprefix
  exact (Option.some.inj hprefix).symm

theorem rl_window_raw_prefix (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val) (exterior : Int → Phys)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw (rlStart hnt a u exterior) = some out)
    (hlen : windowWidth u + 1 ≤ raw.length) :
    ∃ tail, raw = rlWindowArrows p hnt blank a u hleft ++ tail ∧
      run (program p hnt blank) (fun _ => true) tail
        { state := .atLeft a.target, head := 0
          tape := windowTape (rlWindow u a hleft) exterior } = some out := by
  obtain ⟨tail, middle, heq, hpre, htail⟩ := nonbranchPrefix_split_successful_run
    p hnt blank _ raw _ out (rl_window_nonbranch p hnt blank a u hleft exterior)
    hrun (by simpa [rlWindowArrows_length] using hlen)
  rw [rl_window_run p hnt blank a u hleft exterior] at hpre
  have hm := Option.some.inj hpre
  subst middle
  exact ⟨tail, heq, htail⟩

end PakFixedPolyomino.ULogSourceObliviousRLWindowInverse
