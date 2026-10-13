import PakFixedPolyomino.ULogSourceObliviousInitialCells

/-! # The actual initial scan of a complete logical window

Every cell is read, the unique marked cell selects one literal occupied
source slot, and the scan reaches the right delimiter with unchanged tape.
-/

namespace PakFixedPolyomino.ULogSourceObliviousInitialWindowExecution

open FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceOneHotReader (zero one tapeOfBit)
open ULogSourceOneHotBlocks ULogSourceObliviousWindow
open ULogSourceObliviousScanProgram ULogSourceObliviousScanExecution
open ULogSourceObliviousUpdateExecution ULogSourceObliviousInitialCells
open ULogSourceObliviousLRWindowExecution
open ULogSourceOneHotMacroEquiv (SourceChoice)

variable {ns nt : ℕ}

def cellHead (nt k : ℕ) : Int := ((1 + k * (nt + 1) : ℕ) : Int)

theorem cellHead_succ (nt k : ℕ) :
    cellHead nt (k + 1) = cellHead nt k + 1 + (nt : Int) := by
  simp [cellHead, Nat.add_mul, Nat.cast_add, Nat.cast_mul]
  ring

def selectedAt (w : LogicalWindow nt) (a : BoundedAction ns nt) (k : ℕ) :
    Option (BoundedAction ns nt) := if w.head.val < k then some a else none

theorem windowCell_oneHot (w : LogicalWindow nt) (exterior : Int → Phys)
    (k : Fin w.cells.length) :
    ULogSourceLogicalBlockReader.IsOneHotAt (w.cells.get k)
      (windowTape w exterior) (cellHead nt k.val + 1) := by
  intro i hi
  have h := windowTape_cell_bit w exterior k ⟨i, hi⟩
  rw [encodeOneHot_getElem (w.cells.get k) i hi] at h
  have hc : ((1 + k.val * (nt + 1) + 1 + i : ℕ) : Int) =
      cellHead nt k.val + 1 + (i : Int) := by
    simp [cellHead, Nat.cast_add]
  rw [hc] at h
  have hb : tapeOfBit (if i = (w.cells.get k).val then true else false) =
      (if i = (w.cells.get k).val then one else zero) := by
    split_ifs <;> rfl
  exact h.trans hb

def scanCellArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (choice : SourceChoice p q (w.cells.get w.head))
    (exterior : Int → Phys) (k : Fin w.cells.length) : List (ScanArrow p hnt blank) :=
  if k = w.head then
    markedCellArrows p hnt blank (w.cells.get w.head) q choice
      (windowTape w exterior) (cellHead nt k.val)
  else
    unmarkedCellArrows p hnt blank q (selectedAt w choice.action k.val)
      (windowTape w exterior) (cellHead nt k.val)

@[simp] theorem scanCellArrows_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt)
    (choice : SourceChoice p q (w.cells.get w.head)) (exterior : Int → Phys)
    (k : Fin w.cells.length) :
    (scanCellArrows p hnt blank q w choice exterior k).length =
      nt + 1 + if k = w.head then 1 else 0 := by
  unfold scanCellArrows
  split_ifs <;> simp

theorem scanCell_run (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (choice : SourceChoice p q (w.cells.get w.head))
    (exterior : Int → Phys) (k : Fin w.cells.length) :
    run (program p hnt blank) (fun _ => true) (scanCellArrows p hnt blank q w choice exterior k)
      { state := .flag q (selectedAt w choice.action k.val)
        head := cellHead nt k.val, tape := windowTape w exterior } =
      some { state := .flag q (selectedAt w choice.action (k.val + 1))
             head := cellHead nt (k.val + 1), tape := windowTape w exterior } := by
  by_cases hk : k = w.head
  · subst k
    have hf : windowTape w exterior (cellHead nt w.head.val) = one := by
      simpa [cellHead, tapeOfBit] using windowTape_cell_flag w exterior w.head
    have hrun := markedCell_run p hnt blank (w.cells.get w.head) q choice
      (windowTape w exterior) (cellHead nt w.head.val) hf (windowCell_oneHot w exterior w.head)
    simpa [scanCellArrows, selectedAt, cellHead_succ] using hrun
  · have hv : k.val ≠ w.head.val := fun h => hk (Fin.ext h)
    have hf : windowTape w exterior (cellHead nt k.val) = zero := by
      simpa [cellHead, hv, tapeOfBit] using windowTape_cell_flag w exterior k
    have hs : selectedAt w choice.action (k.val + 1) = selectedAt w choice.action k.val := by
      unfold selectedAt
      by_cases hlt : w.head.val < k.val
      · simp [hlt, show w.head.val < k.val + 1 by omega]
      · simp [hlt, show ¬w.head.val < k.val + 1 by omega]
    have hrun := unmarkedCell_run p hnt blank (w.cells.get k) q
      (selectedAt w choice.action k.val) (windowTape w exterior) (cellHead nt k.val)
      hf (windowCell_oneHot w exterior k)
    simpa [scanCellArrows, hk, hs, cellHead_succ] using hrun

def scanInteriorArrowsTake (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (choice : SourceChoice p q (w.cells.get w.head))
    (exterior : Int → Phys) (r : ℕ) (hr : r ≤ w.cells.length) :
    List (ScanArrow p hnt blank) :=
  (List.ofFn fun k : Fin r =>
    scanCellArrows p hnt blank q w choice exterior ⟨k.val, by omega⟩).flatten

theorem scanInteriorArrowsTake_succ (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt)
    (choice : SourceChoice p q (w.cells.get w.head)) (exterior : Int → Phys)
    (r : ℕ) (hr : r < w.cells.length) :
    scanInteriorArrowsTake p hnt blank q w choice exterior (r + 1) (Nat.succ_le_of_lt hr) =
      scanInteriorArrowsTake p hnt blank q w choice exterior r (Nat.le_of_lt hr) ++
        scanCellArrows p hnt blank q w choice exterior ⟨r, hr⟩ := by
  unfold scanInteriorArrowsTake
  rw [ofFn_snoc]
  simp [List.flatten_append]

theorem scanInteriorArrowsTake_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt)
    (choice : SourceChoice p q (w.cells.get w.head)) (exterior : Int → Phys)
    (r : ℕ) (hr : r ≤ w.cells.length) :
    (scanInteriorArrowsTake p hnt blank q w choice exterior r hr).length =
      r * (nt + 1) + if w.head.val < r then 1 else 0 := by
  induction r with
  | zero => simp [scanInteriorArrowsTake]
  | succ r ih =>
      have hlt : r < w.cells.length := by omega
      rw [scanInteriorArrowsTake_succ p hnt blank q w choice exterior r hlt,
        List.length_append, ih (Nat.le_of_lt hlt), scanCellArrows_length]
      simp only [Fin.ext_iff, Nat.succ_mul]
      split_ifs <;> omega

def scanMid (q : Fin ns) (w : LogicalWindow nt) (a : BoundedAction ns nt)
    (exterior : Int → Phys) (r : ℕ) : ScanCfg ns nt :=
  { state := .flag q (selectedAt w a r)
    head := cellHead nt r
    tape := windowTape w exterior }

theorem scan_take_cells (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (choice : SourceChoice p q (w.cells.get w.head))
    (exterior : Int → Phys) (r : ℕ) (hr : r ≤ w.cells.length) :
    run (program p hnt blank) (fun _ => true)
      (scanInteriorArrowsTake p hnt blank q w choice exterior r hr)
      (scanMid q w choice.action exterior 0) = some (scanMid q w choice.action exterior r) := by
  induction r with
  | zero => simp [scanInteriorArrowsTake]
  | succ r ih =>
      have hlt : r < w.cells.length := by omega
      rw [scanInteriorArrowsTake_succ p hnt blank q w choice exterior r hlt,
        run_append p hnt blank, ih (Nat.le_of_lt hlt), Option.bind_some]
      simpa [scanMid] using scanCell_run p hnt blank q w choice exterior ⟨r, hlt⟩

def scanInteriorArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (choice : SourceChoice p q (w.cells.get w.head))
    (exterior : Int → Phys) : List (ScanArrow p hnt blank) :=
  scanInteriorArrowsTake p hnt blank q w choice exterior w.cells.length le_rfl

@[simp] theorem scanInteriorArrows_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt)
    (choice : SourceChoice p q (w.cells.get w.head)) (exterior : Int → Phys) :
    (scanInteriorArrows p hnt blank q w choice exterior).length = windowWidth w + 1 := by
  rw [scanInteriorArrows, scanInteriorArrowsTake_length]
  simp [w.head.isLt, windowWidth_eq]

theorem scan_interior_run (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (choice : SourceChoice p q (w.cells.get w.head))
    (exterior : Int → Phys) :
    run (program p hnt blank) (fun _ => true) (scanInteriorArrows p hnt blank q w choice exterior)
      { state := .flag q none, head := 1, tape := windowTape w exterior } =
      some (startConfig q choice.action w exterior) := by
  simpa [scanInteriorArrows, scanMid, selectedAt, w.head.isLt, cellHead,
    startConfig, windowWidth_eq, Nat.cast_add, add_comm] using
    scan_take_cells p hnt blank q w choice exterior w.cells.length le_rfl

def startScanArrow (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt) (q : Fin ns) :
    ScanArrow p hnt blank :=
  deterministicArrow p hnt blank (.atLeft q) physBlank
    ⟨physBlank, .flag q none, .right⟩ (by simp [deterministicAction])

def initialWindowConfig (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys) :
    ScanCfg ns nt := { state := .atLeft q, head := 0, tape := windowTape w exterior }

theorem startScanArrow_step (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys) :
    FiniteOneTapeSemantics.step (program p hnt blank) (fun _ => true)
      (initialWindowConfig q w exterior) (startScanArrow p hnt blank q) =
      some { state := .flag q none, head := 1, tape := windowTape w exterior } := by
  have hact : deterministicAction p hnt blank (.atLeft q) physBlank =
      some ⟨physBlank, .flag q none, .right⟩ := by simp [deterministicAction]
  have hrun := deterministicArrow_step p hnt blank (initialWindowConfig q w exterior)
    (.atLeft q) physBlank ⟨physBlank, .flag q none, .right⟩ rfl
    (windowTape_left w exterior) hact
  have ht : writtenTape (initialWindowConfig q w exterior) physBlank = windowTape w exterior := by
    change Function.update (windowTape w exterior) 0 physBlank = windowTape w exterior
    rw [← windowTape_left w exterior, Function.update_eq_self]
  rw [ht] at hrun
  simpa only [startScanArrow, initialWindowConfig, moveHead, zero_add] using hrun

def initialScanArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (choice : SourceChoice p q (w.cells.get w.head))
    (exterior : Int → Phys) : List (ScanArrow p hnt blank) :=
  startScanArrow p hnt blank q :: scanInteriorArrows p hnt blank q w choice exterior

@[simp] theorem initialScanArrows_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt)
    (choice : SourceChoice p q (w.cells.get w.head)) (exterior : Int → Phys) :
    (initialScanArrows p hnt blank q w choice exterior).length = windowWidth w + 2 := by
  simp [initialScanArrows]

theorem initial_scan_run (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (choice : SourceChoice p q (w.cells.get w.head))
    (exterior : Int → Phys) :
    run (program p hnt blank) (fun _ => true) (initialScanArrows p hnt blank q w choice exterior)
      (initialWindowConfig q w exterior) = some (startConfig q choice.action w exterior) := by
  rw [initialScanArrows, run_cons, startScanArrow_step, Option.bind_some, scan_interior_run]

end PakFixedPolyomino.ULogSourceObliviousInitialWindowExecution
