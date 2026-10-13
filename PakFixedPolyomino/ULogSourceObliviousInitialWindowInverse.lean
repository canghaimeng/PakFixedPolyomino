import PakFixedPolyomino.ULogSourceObliviousInitialWindowExecution

/-! # Recovering the unique source slot from every raw initial scan

The prefix before the marked cell's branch is independent of any future
source choice. Both deterministic parts execute on the actual window tape.
-/

namespace PakFixedPolyomino.ULogSourceObliviousInitialWindowInverse

open FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceOneHotReader (zero one tapeOfBit)
open ULogSourceObliviousWindow ULogSourceObliviousScanProgram
open ULogSourceObliviousScanExecution ULogSourceObliviousUpdateExecution
open ULogSourceObliviousInitialCells ULogSourceObliviousInitialWindowExecution
open ULogSourceObliviousLRWindowExecution
open ULogSourceObliviousRunPrefix ULogSourceObliviousScanInverse
open ULogSourceObliviousReturnInverse (nonbranchPrefix_append)
open ULogSourceOneHotMacroEquiv (SourceChoice)

variable {ns nt : ℕ}

def unmarkedRangeArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (w : LogicalWindow nt) (exterior : Int → Phys) (start : ℕ) :
    ℕ → List (ScanArrow p hnt blank)
  | 0 => []
  | count + 1 => unmarkedRangeArrows p hnt blank q selected w exterior start count ++
      unmarkedCellArrows p hnt blank q selected (windowTape w exterior)
        (cellHead nt (start + count))

def rangeConfig (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (w : LogicalWindow nt) (exterior : Int → Phys) (k : ℕ) : ScanCfg ns nt :=
  { state := .flag q selected, head := cellHead nt k, tape := windowTape w exterior }

@[simp] theorem unmarkedRangeArrows_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (w : LogicalWindow nt) (exterior : Int → Phys) (start count : ℕ) :
    (unmarkedRangeArrows p hnt blank q selected w exterior start count).length =
      count * (nt + 1) := by
  induction count with
  | zero => simp [unmarkedRangeArrows]
  | succ count ih => simp [unmarkedRangeArrows, ih, Nat.add_mul]

theorem unmarkedRange_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (w : LogicalWindow nt) (exterior : Int → Phys) (start count : ℕ)
    (hbound : start + count ≤ w.cells.length)
    (hnone : ∀ j, j < count → start + j ≠ w.head.val) :
    run (program p hnt blank) (fun _ => true)
      (unmarkedRangeArrows p hnt blank q selected w exterior start count)
      (rangeConfig q selected w exterior start) =
      some (rangeConfig q selected w exterior (start + count)) := by
  induction count with
  | zero => simp [unmarkedRangeArrows]
  | succ count ih =>
      have hlt : start + count < w.cells.length := by omega
      have hneq := hnone count (by omega)
      have hf : windowTape w exterior (cellHead nt (start + count)) = zero := by
        simpa [cellHead, hneq, tapeOfBit] using
          windowTape_cell_flag w exterior ⟨start + count, hlt⟩
      rw [unmarkedRangeArrows, run_append p hnt blank,
        ih (by omega) (fun j hj => hnone j (by omega)), Option.bind_some]
      have hc : cellHead nt (start + (count + 1)) = cellHead nt (start + count) + 1 + nt := by
        rw [← Nat.add_assoc, cellHead_succ]
      simpa only [rangeConfig, hc] using
        unmarkedCell_run p hnt blank (w.cells.get ⟨start + count, hlt⟩) q selected
          (windowTape w exterior) (cellHead nt (start + count)) hf
          (windowCell_oneHot w exterior ⟨start + count, hlt⟩)

theorem unmarkedRange_nonbranch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (selected : Option (BoundedAction ns nt))
    (w : LogicalWindow nt) (exterior : Int → Phys) (start count : ℕ)
    (hbound : start + count ≤ w.cells.length)
    (hnone : ∀ j, j < count → start + j ≠ w.head.val) :
    NonbranchPrefix p hnt blank
      (unmarkedRangeArrows p hnt blank q selected w exterior start count)
      (rangeConfig q selected w exterior start) := by
  induction count with
  | zero => trivial
  | succ count ih =>
      have hb : start + count ≤ w.cells.length := by omega
      have hn : ∀ j, j < count → start + j ≠ w.head.val :=
        fun j hj => hnone j (by omega)
      have hlt : start + count < w.cells.length := by omega
      have hneq := hnone count (by omega)
      have hf : windowTape w exterior (cellHead nt (start + count)) = zero := by
        simpa [cellHead, hneq, tapeOfBit] using
          windowTape_cell_flag w exterior ⟨start + count, hlt⟩
      exact nonbranchPrefix_append p hnt blank _ _ _ _ (ih hb hn)
        (unmarkedRange_run p hnt blank q selected w exterior start count hb hn)
        (unmarkedCell_nonbranch p hnt blank (w.cells.get ⟨start + count, hlt⟩)
          q selected (windowTape w exterior) (cellHead nt (start + count)) hf
          (windowCell_oneHot w exterior ⟨start + count, hlt⟩))

def preBranchArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys) :
    List (ScanArrow p hnt blank) :=
  startScanArrow p hnt blank q ::
    (unmarkedRangeArrows p hnt blank q none w exterior 0 w.head.val ++
      markedCellPreArrows p hnt blank q (windowTape w exterior) (cellHead nt w.head.val))

def preBranchConfig (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys) :
    ScanCfg ns nt :=
  { state := .branch q (w.cells.get w.head)
    head := cellHead nt (w.head.val + 1), tape := windowTape w exterior }

@[simp] theorem preBranchArrows_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys) :
    (preBranchArrows p hnt blank q w exterior).length =
      (w.head.val + 1) * (nt + 1) + 1 := by
  simp [preBranchArrows, Nat.add_mul]

theorem preBranch_run (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys) :
    run (program p hnt blank) (fun _ => true) (preBranchArrows p hnt blank q w exterior)
      (initialWindowConfig q w exterior) = some (preBranchConfig q w exterior) := by
  have hb : 0 + w.head.val ≤ w.cells.length := by omega
  have hn : ∀ j, j < w.head.val → 0 + j ≠ w.head.val := by omega
  have hf : windowTape w exterior (cellHead nt w.head.val) = one := by
    simpa [cellHead, tapeOfBit] using windowTape_cell_flag w exterior w.head
  rw [preBranchArrows, run_cons, startScanArrow_step, Option.bind_some,
    run_append p hnt blank]
  have hzero : rangeConfig q none w exterior 0 =
      { state := .flag q none, head := 1, tape := windowTape w exterior } := by
    simp [rangeConfig, cellHead]
  rw [← hzero]
  rw [unmarkedRange_run p hnt blank q none w exterior 0 w.head.val hb hn, Option.bind_some]
  simpa [rangeConfig, preBranchConfig, cellHead_succ] using
    markedCellPre_run p hnt blank (w.cells.get w.head) q (windowTape w exterior)
      (cellHead nt w.head.val) hf (windowCell_oneHot w exterior w.head)

theorem preBranch_nonbranch (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys) :
    NonbranchPrefix p hnt blank (preBranchArrows p hnt blank q w exterior)
      (initialWindowConfig q w exterior) := by
  have hb : 0 + w.head.val ≤ w.cells.length := by omega
  have hn : ∀ j, j < w.head.val → 0 + j ≠ w.head.val := by omega
  have hf : windowTape w exterior (cellHead nt w.head.val) = one := by
    simpa [cellHead, tapeOfBit] using windowTape_cell_flag w exterior w.head
  have hm := markedCellPre_nonbranch p hnt blank (w.cells.get w.head) q
    (windowTape w exterior) (cellHead nt w.head.val) hf
    (windowCell_oneHot w exterior w.head)
  refine ⟨?_, rangeConfig q none w exterior 0, ?_, ?_⟩
  · intro q' read; simp [initialWindowConfig]
  · simpa [rangeConfig, cellHead] using startScanArrow_step p hnt blank q w exterior
  · exact nonbranchPrefix_append p hnt blank _ _ _ _
      (unmarkedRange_nonbranch p hnt blank q none w exterior 0 w.head.val hb hn)
      (unmarkedRange_run p hnt blank q none w exterior 0 w.head.val hb hn)
      (by simpa [rangeConfig] using hm)

def postBranchArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (a : BoundedAction ns nt) (w : LogicalWindow nt) (exterior : Int → Phys) :
    List (ScanArrow p hnt blank) :=
  unmarkedRangeArrows p hnt blank q (some a) w exterior (w.head.val + 1)
    (w.cells.length - w.head.val - 1)

def postBranchConfig (q : Fin ns) (a : BoundedAction ns nt)
    (w : LogicalWindow nt) (exterior : Int → Phys) : ScanCfg ns nt :=
  rangeConfig q (some a) w exterior (w.head.val + 1)

@[simp] theorem postBranchArrows_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt)
    (w : LogicalWindow nt) (exterior : Int → Phys) :
    (postBranchArrows p hnt blank q a w exterior).length =
      (w.cells.length - w.head.val - 1) * (nt + 1) := by
  simp [postBranchArrows]

theorem postBranch_run (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (a : BoundedAction ns nt) (w : LogicalWindow nt) (exterior : Int → Phys) :
    run (program p hnt blank) (fun _ => true) (postBranchArrows p hnt blank q a w exterior)
      (postBranchConfig q a w exterior) = some (startConfig q a w exterior) := by
  have he : w.head.val + 1 + (w.cells.length - w.head.val - 1) = w.cells.length := by
    have := w.head.isLt; omega
  have hn : ∀ j, j < w.cells.length - w.head.val - 1 →
      w.head.val + 1 + j ≠ w.head.val := by omega
  have hr := unmarkedRange_run p hnt blank q (some a) w exterior (w.head.val + 1)
    (w.cells.length - w.head.val - 1) (by omega) hn
  rw [he] at hr
  simpa [postBranchArrows, postBranchConfig, rangeConfig, startConfig, cellHead,
    windowWidth_eq, Nat.cast_add, add_comm] using hr

theorem postBranch_nonbranch (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (a : BoundedAction ns nt) (w : LogicalWindow nt) (exterior : Int → Phys) :
    NonbranchPrefix p hnt blank (postBranchArrows p hnt blank q a w exterior)
      (postBranchConfig q a w exterior) := by
  apply unmarkedRange_nonbranch
  · have := w.head.isLt; omega
  · omega

def sourceScanArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (choice : SourceChoice p q (w.cells.get w.head))
    (exterior : Int → Phys) : List (ScanArrow p hnt blank) :=
  preBranchArrows p hnt blank q w exterior ++
    branchArrow p hnt blank q (w.cells.get w.head)
      (windowTape w exterior (cellHead nt (w.head.val + 1)))
      choice.slot choice.action choice.occupied ::
        postBranchArrows p hnt blank q choice.action w exterior

theorem scan_length_partition (w : LogicalWindow nt) :
    ((w.head.val + 1) * (nt + 1) + 1) + 1 +
        (w.cells.length - w.head.val - 1) * (nt + 1) = windowWidth w + 2 := by
  have he : w.head.val + 1 + (w.cells.length - w.head.val - 1) = w.cells.length := by
    have := w.head.isLt; omega
  calc
    _ = (w.head.val + 1 + (w.cells.length - w.head.val - 1)) * (nt + 1) + 2 := by ring
    _ = windowWidth w + 2 := by rw [he, windowWidth_eq]

@[simp] theorem sourceScanArrows_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt)
    (choice : SourceChoice p q (w.cells.get w.head)) (exterior : Int → Phys) :
    (sourceScanArrows p hnt blank q w choice exterior).length = windowWidth w + 2 := by
  simp only [sourceScanArrows, List.length_append, List.length_cons,
    preBranchArrows_length, postBranchArrows_length]
  have := scan_length_partition w
  omega

theorem sourceScan_run (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (choice : SourceChoice p q (w.cells.get w.head))
    (exterior : Int → Phys) :
    run (program p hnt blank) (fun _ => true) (sourceScanArrows p hnt blank q w choice exterior)
      (initialWindowConfig q w exterior) = some (startConfig q choice.action w exterior) := by
  have hb := branchArrow_step p hnt blank q (w.cells.get w.head)
    (preBranchConfig q w exterior) choice rfl
  change FiniteOneTapeSemantics.step (program p hnt blank) (fun _ => true)
    (preBranchConfig q w exterior)
    (branchArrow p hnt blank q (w.cells.get w.head)
      (windowTape w exterior (cellHead nt (w.head.val + 1)))
      choice.slot choice.action choice.occupied) =
      some (postBranchConfig q choice.action w exterior) at hb
  rw [sourceScanArrows, run_append p hnt blank, preBranch_run, Option.bind_some, run_cons,
    hb, Option.bind_some]
  exact postBranch_run p hnt blank q choice.action w exterior

/-- Any sufficiently long successful raw run contains this exact initial
scan. The occupied source slot is recovered from the actual branch arrow. -/
theorem raw_scan_prefix (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw
      (initialWindowConfig q w exterior) = some out)
    (hlength : windowWidth w + 2 ≤ raw.length) :
    ∃ (choice : SourceChoice p q (w.cells.get w.head)) (tail : List (ScanArrow p hnt blank)),
      raw = sourceScanArrows p hnt blank q w choice exterior ++ tail ∧
      run (program p hnt blank) (fun _ => true) tail
        (startConfig q choice.action w exterior) = some out := by
  have hpart := scan_length_partition w
  have hpre : (preBranchArrows p hnt blank q w exterior).length < raw.length := by
    rw [preBranchArrows_length]; omega
  obtain ⟨tail, boundary, heq, hboundary, htail⟩ := nonbranchPrefix_split_successful_run
    p hnt blank (preBranchArrows p hnt blank q w exterior) raw
      (initialWindowConfig q w exterior) out (preBranch_nonbranch p hnt blank q w exterior)
      hrun (by omega)
  have hc : boundary = preBranchConfig q w exterior :=
    Option.some.inj (hboundary.symm.trans (preBranch_run p hnt blank q w exterior))
  subst boundary
  cases tail with
  | nil =>
      have he := congrArg List.length heq
      simp only [List.length_append, List.length_nil, Nat.add_zero] at he
      omega
  | cons b rest =>
      cases hs : FiniteOneTapeSemantics.step (program p hnt blank) (fun _ => true)
        (preBranchConfig q w exterior) b with
      | none => simp [run, hs] at htail
      | some d =>
          have hrest : run (program p hnt blank) (fun _ => true) rest d = some out := by
            simpa only [run_cons, hs, Option.bind_some] using htail
          obtain ⟨choice, hb, hd⟩ := branch_success_inverse p hnt blank q
            (w.cells.get w.head) (windowTape w exterior) (cellHead nt (w.head.val + 1)) b d hs
          change d = postBranchConfig q choice.action w exterior at hd
          rw [hd] at hrest
          have hpost : (postBranchArrows p hnt blank q choice.action w exterior).length ≤
              rest.length := by
            have he := congrArg List.length heq
            simp only [List.length_append, List.length_cons, preBranchArrows_length] at he
            rw [postBranchArrows_length]
            omega
          obtain ⟨finalTail, finalBoundary, heRest, hfinal, hfinalTail⟩ :=
            nonbranchPrefix_split_successful_run p hnt blank
              (postBranchArrows p hnt blank q choice.action w exterior) rest
              (postBranchConfig q choice.action w exterior) out
              (postBranch_nonbranch p hnt blank q choice.action w exterior) hrest hpost
          have hf : finalBoundary = startConfig q choice.action w exterior :=
            Option.some.inj (hfinal.symm.trans (postBranch_run p hnt blank q choice.action w exterior))
          subst finalBoundary
          refine ⟨choice, finalTail, ?_, hfinalTail⟩
          rw [heq, hb, heRest]
          simp [sourceScanArrows, List.append_assoc, List.cons_append]

/-- This converse quantifies over all raw words of the physical scan length. -/
theorem raw_scan_unique (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw
      (initialWindowConfig q w exterior) = some out)
    (hlength : raw.length = windowWidth w + 2) :
    ∃ choice : SourceChoice p q (w.cells.get w.head),
      raw = sourceScanArrows p hnt blank q w choice exterior ∧
      out = startConfig q choice.action w exterior := by
  obtain ⟨choice, tail, heq, htail⟩ := raw_scan_prefix p hnt blank q w exterior raw out hrun
    (by omega)
  have ht : tail = [] := by
    apply List.length_eq_zero_iff.mp
    have he := congrArg List.length heq
    simp only [List.length_append, sourceScanArrows_length] at he
    omega
  subst tail
  refine ⟨choice, by simpa using heq, ?_⟩
  exact (Option.some.inj htail).symm

theorem sourceScanArrows_injective (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys) :
    Function.Injective (fun choice : SourceChoice p q (w.cells.get w.head) =>
      sourceScanArrows p hnt blank q w choice exterior) := by
  intro a b h
  unfold sourceScanArrows at h
  have hc := List.append_cancel_left h
  have hh := (List.cons.inj hc).1
  apply SourceChoice.ext
  exact congrArg (fun arrow : ScanArrow p hnt blank => arrow.val.2) hh

/-- No source choice or forward-image condition occurs in this raw domain. -/
def RawInitialScan (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys) :=
  {raw : List (ScanArrow p hnt blank) // raw.length = windowWidth w + 2 ∧
    ∃ out, run (program p hnt blank) (fun _ => true) raw
      (initialWindowConfig q w exterior) = some out}

noncomputable def recoverInitialScan (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys)
    (raw : RawInitialScan p hnt blank q w exterior) : SourceChoice p q (w.cells.get w.head) :=
  Classical.choose (raw_scan_unique p hnt blank q w exterior raw.val
    (Classical.choose raw.property.2) (Classical.choose_spec raw.property.2) raw.property.1)

theorem recoverInitialScan_correct (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys)
    (raw : RawInitialScan p hnt blank q w exterior) :
    raw.val = sourceScanArrows p hnt blank q w
      (recoverInitialScan p hnt blank q w exterior raw) exterior :=
  (Classical.choose_spec (raw_scan_unique p hnt blank q w exterior raw.val
    (Classical.choose raw.property.2) (Classical.choose_spec raw.property.2) raw.property.1)).1

noncomputable def initialScanEquiv (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys) :
    SourceChoice p q (w.cells.get w.head) ≃ RawInitialScan p hnt blank q w exterior where
  toFun choice := ⟨sourceScanArrows p hnt blank q w choice exterior,
    sourceScanArrows_length p hnt blank q w choice exterior,
    startConfig q choice.action w exterior, sourceScan_run p hnt blank q w choice exterior⟩
  invFun := recoverInitialScan p hnt blank q w exterior
  left_inv choice := by
    apply sourceScanArrows_injective p hnt blank q w exterior
    exact (recoverInitialScan_correct p hnt blank q w exterior
      ⟨sourceScanArrows p hnt blank q w choice exterior,
        sourceScanArrows_length p hnt blank q w choice exterior,
        startConfig q choice.action w exterior, sourceScan_run p hnt blank q w choice exterior⟩).symm
  right_inv raw := by
    apply Subtype.ext
    exact (recoverInitialScan_correct p hnt blank q w exterior raw).symm

end PakFixedPolyomino.ULogSourceObliviousInitialWindowInverse
