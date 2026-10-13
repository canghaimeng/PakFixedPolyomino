import PakFixedPolyomino.FiniteOneTapeShortPrefix
import PakFixedPolyomino.ULogSourceObliviousCompletedCyclePrefix

/-! Every source in an actual deterministic scanner phase is outside atLeft.
This is a literal-arrow property of the operational plans, not a condition
on the arbitrary raw run compared with them. -/

namespace PakFixedPolyomino.ULogSourceObliviousPhaseSources

open FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceObliviousScanProgram ULogSourceObliviousWindow
open ULogSourceObliviousUpdateExecution ULogSourceObliviousScanExecution
open ULogSourceObliviousInitialCells ULogSourceObliviousInitialWindowInverse
open ULogSourceObliviousInitialWindowExecution ULogSourceObliviousCycleExecution
open ULogSourceObliviousSafeSuffix ULogSourceObliviousRunPrefix
open ULogSourceObliviousLRWindowExecution ULogSourceObliviousRLWindowExecution
open ULogSourceObliviousOverflowExecution

variable {ns nt : ℕ}

def NotAtLeft (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : ScanArrow p hnt blank) : Prop := ∀ q, a.1.1.1 ≠ State.atLeft q

theorem readArrows_sources (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (selected : Option (BoundedAction ns nt)) (isHead : Bool)
    (c : ReaderConfig (nt := nt)) (k : ℕ) :
    ∀ a ∈ readArrows p hnt blank q selected isHead c k,
      NotAtLeft p hnt blank a := by
  induction k generalizing c with
  | zero => simp [readArrows]
  | succ k ih =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [NotAtLeft, readLiteralArrow]
      · exact ih _ a ha

theorem unmarkedCell_sources (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (selected : Option (BoundedAction ns nt)) (tape : Int → Phys) (head : Int) :
    ∀ a ∈ unmarkedCellArrows p hnt blank q selected tape head,
      NotAtLeft p hnt blank a := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · simp [NotAtLeft, flagZeroArrow, deterministicArrow]
  · exact readArrows_sources p hnt blank q selected false _ nt a ha

theorem markedCellPre_sources (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (tape : Int → Phys) (head : Int) :
    ∀ a ∈ markedCellPreArrows p hnt blank q tape head,
      NotAtLeft p hnt blank a := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · simp [NotAtLeft, flagHeadArrow]
  · exact readArrows_sources p hnt blank q none true _ nt a ha

theorem unmarkedRange_sources (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (selected : Option (BoundedAction ns nt)) (w : LogicalWindow nt)
    (exterior : Int → Phys) (start count : ℕ) :
    ∀ a ∈ unmarkedRangeArrows p hnt blank q selected w exterior start count,
      NotAtLeft p hnt blank a := by
  induction count with
  | zero => simp [unmarkedRangeArrows]
  | succ count ih =>
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact ih a ha
      · exact unmarkedCell_sources p hnt blank q selected _ _ a ha

theorem returnLeft_sources (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (action : BoundedAction ns nt) (w : LogicalWindow nt) :
    ∀ a ∈ returnLeftArrows p hnt blank q action w,
      NotAtLeft p hnt blank a := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · simp [NotAtLeft, postScanBoundaryArrow, deterministicArrow]
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
      simp [NotAtLeft, returnLeftInteriorArrow, deterministicArrow]
    · have heq := List.mem_singleton.mp ha
      subst a
      simp [NotAtLeft, returnLeftBoundaryArrow, deterministicArrow]

theorem lrCell_sources (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (action : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : action.move = .right → w.head.val + 1 < w.cells.length)
    (k : Fin w.cells.length) :
    ∀ a ∈ lrCellArrows p hnt blank action w hright k,
      NotAtLeft p hnt blank a := by
  intro a ha
  unfold lrCellArrows ULogSourceObliviousLRCellExecution.cellArrows at ha
  rcases List.mem_cons.mp ha with rfl | ha
  · simp [NotAtLeft, updateLRFlagInteriorArrow, deterministicArrow]
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    simp only [NotAtLeft, skipLRArrow]
    split <;> simp [deterministicArrow]

theorem lrWindow_sources (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (action : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : action.move = .right → w.head.val + 1 < w.cells.length) :
    ∀ a ∈ lrWindowArrows p hnt blank action w hright,
      NotAtLeft p hnt blank a := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨xs, hxs, ha⟩ := List.mem_flatten.mp ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hxs
    exact lrCell_sources p hnt blank action w hright _ a ha
  · have heq := List.mem_singleton.mp ha
    subst a
    simp [NotAtLeft, updateLRFlagRightBoundaryArrow, deterministicArrow]

theorem rlCell_sources (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (action : BoundedAction ns nt) (w : LogicalWindow nt)
    (hleft : action.move = .left → 0 < w.head.val) (k : Fin w.cells.length) :
    ∀ a ∈ rlCellArrows p hnt blank action w hleft k,
      NotAtLeft p hnt blank a := by
  intro a ha
  unfold rlCellArrows ULogSourceObliviousRLCellExecution.cellArrows at ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    simp only [NotAtLeft, skipRLArrow]
    split <;> simp [deterministicArrow]
  · have heq := List.mem_singleton.mp ha
    subst a
    simp [NotAtLeft, updateRLFlagArrow, deterministicArrow]

theorem rlWindow_sources (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (action : BoundedAction ns nt) (w : LogicalWindow nt)
    (hleft : action.move = .left → 0 < w.head.val) :
    ∀ a ∈ rlWindowArrows p hnt blank action w hleft,
      NotAtLeft p hnt blank a := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨xs, hxs, ha⟩ := List.mem_flatten.mp ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hxs
    exact rlCell_sources p hnt blank action w hleft _ a ha
  · have heq := List.mem_singleton.mp ha
    subst a
    simp [NotAtLeft, skipRLLeftBoundaryArrow, deterministicArrow]

theorem safeSuffix_sources (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (action : BoundedAction ns nt) (w next : LogicalWindow nt)
    (hsafe : w.applyAction? action = some next) :
    ∀ a ∈ safeSuffixArrows p hnt blank q action w next hsafe,
      NotAtLeft p hnt blank a := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · exact returnLeft_sources p hnt blank q action w a ha
    · exact lrWindow_sources p hnt blank action w _ a ha
  · exact rlWindow_sources p hnt blank action _ _ a ha


theorem preBranch_tail_sources (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys) :
    ∀ a ∈ (preBranchArrows p hnt blank q w exterior).tail,
      NotAtLeft p hnt blank a := by
  intro a ha
  change a ∈ unmarkedRangeArrows p hnt blank q none w exterior 0 w.head.val ++
    markedCellPreArrows p hnt blank q (windowTape w exterior) (cellHead nt w.head.val) at ha
  rcases List.mem_append.mp ha with ha | ha
  · exact unmarkedRange_sources p hnt blank q none w exterior 0 w.head.val a ha
  · exact markedCellPre_sources p hnt blank q _ _ a ha

theorem postBranch_sources (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (action : BoundedAction ns nt)
    (w : LogicalWindow nt) (exterior : Int → Phys) :
    ∀ a ∈ postBranchArrows p hnt blank q action w exterior,
      NotAtLeft p hnt blank a :=
  unmarkedRange_sources p hnt blank q (some action) w exterior _ _

theorem overflowLRCell_sources (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (action : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : action.move = .right) (hover : w.head.val + 1 = w.cells.length)
    (k : Fin w.cells.length) :
    ∀ a ∈ overflowLRCellArrows p hnt blank action w hmove hover k,
      NotAtLeft p hnt blank a := by
  intro a ha
  unfold overflowLRCellArrows ULogSourceObliviousLRCellExecution.cellArrows at ha
  rcases List.mem_cons.mp ha with rfl | ha
  · simp [NotAtLeft, ULogSourceObliviousUpdateExecution.updateLRFlagInteriorArrow,
      deterministicArrow]
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    simp only [NotAtLeft, ULogSourceObliviousUpdateExecution.skipLRArrow]
    split <;> simp [deterministicArrow]

theorem overflowLRReject_sources (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (action : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : action.move = .right) (hover : w.head.val + 1 = w.cells.length) :
    ∀ a ∈ overflowLRReject p hnt blank action w hmove hover,
      NotAtLeft p hnt blank a := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨xs, hxs, ha⟩ := List.mem_flatten.mp ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hxs
    exact overflowLRCell_sources p hnt blank action w hmove hover _ a ha
  · have heq := List.mem_singleton.mp ha
    subst a
    simp [NotAtLeft, updateLRFlagOverflowArrow, deterministicArrow]

theorem unsafeRightPrefix_sources (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (action : BoundedAction ns nt)
    (w : LogicalWindow nt)
    (hmove : action.move = .right) (hover : w.head.val + 1 = w.cells.length) :
    ∀ a ∈ unsafeRightPrefix p hnt blank q action w hmove hover,
      NotAtLeft p hnt blank a := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact returnLeft_sources p hnt blank q action w a ha
  · exact overflowLRReject_sources p hnt blank action w hmove hover a ha

theorem overflowRLCell_sources (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (action : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : action.move = .left) (hover : w.head.val = 0)
    (k : Fin w.cells.length) :
    ∀ a ∈ overflowRLCellArrows p hnt blank action w hmove hover k,
      NotAtLeft p hnt blank a := by
  intro a ha
  unfold overflowRLCellArrows ULogSourceObliviousRLCellExecution.cellArrows at ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    simp only [NotAtLeft, ULogSourceObliviousUpdateExecution.skipRLArrow]
    split <;> simp [deterministicArrow]
  · have heq := List.mem_singleton.mp ha
    subst a
    simp [NotAtLeft, ULogSourceObliviousUpdateExecution.updateRLFlagArrow,
      deterministicArrow]

theorem overflowRLReject_sources (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (action : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : action.move = .left) (hover : w.head.val = 0) :
    ∀ a ∈ overflowRLReject p hnt blank action w hmove hover,
      NotAtLeft p hnt blank a := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨xs, hxs, ha⟩ := List.mem_flatten.mp ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hxs
    exact overflowRLCell_sources p hnt blank action w hmove hover _ a ha
  · have heq := List.mem_singleton.mp ha
    subst a
    simp [NotAtLeft, skipRLOverflowArrow, deterministicArrow]

theorem unsafeLeftPrefix_sources (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (action : BoundedAction ns nt)
    (w : LogicalWindow nt) (hmove : action.move = .left) (hover : w.head.val = 0) :
    ∀ a ∈ unsafeLeftPrefix p hnt blank q action w hmove hover,
      NotAtLeft p hnt blank a := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · exact returnLeft_sources p hnt blank q action w a ha
    · exact lrWindow_sources p hnt blank action w _ a ha
  · exact overflowRLReject_sources p hnt blank action _ _ _ a ha

end PakFixedPolyomino.ULogSourceObliviousPhaseSources
