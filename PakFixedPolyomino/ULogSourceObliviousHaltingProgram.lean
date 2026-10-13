import PakFixedPolyomino.FiniteOneTapeHaltingRestriction
import PakFixedPolyomino.StandardMachineScannerAcceptance

/-! # Actual accepting and rejecting halt dispatch for the source scanner

The finite rule table is terminalized at the source accepting/rejecting
atLeft states and at the scanner rejection state. Source actions and every
remaining literal physical transition are preserved. Input loading, a fixed
universal interpreter, arbitrary stopping-length grammar and frame resources
remain separate obligations.
-/

namespace PakFixedPolyomino.ULogSourceObliviousHaltingProgram

open FiniteOneTapeProgram FiniteOneTapeSemantics FiniteOneTapeHaltingRestriction
open ULogCompiler StandardNondeterministicMachine
open StandardMachineZipperBridge (toBounded)
open ULogSourceObliviousScanProgram ULogSourceObliviousWindow
open ULogSourceObliviousUpdateExecution ULogSourceObliviousScanExecution
open ULogSourceObliviousInitialCells ULogSourceObliviousInitialWindowInverse
open ULogSourceObliviousInitialWindowExecution ULogSourceObliviousCycleExecution
open ULogSourceObliviousCycleTraces ULogSourceObliviousSafeSuffix
open ULogSourceObliviousLRWindowExecution ULogSourceObliviousRLWindowExecution

variable {ns nt : ℕ}

def halted (M : Machine ns nt 2) (s : State ns nt) : Bool :=
  decide (s = State.atLeft M.accept ∨ s = State.atLeft M.reject ∨ s = State.reject)

def haltProgram (M : Machine ns nt 2) : Program (State ns nt) Phys :=
  terminalize (program (toBounded M) (Nat.zero_lt_of_lt M.blank.isLt) M.blank) (halted M)

@[simp] theorem halted_accept (M : Machine ns nt 2) :
    halted M (.atLeft M.accept) = true := by simp [halted]

@[simp] theorem halted_source_reject (M : Machine ns nt 2) :
    halted M (.atLeft M.reject) = true := by simp [halted]

@[simp] theorem halted_scanner_reject (M : Machine ns nt 2) :
    halted M .reject = true := by simp [halted]

theorem haltProgram_accept_terminal (M : Machine ns nt 2) (x : Phys) (slot : Fin 2) :
    (haltProgram M).rule (.atLeft M.accept) x slot = none := by
  simp [haltProgram, terminalize]

theorem haltProgram_reject_terminal (M : Machine ns nt 2) (x : Phys) (slot : Fin 2) :
    (haltProgram M).rule .reject x slot = none := by
  simp [haltProgram, terminalize]

theorem haltProgram_source_reject_terminal (M : Machine ns nt 2) (x : Phys) (slot : Fin 2) :
    (haltProgram M).rule (.atLeft M.reject) x slot = none := by
  simp [haltProgram, terminalize]

theorem sourceChoice_not_terminal (M : Machine ns nt 2) (q : Fin ns) (read : Fin nt)
    (choice : ULogSourceOneHotMacroEquiv.SourceChoice (toBounded M) q read) :
    q ≠ M.accept ∧ q ≠ M.reject := by
  constructor
  · intro hq
    subst q
    have h := choice.occupied
    simp [toBounded, M.accept_terminal] at h
  · intro hq
    subst q
    have h := choice.occupied
    simp [toBounded, M.reject_terminal] at h

def LiveArrow (M : Machine ns nt 2) (hnt : 0 < nt) (blank : Fin nt)
    (a : ScanArrow (toBounded M) hnt blank) : Prop := halted M a.1.1.1 = false

theorem readArrows_live (M : Machine ns nt 2) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (selected : Option (BoundedAction ns nt)) (isHead : Bool)
    (c : ReaderConfig (nt := nt)) (k : ℕ) :
    ∀ a ∈ readArrows (toBounded M) hnt blank q selected isHead c k,
      LiveArrow M hnt blank a := by
  induction k generalizing c with
  | zero => simp [readArrows]
  | succ k ih =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [LiveArrow, halted, readLiteralArrow]
      · exact ih _ a ha

theorem unmarkedCell_live (M : Machine ns nt 2) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (selected : Option (BoundedAction ns nt)) (tape : Int → Phys) (head : Int) :
    ∀ a ∈ unmarkedCellArrows (toBounded M) hnt blank q selected tape head,
      LiveArrow M hnt blank a := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · simp [LiveArrow, halted, flagZeroArrow, deterministicArrow]
  · exact readArrows_live M hnt blank q selected false _ nt a ha

theorem markedCellPre_live (M : Machine ns nt 2) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (tape : Int → Phys) (head : Int) :
    ∀ a ∈ markedCellPreArrows (toBounded M) hnt blank q tape head,
      LiveArrow M hnt blank a := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · simp [LiveArrow, halted, flagHeadArrow]
  · exact readArrows_live M hnt blank q none true _ nt a ha

theorem unmarkedRange_live (M : Machine ns nt 2) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (selected : Option (BoundedAction ns nt)) (w : LogicalWindow nt)
    (exterior : Int → Phys) (start count : ℕ) :
    ∀ a ∈ unmarkedRangeArrows (toBounded M) hnt blank q selected w exterior start count,
      LiveArrow M hnt blank a := by
  induction count with
  | zero => simp [unmarkedRangeArrows]
  | succ count ih =>
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact ih a ha
      · exact unmarkedCell_live M hnt blank q selected _ _ a ha

theorem sourceScan_live (M : Machine ns nt 2) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt)
    (choice : ULogSourceOneHotMacroEquiv.SourceChoice (toBounded M) q (w.cells.get w.head))
    (exterior : Int → Phys) :
    ∀ a ∈ sourceScanArrows (toBounded M) hnt blank q w choice exterior,
      LiveArrow M hnt blank a := by
  intro a ha
  rcases List.mem_append.mp ha with hpre | hpost
  · rcases List.mem_cons.mp hpre with rfl | hpre
    · obtain ⟨hacc, hrej⟩ := sourceChoice_not_terminal M q _ choice
      simp [LiveArrow, halted, startScanArrow, deterministicArrow, hacc, hrej]
    · rcases List.mem_append.mp hpre with hpre | hpre
      · exact unmarkedRange_live M hnt blank q none w exterior 0 w.head.val a hpre
      · exact markedCellPre_live M hnt blank q _ _ a hpre
  · rcases List.mem_cons.mp hpost with rfl | hpost
    · simp [LiveArrow, halted, branchArrow]
    · exact unmarkedRange_live M hnt blank q (some choice.action) w exterior
        (w.head.val + 1) (w.cells.length - w.head.val - 1) a hpost

theorem returnLeft_live (M : Machine ns nt 2) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (action : BoundedAction ns nt) (w : LogicalWindow nt) :
    ∀ a ∈ returnLeftArrows (toBounded M) hnt blank q action w,
      LiveArrow M hnt blank a := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · simp [LiveArrow, halted, postScanBoundaryArrow, deterministicArrow]
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
      simp [LiveArrow, halted, returnLeftInteriorArrow, deterministicArrow]
    · have heq := List.mem_singleton.mp ha
      subst a
      simp [LiveArrow, halted, returnLeftBoundaryArrow, deterministicArrow]

theorem lrCell_live (M : Machine ns nt 2) (hnt : 0 < nt) (blank : Fin nt)
    (action : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : action.move = .right → w.head.val + 1 < w.cells.length)
    (k : Fin w.cells.length) :
    ∀ a ∈ lrCellArrows (toBounded M) hnt blank action w hright k,
      LiveArrow M hnt blank a := by
  intro a ha
  unfold lrCellArrows ULogSourceObliviousLRCellExecution.cellArrows at ha
  rcases List.mem_cons.mp ha with rfl | ha
  · simp [LiveArrow, halted, updateLRFlagInteriorArrow, deterministicArrow]
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    simp only [LiveArrow, halted, skipLRArrow]
    split <;> simp [deterministicArrow]

theorem lrWindow_live (M : Machine ns nt 2) (hnt : 0 < nt) (blank : Fin nt)
    (action : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : action.move = .right → w.head.val + 1 < w.cells.length) :
    ∀ a ∈ lrWindowArrows (toBounded M) hnt blank action w hright,
      LiveArrow M hnt blank a := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨xs, hxs, ha⟩ := List.mem_flatten.mp ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hxs
    exact lrCell_live M hnt blank action w hright _ a ha
  · have heq := List.mem_singleton.mp ha
    subst a
    simp [LiveArrow, halted, updateLRFlagRightBoundaryArrow, deterministicArrow]

theorem rlCell_live (M : Machine ns nt 2) (hnt : 0 < nt) (blank : Fin nt)
    (action : BoundedAction ns nt) (w : LogicalWindow nt)
    (hleft : action.move = .left → 0 < w.head.val) (k : Fin w.cells.length) :
    ∀ a ∈ rlCellArrows (toBounded M) hnt blank action w hleft k,
      LiveArrow M hnt blank a := by
  intro a ha
  unfold rlCellArrows ULogSourceObliviousRLCellExecution.cellArrows at ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    simp only [LiveArrow, halted, skipRLArrow]
    split <;> simp [deterministicArrow]
  · have heq := List.mem_singleton.mp ha
    subst a
    simp [LiveArrow, halted, updateRLFlagArrow, deterministicArrow]

theorem rlWindow_live (M : Machine ns nt 2) (hnt : 0 < nt) (blank : Fin nt)
    (action : BoundedAction ns nt) (w : LogicalWindow nt)
    (hleft : action.move = .left → 0 < w.head.val) :
    ∀ a ∈ rlWindowArrows (toBounded M) hnt blank action w hleft,
      LiveArrow M hnt blank a := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨xs, hxs, ha⟩ := List.mem_flatten.mp ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hxs
    exact rlCell_live M hnt blank action w hleft _ a ha
  · have heq := List.mem_singleton.mp ha
    subst a
    simp [LiveArrow, halted, skipRLLeftBoundaryArrow, deterministicArrow]

theorem safeSuffix_live (M : Machine ns nt 2) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (action : BoundedAction ns nt) (w next : LogicalWindow nt)
    (hsafe : w.applyAction? action = some next) :
    ∀ a ∈ safeSuffixArrows (toBounded M) hnt blank q action w next hsafe,
      LiveArrow M hnt blank a := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · exact returnLeft_live M hnt blank q action w a ha
    · exact lrWindow_live M hnt blank action w _ a ha
  · exact rlWindow_live M hnt blank action _ _ a ha

theorem cycle_live (M : Machine ns nt 2) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt)
    (choice : ULogSourceOneHotMacroEquiv.SourceChoice (toBounded M) q (w.cells.get w.head))
    (next : LogicalWindow nt) (hsafe : w.applyAction? choice.action = some next)
    (exterior : Int → Phys) :
    ∀ a ∈ cycleArrows (toBounded M) hnt blank q w choice next hsafe exterior,
      LiveArrow M hnt blank a := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact sourceScan_live M hnt blank q w choice exterior a ha
  · exact safeSuffix_live M hnt blank q choice.action w next hsafe a ha

theorem trace_live (M : Machine ns nt 2) (hnt : 0 < nt) (blank : Fin nt)
    (exterior : Int → Phys) (n : ℕ) (q : Fin ns) (w : LogicalWindow nt)
    (t : Trace (toBounded M) n q w) :
    ∀ a ∈ arrows (toBounded M) hnt blank exterior n q w t,
      LiveArrow M hnt blank a := by
  induction n generalizing q w with
  | zero => simp [arrows]
  | succ n ih =>
      rcases t with ⟨s, tail⟩
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact cycle_live M hnt blank q w s.1 _ _ exterior a ha
      · exact ih _ _ tail a ha

/-- This property is derived for EVERY raw completed-cycle run by the raw
inverse, rather than added as an image/safety premise on its domain. -/
theorem all_raw_cycles_live (M : Machine ns nt 2) (hnt : 0 < nt) (blank : Fin nt)
    (exterior : Int → Phys) (n : ℕ) (q : Fin ns) (w : LogicalWindow nt)
    (raw : RawCycles (toBounded M) hnt blank exterior n q w) :
    ∀ a ∈ raw.1, LiveArrow M hnt blank a := by
  obtain ⟨out, hrun, hleft⟩ := raw.2.2
  obtain ⟨t, hword, _⟩ := raw_trace_inverse (toBounded M) hnt blank exterior n q w
    raw.1 out hrun raw.2.1 hleft
  rw [hword]
  exact trace_live M hnt blank exterior n q w t

end PakFixedPolyomino.ULogSourceObliviousHaltingProgram
