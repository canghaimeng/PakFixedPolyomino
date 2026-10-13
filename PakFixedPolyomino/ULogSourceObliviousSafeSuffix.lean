import PakFixedPolyomino.ULogSourceObliviousLRWindowInverse
import PakFixedPolyomino.ULogSourceObliviousRLWindowInverse

/-! # The actual safe return/update suffix

The W+2 return and the two W+1 update windows compose through their actual
endpoints. Their logical result is precisely applyAction?, and every
successful unrestricted raw history of sufficient length has this suffix.
-/

namespace PakFixedPolyomino.ULogSourceObliviousSafeSuffix

open FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceObliviousWindow ULogSourceObliviousScanProgram
open ULogSourceObliviousScanExecution ULogSourceObliviousUpdateExecution
open ULogSourceObliviousRunPrefix ULogSourceObliviousReturnInverse
open ULogSourceObliviousLRWindowExecution ULogSourceObliviousLRWindowInverse
open ULogSourceObliviousRLWindowExecution ULogSourceObliviousRLWindowInverse

variable {ns nt : ℕ}

theorem leftAfterLR (w : LogicalWindow nt) (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (hleft : a.move = .left → 0 < w.head.val) :
    a.move = .left → 0 < (lrWindow w a hright).head.val := by
  intro hmove
  simpa [lrWindow, hmove] using hleft hmove

theorem windows_applyAction (w : LogicalWindow nt) (a : BoundedAction ns nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (hleft : a.move = .left → 0 < w.head.val) :
    w.applyAction? a = some
      (rlWindow (lrWindow w a hright) a (leftAfterLR w a hright hleft)) := by
  cases hm : a.move with
  | stay => simp [LogicalWindow.applyAction?, moveIndex, hm, lrWindow, rlWindow]
  | right =>
      have hr := hright hm
      simp [LogicalWindow.applyAction?, moveIndex, hm, hr, lrWindow, rlWindow]
  | left =>
      have hl := hleft hm
      simp [LogicalWindow.applyAction?, moveIndex, hm, hl, lrWindow, rlWindow]

theorem safeRight (w next : LogicalWindow nt) (a : BoundedAction ns nt)
    (hsafe : w.applyAction? a = some next) :
    a.move = .right → w.head.val + 1 < w.cells.length := by
  intro hm
  exact (applyAction?_right w a hm).mp (by simp [hsafe])

theorem safeLeft (w next : LogicalWindow nt) (a : BoundedAction ns nt)
    (hsafe : w.applyAction? a = some next) :
    a.move = .left → 0 < w.head.val := by
  intro hm
  exact (applyAction?_left w a hm).mp (by simp [hsafe])

def suffixArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (hleft : a.move = .left → 0 < w.head.val) : List (ScanArrow p hnt blank) :=
  (returnLeftArrows p hnt blank q a w ++ lrWindowArrows p hnt blank a w hright) ++
    rlWindowArrows p hnt blank a (lrWindow w a hright) (leftAfterLR w a hright hleft)

@[simp] theorem suffixArrows_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (hleft : a.move = .left → 0 < w.head.val) :
    (suffixArrows p hnt blank q a w hright hleft).length = 3 * windowWidth w + 4 := by
  simp only [suffixArrows, List.length_append, returnLeftArrows_length,
    lrWindowArrows_length, rlWindowArrows_length, lrWindow_windowWidth]
  omega

theorem return_lr_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (exterior : Int → Phys) :
    run (program p hnt blank) (fun _ => true)
      (returnLeftArrows p hnt blank q a w ++ lrWindowArrows p hnt blank a w hright)
      (startConfig q a w exterior) =
      some (rlStart hnt a (lrWindow w a hright) exterior) := by
  rw [run_append p hnt blank, returnLeft_run, Option.bind_some]
  simpa [lrStart, rlStart, lrWindow_windowWidth] using
    lr_window_run p hnt blank a w hright exterior

theorem suffix_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (hleft : a.move = .left → 0 < w.head.val) (exterior : Int → Phys) :
    run (program p hnt blank) (fun _ => true)
      (suffixArrows p hnt blank q a w hright hleft) (startConfig q a w exterior) =
      some {
        state := .atLeft a.target
        head := 0
        tape := windowTape
          (rlWindow (lrWindow w a hright) a (leftAfterLR w a hright hleft)) exterior } := by
  rw [suffixArrows, run_append p hnt blank, return_lr_run, Option.bind_some]
  exact rl_window_run p hnt blank a (lrWindow w a hright)
    (leftAfterLR w a hright hleft) exterior

theorem suffix_nonbranch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (hleft : a.move = .left → 0 < w.head.val) (exterior : Int → Phys) :
    NonbranchPrefix p hnt blank (suffixArrows p hnt blank q a w hright hleft)
      (startConfig q a w exterior) := by
  unfold suffixArrows
  apply nonbranchPrefix_append p hnt blank _ _ _
    (rlStart hnt a (lrWindow w a hright) exterior) ?_
    (return_lr_run p hnt blank q a w hright exterior)
    (rl_window_nonbranch p hnt blank a (lrWindow w a hright)
      (leftAfterLR w a hright hleft) exterior)
  exact nonbranchPrefix_append p hnt blank _ _ _ (lrStart a w exterior)
    (returnLeft_nonbranchPrefix p hnt blank q a w exterior)
    (returnLeft_run p hnt blank q a w exterior)
    (lr_window_nonbranch p hnt blank a w hright exterior)

def safeSuffixArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (a : BoundedAction ns nt) (w next : LogicalWindow nt)
    (hsafe : w.applyAction? a = some next) : List (ScanArrow p hnt blank) :=
  suffixArrows p hnt blank q a w (safeRight w next a hsafe) (safeLeft w next a hsafe)

@[simp] theorem safeSuffixArrows_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt) (w next : LogicalWindow nt)
    (hsafe : w.applyAction? a = some next) :
    (safeSuffixArrows p hnt blank q a w next hsafe).length = 3 * windowWidth w + 4 :=
  suffixArrows_length p hnt blank q a w _ _

theorem safe_suffix_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt) (w next : LogicalWindow nt)
    (hsafe : w.applyAction? a = some next) (exterior : Int → Phys) :
    run (program p hnt blank) (fun _ => true)
      (safeSuffixArrows p hnt blank q a w next hsafe) (startConfig q a w exterior) =
      some { state := .atLeft a.target, head := 0, tape := windowTape next exterior } := by
  have heffect := windows_applyAction w a (safeRight w next a hsafe) (safeLeft w next a hsafe)
  rw [hsafe] at heffect
  have heq := Option.some.inj heffect
  simpa only [safeSuffixArrows, ← heq] using suffix_run p hnt blank q a w
    (safeRight w next a hsafe) (safeLeft w next a hsafe) exterior

theorem safe_suffix_nonbranch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt) (w next : LogicalWindow nt)
    (hsafe : w.applyAction? a = some next) (exterior : Int → Phys) :
    NonbranchPrefix p hnt blank (safeSuffixArrows p hnt blank q a w next hsafe)
      (startConfig q a w exterior) :=
  suffix_nonbranch p hnt blank q a w _ _ exterior

theorem safe_suffix_raw_unique (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt) (w next : LogicalWindow nt)
    (hsafe : w.applyAction? a = some next) (exterior : Int → Phys)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw (startConfig q a w exterior) = some out)
    (hlen : raw.length = 3 * windowWidth w + 4) :
    raw = safeSuffixArrows p hnt blank q a w next hsafe ∧
      out = { state := .atLeft a.target, head := 0, tape := windowTape next exterior } := by
  have hforced := nonbranchPrefix_forced p hnt blank _ _
    (safe_suffix_nonbranch p hnt blank q a w next hsafe exterior)
  obtain ⟨heq, hprefix⟩ := forcedPrefix_unique_successful_run (program p hnt blank)
    (fun _ => true) _ raw _ out hforced hrun
    (by rw [safeSuffixArrows_length, hlen])
  refine ⟨heq, ?_⟩
  rw [safe_suffix_run p hnt blank q a w next hsafe exterior] at hprefix
  exact (Option.some.inj hprefix).symm

theorem safe_suffix_raw_prefix (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt) (w next : LogicalWindow nt)
    (hsafe : w.applyAction? a = some next) (exterior : Int → Phys)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw (startConfig q a w exterior) = some out)
    (hlen : 3 * windowWidth w + 4 ≤ raw.length) :
    ∃ tail, raw = safeSuffixArrows p hnt blank q a w next hsafe ++ tail ∧
      run (program p hnt blank) (fun _ => true) tail
        { state := .atLeft a.target, head := 0, tape := windowTape next exterior } = some out := by
  obtain ⟨tail, middle, heq, hpre, htail⟩ := nonbranchPrefix_split_successful_run
    p hnt blank _ raw _ out (safe_suffix_nonbranch p hnt blank q a w next hsafe exterior)
    hrun (by simpa [safeSuffixArrows_length] using hlen)
  rw [safe_suffix_run p hnt blank q a w next hsafe exterior] at hpre
  have hm := Option.some.inj hpre
  subst middle
  exact ⟨tail, heq, htail⟩

/-- Operational construction and inversion, with boundary safety obtained
from the actual logical action result. No chosen-image premise is used. -/
theorem safe_suffix_correct (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt) (w next : LogicalWindow nt)
    (hsafe : w.applyAction? a = some next) (exterior : Int → Phys) :
    run (program p hnt blank) (fun _ => true)
        (safeSuffixArrows p hnt blank q a w next hsafe) (startConfig q a w exterior) =
        some { state := .atLeft a.target, head := 0, tape := windowTape next exterior } ∧
      (safeSuffixArrows p hnt blank q a w next hsafe).length = 3 * windowWidth w + 4 ∧
      NonbranchPrefix p hnt blank (safeSuffixArrows p hnt blank q a w next hsafe)
        (startConfig q a w exterior) ∧
      ∀ (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt),
        run (program p hnt blank) (fun _ => true) raw (startConfig q a w exterior) = some out →
        3 * windowWidth w + 4 ≤ raw.length →
        ∃ tail, raw = safeSuffixArrows p hnt blank q a w next hsafe ++ tail ∧
          run (program p hnt blank) (fun _ => true) tail
            { state := .atLeft a.target, head := 0, tape := windowTape next exterior } = some out :=
  ⟨safe_suffix_run p hnt blank q a w next hsafe exterior,
    safeSuffixArrows_length p hnt blank q a w next hsafe,
    safe_suffix_nonbranch p hnt blank q a w next hsafe exterior,
    safe_suffix_raw_prefix p hnt blank q a w next hsafe exterior⟩

end PakFixedPolyomino.ULogSourceObliviousSafeSuffix
