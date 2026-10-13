import PakFixedPolyomino.ULogSourceObliviousSafeSuffix

/-! # Every operational interior prefix of the update windows

The head formula holds at every arrow, including inside a symbol block.
Successful prefix existence follows from the actual complete run.
-/

namespace PakFixedPolyomino.FiniteOneTapeSemantics

open OneTapeTableau FiniteOneTapeProgram

variable {State Tape : Type*} [Fintype State] [Fintype Tape]
variable [DecidableEq State] [DecidableEq Tape]

omit [Fintype State] [Fintype Tape] in
theorem step_some_head (P : Program State Tape) (movable : Tape → Bool)
    (c out : Config State Tape) (a : Arrow P) (hs : step P movable c a = some out) :
    out.head = moveHead (transition P a).move c.head := by
  unfold step at hs
  dsimp only at hs
  split at hs
  · simp at hs
  · split at hs
    · exact Option.some.inj hs |>.symm ▸ rfl
    · simp at hs

omit [Fintype State] [Fintype Tape] in
theorem run_take_exists (P : Program State Tape) (movable : Tape → Bool)
    (arrows : List (Arrow P)) (c out : Config State Tape)
    (hrun : run P movable arrows c = some out) (k : ℕ) (hk : k ≤ arrows.length) :
    ∃ middle, run P movable (arrows.take k) c = some middle := by
  induction k generalizing arrows c with
  | zero => exact ⟨c, rfl⟩
  | succ k ih =>
      cases arrows with
      | nil => simp at hk
      | cons a arrows =>
          cases hs : step P movable c a with
          | none => simp [run, hs] at hrun
          | some d =>
              obtain ⟨middle, hm⟩ := ih arrows d (by simpa [run, hs] using hrun)
                (by simpa using hk)
              exact ⟨middle, by simpa [List.take_succ_cons, run, hs] using hm⟩

theorem run_head_right (P : Program State Tape) (movable : Tape → Bool)
    (arrows : List (Arrow P)) (c out : Config State Tape)
    (hmoves : ∀ a ∈ arrows, (transition P a).move = .right)
    (hrun : run P movable arrows c = some out) :
    out.head = c.head + (arrows.length : Int) := by
  induction arrows generalizing c with
  | nil => simp only [run_nil, Option.some.injEq] at hrun; subst out; simp
  | cons a arrows ih =>
      cases hs : step P movable c a with
      | none => simp [run, hs] at hrun
      | some d =>
          have hd := step_some_head P movable c d a hs
          rw [hmoves a (by simp), moveHead] at hd
          have hout := ih d (fun b hb => hmoves b (by simp [hb]))
            (by simpa [run, hs] using hrun)
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          omega

theorem run_head_left (P : Program State Tape) (movable : Tape → Bool)
    (arrows : List (Arrow P)) (c out : Config State Tape)
    (hmoves : ∀ a ∈ arrows, (transition P a).move = .left)
    (hrun : run P movable arrows c = some out) :
    out.head = c.head - (arrows.length : Int) := by
  induction arrows generalizing c with
  | nil => simp only [run_nil, Option.some.injEq] at hrun; subst out; simp
  | cons a arrows ih =>
      cases hs : step P movable c a with
      | none => simp [run, hs] at hrun
      | some d =>
          have hd := step_some_head P movable c d a hs
          rw [hmoves a (by simp), moveHead] at hd
          have hout := ih d (fun b hb => hmoves b (by simp [hb]))
            (by simpa [run, hs] using hrun)
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          omega

end PakFixedPolyomino.FiniteOneTapeSemantics

namespace PakFixedPolyomino.ULogSourceObliviousWindowFootprint

open FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceObliviousWindow ULogSourceObliviousScanProgram
open ULogSourceObliviousScanExecution ULogSourceObliviousUpdateExecution
open ULogSourceObliviousLRWindowExecution ULogSourceObliviousRLWindowExecution
open ULogSourceObliviousSafeSuffix

variable {ns nt : ℕ}

theorem skipLRArrow_move (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed rewrite : Bool) (i : Fin nt) (x : Phys)
    (hv : validBit x = true) :
    (transition (program p hnt blank) (skipLRArrow p hnt blank a armed rewrite i x hv)).move =
      .right := by
  unfold skipLRArrow
  split <;> simp [transition]

theorem skipRLArrow_move (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed : Bool) (i : Fin nt) (x : Phys)
    (hv : validBit x = true) (hne : x ≠ ULogSourceOneHotReader.blank) :
    (transition (program p hnt blank) (skipRLArrow p hnt blank a armed i x hv hne)).move =
      .left := by
  unfold skipRLArrow
  split <;> simp [transition]

theorem lrCellArrows_moves (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (k : Fin w.cells.length) :
    ∀ b ∈ lrCellArrows p hnt blank a w hright k, (transition (program p hnt blank) b).move = .right := by
  intro b hb
  simp only [lrCellArrows, ULogSourceObliviousLRCellExecution.cellArrows, List.mem_cons] at hb
  rcases hb with rfl | hb
  · simp [updateLRFlagInteriorArrow, transition]
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact skipLRArrow_move p hnt blank a _ _ i _ _

theorem rlCellArrows_moves (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val) (k : Fin u.cells.length) :
    ∀ b ∈ rlCellArrows p hnt blank a u hleft k, (transition (program p hnt blank) b).move = .left := by
  intro b hb
  simp only [rlCellArrows, ULogSourceObliviousRLCellExecution.cellArrows,
    List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact skipRLArrow_move p hnt blank a _ _ _ _ _
  · simp [updateRLFlagArrow, transition]

theorem lrInteriorArrows_moves (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length) :
    ∀ b ∈ lrInteriorArrows p hnt blank a w hright, (transition (program p hnt blank) b).move = .right := by
  intro b hb
  obtain ⟨cell, hc, hb⟩ := List.mem_flatten.mp hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  exact lrCellArrows_moves p hnt blank a w hright _ b hb

theorem rlInteriorArrows_moves (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val) :
    ∀ b ∈ rlInteriorArrows p hnt blank a u hleft, (transition (program p hnt blank) b).move = .left := by
  intro b hb
  obtain ⟨cell, hc, hb⟩ := List.mem_flatten.mp hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  exact rlCellArrows_moves p hnt blank a u hleft _ b hb

theorem lr_every_prefix_head (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length)
    (exterior : Int → Phys) (k : ℕ) (hk : k ≤ windowWidth w) :
    ∃ middle, run (program p hnt blank) (fun _ => true)
      ((lrInteriorArrows p hnt blank a w hright).take k) (lrStart a w exterior) = some middle ∧
      middle.head = 1 + (k : Int) := by
  have hlen : k ≤ (lrInteriorArrows p hnt blank a w hright).length := by
    simpa [lrInteriorArrows_length] using hk
  obtain ⟨middle, hrun⟩ := run_take_exists (program p hnt blank) (fun _ => true) _ _ _
    (lr_interior_run p hnt blank a w hright exterior) k hlen
  refine ⟨middle, hrun, ?_⟩
  have hh := run_head_right (program p hnt blank) (fun _ => true) _ _ middle
    (fun b hb => lrInteriorArrows_moves p hnt blank a w hright b (List.mem_of_mem_take hb)) hrun
  simpa [lrStart, List.length_take, Nat.min_eq_left hlen] using hh

theorem rl_every_prefix_head (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val)
    (exterior : Int → Phys) (k : ℕ) (hk : k ≤ windowWidth u) :
    ∃ middle, run (program p hnt blank) (fun _ => true)
      ((rlInteriorArrows p hnt blank a u hleft).take k) (rlStart hnt a u exterior) = some middle ∧
      middle.head = (windowWidth u : Int) - (k : Int) := by
  have hlen : k ≤ (rlInteriorArrows p hnt blank a u hleft).length := by
    simpa [rlInteriorArrows_length] using hk
  obtain ⟨middle, hrun⟩ := run_take_exists (program p hnt blank) (fun _ => true) _ _ _
    (rl_interior_run p hnt blank a u hleft exterior) k hlen
  refine ⟨middle, hrun, ?_⟩
  have hh := run_head_left (program p hnt blank) (fun _ => true) _ _ middle
    (fun b hb => rlInteriorArrows_moves p hnt blank a u hleft b (List.mem_of_mem_take hb)) hrun
  simpa [rlStart, List.length_take, Nat.min_eq_left hlen] using hh

/-- Every chronological prefix exists and has its head in the interval. -/
def PrefixInInterval (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (lo hi : Int) (arrows : List (ScanArrow p hnt blank)) (c : ScanCfg ns nt) : Prop :=
  ∀ k ≤ arrows.length, ∃ middle,
    run (program p hnt blank) (fun _ => true) (arrows.take k) c = some middle ∧
      lo ≤ middle.head ∧ middle.head ≤ hi

theorem prefixInInterval_append (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (lo hi : Int) (xs ys : List (ScanArrow p hnt blank)) (c middle : ScanCfg ns nt)
    (hx : PrefixInInterval p hnt blank lo hi xs c)
    (hrun : run (program p hnt blank) (fun _ => true) xs c = some middle)
    (hy : PrefixInInterval p hnt blank lo hi ys middle) :
    PrefixInInterval p hnt blank lo hi (xs ++ ys) c := by
  intro k hk
  by_cases hle : k ≤ xs.length
  · obtain ⟨out, hpre, hlo, hhi⟩ := hx k hle
    exact ⟨out, by simpa [List.take_append_of_le_length hle] using hpre, hlo, hhi⟩
  · have hsub : k - xs.length ≤ ys.length := by simp only [List.length_append] at hk; omega
    obtain ⟨out, hpre, hlo, hhi⟩ := hy (k - xs.length) hsub
    refine ⟨out, ?_, hlo, hhi⟩
    rw [List.take_append, List.take_of_length_le (by omega), run_append p hnt blank,
      hrun, Option.bind_some]
    exact hpre

theorem lr_window_prefix_interval (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hright : a.move = .right → w.head.val + 1 < w.cells.length) (exterior : Int → Phys) :
    PrefixInInterval p hnt blank 0 (windowWidth w + 1 : Int)
      (lrWindowArrows p hnt blank a w hright) (lrStart a w exterior) := by
  intro k hk
  by_cases hle : k ≤ windowWidth w
  · obtain ⟨middle, hrun, hh⟩ := lr_every_prefix_head p hnt blank a w hright exterior k hle
    refine ⟨middle, ?_, ?_, ?_⟩
    · rw [lrWindowArrows, List.take_append_of_le_length
        (by simpa only [lrInteriorArrows_length] using hle)]
      exact hrun
    · rw [hh]; omega
    · rw [hh]; omega
  · have heq : k = windowWidth w + 1 := by simp only [lrWindowArrows_length] at hk; omega
    subst k
    refine ⟨{
      state := .skipRL a false ⟨nt - 1, by omega⟩
      head := (windowWidth w : Int)
      tape := windowTape (lrWindow w a hright) exterior },
      ?_, ?_, ?_⟩
    · rw [List.take_of_length_le (by rw [lrWindowArrows_length])]
      exact lr_window_run p hnt blank a w hright exterior
    · change 0 ≤ (windowWidth w : Int); omega
    · change (windowWidth w : Int) ≤ (windowWidth w + 1 : Int); omega

theorem rl_window_prefix_interval (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hleft : a.move = .left → 0 < u.head.val) (exterior : Int → Phys) :
    PrefixInInterval p hnt blank 0 (windowWidth u + 1 : Int)
      (rlWindowArrows p hnt blank a u hleft) (rlStart hnt a u exterior) := by
  intro k hk
  by_cases hle : k ≤ windowWidth u
  · obtain ⟨middle, hrun, hh⟩ := rl_every_prefix_head p hnt blank a u hleft exterior k hle
    refine ⟨middle, ?_, ?_, ?_⟩
    · rw [rlWindowArrows, List.take_append_of_le_length
        (by simpa only [rlInteriorArrows_length] using hle)]
      exact hrun
    · rw [hh]; omega
    · rw [hh]; omega
  · have heq : k = windowWidth u + 1 := by simp only [rlWindowArrows_length] at hk; omega
    subst k
    refine ⟨{
      state := .atLeft a.target
      head := 0
      tape := windowTape (rlWindow u a hleft) exterior }, ?_, ?_, ?_⟩
    · rw [List.take_of_length_le (by rw [rlWindowArrows_length])]
      exact rl_window_run p hnt blank a u hleft exterior
    · change 0 ≤ (0 : Int); omega
    · change (0 : Int) ≤ (windowWidth u + 1 : Int); omega

def returnBeforeBoundary (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (a : BoundedAction ns nt) (w : LogicalWindow nt) :
    List (ScanArrow p hnt blank) :=
  postScanBoundaryArrow p hnt blank q a ::
    returnLeftInteriorArrows p hnt blank a w.encode (fun _x hx => encode_mem_ne_blank w hx)

@[simp] theorem returnBeforeBoundary_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt) (w : LogicalWindow nt) :
    (returnBeforeBoundary p hnt blank q a w).length = windowWidth w + 1 := by
  simp [returnBeforeBoundary, windowWidth]

theorem returnBeforeBoundary_moves (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt) (w : LogicalWindow nt) :
    ∀ b ∈ returnBeforeBoundary p hnt blank q a w,
      (transition (program p hnt blank) b).move = .left := by
  intro b hb
  simp only [returnBeforeBoundary, List.mem_cons] at hb
  rcases hb with rfl | hb
  · simp [postScanBoundaryArrow, transition]
  · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hb
    simp [returnLeftInteriorArrow, transition]

theorem return_window_prefix_interval (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (exterior : Int → Phys) :
    PrefixInInterval p hnt blank 0 (windowWidth w + 1 : Int)
      (returnLeftArrows p hnt blank q a w) (startConfig q a w exterior) := by
  intro k hk
  by_cases hle : k ≤ windowWidth w + 1
  · obtain ⟨middle, hrun⟩ := run_take_exists (program p hnt blank) (fun _ => true) _ _ _
      (returnLeft_run p hnt blank q a w exterior) k hk
    have htake : (returnLeftArrows p hnt blank q a w).take k =
        (returnBeforeBoundary p hnt blank q a w).take k := by
      change ((returnBeforeBoundary p hnt blank q a w) ++ [returnLeftBoundaryArrow p hnt blank a]).take k = _
      exact List.take_append_of_le_length (by simpa using hle)
    have hh := run_head_left (program p hnt blank) (fun _ => true) _ _ middle
      (fun b hb => returnBeforeBoundary_moves p hnt blank q a w b (List.mem_of_mem_take hb))
      (by simpa only [htake] using hrun)
    have hhead : middle.head = (windowWidth w + 1 : Int) - (k : Int) := by
      simpa [startConfig, List.length_take, Nat.min_eq_left (by simpa using hle)] using hh
    refine ⟨middle, hrun, ?_, ?_⟩ <;> rw [hhead] <;> omega
  · have heq : k = windowWidth w + 2 := by simp only [returnLeftArrows_length] at hk; omega
    subst k
    refine ⟨{ state := .updateLRFlag a false, head := 1, tape := windowTape w exterior },
      ?_, ?_, ?_⟩
    · rw [List.take_of_length_le (by simp)]
      exact returnLeft_run p hnt blank q a w exterior
    · change 0 ≤ (1 : Int); omega
    · change (1 : Int) ≤ (windowWidth w + 1 : Int); omega

theorem safe_suffix_prefix_interval (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt) (w next : LogicalWindow nt)
    (hsafe : w.applyAction? a = some next) (exterior : Int → Phys) :
    PrefixInInterval p hnt blank 0 (windowWidth w + 1 : Int)
      (safeSuffixArrows p hnt blank q a w next hsafe) (startConfig q a w exterior) := by
  let hr := safeRight w next a hsafe
  let hl := safeLeft w next a hsafe
  change PrefixInInterval p hnt blank 0 _
    ((returnLeftArrows p hnt blank q a w ++ lrWindowArrows p hnt blank a w hr) ++
      rlWindowArrows p hnt blank a (lrWindow w a hr) (leftAfterLR w a hr hl)) _
  apply prefixInInterval_append p hnt blank _ _ _ _ _
    (rlStart hnt a (lrWindow w a hr) exterior) ?_
    (return_lr_run p hnt blank q a w hr exterior) ?_
  · exact prefixInInterval_append p hnt blank _ _ _ _ _ (lrStart a w exterior)
      (return_window_prefix_interval p hnt blank q a w exterior)
      (returnLeft_run p hnt blank q a w exterior)
      (lr_window_prefix_interval p hnt blank a w hr exterior)
  · simpa only [lrWindow_windowWidth] using rl_window_prefix_interval p hnt blank a
      (lrWindow w a hr) (leftAfterLR w a hr hl) exterior

theorem safe_suffix_footprint (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt) (w next : LogicalWindow nt)
    (hsafe : w.applyAction? a = some next) (exterior : Int → Phys) :
    PrefixInInterval p hnt blank 0 (windowWidth w + 1 : Int)
        (safeSuffixArrows p hnt blank q a w next hsafe) (startConfig q a w exterior) ∧
      (∀ k ≤ windowWidth w, ∃ middle,
        run (program p hnt blank) (fun _ => true)
          ((lrInteriorArrows p hnt blank a w (safeRight w next a hsafe)).take k)
          (lrStart a w exterior) = some middle ∧ middle.head = 1 + (k : Int)) ∧
      (∀ k ≤ windowWidth w, ∃ middle,
        run (program p hnt blank) (fun _ => true)
          ((rlInteriorArrows p hnt blank a (lrWindow w a (safeRight w next a hsafe))
            (leftAfterLR w a (safeRight w next a hsafe) (safeLeft w next a hsafe))).take k)
          (rlStart hnt a (lrWindow w a (safeRight w next a hsafe)) exterior) = some middle ∧
        middle.head = (windowWidth w : Int) - (k : Int)) := by
  refine ⟨safe_suffix_prefix_interval p hnt blank q a w next hsafe exterior,
    lr_every_prefix_head p hnt blank a w (safeRight w next a hsafe) exterior, ?_⟩
  intro k hk
  simpa only [lrWindow_windowWidth] using rl_every_prefix_head p hnt blank a
    (lrWindow w a (safeRight w next a hsafe))
    (leftAfterLR w a (safeRight w next a hsafe) (safeLeft w next a hsafe)) exterior k
    (by simpa only [lrWindow_windowWidth] using hk)

end PakFixedPolyomino.ULogSourceObliviousWindowFootprint
