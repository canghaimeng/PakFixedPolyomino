import PakFixedPolyomino.ULogSourceObliviousCycleExecution
import Mathlib.Tactic

/-! # Operational reject and boundary-overflow executions

`State.reject` has no successful outgoing arrow. An unsafe right move is
rejected on the LR right delimiter, before any RL pass. An unsafe left move
completes LR and is rejected on the final RL left delimiter. Neither
construction builds an out-of-range `Fin` head.
-/

namespace PakFixedPolyomino.ULogSourceObliviousOverflowExecution

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceOneHotReader (zero one tapeOfBit)
open ULogSourceOneHotBlocks (encodeOneHot encodeOneHot_length)
open ULogSourceObliviousWindow ULogSourceObliviousScanProgram
open ULogSourceObliviousScanExecution ULogSourceObliviousUpdateExecution
open ULogSourceObliviousRunPrefix ULogSourceObliviousReturnInverse
open ULogSourceObliviousLRBlockExecution
open ULogSourceObliviousLRCellExecution
open ULogSourceObliviousLRWindowExecution
open ULogSourceObliviousLRWindowInverse
open ULogSourceObliviousRLWindowExecution

variable {ns nt : ℕ}

theorem cfg_ext' (c₁ c₂ : ScanCfg ns nt)
    (hs : c₁.state = c₂.state) (hh : c₁.head = c₂.head)
    (ht : c₁.tape = c₂.tape) : c₁ = c₂ := by
  cases c₁; cases c₂; simp_all

/-! ## Reject is a total operational dead-end -/

theorem reject_rule_none (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (x : Phys) (slot : Fin 2) :
    (program p hnt blank).rule State.reject x slot = none := by
  cases slot using Fin.cases <;> rfl

theorem reject_no_step (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (c : ScanCfg ns nt) (a : ScanArrow p hnt blank)
    (hstate : c.state = State.reject) :
    FiniteOneTapeSemantics.step (program p hnt blank) (fun _ => true) c a = none := by
  cases h : FiniteOneTapeSemantics.step (program p hnt blank) (fun _ => true) c a with
  | none => rfl
  | some c' =>
      have hsrc := (step_some_forces_source (program p hnt blank) (fun _ => true)
        c c' a h).1
      have hsrc' : a.1.1.1 = State.reject := by
        simpa [transition, hstate] using hsrc.symm
      have hr : (program p hnt blank).rule a.1.1.1 a.1.1.2 a.1.2 = none := by
        simpa [hsrc'] using reject_rule_none p hnt blank a.1.1.2 a.1.2
      exact (a.2 hr).elim

theorem reject_run_cons (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (c : ScanCfg ns nt) (a : ScanArrow p hnt blank)
    (as : List (ScanArrow p hnt blank)) (hstate : c.state = State.reject) :
    run (program p hnt blank) (fun _ => true) (a :: as) c = none := by
  simp [run, reject_no_step p hnt blank c a hstate]

theorem reject_run_nonempty (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (c : ScanCfg ns nt) (as : List (ScanArrow p hnt blank))
    (hstate : c.state = State.reject) (hne : as ≠ []) :
    run (program p hnt blank) (fun _ => true) as c = none := by
  match as with
  | [] => exact (hne rfl).elim
  | a :: rest => exact reject_run_cons p hnt blank c a rest hstate

/-! ## applyAction? fails exactly on the two boundary overflows -/

theorem applyAction?_eq_none_iff (w : LogicalWindow nt)
    (a : BoundedAction ns nt) :
    w.applyAction? a = none ↔
      (a.move = .right ∧ w.head.val + 1 = w.cells.length) ∨
      (a.move = .left ∧ w.head.val = 0) := by
  cases hm : a.move with
  | stay =>
      constructor
      · intro hnone
        have hs := applyAction?_isSome_of_stay w a hm
        simp [hnone] at hs
      · rintro (⟨hr, _⟩ | ⟨hl, _⟩)
        · cases hr
        · cases hl
  | right =>
      have hiff := applyAction?_right w a hm
      constructor
      · intro hnone
        refine Or.inl ⟨rfl, ?_⟩
        have : ¬ (w.head.val + 1 < w.cells.length) := by
          intro hlt
          have : (w.applyAction? a).isSome := hiff.mpr hlt
          simp [hnone] at this
        have hle : w.head.val + 1 ≤ w.cells.length := Nat.succ_le_of_lt w.head.isLt
        exact Nat.le_antisymm hle (Nat.not_lt.mp this)
      · rintro (⟨_, heq⟩ | ⟨hl, _⟩)
        · have : ¬ (w.head.val + 1 < w.cells.length) := by omega
          have : ¬ (w.applyAction? a).isSome := fun hs => this (hiff.mp hs)
          exact Option.not_isSome_iff_eq_none.mp this
        · cases hl
  | left =>
      have hiff := applyAction?_left w a hm
      constructor
      · intro hnone
        refine Or.inr ⟨rfl, ?_⟩
        have : ¬ (0 < w.head.val) := by
          intro hpos
          have : (w.applyAction? a).isSome := hiff.mpr hpos
          simp [hnone] at this
        exact Nat.eq_zero_of_not_pos this
      · rintro (⟨hr, _⟩ | ⟨_, heq⟩)
        · cases hr
        · have : ¬ (0 < w.head.val) := by omega
          have : ¬ (w.applyAction? a).isSome := fun hs => this (hiff.mp hs)
          exact Option.not_isSome_iff_eq_none.mp this

theorem vacuous_right_of_left (w : LogicalWindow nt)
    (a : BoundedAction ns nt) (hleft : a.move = .left) :
    a.move = .right → w.head.val + 1 < w.cells.length := by
  intro hm
  have : False := by rw [hleft] at hm; cases hm
  exact this.elim

/-! ## Shared cell-bit fact -/

theorem cellBits_ne_blank (w : LogicalWindow nt) (k : Fin w.cells.length) :
    ∀ y ∈ cellBits w k, y ≠ physBlank := by
  intro y hy
  rcases List.mem_map.mp hy with ⟨b, _, rfl⟩
  exact tapeOfBit_ne_blank b

theorem agrees_flag (w : LogicalWindow nt) (exterior : Int → Phys)
    (k : Fin w.cells.length) (tape : Int → Phys)
    (h : ∀ z, ((1 + k.val * (nt + 1) : ℕ) : Int) ≤ z →
      tape z = windowTape w exterior z) :
    tape ((1 + k.val * (nt + 1) : ℕ) : Int) =
      tapeOfBit (decide (k.val = w.head.val)) :=
  (h _ le_rfl).trans (windowTape_cell_flag w exterior k)

theorem agrees_bits (w : LogicalWindow nt) (exterior : Int → Phys)
    (k : Fin w.cells.length) (tape : Int → Phys)
    (h : ∀ z, ((1 + k.val * (nt + 1) : ℕ) : Int) ≤ z →
      tape z = windowTape w exterior z) :
    ∀ i : Fin nt,
      tape (((1 + k.val * (nt + 1) : ℕ) : Int) + 1 + (i.val : Int)) =
        (cellBits w k).get ⟨i.val, by simp [cellBits, encodeOneHot_length]⟩ := by
  intro i
  have hlo : ((1 + k.val * (nt + 1) : ℕ) : Int) ≤
      ((1 + k.val * (nt + 1) : ℕ) : Int) + 1 + (i.val : Int) := by omega
  have hcast :
      ((1 + k.val * (nt + 1) : ℕ) : Int) + 1 + (i.val : Int) =
        ((1 + k.val * (nt + 1) + 1 + i.val : ℕ) : Int) := by
    simp [Nat.cast_add, Nat.cast_one]
  exact (h _ hlo).trans (by
    rw [hcast]
    simpa [cellBits, List.get_eq_getElem, List.getElem_map] using
      windowTape_cell_bit w exterior k i)

theorem cell_output_agrees (a : BoundedAction ns nt) (hnt : 0 < nt)
    (c : ScanCfg ns nt) (write : Phys) (x : Phys)
    (bits : List Phys) (hbits : bits.length = nt) (z : Int)
    (hz : c.head + 1 + (nt : Int) ≤ z) :
    writeBlock (Function.update c.tape c.head write) (c.head + 1)
      (outputBits a (x = one) bits) z = c.tape z := by
  have hlen : (outputBits a (x = one) bits).length = nt := by
    simpa using outputBits_length a (x = one) bits hbits
  have hge : (c.head + 1 + ((outputBits a (x = one) bits).length : Int)) ≤ z := by
    simpa [hlen] using hz
  have hne : z ≠ c.head := by omega
  rw [writeBlock_ge _ _ _ z hge, Function.update_of_ne hne]

/-! ## Unsafe right: LR interior without an out-of-range Fin head -/

theorem updateLR_unsafe_right (w : LogicalWindow nt)
    (a : BoundedAction ns nt) (k : Fin w.cells.length)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length) :
    updateLR a (lrArmed w a k.val)
      (tapeOfBit (decide (k.val = w.head.val))) =
      some (tapeOfBit false, lrArmed w a (k.val + 1)) := by
  have hxvalid : validBit (tapeOfBit (decide (k.val = w.head.val))) = true :=
    validBit_tapeOfBit _
  have hkne : k.val ≠ w.head.val + 1 := by
    have := k.isLt
    omega
  unfold updateLR
  simp [hxvalid, hmove, lrArmed, hkne]
  by_cases hk0 : k.val = w.head.val
  · simp [hk0, tapeOfBit, one, zero, lrArmed, hmove]
  · have hk1 : k.val + 1 ≠ w.head.val + 1 := by omega
    simp [hk0, hk1, tapeOfBit, one, zero, lrArmed, hmove]

def overflowLRCellArrows (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length)
    (k : Fin w.cells.length) : List (ScanArrow p hnt blank) :=
  cellArrows p hnt blank a (lrArmed w a k.val)
    (tapeOfBit (decide (k.val = w.head.val))) (tapeOfBit false)
    (lrArmed w a (k.val + 1)) (tapeOfBit_ne_blank _)
    (updateLR_unsafe_right w a k hmove hover)
    (cellBits w k) (cellBits_length w k) (cellBits_valid w k)

@[simp] theorem overflowLRCellArrows_length (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (a : BoundedAction ns nt)
    (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length)
    (k : Fin w.cells.length) :
    (overflowLRCellArrows p hnt blank a w hmove hover k).length = nt + 1 := by
  simp [overflowLRCellArrows]

def overflowLRTake (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length)
    (k : ℕ) (hk : k ≤ w.cells.length) : List (ScanArrow p hnt blank) :=
  (List.ofFn fun j : Fin k =>
    overflowLRCellArrows p hnt blank a w hmove hover ⟨j.val, by omega⟩).flatten

theorem overflowLRTake_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length)
    (k : ℕ) (hk : k ≤ w.cells.length) :
    (overflowLRTake p hnt blank a w hmove hover k hk).length = k * (nt + 1) := by
  unfold overflowLRTake
  rw [List.length_flatten, List.map_ofFn]
  have hrep :
      (List.ofFn (List.length ∘ fun j : Fin k =>
        overflowLRCellArrows p hnt blank a w hmove hover ⟨j.val, by omega⟩)) =
        List.replicate k (nt + 1) := by
    apply List.ext_getElem
    · simp
    · intro i hi _
      simp [Function.comp, overflowLRCellArrows_length]
  rw [hrep, sum_replicate_nat]

theorem overflowLRTake_succ (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length)
    (k : ℕ) (hk : k < w.cells.length) :
    overflowLRTake p hnt blank a w hmove hover (k + 1) (Nat.succ_le_of_lt hk) =
      overflowLRTake p hnt blank a w hmove hover k (Nat.le_of_lt hk) ++
        overflowLRCellArrows p hnt blank a w hmove hover ⟨k, hk⟩ := by
  unfold overflowLRTake
  rw [ofFn_snoc]
  simp [List.flatten_append]

theorem overflowLR_head_succ (k : ℕ) :
    ((1 + k * (nt + 1) : ℕ) : Int) + 1 + (nt : Int) =
      ((1 + (k + 1) * (nt + 1) : ℕ) : Int) := by
  have hnat : 1 + k * (nt + 1) + 1 + nt = 1 + (k + 1) * (nt + 1) := by
    rw [Nat.succ_mul]; omega
  have hcast :
      ((1 + k * (nt + 1) + 1 + nt : ℕ) : Int) =
        ((1 + k * (nt + 1) : ℕ) : Int) + 1 + (nt : Int) := by
    simp [Nat.cast_add, Nat.cast_one]
  rw [← hcast, hnat]

theorem nat_block_add (k n : ℕ) :
    1 + k * (n + 1) + n = (k + 1) * (n + 1) := by
  rw [Nat.succ_mul, add_comm (1 + k * (n + 1)) n, ← add_assoc n 1,
    add_comm (n + 1)]

theorem nat_le_block_succ (k n : ℕ) :
    1 + k * (n + 1) ≤ 1 + (k + 1) * (n + 1) :=
  Nat.add_le_add_left (Nat.mul_le_mul_right (n + 1) (Nat.le_succ k)) 1

theorem nat_sub_succ_pred {n r : ℕ} (hr : r < n) :
    n - r = n - 1 - r + 1 := by
  omega

theorem nat_sub_succ {n r : ℕ} (hr : r < n) :
    n - (r + 1) = n - 1 - r := by
  omega

theorem overflowLR_take_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length)
    (exterior : Int → Phys) (k : ℕ) (hk : k ≤ w.cells.length) :
    ∃ tape : Int → Phys,
      (∀ z, ((1 + k * (nt + 1) : ℕ) : Int) ≤ z →
        tape z = windowTape w exterior z) ∧
      run (program p hnt blank) (fun _ => true)
        (overflowLRTake p hnt blank a w hmove hover k hk)
        (lrStart a w exterior) = some {
          state := .updateLRFlag a (lrArmed w a k)
          head := ((1 + k * (nt + 1) : ℕ) : Int)
          tape := tape } := by
  induction k with
  | zero =>
      refine ⟨windowTape w exterior, fun _ _ => rfl, ?_⟩
      simp [overflowLRTake, lrStart, lrArmed_zero]
  | succ k ih =>
      have hk' : k < w.cells.length := by omega
      have hle : k ≤ w.cells.length := Nat.le_of_lt hk'
      obtain ⟨tape, hagree, hrun⟩ := ih hle
      rw [overflowLRTake_succ p hnt blank a w hmove hover k hk',
        run_append p hnt blank, hrun, Option.bind_some]
      let kk : Fin w.cells.length := ⟨k, hk'⟩
      let c : ScanCfg ns nt :=
        { state := .updateLRFlag a (lrArmed w a k)
          head := ((1 + k * (nt + 1) : ℕ) : Int)
          tape := tape }
      have hflag := agrees_flag w exterior kk tape hagree
      have hbits := agrees_bits w exterior kk tape hagree
      have hcell :=
        cell_run p hnt blank a (lrArmed w a k)
          (tapeOfBit (decide (k = w.head.val))) (tapeOfBit false)
          (lrArmed w a (k + 1)) (tapeOfBit_ne_blank _)
          (updateLR_unsafe_right w a kk hmove hover)
          (cellBits w kk) (cellBits_length w kk) (cellBits_valid w kk)
          c rfl (by simpa [c] using hflag)
          (by
            intro i
            simpa [c, cellBits, List.get_eq_getElem] using hbits i)
      refine ⟨writeBlock (Function.update tape
          ((1 + k * (nt + 1) : ℕ) : Int) (tapeOfBit false))
          (((1 + k * (nt + 1) : ℕ) : Int) + 1)
          (outputBits a (tapeOfBit (decide (k = w.head.val)) = one)
            (cellBits w kk)), ?_, ?_⟩
      · intro z hz
        have hz' : ((1 + k * (nt + 1) : ℕ) : Int) + 1 + (nt : Int) ≤ z := by
          rwa [overflowLR_head_succ (nt := nt) k]
        have hbitsL : (cellBits w kk).length = nt := cellBits_length w kk
        rw [cell_output_agrees (nt := nt) a hnt c (tapeOfBit false)
          (tapeOfBit (decide (k = w.head.val))) (cellBits w kk) hbitsL z
          (by simpa [c] using hz')]
        have hmono : ((1 + k * (nt + 1) : ℕ) : Int) ≤
            ((1 + (k + 1) * (nt + 1) : ℕ) : Int) :=
          Nat.cast_le.mpr (nat_le_block_succ k nt)
        exact hagree z (le_trans hmono hz)
      · apply Eq.trans (by simpa [overflowLRCellArrows, c] using hcell)
        apply congrArg some
        apply cfg_ext'
        · rfl
        · exact overflowLR_head_succ (nt := nt) k
        · rfl

theorem overflowLR_take_nonbranch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length)
    (exterior : Int → Phys) (k : ℕ) (hk : k ≤ w.cells.length) :
    NonbranchPrefix p hnt blank
      (overflowLRTake p hnt blank a w hmove hover k hk)
      (lrStart a w exterior) := by
  induction k with
  | zero => simp [overflowLRTake, NonbranchPrefix]
  | succ k ih =>
      have hk' : k < w.cells.length := by omega
      have hle : k ≤ w.cells.length := Nat.le_of_lt hk'
      rw [overflowLRTake_succ p hnt blank a w hmove hover k hk']
      obtain ⟨tape, hagree, hrun⟩ :=
        overflowLR_take_run p hnt blank a w hmove hover exterior k hle
      apply nonbranchPrefix_append p hnt blank _ _ _
        { state := .updateLRFlag a (lrArmed w a k)
          head := ((1 + k * (nt + 1) : ℕ) : Int)
          tape := tape }
        (ih hle) hrun
      let kk : Fin w.cells.length := ⟨k, hk'⟩
      let c : ScanCfg ns nt :=
        { state := .updateLRFlag a (lrArmed w a k)
          head := ((1 + k * (nt + 1) : ℕ) : Int)
          tape := tape }
      unfold overflowLRCellArrows
      exact cell_nonbranchPrefix p hnt blank a (lrArmed w a k)
        (tapeOfBit (decide (k = w.head.val))) (tapeOfBit false)
        (lrArmed w a (k + 1)) (tapeOfBit_ne_blank _)
        (updateLR_unsafe_right w a kk hmove hover)
        (cellBits w kk) (cellBits_length w kk) (cellBits_valid w kk)
        c rfl (agrees_flag w exterior kk tape hagree)
        (by intro i; simpa [c] using agrees_bits w exterior kk tape hagree i)

def overflowLRInterior (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length) :
    List (ScanArrow p hnt blank) :=
  overflowLRTake p hnt blank a w hmove hover w.cells.length le_rfl

theorem overflowLRInterior_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length) :
    (overflowLRInterior p hnt blank a w hmove hover).length = windowWidth w := by
  simpa [overflowLRInterior, windowWidth] using
    overflowLRTake_length p hnt blank a w hmove hover w.cells.length le_rfl

theorem lrArmed_overflow_right (w : LogicalWindow nt)
    (a : BoundedAction ns nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length) :
    lrArmed w a w.cells.length = true := by
  simp [lrArmed, hmove, hover]

def updateLRFlagOverflowArrow (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) : ScanArrow p hnt blank :=
  deterministicArrow p hnt blank (.updateLRFlag a true) physBlank
    ⟨physBlank, .reject, .stay⟩
    (by simp [deterministicAction])

theorem updateLRFlagOverflowArrow_step (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (a : BoundedAction ns nt)
    (c : ScanCfg ns nt)
    (hstate : c.state = .updateLRFlag a true)
    (hread : c.tape c.head = physBlank) :
    FiniteOneTapeSemantics.step (program p hnt blank) (fun _ => true) c
      (updateLRFlagOverflowArrow p hnt blank a) = some {
        state := .reject
        head := c.head
        tape := c.tape } := by
  let act : Action (State ns nt) Phys := ⟨physBlank, .reject, .stay⟩
  have hact : deterministicAction p hnt blank (.updateLRFlag a true) physBlank =
      some act := by simp [act, deterministicAction]
  have harrow : updateLRFlagOverflowArrow p hnt blank a =
      deterministicArrow p hnt blank (.updateLRFlag a true) physBlank act hact :=
    Subtype.ext rfl
  rw [harrow]
  have htape : writtenTape c physBlank = c.tape := by
    simpa [hread] using writtenTape_id (c := c)
  have hs := deterministicArrow_step p hnt blank c (.updateLRFlag a true)
    physBlank act hstate hread hact
  simpa [act, htape, moveHead] using hs

theorem overflowLR_interior_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length)
    (exterior : Int → Phys) :
    ∃ tape : Int → Phys,
      tape (windowWidth w + 1 : Int) = physBlank ∧
      run (program p hnt blank) (fun _ => true)
        (overflowLRInterior p hnt blank a w hmove hover)
        (lrStart a w exterior) = some {
          state := .updateLRFlag a true
          head := (windowWidth w + 1 : Int)
          tape := tape } := by
  obtain ⟨tape, hagree, hrun⟩ :=
    overflowLR_take_run p hnt blank a w hmove hover exterior
      w.cells.length le_rfl
  have hhead : ((1 + w.cells.length * (nt + 1) : ℕ) : Int) =
      (windowWidth w + 1 : Int) := by
    simp [windowWidth, Nat.cast_add, Nat.cast_one, add_comm]
  refine ⟨tape, ?_, ?_⟩
  · rw [← hhead]
    have hread := hagree ((1 + w.cells.length * (nt + 1) : ℕ) : Int) le_rfl
    rw [hread, hhead]
    exact windowTape_right w exterior
  · simpa [overflowLRInterior, lrArmed_overflow_right w a hmove hover, hhead] using hrun

def overflowLRReject (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length) :
    List (ScanArrow p hnt blank) :=
  overflowLRInterior p hnt blank a w hmove hover ++
    [updateLRFlagOverflowArrow p hnt blank a]

theorem overflowLRReject_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length) :
    (overflowLRReject p hnt blank a w hmove hover).length = windowWidth w + 1 := by
  simp [overflowLRReject, overflowLRInterior_length]

theorem overflowLRReject_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length)
    (exterior : Int → Phys) :
    ∃ tape : Int → Phys,
      run (program p hnt blank) (fun _ => true)
        (overflowLRReject p hnt blank a w hmove hover)
        (lrStart a w exterior) = some {
          state := .reject
          head := (windowWidth w + 1 : Int)
          tape := tape } := by
  obtain ⟨tape, hblank, hrun⟩ :=
    overflowLR_interior_run p hnt blank a w hmove hover exterior
  refine ⟨tape, ?_⟩
  rw [overflowLRReject, run_append p hnt blank, hrun, Option.bind_some, run_cons,
    updateLRFlagOverflowArrow_step p hnt blank a _ rfl hblank, Option.bind_some, run_nil]

theorem overflowLRReject_nonbranch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length)
    (exterior : Int → Phys) :
    NonbranchPrefix p hnt blank
      (overflowLRReject p hnt blank a w hmove hover)
      (lrStart a w exterior) := by
  obtain ⟨tape, hblank, hrun⟩ :=
    overflowLR_interior_run p hnt blank a w hmove hover exterior
  unfold overflowLRReject
  apply nonbranchPrefix_append p hnt blank _ _ _
    { state := .updateLRFlag a true
      head := (windowWidth w + 1 : Int)
      tape := tape }
    (overflowLR_take_nonbranch p hnt blank a w hmove hover exterior
      w.cells.length le_rfl)
    (by simpa [overflowLRInterior] using hrun)
  refine ⟨?_, _, updateLRFlagOverflowArrow_step p hnt blank a _ rfl hblank, trivial⟩
  intro q read
  simp

def unsafeRightPrefix (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt)
    (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length) :
    List (ScanArrow p hnt blank) :=
  returnLeftArrows p hnt blank q a w ++
    overflowLRReject p hnt blank a w hmove hover

theorem unsafeRightPrefix_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt)
    (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length) :
    (unsafeRightPrefix p hnt blank q a w hmove hover).length =
      2 * windowWidth w + 3 := by
  simp [unsafeRightPrefix, overflowLRReject_length]
  omega

theorem unsafeRightPrefix_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt)
    (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length)
    (exterior : Int → Phys) :
    ∃ tape : Int → Phys,
      run (program p hnt blank) (fun _ => true)
        (unsafeRightPrefix p hnt blank q a w hmove hover)
        (startConfig q a w exterior) = some {
          state := .reject
          head := (windowWidth w + 1 : Int)
          tape := tape } := by
  obtain ⟨tape, hrun⟩ := overflowLRReject_run p hnt blank a w hmove hover exterior
  refine ⟨tape, ?_⟩
  rw [unsafeRightPrefix, run_append p hnt blank, returnLeft_run, Option.bind_some]
  simpa [lrStart] using hrun

theorem unsafeRightPrefix_nonbranch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt)
    (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length)
    (exterior : Int → Phys) :
    NonbranchPrefix p hnt blank
      (unsafeRightPrefix p hnt blank q a w hmove hover)
      (startConfig q a w exterior) := by
  obtain ⟨tape, hrun⟩ := overflowLRReject_run p hnt blank a w hmove hover exterior
  unfold unsafeRightPrefix
  apply nonbranchPrefix_append p hnt blank _ _ _ (lrStart a w exterior)
    (returnLeft_nonbranchPrefix p hnt blank q a w exterior)
    (returnLeft_run p hnt blank q a w exterior)
  simpa [lrStart] using
    overflowLRReject_nonbranch p hnt blank a w hmove hover exterior

theorem unsafe_right_no_suffix_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt)
    (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length)
    (exterior : Int → Phys) (raw : List (ScanArrow p hnt blank))
    (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw
      (startConfig q a w exterior) = some out)
    (hlen : raw.length = 3 * windowWidth w + 4) : False := by
  have hpreLen : (unsafeRightPrefix p hnt blank q a w hmove hover).length ≤
      raw.length := by
    rw [unsafeRightPrefix_length, hlen]
    have := windowWidth_pos w
    omega
  obtain ⟨tail, boundary, heq, hpre, htail⟩ :=
    nonbranchPrefix_split_successful_run p hnt blank
      (unsafeRightPrefix p hnt blank q a w hmove hover) raw
      (startConfig q a w exterior) out
      (unsafeRightPrefix_nonbranch p hnt blank q a w hmove hover exterior)
      hrun hpreLen
  obtain ⟨tape, hfwd⟩ :=
    unsafeRightPrefix_run p hnt blank q a w hmove hover exterior
  have hb : boundary = {
      state := .reject
      head := (windowWidth w + 1 : Int)
      tape := tape } := Option.some.inj (hpre.symm.trans hfwd)
  subst boundary
  have htl : tail ≠ [] := by
    intro hnil
    subst tail
    have he := congrArg List.length heq
    simp only [List.length_append, List.length_nil, Nat.add_zero] at he
    rw [unsafeRightPrefix_length, hlen] at he
    have := windowWidth_pos w
    omega
  have hnone := reject_run_nonempty p hnt blank
    { state := .reject, head := (windowWidth w + 1 : Int), tape := tape }
    tail rfl htl
  simp [hnone] at htail

/-! ## Unsafe left: LR is safe; RL rejects at the left delimiter -/

theorem updateRL_unsafe_left (u : LogicalWindow nt)
    (a : BoundedAction ns nt) (k : Fin u.cells.length)
    (hmove : a.move = .left) (hhead : u.head.val = 0) :
    updateRL a false (tapeOfBit (decide (k.val = u.head.val))) =
      some (tapeOfBit false, decide (k.val = u.head.val)) := by
  have hxvalid : validBit (tapeOfBit (decide (k.val = u.head.val))) = true :=
    validBit_tapeOfBit _
  unfold updateRL
  simp only [hxvalid, hmove, ite_true]
  by_cases hk : k.val = u.head.val
  · simp [hk, tapeOfBit, one, zero]
  · simp [hk, tapeOfBit, one, zero]

def overflowRLCellArrows (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hmove : a.move = .left) (hhead : u.head.val = 0)
    (k : Fin u.cells.length) : List (ScanArrow p hnt blank) :=
  ULogSourceObliviousRLCellExecution.cellArrows p hnt blank a false
    (tapeOfBit (decide (k.val = u.head.val))) (tapeOfBit false)
    (decide (k.val = u.head.val))
    (updateRL_unsafe_left u a k hmove hhead)
    (cellBits u k) (cellBits_length u k) (cellBits_valid u k)
    (cellBits_ne_blank u k)

@[simp] theorem overflowRLCellArrows_length (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (a : BoundedAction ns nt)
    (u : LogicalWindow nt)
    (hmove : a.move = .left) (hhead : u.head.val = 0)
    (k : Fin u.cells.length) :
    (overflowRLCellArrows p hnt blank a u hmove hhead k).length = nt + 1 := by
  simp [overflowRLCellArrows]

def overflowRLTake (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hmove : a.move = .left) (hhead : u.head.val = 0)
    (r : ℕ) (hr : r ≤ u.cells.length) : List (ScanArrow p hnt blank) :=
  (List.ofFn fun j : Fin r =>
    overflowRLCellArrows p hnt blank a u hmove hhead
      ⟨u.cells.length - 1 - j.val, by omega⟩).flatten

theorem overflowRLTake_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hmove : a.move = .left) (hhead : u.head.val = 0)
    (r : ℕ) (hr : r ≤ u.cells.length) :
    (overflowRLTake p hnt blank a u hmove hhead r hr).length = r * (nt + 1) := by
  unfold overflowRLTake
  rw [List.length_flatten, List.map_ofFn]
  have hrep :
      (List.ofFn (List.length ∘ fun j : Fin r =>
        overflowRLCellArrows p hnt blank a u hmove hhead
          ⟨u.cells.length - 1 - j.val, by omega⟩)) =
        List.replicate r (nt + 1) := by
    apply List.ext_getElem
    · simp
    · intro i hi _
      simp [Function.comp, overflowRLCellArrows_length]
  rw [hrep, sum_replicate_nat]

theorem overflowRLTake_succ (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hmove : a.move = .left) (hhead : u.head.val = 0)
    (r : ℕ) (hr : r < u.cells.length) :
    overflowRLTake p hnt blank a u hmove hhead (r + 1) (Nat.succ_le_of_lt hr) =
      overflowRLTake p hnt blank a u hmove hhead r (Nat.le_of_lt hr) ++
        overflowRLCellArrows p hnt blank a u hmove hhead
          ⟨u.cells.length - 1 - r, by omega⟩ := by
  unfold overflowRLTake
  rw [ofFn_snoc]
  simp [List.flatten_append]

theorem overflowRL_agree_flag (u : LogicalWindow nt) (exterior : Int → Phys)
    (k : Fin u.cells.length) (tape : Int → Phys)
    (h : ∀ z, z ≤ ((1 + k.val * (nt + 1) + nt : ℕ) : Int) →
      tape z = windowTape u exterior z) :
    tape (rlFlagInt nt k.val) =
      tapeOfBit (decide (k.val = u.head.val)) := by
  have hlo : rlFlagInt nt k.val ≤ ((1 + k.val * (nt + 1) + nt : ℕ) : Int) := by
    simp only [rlFlagInt, Nat.cast_add, Nat.cast_one]
    omega
  exact (h _ hlo).trans (by
    simpa [rlFlagInt] using windowTape_cell_flag u exterior k)

theorem overflowRL_agree_bits (u : LogicalWindow nt) (exterior : Int → Phys)
    (k : Fin u.cells.length) (tape : Int → Phys)
    (h : ∀ z, z ≤ ((1 + k.val * (nt + 1) + nt : ℕ) : Int) →
      tape z = windowTape u exterior z) :
    ∀ i : Fin nt,
      tape (((2 + k.val * (nt + 1) : ℕ) : Int) + (i.val : Int)) =
        (cellBits u k).get ⟨i.val, by simp [cellBits, encodeOneHot_length]⟩ := by
  intro i
  have hcoord := rl_base_bit nt k.val i
  have hlo : ((2 + k.val * (nt + 1) : ℕ) : Int) + (i.val : Int) ≤
      ((1 + k.val * (nt + 1) + nt : ℕ) : Int) := by
    simp [Nat.cast_add, Nat.cast_one]; omega
  exact (h _ hlo).trans (by
    rw [hcoord]
    simpa [cellBits, List.get_eq_getElem, List.getElem_map] using
      windowTape_cell_bit u exterior k i)

theorem overflowRL_take_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hmove : a.move = .left) (hhead : u.head.val = 0)
    (exterior : Int → Phys) (r : ℕ) (hr : r ≤ u.cells.length) :
    ∃ tape : Int → Phys,
      (∀ z, z ≤ (((u.cells.length - r) * (nt + 1) : ℕ) : Int) →
        tape z = windowTape u exterior z) ∧
      run (program p hnt blank) (fun _ => true)
        (overflowRLTake p hnt blank a u hmove hhead r hr)
        (rlStart hnt a u exterior) = some {
          state := .skipRL a (decide (r = u.cells.length)) ⟨nt - 1, by omega⟩
          head := (((u.cells.length - r) * (nt + 1) : ℕ) : Int)
          tape := tape } := by
  induction r with
  | zero =>
      refine ⟨windowTape u exterior, fun _ _ => rfl, ?_⟩
      simp only [overflowRLTake, List.ofFn_zero, List.flatten_nil, run_nil]
      apply congrArg some
      apply cfg_ext'
      · have hne : 0 ≠ u.cells.length := Nat.ne_of_lt (window_cells_pos u)
        simp [rlStart, hne]
      · have : ((u.cells.length * (nt + 1) : ℕ) : Int) = (windowWidth u : Int) := by
          simp [windowWidth]
        simp [rlStart, this]
      · rfl
  | succ r ih =>
      have hr' : r < u.cells.length := by omega
      have hle : r ≤ u.cells.length := Nat.le_of_lt hr'
      obtain ⟨tape, hagree, hrun⟩ := ih hle
      rw [overflowRLTake_succ p hnt blank a u hmove hhead r hr',
        run_append p hnt blank, hrun, Option.bind_some]
      let k : Fin u.cells.length := ⟨u.cells.length - 1 - r, by omega⟩
      have hidx : u.cells.length - r = k.val + 1 :=
        nat_sub_succ_pred hr'
      have hidx2 : u.cells.length - (r + 1) = k.val :=
        nat_sub_succ hr'
      have hrne : r ≠ u.cells.length := Nat.ne_of_lt hr'
      let c : ScanCfg ns nt :=
        { state := .skipRL a false ⟨nt - 1, by omega⟩
          head := (((u.cells.length - r) * (nt + 1) : ℕ) : Int)
          tape := tape }
      have hcfg :
          ({ state := .skipRL a (decide (r = u.cells.length)) ⟨nt - 1, by omega⟩
             head := (((u.cells.length - r) * (nt + 1) : ℕ) : Int)
             tape := tape } : ScanCfg ns nt) = c := by
        apply cfg_ext'
        · simp [c, hrne]
        · rfl
        · rfl
      rw [hcfg]
      have hheadC : c.head =
          ((2 + k.val * (nt + 1) : ℕ) : Int) + (nt : Int) - 1 := by
        simp only [c]
        have hbase := rl_base_head nt k.val
        rw [hidx]
        exact hbase.symm
      have hup : ((1 + k.val * (nt + 1) + nt : ℕ) : Int) =
          (((u.cells.length - r) * (nt + 1) : ℕ) : Int) := by
        have hnat : 1 + k.val * (nt + 1) + nt = (k.val + 1) * (nt + 1) :=
          nat_block_add k.val nt
        rw [hnat, hidx]
      have hagree' : ∀ z, z ≤ ((1 + k.val * (nt + 1) + nt : ℕ) : Int) →
          tape z = windowTape u exterior z := by
        intro z hz
        apply hagree z
        rw [← hup]
        exact hz
      have hcell :=
        ULogSourceObliviousRLCellExecution.cell_run p hnt blank a false
          (tapeOfBit (decide (k.val = u.head.val))) (tapeOfBit false)
          (decide (k.val = u.head.val))
          (updateRL_unsafe_left u a k hmove hhead)
          (cellBits u k) (cellBits_length u k) (cellBits_valid u k)
          (cellBits_ne_blank u k) c rfl
          ((2 + k.val * (nt + 1) : ℕ) : Int) hheadC
          (by
            intro i
            simpa [c] using overflowRL_agree_bits u exterior k tape hagree' i)
          (by
            have hf := overflowRL_agree_flag u exterior k tape hagree'
            have hcoord := (rl_base_flag nt k.val).symm
            simpa [c, hcoord] using hf)
      have harmed' :
          decide (k.val = u.head.val) = decide (r + 1 = u.cells.length) := by
        have : (r + 1 = u.cells.length) ↔ (k.val = 0) := by
          change (r + 1 = u.cells.length) ↔ (u.cells.length - 1 - r = 0)
          constructor <;> intro h <;> omega
        simp [hhead, this]
      have hend := rl_base_end nt k.val
      refine ⟨Function.update tape (((2 + k.val * (nt + 1) : ℕ) : Int) - 1)
          (tapeOfBit false), ?_, ?_⟩
      · intro z hz
        have hbound :
            (((u.cells.length - (r + 1)) * (nt + 1) : ℕ) : Int) =
              ((2 + k.val * (nt + 1) : ℕ) : Int) - 2 := by
          rw [hidx2]
          exact hend.symm
        have hne : z ≠ ((2 + k.val * (nt + 1) : ℕ) : Int) - 1 := by
          intro heq
          have hle' : z ≤ ((2 + k.val * (nt + 1) : ℕ) : Int) - 2 := by
            rw [← hbound]
            exact hz
          have hlt : ((2 + k.val * (nt + 1) : ℕ) : Int) - 2 <
              ((2 + k.val * (nt + 1) : ℕ) : Int) - 1 := by omega
          rw [heq] at hle'
          exact not_le_of_gt hlt hle'
        rw [Function.update_of_ne hne]
        apply hagree z
        have hmono :
            (((u.cells.length - (r + 1)) * (nt + 1) : ℕ) : Int) ≤
              (((u.cells.length - r) * (nt + 1) : ℕ) : Int) :=
          Nat.cast_le.mpr (Nat.mul_le_mul_right (nt + 1)
            (by omega))
        exact le_trans hz hmono
      · have harrows :
            overflowRLCellArrows p hnt blank a u hmove hhead
              ⟨u.cells.length - 1 - r, by omega⟩ =
              overflowRLCellArrows p hnt blank a u hmove hhead k :=
          rfl
        rw [harrows, overflowRLCellArrows, hcell]
        apply congrArg some
        apply cfg_ext'
        · simpa using harmed'
        · rw [hidx2]
          exact hend
        · rfl

theorem overflowRL_take_nonbranch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hmove : a.move = .left) (hhead : u.head.val = 0)
    (exterior : Int → Phys) (r : ℕ) (hr : r ≤ u.cells.length) :
    NonbranchPrefix p hnt blank
      (overflowRLTake p hnt blank a u hmove hhead r hr)
      (rlStart hnt a u exterior) := by
  induction r with
  | zero => simp [overflowRLTake, NonbranchPrefix]
  | succ r ih =>
      have hr' : r < u.cells.length := by omega
      have hle : r ≤ u.cells.length := Nat.le_of_lt hr'
      rw [overflowRLTake_succ p hnt blank a u hmove hhead r hr']
      obtain ⟨tape, hagree, hrun⟩ :=
        overflowRL_take_run p hnt blank a u hmove hhead exterior r hle
      have hrne : r ≠ u.cells.length := Nat.ne_of_lt hr'
      apply nonbranchPrefix_append p hnt blank _ _ _
        { state := .skipRL a false ⟨nt - 1, by omega⟩
          head := (((u.cells.length - r) * (nt + 1) : ℕ) : Int)
          tape := tape }
        (ih hle)
        (by simpa [hrne] using hrun)
      let k : Fin u.cells.length := ⟨u.cells.length - 1 - r, by omega⟩
      have hidx : u.cells.length - r = k.val + 1 :=
        nat_sub_succ_pred hr'
      let c : ScanCfg ns nt :=
        { state := .skipRL a false ⟨nt - 1, by omega⟩
          head := (((u.cells.length - r) * (nt + 1) : ℕ) : Int)
          tape := tape }
      have hheadC : c.head =
          ((2 + k.val * (nt + 1) : ℕ) : Int) + (nt : Int) - 1 := by
        simp only [c]
        have hbase := rl_base_head nt k.val
        rw [hidx]
        exact hbase.symm
      have hup : ((1 + k.val * (nt + 1) + nt : ℕ) : Int) =
          (((u.cells.length - r) * (nt + 1) : ℕ) : Int) := by
        have hnat : 1 + k.val * (nt + 1) + nt = (k.val + 1) * (nt + 1) :=
          nat_block_add k.val nt
        rw [hnat, hidx]
      have hagree' : ∀ z, z ≤ ((1 + k.val * (nt + 1) + nt : ℕ) : Int) →
          tape z = windowTape u exterior z := by
        intro z hz
        apply hagree z
        rw [← hup]
        exact hz
      unfold overflowRLCellArrows
      exact ULogSourceObliviousRLCellExecution.cell_nonbranchPrefix p hnt blank a
        false (tapeOfBit (decide (k.val = u.head.val))) (tapeOfBit false)
        (decide (k.val = u.head.val))
        (updateRL_unsafe_left u a k hmove hhead)
        (cellBits u k) (cellBits_length u k) (cellBits_valid u k)
        (cellBits_ne_blank u k) c rfl
        ((2 + k.val * (nt + 1) : ℕ) : Int) hheadC
        (by intro i; simpa [c] using overflowRL_agree_bits u exterior k tape hagree' i)
        (by
          have hf := overflowRL_agree_flag u exterior k tape hagree'
          have hcoord := (rl_base_flag nt k.val).symm
          simpa [c, hcoord] using hf)

def overflowRLInterior (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hmove : a.move = .left) (hhead : u.head.val = 0) :
    List (ScanArrow p hnt blank) :=
  overflowRLTake p hnt blank a u hmove hhead u.cells.length le_rfl

theorem overflowRLInterior_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hmove : a.move = .left) (hhead : u.head.val = 0) :
    (overflowRLInterior p hnt blank a u hmove hhead).length = windowWidth u := by
  simpa [overflowRLInterior, windowWidth] using
    overflowRLTake_length p hnt blank a u hmove hhead u.cells.length le_rfl

theorem overflowRL_interior_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hmove : a.move = .left) (hhead : u.head.val = 0)
    (exterior : Int → Phys) :
    ∃ tape : Int → Phys,
      tape (0 : Int) = physBlank ∧
      run (program p hnt blank) (fun _ => true)
        (overflowRLInterior p hnt blank a u hmove hhead)
        (rlStart hnt a u exterior) = some {
          state := .skipRL a true ⟨nt - 1, by omega⟩
          head := (0 : Int)
          tape := tape } := by
  obtain ⟨tape, hagree, hrun⟩ :=
    overflowRL_take_run p hnt blank a u hmove hhead exterior
      u.cells.length le_rfl
  refine ⟨tape, ?_, ?_⟩
  · exact (hagree 0 (by simp)).trans (windowTape_left u exterior)
  · simpa [overflowRLInterior] using hrun

def skipRLOverflowArrow (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) : ScanArrow p hnt blank :=
  deterministicArrow p hnt blank (.skipRL a true ⟨nt - 1, by omega⟩) physBlank
    ⟨physBlank, .reject, .stay⟩
    (by simp [deterministicAction])

theorem skipRLOverflowArrow_step (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (a : BoundedAction ns nt)
    (c : ScanCfg ns nt)
    (hstate : c.state = .skipRL a true ⟨nt - 1, by omega⟩)
    (hread : c.tape c.head = physBlank) :
    FiniteOneTapeSemantics.step (program p hnt blank) (fun _ => true) c
      (skipRLOverflowArrow p hnt blank a) = some {
        state := .reject
        head := c.head
        tape := c.tape } := by
  let act : Action (State ns nt) Phys := ⟨physBlank, .reject, .stay⟩
  have hact : deterministicAction p hnt blank
      (.skipRL a true ⟨nt - 1, by omega⟩) physBlank = some act := by
    simp [act, deterministicAction]
  have harrow : skipRLOverflowArrow p hnt blank a =
      deterministicArrow p hnt blank
        (.skipRL a true ⟨nt - 1, by omega⟩) physBlank act hact :=
    Subtype.ext rfl
  rw [harrow]
  have htape : writtenTape c physBlank = c.tape := by
    simpa [hread] using writtenTape_id (c := c)
  have hs := deterministicArrow_step p hnt blank c
    (.skipRL a true ⟨nt - 1, by omega⟩) physBlank act hstate hread hact
  simpa [act, htape, moveHead] using hs

def overflowRLReject (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hmove : a.move = .left) (hhead : u.head.val = 0) :
    List (ScanArrow p hnt blank) :=
  overflowRLInterior p hnt blank a u hmove hhead ++
    [skipRLOverflowArrow p hnt blank a]

theorem overflowRLReject_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hmove : a.move = .left) (hhead : u.head.val = 0) :
    (overflowRLReject p hnt blank a u hmove hhead).length = windowWidth u + 1 := by
  simp [overflowRLReject, overflowRLInterior_length]

theorem overflowRLReject_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hmove : a.move = .left) (hhead : u.head.val = 0)
    (exterior : Int → Phys) :
    ∃ tape : Int → Phys,
      run (program p hnt blank) (fun _ => true)
        (overflowRLReject p hnt blank a u hmove hhead)
        (rlStart hnt a u exterior) = some {
          state := .reject
          head := (0 : Int)
          tape := tape } := by
  obtain ⟨tape, hblank, hrun⟩ :=
    overflowRL_interior_run p hnt blank a u hmove hhead exterior
  refine ⟨tape, ?_⟩
  rw [overflowRLReject, run_append p hnt blank, hrun, Option.bind_some, run_cons,
    skipRLOverflowArrow_step p hnt blank a _ rfl hblank, Option.bind_some, run_nil]

theorem overflowRLReject_nonbranch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hmove : a.move = .left) (hhead : u.head.val = 0)
    (exterior : Int → Phys) :
    NonbranchPrefix p hnt blank
      (overflowRLReject p hnt blank a u hmove hhead)
      (rlStart hnt a u exterior) := by
  obtain ⟨tape, hblank, hrun⟩ :=
    overflowRL_interior_run p hnt blank a u hmove hhead exterior
  unfold overflowRLReject
  apply nonbranchPrefix_append p hnt blank _ _ _
    { state := .skipRL a true ⟨nt - 1, by omega⟩
      head := (0 : Int)
      tape := tape }
    (overflowRL_take_nonbranch p hnt blank a u hmove hhead exterior
      u.cells.length le_rfl)
    (by simpa [overflowRLInterior] using hrun)
  refine ⟨?_, _, skipRLOverflowArrow_step p hnt blank a _ rfl hblank, trivial⟩
  intro q read
  simp

theorem lrWindow_head_of_left (w : LogicalWindow nt)
    (a : BoundedAction ns nt) (hleft : a.move = .left) :
    (lrWindow w a (vacuous_right_of_left w a hleft)).head.val = w.head.val :=
  lrWindow_head_not_right w a (vacuous_right_of_left w a hleft) (by
    intro hm
    have : False := by rw [hleft] at hm; cases hm
    exact this.elim)

def unsafeLeftPrefix (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt)
    (w : LogicalWindow nt) (hmove : a.move = .left) (hhd : w.head.val = 0) :
    List (ScanArrow p hnt blank) :=
  (returnLeftArrows p hnt blank q a w ++
    lrWindowArrows p hnt blank a w (vacuous_right_of_left w a hmove)) ++
    overflowRLReject p hnt blank a
      (lrWindow w a (vacuous_right_of_left w a hmove)) hmove
      (by simpa using lrWindow_head_of_left w a hmove ▸ hhd)

theorem unsafeLeftPrefix_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt)
    (w : LogicalWindow nt) (hmove : a.move = .left) (hhd : w.head.val = 0) :
    (unsafeLeftPrefix p hnt blank q a w hmove hhd).length =
      3 * windowWidth w + 4 := by
  simp [unsafeLeftPrefix, overflowRLReject_length, lrWindowArrows_length,
    returnLeftArrows_length, lrWindow_windowWidth]
  omega

theorem unsafeLeftPrefix_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt)
    (w : LogicalWindow nt) (hmove : a.move = .left) (hhd : w.head.val = 0)
    (exterior : Int → Phys) :
    ∃ tape : Int → Phys,
      run (program p hnt blank) (fun _ => true)
        (unsafeLeftPrefix p hnt blank q a w hmove hhd)
        (startConfig q a w exterior) = some {
          state := .reject
          head := (0 : Int)
          tape := tape } := by
  have hright := vacuous_right_of_left w a hmove
  have hlr := lr_window_run p hnt blank a w hright exterior
  have hret := returnLeft_run p hnt blank q a w exterior
  have hhead0 : (lrWindow w a hright).head.val = 0 := by
    simpa using lrWindow_head_of_left w a hmove ▸ hhd
  obtain ⟨tape, hrl⟩ :=
    overflowRLReject_run p hnt blank a (lrWindow w a hright) hmove hhead0 exterior
  refine ⟨tape, ?_⟩
  rw [unsafeLeftPrefix, run_append p hnt blank, run_append p hnt blank, hret,
    Option.bind_some]
  have hmid :
      run (program p hnt blank) (fun _ => true)
        (lrWindowArrows p hnt blank a w hright)
        { state := .updateLRFlag a false, head := 1,
          tape := windowTape w exterior } =
        some (rlStart hnt a (lrWindow w a hright) exterior) := by
    simpa [lrStart, rlStart, lrWindow_windowWidth] using hlr
  rw [hmid, Option.bind_some]
  exact hrl

theorem unsafeLeftPrefix_nonbranch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt)
    (w : LogicalWindow nt) (hmove : a.move = .left) (hhd : w.head.val = 0)
    (exterior : Int → Phys) :
    NonbranchPrefix p hnt blank
      (unsafeLeftPrefix p hnt blank q a w hmove hhd)
      (startConfig q a w exterior) := by
  have hright := vacuous_right_of_left w a hmove
  have hhead0 : (lrWindow w a hright).head.val = 0 := by
    simpa using lrWindow_head_of_left w a hmove ▸ hhd
  unfold unsafeLeftPrefix
  apply nonbranchPrefix_append p hnt blank _ _ _
    (rlStart hnt a (lrWindow w a hright) exterior)
  · apply nonbranchPrefix_append p hnt blank _ _ _ (lrStart a w exterior)
      (returnLeft_nonbranchPrefix p hnt blank q a w exterior)
      (returnLeft_run p hnt blank q a w exterior)
    exact lr_window_nonbranch p hnt blank a w hright exterior
  · rw [run_append p hnt blank, returnLeft_run, Option.bind_some]
    simpa [lrStart, rlStart, lrWindow_windowWidth] using
      lr_window_run p hnt blank a w hright exterior
  · exact overflowRLReject_nonbranch p hnt blank a (lrWindow w a hright)
      hmove hhead0 exterior

theorem unsafe_left_suffix_reject (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt)
    (w : LogicalWindow nt) (hmove : a.move = .left) (hhd : w.head.val = 0)
    (exterior : Int → Phys) (raw : List (ScanArrow p hnt blank))
    (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw
      (startConfig q a w exterior) = some out)
    (hlen : raw.length = 3 * windowWidth w + 4) :
    out.state = State.reject := by
  have hforced := nonbranchPrefix_forced p hnt blank _ _
    (unsafeLeftPrefix_nonbranch p hnt blank q a w hmove hhd exterior)
  obtain ⟨heq, hprefix⟩ := forcedPrefix_unique_successful_run
    (program p hnt blank) (fun _ => true) _ raw _ out hforced hrun
    (by rw [unsafeLeftPrefix_length, hlen])
  obtain ⟨tape, hfwd⟩ :=
    unsafeLeftPrefix_run p hnt blank q a w hmove hhd exterior
  have hout : out = {
      state := .reject
      head := (0 : Int)
      tape := tape } := Option.some.inj (hprefix.symm.trans hfwd)
  simp [hout]

theorem reject_ne_atLeft {r : Fin ns} :
    State.reject ≠ State.atLeft (ns := ns) (nt := nt) r := by
  intro h
  cases h

end PakFixedPolyomino.ULogSourceObliviousOverflowExecution
