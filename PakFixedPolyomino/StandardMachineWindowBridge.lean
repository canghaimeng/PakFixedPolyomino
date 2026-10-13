import PakFixedPolyomino.StandardMachineZipperBridge
import PakFixedPolyomino.StandardMachineRunResources
import PakFixedPolyomino.ULogSourceObliviousLogicalRuns

/-! # Materialized windows for ordinary one-cell source runs

The window consists of actual tape letters at a fixed integer origin.
Its head index is the translated ordinary physical head. The eventual source
bridge must derive fitting from actual successful-prefix geometry, rather
than assume a space certificate as part of the standard source class.
-/

namespace PakFixedPolyomino.StandardMachineWindowBridge

open StandardNondeterministicMachine
open StandardMachineZipperBridge (toBounded toBoundedAction slotIndex)
open ULogCompiler ULogSourceObliviousWindow
open FiniteOneTapeSemantics (moveHead writtenTape)
open FiniteOneTapeProgram (Action)

variable {ns nt : ℕ}

def HeadIn (origin : Int) (size : ℕ) (c : Configuration ns nt) : Prop :=
  0 ≤ c.head - origin ∧ c.head - origin < (size : Int)

def window (origin : Int) (size : ℕ) (c : Configuration ns nt)
    (h : HeadIn origin size c) : LogicalWindow nt where
  cells := List.ofFn (fun i : Fin size => c.tape (origin + i.val))
  head := ⟨(c.head - origin).toNat, by
    simp only [List.length_ofFn]
    exact Int.toNat_lt h.1 |>.mpr h.2⟩

@[simp] theorem window_length (origin : Int) (size : ℕ) (c : Configuration ns nt)
    (h : HeadIn origin size c) : (window origin size c h).cells.length = size := by
  simp [window]

theorem window_head (origin : Int) (size : ℕ) (c : Configuration ns nt)
    (h : HeadIn origin size c) :
    origin + ((window origin size c h).head.val : Int) = c.head := by
  simp only [window, Int.toNat_of_nonneg h.1]
  omega

theorem window_read (origin : Int) (size : ℕ) (c : Configuration ns nt)
    (h : HeadIn origin size c) :
    (window origin size c h).cells.get (window origin size c h).head =
      c.tape c.head := by
  simp only [window, List.get_ofFn]
  congr 1
  change origin + ((c.head - origin).toNat : Int) = c.head
  have hc := Int.toNat_of_nonneg h.1
  omega

def actionConfig (a : Action (Fin ns) (Fin nt)) (c : Configuration ns nt) :
    Configuration ns nt where
  state := a.target
  head := moveHead a.move c.head
  tape := writtenTape c a.write

theorem window_written (origin : Int) (size : ℕ) (c : Configuration ns nt)
    (a : Action (Fin ns) (Fin nt)) (h : HeadIn origin size c)
    (hnext : HeadIn origin size (actionConfig a c)) :
    (window origin size c h).cells.set (window origin size c h).head a.write =
      (window origin size (actionConfig a c) hnext).cells := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hcast : ((c.head - origin).toNat : Int) = c.head - origin :=
      Int.toNat_of_nonneg h.1
    have hiff : i = (c.head - origin).toNat ↔ origin + (i : Int) = c.head := by
      omega
    simp only [window, List.getElem_set, List.getElem_ofFn, actionConfig,
      writtenTape, Function.update_apply]
    by_cases heq : i = (c.head - origin).toNat
    · rw [if_pos heq.symm, if_pos (hiff.mp heq)]
    · rw [if_neg (Ne.symm heq), if_neg (mt hiff.mpr heq)]

theorem window_move (origin : Int) (size : ℕ) (c : Configuration ns nt)
    (a : Action (Fin ns) (Fin nt)) (h : HeadIn origin size c)
    (hnext : HeadIn origin size (actionConfig a c)) :
    moveIndex a.move (window origin size c h).head =
      some ⟨((actionConfig a c).head - origin).toNat, by
        rw [window_length]
        exact Int.toNat_lt hnext.1 |>.mpr hnext.2⟩ := by
  have hcast : ((c.head - origin).toNat : Int) = c.head - origin :=
    Int.toNat_of_nonneg h.1
  have hncast : (((actionConfig a c).head - origin).toNat : Int) =
      (actionConfig a c).head - origin := Int.toNat_of_nonneg hnext.1
  cases hm : a.move with
  | stay =>
      simp only [moveIndex_stay]
      congr 1
      apply Fin.ext
      simp only [window, actionConfig, moveHead, hm]
  | right =>
      have hbval : (c.head - origin).toNat + 1 < size := by
        have hh := hnext.2
        simp only [actionConfig, moveHead, hm] at hh
        omega
      have hb : (window origin size c h).head.val + 1 <
          (window origin size c h).cells.length := by simpa [window] using hbval
      rw [moveIndex_right _ hb]
      congr 1
      apply Fin.ext
      simp only [actionConfig, moveHead, hm] at hncast
      change (c.head - origin).toNat + 1 = ((actionConfig a c).head - origin).toNat
      simp only [actionConfig, hm, moveHead]
      omega
  | left =>
      have hb : 0 < (window origin size c h).head.val := by
        change 0 < (c.head - origin).toNat
        have hh := hnext.1
        simp only [actionConfig, moveHead, hm] at hh
        omega
      rw [moveIndex_left _ hb]
      congr 1
      apply Fin.ext
      simp only [actionConfig, moveHead, hm] at hncast
      change (c.head - origin).toNat - 1 = ((actionConfig a c).head - origin).toNat
      simp only [actionConfig, hm, moveHead]
      omega

theorem window_ext (a b : LogicalWindow nt)
    (hc : a.cells = b.cells) (hh : a.head.val = b.head.val) : a = b := by
  cases a with
  | mk cells head =>
      cases b with
      | mk cells' head' =>
          simp only at hc hh
          subst cells'
          have heq : head = head' := Fin.ext hh
          subst head'
          rfl

theorem window_apply (origin : Int) (size : ℕ) (c : Configuration ns nt)
    (a : Action (Fin ns) (Fin nt)) (h : HeadIn origin size c)
    (hnext : HeadIn origin size (actionConfig a c)) :
    (window origin size c h).applyAction? (toBoundedAction a) =
      some (window origin size (actionConfig a c) hnext) := by
  unfold LogicalWindow.applyAction?
  change ((moveIndex a.move (window origin size c h).head).bind fun nextHead =>
    some ({ cells := (window origin size c h).cells.set (window origin size c h).head a.write
            head := ⟨nextHead.val, by simpa using nextHead.isLt⟩ } : LogicalWindow nt)) =
      some (window origin size (actionConfig a c) hnext)
  rw [window_move origin size c a h hnext]
  simp only [Option.bind_some]
  congr 1
  have hc := window_written origin size c a h hnext
  simp only [window] at hc ⊢
  exact window_ext _ _ hc rfl

theorem slotIndex_pred (slot : Fin 2) : slotIndex (decide (slot = 1)) = slot := by
  fin_cases slot <;> rfl

theorem step_window (M : Machine ns nt 2) (slot : Fin 2)
    (origin : Int) (size : ℕ) (c out : Configuration ns nt)
    (hc : HeadIn origin size c) (hout : HeadIn origin size out)
    (hstep : step M slot c = some out) :
    ULogSourceObliviousLogicalRuns.step (toBounded M) slot
      (c.state, window origin size c hc) =
        some (out.state, window origin size out hout) := by
  cases hrule : M.rule c.state (c.tape c.head) slot with
  | none => simp [step, hrule] at hstep
  | some a =>
      have heq : actionConfig a c = out := by simpa [step, hrule, actionConfig] using hstep
      subst out
      simp only [ULogSourceObliviousLogicalRuns.step, window_read, toBounded,
        slotIndex_pred, hrule, Option.map_some, Option.bind_some]
      rw [window_apply origin size c a hc hout]
      rfl

theorem headIn_of_safe_action (origin : Int) (size : ℕ)
    (c : Configuration ns nt) (a : Action (Fin ns) (Fin nt))
    (hc : HeadIn origin size c)
    (hsafe : (moveIndex a.move (window origin size c hc).head).isSome = true) :
    HeadIn origin size (actionConfig a c) := by
  have hcast : ((c.head - origin).toNat : Int) = c.head - origin :=
    Int.toNat_of_nonneg hc.1
  obtain ⟨hlo, hhi⟩ := hc
  cases hm : a.move with
  | stay => simpa [HeadIn, actionConfig, moveHead, hm] using And.intro hlo hhi
  | right =>
      have hb : (window origin size c ⟨hlo, hhi⟩).head.val + 1 <
          (window origin size c ⟨hlo, hhi⟩).cells.length := by
        by_contra hn
        simp [moveIndex, hm, hn] at hsafe
      simp only [window, List.length_ofFn] at hb
      simp only [HeadIn, actionConfig, moveHead, hm]
      constructor <;> omega
  | left =>
      have hb : 0 < (window origin size c ⟨hlo, hhi⟩).head.val := by
        by_contra hn
        simp [moveIndex, hm, hn] at hsafe
      simp only [window] at hb
      simp only [HeadIn, actionConfig, moveHead, hm]
      constructor <;> omega

theorem logical_step_inverse (M : Machine ns nt 2) (slot : Fin 2)
    (origin : Int) (size : ℕ) (c : Configuration ns nt)
    (hc : HeadIn origin size c)
    (out : ULogSourceObliviousLogicalRuns.Configuration ns nt)
    (hrun : ULogSourceObliviousLogicalRuns.step (toBounded M) slot
      (c.state, window origin size c hc) = some out) :
    ∃ next : Configuration ns nt, ∃ hnext : HeadIn origin size next,
      step M slot c = some next ∧
        out = (next.state, window origin size next hnext) := by
  cases hrule : M.rule c.state (c.tape c.head) slot with
  | none =>
      simp only [ULogSourceObliviousLogicalRuns.step, window_read, toBounded,
        slotIndex_pred, hrule, Option.map_none, Option.bind_none] at hrun
      cases hrun
  | some a =>
      have hs : ((window origin size c hc).applyAction? (toBoundedAction a)).isSome = true := by
        simp only [ULogSourceObliviousLogicalRuns.step, window_read, toBounded,
          slotIndex_pred, hrule, Option.map_some, Option.bind_some] at hrun
        cases ha : (window origin size c hc).applyAction? (toBoundedAction a) with
        | none => simp [ha] at hrun
        | some next => simp [ha]
      have hmove : (moveIndex a.move (window origin size c hc).head).isSome = true := by
        simpa [LogicalWindow.applyAction?, toBoundedAction, Option.isSome_bind] using hs
      let next := actionConfig a c
      have hnext : HeadIn origin size next := headIn_of_safe_action origin size c a hc hmove
      have hstep : step M slot c = some next := by simp [step, hrule, next, actionConfig]
      refine ⟨next, hnext, hstep, ?_⟩
      exact (Option.some.inj
        ((step_window M slot origin size c next hc hnext hstep).symm.trans hrun)).symm

theorem run_window_forward (M : Machine ns nt 2) (word : List (Fin 2))
    (origin : Int) (size : ℕ) (c out : Configuration ns nt)
    (hc : HeadIn origin size c)
    (hlo : origin ≤ c.head - (word.length : Int))
    (hhi : c.head + (word.length : Int) < origin + (size : Int))
    (hrun : run M word c = some out) :
    ∃ hout : HeadIn origin size out,
      ULogSourceObliviousLogicalRuns.run (toBounded M) word
        (c.state, window origin size c hc) =
          some (out.state, window origin size out hout) := by
  induction word generalizing c with
  | nil =>
      have heq : c = out := Option.some.inj hrun
      subst out
      exact ⟨hc, rfl⟩
  | cons slot word ih =>
      cases hstep : step M slot c with
      | none => simp [run, hstep] at hrun
      | some middle =>
          have htail : run M word middle = some out := by simpa [run, hstep] using hrun
          obtain ⟨hslo, hshi, _⟩ := step_geometry M slot c middle hstep
          have hmidlo : origin ≤ middle.head - (word.length : Int) := by
            simp only [List.length_cons, Int.natCast_add, Int.natCast_one] at hlo
            omega
          have hmidhi : middle.head + (word.length : Int) < origin + (size : Int) := by
            simp only [List.length_cons, Int.natCast_add, Int.natCast_one] at hhi
            omega
          have hmiddle : HeadIn origin size middle := by constructor <;> omega
          obtain ⟨hout, hlogical⟩ := ih middle hmiddle hmidlo hmidhi htail
          refine ⟨hout, ?_⟩
          simp only [ULogSourceObliviousLogicalRuns.run,
            step_window M slot origin size c middle hc hmiddle hstep, Option.bind_some]
          exact hlogical

theorem run_window_inverse (M : Machine ns nt 2) (word : List (Fin 2))
    (origin : Int) (size : ℕ) (c : Configuration ns nt)
    (hc : HeadIn origin size c)
    (out : ULogSourceObliviousLogicalRuns.Configuration ns nt)
    (hrun : ULogSourceObliviousLogicalRuns.run (toBounded M) word
      (c.state, window origin size c hc) = some out) :
    ∃ next : Configuration ns nt, ∃ hnext : HeadIn origin size next,
      run M word c = some next ∧
        out = (next.state, window origin size next hnext) := by
  induction word generalizing c with
  | nil => exact ⟨c, hc, rfl, (Option.some.inj hrun).symm⟩
  | cons slot word ih =>
      cases hs : ULogSourceObliviousLogicalRuns.step (toBounded M) slot
          (c.state, window origin size c hc) with
      | none => simp [ULogSourceObliviousLogicalRuns.run, hs] at hrun
      | some middle =>
          have htail : ULogSourceObliviousLogicalRuns.run (toBounded M) word middle =
              some out := by simpa [ULogSourceObliviousLogicalRuns.run, hs] using hrun
          obtain ⟨actual, hactual, hstep, hmiddle⟩ :=
            logical_step_inverse M slot origin size c hc middle hs
          subst middle
          obtain ⟨next, hnext, hactualrun, hout⟩ := ih actual hactual htail
          exact ⟨next, hnext, by simp only [run, hstep, Option.bind_some, hactualrun], hout⟩

def inputOrigin (bound : ℕ) : Int := -(bound : Int) - 1

def inputSize (x : List Bool) (bound : ℕ) : ℕ := x.length + 2 * bound + 3

theorem initial_headIn (M : Machine ns nt 2) (x : List Bool) (bound : ℕ) :
    HeadIn (inputOrigin bound) (inputSize x bound) (initial M x) := by
  simp only [HeadIn, inputOrigin, inputSize, initial, Int.natCast_add,
    Int.natCast_mul]
  constructor <;> omega

def inputWindow (M : Machine ns nt 2) (x : List Bool) (bound : ℕ) : LogicalWindow nt :=
  window (inputOrigin bound) (inputSize x bound) (initial M x)
    (initial_headIn M x bound)

theorem initialized_run_window (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (word : List (Fin 2)) (out : Configuration ns nt)
    (hlen : word.length ≤ bound)
    (hrun : run M word (initial M x) = some out) :
    ∃ hout : HeadIn (inputOrigin bound) (inputSize x bound) out,
      ULogSourceObliviousLogicalRuns.run (toBounded M) word
        (M.start, inputWindow M x bound) =
          some (out.state, window (inputOrigin bound) (inputSize x bound) out hout) := by
  apply run_window_forward M word (inputOrigin bound) (inputSize x bound)
    (initial M x) out (initial_headIn M x bound) _ _ hrun
  · simp only [inputOrigin, initial]; omega
  · simp only [inputOrigin, inputSize, initial, Int.natCast_add,
      Int.natCast_mul]; omega

theorem inputWindow_length (M : Machine ns nt 2) (x : List Bool) (bound : ℕ) :
    (inputWindow M x bound).cells.length = x.length + 2 * bound + 3 :=
  window_length _ _ _ _

end PakFixedPolyomino.StandardMachineWindowBridge
