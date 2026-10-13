import PakFixedPolyomino.StandardBitPrepend
import PakFixedPolyomino.StandardBitMetric
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Finite one-tape nondeterministic choice of a fixed label, then a
slot-0-only physical prefix of that label's pairBits code onto every raw
payload. L is a machine constant. No runtime/count certificate premises. -/
set_option maxHeartbeats 0
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace PakFixedPolyomino.StandardBitFiniteChoicePrefix
noncomputable section
open StandardNondeterministicMachine StandardBitMetric
open FiniteOneTapeSemantics (moveHead writtenTape)
open StandardBitPrepend (carryState bit)

def labelCode (L : Nat) (i : Fin L) : List Bool :=
  List.replicate i.val true ++ List.replicate (L - i.val) false
def tokens (L : Nat) (i : Fin L) : List Bool :=
  (pairBits (labelCode L i) []).reverse
def stages (L : Nat) : Nat := 2 * L + 1
def coreFuel (L n : Nat) : Nat := stages L * (2 * n + stages L + 2)
def ns (L : Nat) : Nat := 3 + 5 * L * stages L
def word (L : Nat) (raw : List Bool) (i : Fin L) : List (Fin (L + 1)) :=
  i.castSucc :: List.replicate (coreFuel L raw.length) 0
def boundPoly (L : Nat) : Polynomial Nat :=
  Polynomial.C (2 * stages L) * Polynomial.X +
    Polynomial.C (stages L * (stages L + 2) + 1)

theorem stages_pos (L : Nat) : 0 < stages L := by unfold stages; omega
theorem ns_gt_two (L : Nat) : 2 < ns L := by unfold ns stages; omega
theorem ns_gt_one (L : Nat) : 1 < ns L := by unfold ns stages; omega
theorem ns_gt_zero (L : Nat) : 0 < ns L := by unfold ns stages; omega

theorem labelCode_length (L : Nat) (i : Fin L) : (labelCode L i).length = L := by
  simp [labelCode, Nat.add_sub_of_le (Nat.le_of_lt i.isLt)]

theorem labelCode_get (L : Nat) (i : Fin L) (k : Nat) (hk : k < L) :
    (labelCode L i)[k]'(by simp [labelCode_length, hk]) = decide (k < i.val) := by
  simp only [labelCode]
  by_cases hki : k < i.val
  · have : k < (List.replicate i.val true).length := by simp [hki]
    rw [List.getElem_append_left this]; simp [hki]
  · have hle : (List.replicate i.val true).length ≤ k := by simp; omega
    rw [List.getElem_append_right hle]
    simp [List.getElem_replicate, hki]

theorem labelCode_injective (L : Nat) : Function.Injective (labelCode L) := by
  intro i j h
  have hi := i.isLt
  have hgi := congrArg (fun w : List Bool => w[i.val]?) h
  have hgj := congrArg (fun w : List Bool => w[j.val]?) h
  simp [List.getElem?_eq_getElem, labelCode_length, hi, j.isLt, labelCode_get] at hgi hgj
  apply Fin.ext
  omega

def firstFalseIndex : List Bool → Nat
  | [] => 0
  | false :: _ => 0
  | true :: w => firstFalseIndex w + 1

theorem firstFalseIndex_replicate (n m : Nat) (hm : 0 < m) :
    firstFalseIndex (List.replicate n true ++ List.replicate m false) = n := by
  induction n with
  | zero =>
      cases m with
      | zero => cases hm
      | succ m => simp [firstFalseIndex, List.replicate_succ]
  | succ n ih =>
      simp [List.replicate_succ, firstFalseIndex]
      exact ih

theorem firstFalseIndex_labelCode (L : Nat) (i : Fin L) :
    firstFalseIndex (labelCode L i) = i.val :=
  firstFalseIndex_replicate i.val (L - i.val) (Nat.sub_pos_of_lt i.isLt)

theorem tokens_length (L : Nat) (i : Fin L) : (tokens L i).length = stages L := by
  simp [tokens, stages, pairBits_length, labelCode_length]

theorem pairBits_nil_append (x y : List Bool) : pairBits x [] ++ y = pairBits x y := by
  simp [pairBits]

theorem tokens_reverse_append (L : Nat) (i : Fin L) (raw : List Bool) :
    (tokens L i).reverse ++ raw = pairBits (labelCode L i) raw := by
  simp [tokens, pairBits_nil_append]

def token (L : Nat) (i : Fin L) (j : Fin (stages L)) : Bool :=
  (tokens L i)[j.val]'(by rw [tokens_length]; exact j.isLt)

theorem token_zero (L : Nat) (i : Fin L) : token L i ⟨0, stages_pos L⟩ = false := by
  unfold token tokens
  have hpair : pairBits (labelCode L i) [] =
      (labelCode L i).flatMap (fun b => [true, b]) ++ [false] := by simp [pairBits]
  simp [hpair, List.reverse_append]

theorem carryState_start (b : Bool) :
    carryState b = (StandardBitPrepend.machine b).start := rfl

theorem coreIndex_lt (L : Nat) (i : Fin L) (j : Fin (stages L)) (q : Fin 5) :
    3 + 5 * (i.val * stages L + j.val) + q.val < 3 + 5 * L * stages L := by
  have hi := Nat.succ_le_of_lt i.isLt
  have hmul : (i.val + 1) * stages L ≤ L * stages L := Nat.mul_le_mul_right _ hi
  rw [Nat.add_one_mul] at hmul
  have hidx : i.val * stages L + j.val + 1 ≤ L * stages L := by
    have := j.isLt; omega
  have h5 : 5 * (i.val * stages L + j.val + 1) ≤ 5 * (L * stages L) :=
    Nat.mul_le_mul_left 5 hidx
  have hassoc : 5 * L * stages L = 5 * (L * stages L) := by rw [Nat.mul_assoc]
  have hq := q.isLt
  omega

def encodeCore (L : Nat) (i : Fin L) (j : Fin (stages L)) (q : Fin 5) : Fin (ns L) :=
  ⟨3 + 5 * (i.val * stages L + j.val) + q.val, by simpa [ns] using coreIndex_lt L i j q⟩

def decodeCore (L : Nat) (s : Fin (ns L)) :
    Option (Fin L × Fin (stages L) × Fin 5) :=
  if h3 : 3 ≤ s.val then
    let k := s.val - 3
    let q : Fin 5 := ⟨k % 5, Nat.mod_lt k (by decide)⟩
    if hS : 0 < stages L then
      if hi : k / 5 / stages L < L then
        some (⟨k / 5 / stages L, hi⟩, ⟨k / 5 % stages L, Nat.mod_lt _ hS⟩, q)
      else none
    else none
  else none

theorem encodeCore_val (L : Nat) (i : Fin L) (j : Fin (stages L)) (q : Fin 5) :
    (encodeCore L i j q).val = 3 + 5 * (i.val * stages L + j.val) + q.val := rfl

theorem encodeCore_ge (L : Nat) (i : Fin L) (j : Fin (stages L)) (q : Fin 5) :
    3 ≤ (encodeCore L i j q).val := by simp [encodeCore]; omega

theorem mul_add_mod_of_lt (a b n : Nat) (hb : b < n) : (a * n + b) % n = b := by
  rw [Nat.add_mod, Nat.mul_mod_left a n, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hb]

theorem mul_add_div_of_lt (a b n : Nat) (hn : 0 < n) (hb : b < n) :
    (a * n + b) / n = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right b a hn, Nat.div_eq_of_lt hb, Nat.zero_add]

theorem decode_encode (L : Nat) (i : Fin L) (j : Fin (stages L)) (q : Fin 5) :
    decodeCore L (encodeCore L i j q) = some (i, j, q) := by
  dsimp [decodeCore, encodeCore]
  have h3 : 3 ≤ 3 + 5 * (i.val * stages L + j.val) + q.val := by omega
  rw [if_pos h3]
  have hk : 3 + 5 * (i.val * stages L + j.val) + q.val - 3 =
      5 * (i.val * stages L + j.val) + q.val := by omega
  simp [hk]
  have hmod : (5 * (i.val * stages L + j.val) + q.val) % 5 = q.val := by
    simpa [Nat.mul_comm 5] using mul_add_mod_of_lt (i.val * stages L + j.val) q.val 5 q.isLt
  have hdiv : (5 * (i.val * stages L + j.val) + q.val) / 5 = i.val * stages L + j.val := by
    simpa [Nat.mul_comm 5] using
      mul_add_div_of_lt (i.val * stages L + j.val) q.val 5 (by decide) q.isLt
  simp [hmod, hdiv, stages_pos L]
  have hjmod : (i.val * stages L + j.val) % stages L = j.val :=
    mul_add_mod_of_lt i.val j.val (stages L) j.isLt
  have hidiv : (i.val * stages L + j.val) / stages L = i.val :=
    mul_add_div_of_lt i.val j.val (stages L) (stages_pos L) j.isLt
  simp [hjmod, hidiv, i.isLt, Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt q.isLt]

def coreRule (L : Nat) (i : Fin L) (j : Fin (stages L)) (q : Fin 5)
    (read : Fin 3) (slot : Fin (L + 1)) :
    Option (FiniteOneTapeProgram.Action (Fin (ns L)) (Fin 3)) :=
  if slot = 0 then
    if q = 0 then
      if hj : j.val + 1 < stages L then
        some ⟨read, encodeCore L i ⟨j.val + 1, hj⟩
          (carryState (token L i ⟨j.val + 1, hj⟩)), .stay⟩
      else
        some ⟨read, ⟨0, ns_gt_zero L⟩, .stay⟩
    else if q = 1 then none
    else (StandardBitPrepend.machine (token L i j)).rule q read 0 |>.map fun a =>
      ⟨a.write, encodeCore L i j a.target, a.move⟩
  else none

def chooseRule (L : Nat) (read : Fin 3) (slot : Fin (L + 1)) :
    Option (FiniteOneTapeProgram.Action (Fin (ns L)) (Fin 3)) :=
  if hi : slot.val < L then
    let i : Fin L := ⟨slot.val, hi⟩
    some ⟨read, encodeCore L i ⟨0, stages_pos L⟩
      (carryState (token L i ⟨0, stages_pos L⟩)), .stay⟩
  else none

def ndRule (L : Nat) (q : Fin (ns L)) (read : Fin 3) (slot : Fin (L + 1)) :
    Option (FiniteOneTapeProgram.Action (Fin (ns L)) (Fin 3)) :=
  if q.val = 0 ∨ q.val = 1 then none
  else if q.val = 2 then chooseRule L read slot
  else match decodeCore L q with
    | none => none
    | some p => coreRule L p.1 p.2.1 p.2.2 read slot

def machine (L : Nat) : Machine (ns L) 3 (L + 1) where
  rule := ndRule L
  start := ⟨2, ns_gt_two L⟩
  accept := ⟨0, ns_gt_zero L⟩
  reject := ⟨1, ns_gt_one L⟩
  accept_ne_reject := by intro h; cases h
  blank := 2
  zero := 0
  one := 1
  blank_ne_zero := by decide
  blank_ne_one := by decide
  zero_ne_one := by decide
  accept_terminal := by intro x slot; simp [ndRule]
  reject_terminal := by intro x slot; simp [ndRule]

@[simp] theorem machine_zero (L : Nat) : (machine L).zero = 0 := rfl
@[simp] theorem machine_one (L : Nat) : (machine L).one = 1 := rfl
@[simp] theorem machine_blank (L : Nat) : (machine L).blank = 2 := rfl
@[simp] theorem machine_start (L : Nat) : (machine L).start = ⟨2, ns_gt_two L⟩ := rfl
@[simp] theorem machine_accept (L : Nat) : (machine L).accept = ⟨0, ns_gt_zero L⟩ := rfl
@[simp] theorem machine_reject (L : Nat) : (machine L).reject = ⟨1, ns_gt_one L⟩ := rfl

theorem inputTape_machine (L : Nat) (b : Bool) (x : List Bool) :
    inputTape (machine L) x = inputTape (StandardBitPrepend.machine b) x := by
  funext z; simp [inputTape]

theorem ndRule_choose (L : Nat) (read : Fin 3) (slot : Fin (L + 1)) :
    ndRule L ⟨2, ns_gt_two L⟩ read slot = chooseRule L read slot := by
  simp [ndRule]

theorem ndRule_core (L : Nat) (i : Fin L) (j : Fin (stages L)) (q : Fin 5)
    (read : Fin 3) (slot : Fin (L + 1)) :
    ndRule L (encodeCore L i j q) read slot = coreRule L i j q read slot := by
  have h0 : (encodeCore L i j q).val ≠ 0 := by simp [encodeCore_val]; try omega
  have h1 : (encodeCore L i j q).val ≠ 1 := by simp [encodeCore_val]; try omega
  have h2 : (encodeCore L i j q).val ≠ 2 := by simp [encodeCore_val]; try omega
  have hterm : ¬ ((encodeCore L i j q).val = 0 ∨ (encodeCore L i j q).val = 1) := by
    intro h; rcases h with h | h <;> contradiction
  simp [ndRule, hterm, h2, decode_encode]

def liftConfig (L : Nat) (i : Fin L) (j : Fin (stages L))
    (c : Configuration 5 3) : Configuration (ns L) 3 :=
  { state := encodeCore L i j c.state, head := c.head, tape := c.tape }

def prefixAfter (L : Nat) (i : Fin L) (raw : List Bool) (k : Nat) : List Bool :=
  ((tokens L i).take k).reverse ++ raw

theorem prefixAfter_zero (L : Nat) (i : Fin L) (raw : List Bool) :
    prefixAfter L i raw 0 = raw := by simp [prefixAfter]

theorem take_succ_of_lt (l : List Bool) (k : Nat) (hk : k < l.length) :
    l.take (k + 1) = l.take k ++ [l[k]] := by
  induction l generalizing k with
  | nil => cases hk
  | cons a l ih =>
      cases k with
      | zero => simp
      | succ k =>
          have hk' : k < l.length := by simp at hk; omega
          simpa [List.take] using ih k hk'

theorem prefixAfter_succ (L : Nat) (i : Fin L) (raw : List Bool) (k : Nat)
    (hk : k < stages L) :
    prefixAfter L i raw (k + 1) = token L i ⟨k, hk⟩ :: prefixAfter L i raw k := by
  have hlen : k < (tokens L i).length := by rw [tokens_length]; exact hk
  unfold prefixAfter token
  rw [take_succ_of_lt (tokens L i) k hlen, List.reverse_append]
  simp [List.reverse_cons, List.reverse_nil, List.singleton_append, List.cons_append]

theorem prefixAfter_length (L : Nat) (i : Fin L) (raw : List Bool) (k : Nat)
    (hk : k ≤ stages L) : (prefixAfter L i raw k).length = raw.length + k := by
  simp [prefixAfter, tokens_length, List.length_take]
  omega

theorem prefixAfter_all (L : Nat) (i : Fin L) (raw : List Bool) :
    prefixAfter L i raw (stages L) = pairBits (labelCode L i) raw := by
  have : (tokens L i).take (stages L) = tokens L i := by
    simpa [tokens_length] using List.take_length (tokens L i)
  simp [prefixAfter, this, tokens_reverse_append]

def stageStart (L : Nat) (i : Fin L) (raw : List Bool) (k : Nat)
    (hk : k < stages L) : Configuration (ns L) 3 :=
  liftConfig L i ⟨k, hk⟩
    (initial (StandardBitPrepend.machine (token L i ⟨k, hk⟩)) (prefixAfter L i raw k))

def haltConfig (L : Nat) (i : Fin L) (raw : List Bool) : Configuration (ns L) 3 :=
  { state := ⟨0, ns_gt_zero L⟩, head := 0,
    tape := inputTape (machine L) (pairBits (labelCode L i) raw) }

theorem stageStart_tape (L : Nat) (i : Fin L) (raw : List Bool) (k : Nat)
    (hk : k < stages L) :
    (stageStart L i raw k hk).tape = inputTape (machine L) (prefixAfter L i raw k) := by
  simp [stageStart, liftConfig, initial]
  exact (inputTape_machine L (token L i ⟨k, hk⟩) _).symm

theorem choose_step (L : Nat) (raw : List Bool) (i : Fin L) :
    step (machine L) i.castSucc (initial (machine L) raw) =
      some (stageStart L i raw 0 (stages_pos L)) := by
  have hslot : (i.castSucc : Fin (L + 1)).val < L := i.isLt
  have hr : ndRule L ⟨2, ns_gt_two L⟩ (inputTape (machine L) raw 0) i.castSucc =
      some ⟨inputTape (machine L) raw 0,
        encodeCore L i ⟨0, stages_pos L⟩ (carryState (token L i ⟨0, stages_pos L⟩)),
        .stay⟩ := by
    simp [ndRule, chooseRule, hslot, token_zero, carryState]
  unfold step initial
  rw [show (machine L).rule = ndRule L from rfl,
    show (machine L).start = ⟨2, ns_gt_two L⟩ from rfl, hr]
  simp [moveHead, writtenTape, Function.update_eq_self]
  apply StandardBitMachineComposition.config_ext
  · simp [stageStart, liftConfig, initial, carryState_start]
  · rfl
  · simp [stageStart, liftConfig, initial, prefixAfter_zero]
    exact (inputTape_machine L false raw).symm

theorem prepend_step_source (b : Bool) (c c' : Configuration 5 3)
    (h : step (StandardBitPrepend.machine b) 0 c = some c') :
    c.state ≠ 0 ∧ c.state ≠ 1 := by
  constructor
  · intro hs; simpa [step, hs, StandardBitPrepend.machine] using h
  · intro hs; simpa [step, hs, StandardBitPrepend.machine] using h

theorem lift_step (L : Nat) (i : Fin L) (j : Fin (stages L))
    (c c' : Configuration 5 3)
    (h : step (StandardBitPrepend.machine (token L i j)) 0 c = some c') :
    step (machine L) 0 (liftConfig L i j c) = some (liftConfig L i j c') := by
  have hsrc := prepend_step_source (token L i j) c c' h
  have hq0 : c.state.val ≠ 0 := by
    intro hval; apply hsrc.1; exact Fin.ext hval
  have hq1 : c.state.val ≠ 1 := by
    intro hval; apply hsrc.2; exact Fin.ext hval
  unfold step at h ⊢
  cases hrule : (StandardBitPrepend.machine (token L i j)).rule c.state (c.tape c.head) 0 with
  | none => simp [hrule] at h
  | some a =>
      simp [hrule] at h
      subst c'
      have hr : ndRule L (encodeCore L i j c.state) (c.tape c.head) 0 =
          some ⟨a.write, encodeCore L i j a.target, a.move⟩ := by
        rw [ndRule_core]
        have hq0' : c.state ≠ 0 := hsrc.1
        have hq1' : c.state ≠ 1 := hsrc.2
        simp [coreRule, hq0', hq1', hrule]
      simp [machine, liftConfig, hr, writtenTape]

theorem lift_run (L : Nat) (i : Fin L) (j : Fin (stages L))
    (n : Nat) (c out : Configuration 5 3)
    (h : run (StandardBitPrepend.machine (token L i j)) (StandardBitTime.ticks n) c =
      some out) :
    run (machine L) (List.replicate n 0) (liftConfig L i j c) =
      some (liftConfig L i j out) := by
  induction n generalizing c with
  | zero =>
      simp [StandardBitTime.ticks] at h
      subst out
      simp
  | succ n ih =>
      change run _ (0 :: StandardBitTime.ticks n) c = some out at h
      rw [run_cons] at h
      cases hstep : step (StandardBitPrepend.machine (token L i j)) 0 c with
      | none => simp [hstep] at h
      | some mid =>
          simp [hstep] at h
          rw [List.replicate_succ, run_cons, lift_step (h := hstep), Option.bind_some]
          exact ih mid h

theorem handoff_step (L : Nat) (i : Fin L) (k : Nat) (hk : k < stages L)
    (x : List Bool) :
    step (machine L) 0
      ⟨encodeCore L i ⟨k, hk⟩ 0, 0,
        inputTape (machine L) (token L i ⟨k, hk⟩ :: x)⟩ =
      if hk1 : k + 1 < stages L then
        some ⟨encodeCore L i ⟨k + 1, hk1⟩ (carryState (token L i ⟨k + 1, hk1⟩)),
          0, inputTape (machine L) (token L i ⟨k, hk⟩ :: x)⟩
      else
        some ⟨⟨0, ns_gt_zero L⟩, 0,
          inputTape (machine L) (token L i ⟨k, hk⟩ :: x)⟩ := by
  unfold step
  rw [show (machine L).rule = ndRule L from rfl, ndRule_core]
  have hr : coreRule L i ⟨k, hk⟩ 0
      (inputTape (machine L) (token L i ⟨k, hk⟩ :: x) 0) 0 =
      if hk1 : k + 1 < stages L then
        some ⟨inputTape (machine L) (token L i ⟨k, hk⟩ :: x) 0,
          encodeCore L i ⟨k + 1, hk1⟩ (carryState (token L i ⟨k + 1, hk1⟩)), .stay⟩
      else
        some ⟨inputTape (machine L) (token L i ⟨k, hk⟩ :: x) 0,
          ⟨0, ns_gt_zero L⟩, .stay⟩ := by
    simp [coreRule]
  rw [hr]
  split_ifs <;> simp [moveHead, writtenTape, Function.update_eq_self]

theorem stage_run (L : Nat) (i : Fin L) (raw : List Bool) (k : Nat)
    (hk : k < stages L) :
    run (machine L) (List.replicate (2 * (raw.length + k) + 3) 0)
      (stageStart L i raw k hk) =
      if hk1 : k + 1 < stages L then some (stageStart L i raw (k + 1) hk1)
      else some (haltConfig L i raw) := by
  have hxlen : (prefixAfter L i raw k).length = raw.length + k :=
    prefixAfter_length L i raw k (Nat.le_of_lt hk)
  have hticks : 2 * (raw.length + k) + 3 = 2 * (prefixAfter L i raw k).length + 2 + 1 := by
    omega
  rw [hticks, List.replicate_add,
    show List.replicate 1 (0 : Fin (L + 1)) = [0] from rfl, run_append]
  have hpre := StandardBitPrepend.prepend_run (token L i ⟨k, hk⟩) (prefixAfter L i raw k)
  have hlift := lift_run L i ⟨k, hk⟩ (2 * (prefixAfter L i raw k).length + 2)
    (initial (StandardBitPrepend.machine (token L i ⟨k, hk⟩)) (prefixAfter L i raw k))
    (StandardBitPrepend.finalConfig (token L i ⟨k, hk⟩) (prefixAfter L i raw k)) hpre
  simp [stageStart] at hlift ⊢
  rw [hlift, Option.bind_some]
  have hfin :
      liftConfig L i ⟨k, hk⟩
        (StandardBitPrepend.finalConfig (token L i ⟨k, hk⟩) (prefixAfter L i raw k)) =
      { state := encodeCore L i ⟨k, hk⟩ 0, head := 0,
        tape := inputTape (machine L) (token L i ⟨k, hk⟩ :: prefixAfter L i raw k) } := by
    apply StandardBitMachineComposition.config_ext
    · simp [liftConfig, StandardBitPrepend.finalConfig]
    · simp [liftConfig, StandardBitPrepend.finalConfig]
    · simp [liftConfig, StandardBitPrepend.finalConfig]
      exact (inputTape_machine L (token L i ⟨k, hk⟩) _).symm
  rw [hfin, run_cons, handoff_step L i k hk (prefixAfter L i raw k)]
  split_ifs with hk1
  · simp [run_nil]
    apply StandardBitMachineComposition.config_ext
    · simp [stageStart, liftConfig, initial, carryState_start]
    · rfl
    · rw [← prefixAfter_succ L i raw k hk]
      exact (inputTape_machine L (token L i ⟨k + 1, hk1⟩) _).symm
  · have hkS : k + 1 = stages L := by omega
    simp [run_nil]
    apply StandardBitMachineComposition.config_ext
    · simp [haltConfig]
    · rfl
    · have : token L i ⟨k, hk⟩ :: prefixAfter L i raw k = prefixAfter L i raw (k + 1) :=
        (prefixAfter_succ L i raw k hk).symm
      rw [this, hkS, prefixAfter_all]
      simp [haltConfig]

def restFuel (L m k : Nat) : Nat :=
  (stages L - k) * (2 * (m + k) + (stages L - k) + 2)

theorem restFuel_zero (L m : Nat) : restFuel L m 0 = coreFuel L m := rfl
theorem restFuel_end (L m : Nat) : restFuel L m (stages L) = 0 := by simp [restFuel]

theorem restFuel_succ (L m k : Nat) (hk : k < stages L) :
    restFuel L m k = 2 * (m + k) + 3 + restFuel L m (k + 1) := by
  unfold restFuel
  have hsk : stages L - (k + 1) = stages L - k - 1 := by omega
  rw [hsk]
  have hpos : 0 < stages L - k := Nat.sub_pos_of_lt hk
  revert hpos
  generalize ht : stages L - k = t
  intro hpos
  cases t with
  | zero => cases hpos
  | succ t =>
      simp
      ring

def afterStage (L : Nat) (i : Fin L) (raw : List Bool) (k : Nat)
    (hk : k ≤ stages L) : Configuration (ns L) 3 :=
  if h : k < stages L then stageStart L i raw k h else haltConfig L i raw

theorem rest_run (L : Nat) (i : Fin L) (raw : List Bool) (k : Nat)
    (hk : k ≤ stages L) :
    run (machine L) (List.replicate (restFuel L raw.length k) 0)
      (afterStage L i raw k hk) = some (haltConfig L i raw) := by
  induction hrem : stages L - k generalizing k with
  | zero =>
      have : k = stages L := by omega
      subst k
      simp [restFuel, afterStage, Nat.lt_irrefl]
  | succ t ih =>
      have hklt : k < stages L := by omega
      simp [afterStage, hklt]
      rw [restFuel_succ L raw.length k hklt, List.replicate_add, run_append,
        stage_run L i raw k hklt]
      split_ifs with hk1
      · have hle : k + 1 ≤ stages L := Nat.le_of_lt hk1
        have hrem' : stages L - (k + 1) = t := by omega
        have ih' := ih (k + 1) hle hrem'
        simpa [afterStage, hk1] using ih'
      · have : k + 1 = stages L := by omega
        have hz : restFuel L raw.length (k + 1) = 0 := by simp [restFuel, this]
        simp [hz]

theorem word_run (L : Nat) (raw : List Bool) (i : Fin L) :
    run (machine L) (word L raw i) (initial (machine L) raw) =
      some (haltConfig L i raw) := by
  simp only [word]
  rw [run_cons, choose_step, Option.bind_some]
  have hrest := rest_run L i raw 0 (Nat.zero_le _)
  simpa [afterStage, stages_pos, restFuel_zero] using hrest

theorem boundPoly_eval (L n : Nat) :
    (boundPoly L).eval n = 2 * stages L * n + stages L * (stages L + 2) + 1 := by
  simp [boundPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  omega

theorem word_length (L : Nat) (raw : List Bool) (i : Fin L) :
    (word L raw i).length = (boundPoly L).eval raw.length := by
  simp [word, coreFuel, boundPoly_eval]; ring

theorem accepted_word (L : Nat) (raw : List Bool) (i : Fin L) :
    Accepted (machine L) raw (word L raw i) := by
  refine (accepted_iff (machine L) raw (word L raw i)).mpr ?_
  refine ⟨haltConfig L i raw, word_run L raw i, ?_⟩
  simp [haltConfig]

theorem core_step_slot0 (L : Nat) (i : Fin L) (j : Fin (stages L)) (q : Fin 5)
    (c : Configuration (ns L) 3) (slot : Fin (L + 1)) (c' : Configuration (ns L) 3)
    (hs : c.state = encodeCore L i j q)
    (h : step (machine L) slot c = some c') : slot = 0 := by
  by_contra hne
  have hslot : slot ≠ 0 := hne
  unfold step at h
  rw [hs, show (machine L).rule = ndRule L from rfl, ndRule_core] at h
  simp [coreRule, hslot] at h

theorem step_from_start (L : Nat) (raw : List Bool) (slot : Fin (L + 1))
    (c' : Configuration (ns L) 3)
    (h : step (machine L) slot (initial (machine L) raw) = some c') :
    slot.val < L := by
  unfold step initial machine at h
  simp [ndRule, chooseRule] at h
  exact h.fst

theorem ndRule_slot_ne (L : Nat) (s : Fin (ns L)) (read : Fin 3) (slot : Fin (L + 1))
    (hs : 3 ≤ s.val) (hslot : slot ≠ 0) : ndRule L s read slot = none := by
  have hterm : ¬ (s.val = 0 ∨ s.val = 1) := by omega
  have hne2 : s.val ≠ 2 := by omega
  simp [ndRule, hterm, hne2]
  cases decodeCore L s with
  | none => rfl
  | some p => simp [coreRule, hslot]

theorem coreRule_target (L : Nat) (i : Fin L) (j : Fin (stages L)) (q : Fin 5)
    (read : Fin 3) (slot : Fin (L + 1))
    (a : FiniteOneTapeProgram.Action (Fin (ns L)) (Fin 3))
    (h : coreRule L i j q read slot = some a) :
    a.target.val = 0 ∨ 3 ≤ a.target.val := by
  unfold coreRule at h
  by_cases hs0 : slot = 0
  · simp [hs0] at h
    by_cases hq0 : q = 0
    · simp [hq0] at h
      split_ifs at h with hj
      · cases h; simp [encodeCore_val]; omega
      · cases h; simp
    · simp [hq0] at h
      by_cases hq1 : q = 1
      · simp [hq1] at h
      · simp [hq1] at h
        cases hrule : (StandardBitPrepend.machine (token L i j)).rule q read 0
        · simp [hrule] at h
        · simp [hrule] at h; cases h; simp [encodeCore_val]; omega
  · simp [hs0] at h

theorem rest_all_zero (L : Nat) (i : Fin L) (raw : List Bool)
    (slots : List (Fin (L + 1))) (out : Configuration (ns L) 3)
    (h : run (machine L) slots (stageStart L i raw 0 (stages_pos L)) = some out) :
    slots = List.replicate slots.length 0 := by
  have hcore : 3 ≤ (stageStart L i raw 0 (stages_pos L)).state.val := by
    simp [stageStart, liftConfig, encodeCore_val]; omega
  revert out
  suffices ∀ (c : Configuration (ns L) 3), 3 ≤ c.state.val →
      ∀ out, run (machine L) slots c = some out →
        slots = List.replicate slots.length 0 from this _ hcore
  intro c hc out hrun
  induction slots generalizing c with
  | nil => simp
  | cons slot rest ih =>
      rw [run_cons] at hrun
      cases hstep : step (machine L) slot c with
      | none => simp [hstep] at hrun
      | some mid =>
          simp [hstep] at hrun
          have hslot0 : slot = 0 := by
            by_contra hne
            unfold step at hstep
            rw [show (machine L).rule = ndRule L from rfl] at hstep
            rw [ndRule_slot_ne L c.state (c.tape c.head) slot hc hne] at hstep
            cases hstep
          subst slot
          have hmid : mid.state.val = 0 ∨ 3 ≤ mid.state.val := by
            unfold step at hstep
            rw [show (machine L).rule = ndRule L from rfl] at hstep
            have hne01 : ¬ (c.state.val = 0 ∨ c.state.val = 1) := by omega
            have hne2 : c.state.val ≠ 2 := by omega
            simp [ndRule, hne01, hne2] at hstep
            cases hdec : decodeCore L c.state with
            | none => simp [hdec] at hstep
            | some p =>
                simp [hdec] at hstep
                cases hcr : coreRule L p.1 p.2.1 p.2.2 (c.tape c.head) 0 with
                | none => simp [hcr] at hstep
                | some a =>
                    simp [hcr] at hstep
                    subst mid
                    exact coreRule_target L p.1 p.2.1 p.2.2 (c.tape c.head) 0 a hcr
          cases rest with
          | nil => simp
          | cons s rest =>
              cases hmid with
              | inl hacc =>
                  have hst : mid.state = (machine L).accept := Fin.ext (by simp [hacc])
                  have : run (machine L) (s :: rest) mid = none :=
                    run_accept_nonempty_none (machine L) mid hst (s :: rest) (by simp)
                  simp [this] at hrun
              | inr hge' =>
                  have ih' := ih mid hge' hrun
                  rw [ih']
                  have hlen :
                      (0 :: List.replicate (s :: rest).length (0 : Fin (L + 1))).length =
                        (s :: rest).length + 1 := by
                    rw [List.length_cons, List.length_replicate]
                  rw [hlen, ← List.replicate_succ]

theorem rest_len_le (L : Nat) (i : Fin L) (raw : List Bool) (t : Nat)
    (out : Configuration (ns L) 3)
    (h : run (machine L) (List.replicate t 0) (stageStart L i raw 0 (stages_pos L)) =
      some out) :
    t ≤ coreFuel L raw.length := by
  by_contra hlt
  have hlt' : coreFuel L raw.length < t := Nat.lt_of_not_ge hlt
  have hsplit : List.replicate t (0 : Fin (L + 1)) =
      List.replicate (coreFuel L raw.length) 0 ++
        List.replicate (t - coreFuel L raw.length) 0 := by
    rw [← List.replicate_add, Nat.add_sub_of_le (Nat.le_of_lt hlt')]
  rw [hsplit, run_append] at h
  have hfull := rest_run L i raw 0 (Nat.zero_le _)
  have : restFuel L raw.length 0 = coreFuel L raw.length := restFuel_zero L _
  simp [afterStage, stages_pos, this] at hfull
  simp [hfull] at h
  have hne : t - coreFuel L raw.length ≠ 0 := by omega
  have hnil : List.replicate (t - coreFuel L raw.length) (0 : Fin (L + 1)) ≠ [] := by
    intro hempty
    have := congrArg List.length hempty
    simp at this
    exact hne this
  have := run_accept_nonempty_none (machine L) (haltConfig L i raw)
    (by simp [haltConfig, machine]) (List.replicate (t - coreFuel L raw.length) 0) hnil
  simp [this] at h

theorem rest_accept_time (L : Nat) (i : Fin L) (raw : List Bool) (t : Nat)
    (out : Configuration (ns L) 3)
    (h : run (machine L) (List.replicate t 0) (stageStart L i raw 0 (stages_pos L)) =
      some out)
    (hacc : out.state = (machine L).accept) :
    t = coreFuel L raw.length ∧ out = haltConfig L i raw := by
  have hle := rest_len_le L i raw t out h
  have hsplit : List.replicate (coreFuel L raw.length) (0 : Fin (L + 1)) =
      List.replicate t 0 ++ List.replicate (coreFuel L raw.length - t) 0 := by
    rw [← List.replicate_add, Nat.add_sub_of_le hle]
  have hfull := rest_run L i raw 0 (Nat.zero_le _)
  have hz : restFuel L raw.length 0 = coreFuel L raw.length := restFuel_zero L _
  simp [afterStage, stages_pos, hz] at hfull
  have happ : run (machine L)
      (List.replicate t 0 ++ List.replicate (coreFuel L raw.length - t) 0)
      (stageStart L i raw 0 (stages_pos L)) = some (haltConfig L i raw) := by
    simpa [hsplit] using hfull
  rw [run_append, h, Option.bind_some] at happ
  cases hdiff : coreFuel L raw.length - t with
  | zero =>
      have : t = coreFuel L raw.length := by omega
      simp [hdiff] at happ
      exact ⟨this, happ⟩
  | succ n =>
      have hne : List.replicate (n + 1) (0 : Fin (L + 1)) ≠ [] := by simp
      have := run_accept_nonempty_none (machine L) out hacc
        (List.replicate (n + 1) 0) hne
      simp [hdiff, this] at happ

theorem accepted_inv (L : Nat) (raw : List Bool) (slots : List (Fin (L + 1)))
    (h : Accepted (machine L) raw slots) :
    ∃ i : Fin L, slots = word L raw i := by
  obtain ⟨out, hrun, hst⟩ := (accepted_iff (machine L) raw slots).mp h
  cases slots with
  | nil =>
      simp [run, initial, machine] at hrun
      subst out
      simp [machine] at hst
  | cons slot rest =>
      rw [run_cons] at hrun
      cases hstep : step (machine L) slot (initial (machine L) raw) with
      | none => simp [hstep] at hrun
      | some mid =>
          simp [hstep] at hrun
          have hi := step_from_start L raw slot mid hstep
          let i : Fin L := ⟨slot.val, hi⟩
          have hslot : slot = i.castSucc := Fin.ext rfl
          have hmid : mid = stageStart L i raw 0 (stages_pos L) := by
            have hch := choose_step L raw i
            rw [hslot] at hstep
            rw [hch] at hstep
            exact (Option.some.inj hstep).symm
          rw [hmid] at hrun
          have hzeros := rest_all_zero L i raw rest out hrun
          rw [hzeros] at hrun
          have htime := rest_accept_time L i raw rest.length out hrun
            (by simpa [machine_accept] using hst)
          refine ⟨i, ?_⟩
          rw [hslot, hzeros, htime.1]
          rfl

theorem accepted_iff_word (L : Nat) (raw : List Bool) (slots : List (Fin (L + 1))) :
    Accepted (machine L) raw slots ↔ ∃ i : Fin L, slots = word L raw i := by
  constructor
  · exact accepted_inv L raw slots
  · rintro ⟨i, rfl⟩; exact accepted_word L raw i

theorem choose_runsAtMost (L : Nat) (raw : List Bool) :
    RunsAtMost (machine L) raw ((boundPoly L).eval raw.length) := by
  intro slots out hrun
  have hbound : (boundPoly L).eval raw.length = 1 + coreFuel L raw.length := by
    simp [boundPoly_eval, coreFuel]; ring
  cases slots with
  | nil => simp
  | cons slot rest =>
      rw [run_cons] at hrun
      cases hstep : step (machine L) slot (initial (machine L) raw) with
      | none => simp [hstep] at hrun
      | some mid =>
          simp [hstep] at hrun
          have hi := step_from_start L raw slot mid hstep
          let i : Fin L := ⟨slot.val, hi⟩
          have hslot : slot = i.castSucc := Fin.ext rfl
          have hmid : mid = stageStart L i raw 0 (stages_pos L) := by
            have hch := choose_step L raw i
            rw [hslot] at hstep
            rw [hch] at hstep
            exact (Option.some.inj hstep).symm
          rw [hmid] at hrun
          have hzeros := rest_all_zero L i raw rest out hrun
          rw [hzeros] at hrun
          have hlen := rest_len_le L i raw rest.length out hrun
          simp [hbound]
          omega

def acceptingOf (L : Nat) (raw : List Bool) (i : Fin L) :
    AcceptingCode (machine L) raw ((boundPoly L).eval raw.length) :=
  ⟨WordCode.ofList (word L raw i) (Nat.le_of_eq (word_length L raw i)), by
    simpa using accepted_word L raw i⟩

theorem acceptingOf_injective (L : Nat) (raw : List Bool) :
    Function.Injective (acceptingOf L raw) := by
  intro i j h
  have hlist : word L raw i = word L raw j := by
    have := congrArg (fun c : AcceptingCode (machine L) raw _ => c.val.toList) h
    simpa [acceptingOf] using this
  have hhead : i.castSucc = j.castSucc := by
    have := congrArg List.head? hlist
    simpa [word] using this
  exact Fin.castSucc_injective _ hhead

theorem acceptingOf_surjective (L : Nat) (raw : List Bool) :
    Function.Surjective (acceptingOf L raw) := by
  intro code
  obtain ⟨i, hi⟩ := (accepted_iff_word L raw code.val.toList).mp code.property
  refine ⟨i, ?_⟩
  apply Subtype.ext
  apply WordCode.toList_injective
  simpa [acceptingOf] using hi.symm

noncomputable def acceptingEquiv (L : Nat) (raw : List Bool) :
    Fin L ≃ AcceptingCode (machine L) raw ((boundPoly L).eval raw.length) :=
  Equiv.ofBijective (acceptingOf L raw)
    ⟨acceptingOf_injective L raw, acceptingOf_surjective L raw⟩

theorem choose_count (L : Nat) (raw : List Bool) :
    acceptingCount (machine L) raw ((boundPoly L).eval raw.length) = L := by
  rw [acceptingCount, ← Fintype.card_congr (acceptingEquiv L raw), Fintype.card_fin]

theorem word_output (L : Nat) (raw : List Bool) (i : Fin L) :
    run (machine L) (word L raw i) (initial (machine L) raw) =
      some ⟨(machine L).accept, 0,
        inputTape (machine L) (pairBits (labelCode L i) raw)⟩ := by
  simpa [haltConfig, machine] using word_run L raw i

theorem choose_zero (raw : List Bool) :
    (∀ slots, ¬ Accepted (machine 0) raw slots) ∧
    acceptingCount (machine 0) raw ((boundPoly 0).eval raw.length) = 0 := by
  constructor
  · intro slots h
    obtain ⟨i, _⟩ := (accepted_iff_word 0 raw slots).mp h
    exact i.elim0
  · simpa using choose_count 0 raw

theorem choose_spec (L : Nat) (raw : List Bool) :
    RunsAtMost (machine L) raw ((boundPoly L).eval raw.length) ∧
    acceptingCount (machine L) raw ((boundPoly L).eval raw.length) = L ∧
    (∀ slots, Accepted (machine L) raw slots ↔ ∃ i : Fin L, slots = word L raw i) ∧
    (∀ i : Fin L,
      run (machine L) (word L raw i) (initial (machine L) raw) =
        some ⟨(machine L).accept, 0,
          inputTape (machine L) (pairBits (labelCode L i) raw)⟩) :=
  ⟨choose_runsAtMost L raw, choose_count L raw,
    accepted_iff_word L raw, word_output L raw⟩

end
end PakFixedPolyomino.StandardBitFiniteChoicePrefix
