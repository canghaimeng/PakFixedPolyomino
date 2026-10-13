import PakFixedPolyomino.StandardBitTime
import Mathlib.Tactic

/-! # Common-alphabet deterministic one-tape composition

Any two ordinary deterministic machines, possibly with different finite
alphabets and binary/blank codes, are relabelled into a shared alphabet
with common `0/1/2`. One stay/write hands the first accept state to the
second start state. Combined accept/reject are the second machine's
halting codes. Extra unused codes have no rules.
-/

namespace PakFixedPolyomino.StandardBitMachineComposition

open StandardNondeterministicMachine StandardBitTime
open FiniteOneTapeSemantics (moveHead writtenTape)

variable {nsA ntA nsB ntB : ℕ}

theorem config_ext {ns nt : ℕ} (c₁ c₂ : Configuration ns nt)
    (hs : c₁.state = c₂.state) (hh : c₁.head = c₂.head)
    (ht : c₁.tape = c₂.tape) : c₁ = c₂ := by
  cases c₁; cases c₂; simp_all

def acceptC : Fin (nsA + nsB + 2) := ⟨0, by omega⟩
def rejectC : Fin (nsA + nsB + 2) := ⟨1, by omega⟩
def zeroC : Fin (ntA + ntB + 3) := ⟨0, by omega⟩
def oneC : Fin (ntA + ntB + 3) := ⟨1, by omega⟩
def blankC : Fin (ntA + ntB + 3) := ⟨2, by omega⟩

def encodeTapeA (M : DeterministicMachine nsA ntA) (x : Fin ntA) :
    Fin (ntA + ntB + 3) :=
  if x = M.zero then ⟨0, by omega⟩
  else if x = M.one then ⟨1, by omega⟩
  else if x = M.blank then ⟨2, by omega⟩
  else ⟨3 + x.val, by have := x.isLt; omega⟩

def encodeTapeB (N : DeterministicMachine nsB ntB) (x : Fin ntB) :
    Fin (ntA + ntB + 3) :=
  if x = N.zero then ⟨0, by omega⟩
  else if x = N.one then ⟨1, by omega⟩
  else if x = N.blank then ⟨2, by omega⟩
  else ⟨3 + ntA + x.val, by have := x.isLt; omega⟩

def decodeTapeA (M : DeterministicMachine nsA ntA) (y : Fin (ntA + ntB + 3)) :
    Option (Fin ntA) :=
  if y.val = 0 then some M.zero
  else if y.val = 1 then some M.one
  else if y.val = 2 then some M.blank
  else if h : 3 ≤ y.val ∧ y.val - 3 < ntA then
    let x : Fin ntA := ⟨y.val - 3, h.2⟩
    if x = M.zero ∨ x = M.one ∨ x = M.blank then none else some x
  else none

def decodeTapeB (N : DeterministicMachine nsB ntB) (y : Fin (ntA + ntB + 3)) :
    Option (Fin ntB) :=
  if y.val = 0 then some N.zero
  else if y.val = 1 then some N.one
  else if y.val = 2 then some N.blank
  else if h : 3 + ntA ≤ y.val ∧ y.val - (3 + ntA) < ntB then
    let x : Fin ntB := ⟨y.val - (3 + ntA), h.2⟩
    if x = N.zero ∨ x = N.one ∨ x = N.blank then none else some x
  else none

theorem encodeTapeA_zero (M : DeterministicMachine nsA ntA) :
    encodeTapeA (ntB := ntB) M M.zero = ⟨0, by omega⟩ := by
  unfold encodeTapeA
  rw [if_pos rfl]

theorem encodeTapeA_one (M : DeterministicMachine nsA ntA) :
    encodeTapeA (ntB := ntB) M M.one = ⟨1, by omega⟩ := by
  unfold encodeTapeA
  rw [if_neg M.zero_ne_one.symm, if_pos rfl]

theorem encodeTapeA_blank (M : DeterministicMachine nsA ntA) :
    encodeTapeA (ntB := ntB) M M.blank = ⟨2, by omega⟩ := by
  unfold encodeTapeA
  rw [if_neg M.blank_ne_zero, if_neg M.blank_ne_one, if_pos rfl]

theorem encodeTapeB_zero (N : DeterministicMachine nsB ntB) :
    encodeTapeB (ntA := ntA) N N.zero = ⟨0, by omega⟩ := by
  unfold encodeTapeB
  rw [if_pos rfl]

theorem encodeTapeB_one (N : DeterministicMachine nsB ntB) :
    encodeTapeB (ntA := ntA) N N.one = ⟨1, by omega⟩ := by
  unfold encodeTapeB
  rw [if_neg N.zero_ne_one.symm, if_pos rfl]

theorem encodeTapeB_blank (N : DeterministicMachine nsB ntB) :
    encodeTapeB (ntA := ntA) N N.blank = ⟨2, by omega⟩ := by
  unfold encodeTapeB
  rw [if_neg N.blank_ne_zero, if_neg N.blank_ne_one, if_pos rfl]

theorem encodeTapeA_other (M : DeterministicMachine nsA ntA) (x : Fin ntA)
    (hz : x ≠ M.zero) (ho : x ≠ M.one) (hb : x ≠ M.blank) :
    encodeTapeA (ntB := ntB) M x =
      ⟨3 + x.val, by have := x.isLt; omega⟩ := by
  unfold encodeTapeA
  rw [if_neg hz, if_neg ho, if_neg hb]

theorem encodeTapeB_other (N : DeterministicMachine nsB ntB) (x : Fin ntB)
    (hz : x ≠ N.zero) (ho : x ≠ N.one) (hb : x ≠ N.blank) :
    encodeTapeB (ntA := ntA) N x =
      ⟨3 + ntA + x.val, by have := x.isLt; omega⟩ := by
  unfold encodeTapeB
  rw [if_neg hz, if_neg ho, if_neg hb]

theorem decodeTapeA_encode (M : DeterministicMachine nsA ntA) (x : Fin ntA) :
    decodeTapeA (ntB := ntB) M (encodeTapeA (ntB := ntB) M x) = some x := by
  by_cases hz : x = M.zero
  · subst hz
    rw [encodeTapeA_zero, decodeTapeA]
    simp
  · by_cases ho : x = M.one
    · subst ho
      rw [encodeTapeA_one, decodeTapeA]
      simp
    · by_cases hb : x = M.blank
      · subst hb
        rw [encodeTapeA_blank, decodeTapeA]
        simp
      · rw [encodeTapeA_other (ntB := ntB) M x hz ho hb, decodeTapeA]
        have hxlt := x.isLt
        have n0 : ¬(3 + x.val = 0) := by omega
        have n1 : ¬(3 + x.val = 1) := by omega
        have n2 : ¬(3 + x.val = 2) := by omega
        have hr : 3 ≤ 3 + x.val ∧ 3 + x.val - 3 < ntA := by omega
        rw [if_neg n0, if_neg n1, if_neg n2, dif_pos hr]
        have hx' : (⟨3 + x.val - 3, hr.2⟩ : Fin ntA) = x := by
          apply Fin.ext
          have : 3 + x.val - 3 = x.val := by omega
          simpa
        simp [hx', hz, ho, hb]

theorem decodeTapeB_encode (N : DeterministicMachine nsB ntB) (x : Fin ntB) :
    decodeTapeB (ntA := ntA) N (encodeTapeB (ntA := ntA) N x) = some x := by
  by_cases hz : x = N.zero
  · subst hz
    rw [encodeTapeB_zero, decodeTapeB]
    simp
  · by_cases ho : x = N.one
    · subst ho
      rw [encodeTapeB_one, decodeTapeB]
      simp
    · by_cases hb : x = N.blank
      · subst hb
        rw [encodeTapeB_blank, decodeTapeB]
        simp
      · rw [encodeTapeB_other (ntA := ntA) N x hz ho hb, decodeTapeB]
        have hxlt := x.isLt
        have n0 : ¬(3 + ntA + x.val = 0) := by omega
        have n1 : ¬(3 + ntA + x.val = 1) := by omega
        have n2 : ¬(3 + ntA + x.val = 2) := by omega
        have hr : 3 + ntA ≤ 3 + ntA + x.val ∧
            3 + ntA + x.val - (3 + ntA) < ntB := by omega
        rw [if_neg n0, if_neg n1, if_neg n2, dif_pos hr]
        have hx' : (⟨3 + ntA + x.val - (3 + ntA), hr.2⟩ : Fin ntB) = x := by
          apply Fin.ext
          have : 3 + ntA + x.val - (3 + ntA) = x.val := by omega
          simpa
        simp [hx', hz, ho, hb]

def encodeStateA (q : Fin nsA) : Fin (nsA + nsB + 2) :=
  ⟨2 + q.val, by have := q.isLt; omega⟩

def encodeStateB (N : DeterministicMachine nsB ntB) (q : Fin nsB) :
    Fin (nsA + nsB + 2) :=
  if q = N.accept then ⟨0, by omega⟩
  else if q = N.reject then ⟨1, by omega⟩
  else ⟨2 + nsA + q.val, by have := q.isLt; omega⟩

def decodeStateA (q : Fin (nsA + nsB + 2)) : Option (Fin nsA) :=
  if h : 2 ≤ q.val ∧ q.val < 2 + nsA then
    some ⟨q.val - 2, by omega⟩
  else none

def decodeStateB (q : Fin (nsA + nsB + 2)) : Option (Fin nsB) :=
  if h : 2 + nsA ≤ q.val ∧ q.val < 2 + nsA + nsB then
    some ⟨q.val - (2 + nsA), by omega⟩
  else none

theorem encodeStateA_val (q : Fin nsA) :
    (encodeStateA (nsB := nsB) q).val = 2 + q.val := rfl

theorem encodeStateA_ne_zero (q : Fin nsA) :
    (encodeStateA (nsB := nsB) q).val ≠ 0 := by
  have := q.isLt
  simp [encodeStateA]

theorem encodeStateA_ne_one (q : Fin nsA) :
    (encodeStateA (nsB := nsB) q).val ≠ 1 := by
  have := q.isLt
  simp [encodeStateA]
  omega

theorem encodeStateA_range (q : Fin nsA) :
    2 ≤ (encodeStateA (nsB := nsB) q).val ∧
      (encodeStateA (nsB := nsB) q).val < 2 + nsA := by
  have := q.isLt
  simp [encodeStateA]

theorem decodeStateA_encode (q : Fin nsA) :
    decodeStateA (nsB := nsB) (encodeStateA (nsB := nsB) q) = some q := by
  have hr := encodeStateA_range (nsB := nsB) q
  unfold decodeStateA
  rw [dif_pos hr]
  apply congrArg some
  apply Fin.ext
  have := q.isLt
  simp [encodeStateA]

theorem encodeStateB_accept (N : DeterministicMachine nsB ntB) :
    encodeStateB (nsA := nsA) N N.accept = acceptC := by
  unfold encodeStateB acceptC
  rw [if_pos rfl]

theorem encodeStateB_reject (N : DeterministicMachine nsB ntB) :
    encodeStateB (nsA := nsA) N N.reject = rejectC := by
  unfold encodeStateB rejectC
  rw [if_neg N.accept_ne_reject.symm, if_pos rfl]

theorem encodeStateB_other (N : DeterministicMachine nsB ntB) (q : Fin nsB)
    (ha : q ≠ N.accept) (hr : q ≠ N.reject) :
    encodeStateB (nsA := nsA) N q =
      ⟨2 + nsA + q.val, by have := q.isLt; omega⟩ := by
  unfold encodeStateB
  rw [if_neg ha, if_neg hr]

theorem decodeStateB_encode_other (N : DeterministicMachine nsB ntB)
    (q : Fin nsB) (ha : q ≠ N.accept) (hr : q ≠ N.reject) :
    decodeStateB (nsA := nsA) (encodeStateB (nsA := nsA) N q) = some q := by
  have henc := encodeStateB_other (nsA := nsA) N q ha hr
  have hrange : 2 + nsA ≤ (encodeStateB (nsA := nsA) N q).val ∧
      (encodeStateB (nsA := nsA) N q).val < 2 + nsA + nsB := by
    rw [henc]
    have := q.isLt
    simp
  unfold decodeStateB
  rw [dif_pos hrange]
  apply congrArg some
  apply Fin.ext
  have := q.isLt
  simp [henc]

def liftActionA (M : DeterministicMachine nsA ntA)
    (a : FiniteOneTapeProgram.Action (Fin nsA) (Fin ntA)) :
    FiniteOneTapeProgram.Action (Fin (nsA + nsB + 2)) (Fin (ntA + ntB + 3)) where
  write := encodeTapeA (ntB := ntB) M a.write
  target := encodeStateA (nsB := nsB) a.target
  move := a.move

def liftActionB (N : DeterministicMachine nsB ntB)
    (a : FiniteOneTapeProgram.Action (Fin nsB) (Fin ntB)) :
    FiniteOneTapeProgram.Action (Fin (nsA + nsB + 2)) (Fin (ntA + ntB + 3)) where
  write := encodeTapeB (ntA := ntA) N a.write
  target := encodeStateB (nsA := nsA) N a.target
  move := a.move

def handoffAction (N : DeterministicMachine nsB ntB)
    (x : Fin (ntA + ntB + 3)) :
    FiniteOneTapeProgram.Action (Fin (nsA + nsB + 2)) (Fin (ntA + ntB + 3)) where
  write := x
  target := encodeStateB (nsA := nsA) N N.start
  move := PakFixedPolyomino.OneTapeTableau.Move.stay

def composedRule (M : DeterministicMachine nsA ntA)
    (N : DeterministicMachine nsB ntB)
    (q : Fin (nsA + nsB + 2)) (x : Fin (ntA + ntB + 3)) (_slot : Fin 1) :
    Option (FiniteOneTapeProgram.Action (Fin (nsA + nsB + 2))
      (Fin (ntA + ntB + 3))) :=
  (decodeStateA (nsB := nsB) q).elim
    ((decodeStateB (nsA := nsA) q).elim none fun qB =>
      if qB = N.accept ∨ qB = N.reject then none
      else (decodeTapeB (ntA := ntA) N x).bind fun b =>
        (N.rule qB b 0).map (liftActionB N))
    fun qA =>
      if qA = M.accept then some (handoffAction N x)
      else (decodeTapeA (ntB := ntB) M x).bind fun a =>
        (M.rule qA a 0).map (liftActionA M)

def compose (M : DeterministicMachine nsA ntA)
    (N : DeterministicMachine nsB ntB) :
    DeterministicMachine (nsA + nsB + 2) (ntA + ntB + 3) where
  rule := composedRule M N
  start := encodeStateA (nsB := nsB) M.start
  accept := acceptC
  reject := rejectC
  accept_ne_reject := by
    intro h
    exact Nat.zero_ne_one (congrArg Fin.val h)
  blank := blankC
  zero := zeroC
  one := oneC
  blank_ne_zero := by
    intro h
    have hv := congrArg Fin.val h
    simp [blankC, zeroC] at hv
  blank_ne_one := by
    intro h
    have hv := congrArg Fin.val h
    simp [blankC, oneC] at hv
  zero_ne_one := by
    intro h
    exact Nat.zero_ne_one (congrArg Fin.val h)
  accept_terminal := by
    intro x slot
    have hA : decodeStateA (nsB := nsB) (acceptC (nsA := nsA) (nsB := nsB)) =
        none := by
      have : ¬(2 ≤ (0 : ℕ) ∧ 0 < 2 + nsA) := by omega
      simp [decodeStateA, acceptC, this]
    have hB : decodeStateB (nsA := nsA) (nsB := nsB)
        (acceptC (nsA := nsA) (nsB := nsB)) = none := by
      have : ¬(2 + nsA ≤ (0 : ℕ) ∧ 0 < 2 + nsA + nsB) := by omega
      simp [decodeStateB, acceptC, this]
    simp [composedRule, hA, hB]
  reject_terminal := by
    intro x slot
    have hA : decodeStateA (nsB := nsB) (rejectC (nsA := nsA) (nsB := nsB)) =
        none := by
      have : ¬(2 ≤ (1 : ℕ) ∧ 1 < 2 + nsA) := by omega
      simp [decodeStateA, rejectC, this]
    have hB : decodeStateB (nsA := nsA) (nsB := nsB)
        (rejectC (nsA := nsA) (nsB := nsB)) = none := by
      have : ¬(2 + nsA ≤ (1 : ℕ) ∧ 1 < 2 + nsA + nsB) := by omega
      simp [decodeStateB, rejectC, this]
    simp [composedRule, hA, hB]

theorem compose_symbols (M : DeterministicMachine nsA ntA)
    (N : DeterministicMachine nsB ntB) :
    (compose M N).zero = zeroC ∧ (compose M N).one = oneC ∧
      (compose M N).blank = blankC ∧ (compose M N).accept = acceptC ∧
      (compose M N).start = encodeStateA (nsB := nsB) M.start :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem encodeTapeA_bit (M : DeterministicMachine nsA ntA) (b : Bool) :
    encodeTapeA (ntB := ntB) M (if b then M.one else M.zero) =
      if b then (⟨1, by omega⟩ : Fin (ntA + ntB + 3)) else ⟨0, by omega⟩ := by
  cases b
  · exact encodeTapeA_zero (ntB := ntB) M
  · exact encodeTapeA_one (ntB := ntB) M

theorem encodeTapeB_bit (N : DeterministicMachine nsB ntB) (b : Bool) :
    encodeTapeB (ntA := ntA) N (if b then N.one else N.zero) =
      if b then (⟨1, by omega⟩ : Fin (ntA + ntB + 3)) else ⟨0, by omega⟩ := by
  cases b
  · exact encodeTapeB_zero (ntA := ntA) N
  · exact encodeTapeB_one (ntA := ntA) N

theorem encodeTapeA_input (M : DeterministicMachine nsA ntA)
    (N : DeterministicMachine nsB ntB) (x : List Bool) (z : Int) :
    encodeTapeA (ntB := ntB) M (inputTape M x z) =
      inputTape (compose M N) x z := by
  by_cases hz : 0 ≤ z
  · by_cases hi : z.toNat < x.length
    · cases hbit : x[z.toNat]
      · simp [inputTape, hz, hi, hbit, encodeTapeA_zero, compose, zeroC]
      · simp [inputTape, hz, hi, hbit, encodeTapeA_one, compose, oneC]
    · simp [inputTape, hz, hi, encodeTapeA_blank, compose, blankC]
  · simp [inputTape, hz, encodeTapeA_blank, compose, blankC]

theorem encodeTapeB_input (M : DeterministicMachine nsA ntA)
    (N : DeterministicMachine nsB ntB) (x : List Bool) (z : Int) :
    encodeTapeB (ntA := ntA) N (inputTape N x z) =
      inputTape (compose M N) x z := by
  by_cases hz : 0 ≤ z
  · by_cases hi : z.toNat < x.length
    · cases hbit : x[z.toNat]
      · simp [inputTape, hz, hi, hbit, encodeTapeB_zero, compose, zeroC]
      · simp [inputTape, hz, hi, hbit, encodeTapeB_one, compose, oneC]
    · simp [inputTape, hz, hi, encodeTapeB_blank, compose, blankC]
  · simp [inputTape, hz, encodeTapeB_blank, compose, blankC]

def encodeConfigA (M : DeterministicMachine nsA ntA)
    (c : Configuration nsA ntA) : Configuration (nsA + nsB + 2) (ntA + ntB + 3) :=
  { state := encodeStateA (nsB := nsB) c.state
    head := c.head
    tape := fun z => encodeTapeA (ntB := ntB) M (c.tape z) }

def encodeConfigB (N : DeterministicMachine nsB ntB)
    (c : Configuration nsB ntB) : Configuration (nsA + nsB + 2) (ntA + ntB + 3) :=
  { state := encodeStateB (nsA := nsA) N c.state
    head := c.head
    tape := fun z => encodeTapeB (ntA := ntA) N (c.tape z) }

theorem encodeConfigA_initial (M : DeterministicMachine nsA ntA)
    (N : DeterministicMachine nsB ntB) (x : List Bool) :
    encodeConfigA (nsB := nsB) (ntB := ntB) M (initial M x) =
      initial (compose M N) x := by
  apply config_ext
  · rfl
  · rfl
  · funext z
    exact encodeTapeA_input M N x z

theorem encodeConfigB_initial (M : DeterministicMachine nsA ntA)
    (N : DeterministicMachine nsB ntB) (x : List Bool) :
    encodeConfigB (nsA := nsA) (ntA := ntA) N (initial N x) =
      { state := encodeStateB (nsA := nsA) N N.start
        head := 0
        tape := inputTape (compose M N) x } := by
  apply config_ext
  · rfl
  · rfl
  · funext z
    exact encodeTapeB_input M N x z

theorem encode_updateA (M : DeterministicMachine nsA ntA)
    (tape : Int → Fin ntA) (head : Int) (w : Fin ntA) :
    (fun z => encodeTapeA (ntB := ntB) M (Function.update tape head w z)) =
      Function.update (fun z => encodeTapeA (ntB := ntB) M (tape z)) head
        (encodeTapeA (ntB := ntB) M w) := by
  funext z
  by_cases hz : z = head
  · subst z; simp [Function.update_self]
  · simp [Function.update_of_ne hz]

theorem encode_updateB (N : DeterministicMachine nsB ntB)
    (tape : Int → Fin ntB) (head : Int) (w : Fin ntB) :
    (fun z => encodeTapeB (ntA := ntA) N (Function.update tape head w z)) =
      Function.update (fun z => encodeTapeB (ntA := ntA) N (tape z)) head
        (encodeTapeB (ntA := ntA) N w) := by
  funext z
  by_cases hz : z = head
  · subst z; simp [Function.update_self]
  · simp [Function.update_of_ne hz]

theorem composedRule_phaseA (M : DeterministicMachine nsA ntA)
    (N : DeterministicMachine nsB ntB) (q : Fin nsA) (x : Fin ntA)
    (hacc : q ≠ M.accept) :
    composedRule M N (encodeStateA (nsB := nsB) q)
      (encodeTapeA (ntB := ntB) M x) 0 =
      (M.rule q x 0).map (liftActionA M) := by
  simp [composedRule, decodeStateA_encode, hacc, decodeTapeA_encode]

theorem composedRule_handoff (M : DeterministicMachine nsA ntA)
    (N : DeterministicMachine nsB ntB) (x : Fin (ntA + ntB + 3)) :
    composedRule M N (encodeStateA (nsB := nsB) M.accept) x 0 =
      some (handoffAction N x) := by
  simp [composedRule, decodeStateA_encode]

theorem composedRule_phaseB (M : DeterministicMachine nsA ntA)
    (N : DeterministicMachine nsB ntB) (q : Fin nsB) (x : Fin ntB)
    (hacc : q ≠ N.accept) (hrej : q ≠ N.reject) :
    composedRule M N (encodeStateB (nsA := nsA) N q)
      (encodeTapeB (ntA := ntA) N x) 0 =
      (N.rule q x 0).map (liftActionB N) := by
  have hA : decodeStateA (nsB := nsB) (encodeStateB (nsA := nsA) N q) = none := by
    have henc := encodeStateB_other (nsA := nsA) N q hacc hrej
    have hn : ¬(2 ≤ (encodeStateB (nsA := nsA) N q).val ∧
        (encodeStateB (nsA := nsA) N q).val < 2 + nsA) := by
      rw [henc]
      have := q.isLt
      simp
    simp [decodeStateA, hn]
  simp [composedRule, hA, decodeStateB_encode_other, hacc, hrej,
    decodeTapeB_encode]

theorem step_phaseA (M : DeterministicMachine nsA ntA)
    (N : DeterministicMachine nsB ntB) (c : Configuration nsA ntA)
    (hacc : c.state ≠ M.accept) :
    step (compose M N) 0 (encodeConfigA (nsB := nsB) (ntB := ntB) M c) =
      (step M 0 c).map (encodeConfigA (nsB := nsB) (ntB := ntB) M) := by
  simp only [step, compose, encodeConfigA]
  rw [composedRule_phaseA M N c.state (c.tape c.head) hacc]
  cases hrule : M.rule c.state (c.tape c.head) 0 with
  | none => simp
  | some a =>
      simp [liftActionA, writtenTape, moveHead, encodeConfigA]
      exact (encode_updateA (ntB := ntB) M c.tape c.head a.write).symm

theorem step_handoff (M : DeterministicMachine nsA ntA)
    (N : DeterministicMachine nsB ntB) (c : Configuration nsA ntA)
    (hacc : c.state = M.accept) :
    step (compose M N) 0 (encodeConfigA (nsB := nsB) (ntB := ntB) M c) =
      some { state := encodeStateB (nsA := nsA) N N.start
             head := c.head
             tape := fun z => encodeTapeA (ntB := ntB) M (c.tape z) } := by
  simp only [step, compose, encodeConfigA, hacc]
  rw [composedRule_handoff M N (encodeTapeA (ntB := ntB) M (c.tape c.head))]
  simp [handoffAction, writtenTape, moveHead]

theorem step_phaseB (M : DeterministicMachine nsA ntA)
    (N : DeterministicMachine nsB ntB) (c : Configuration nsB ntB)
    (hacc : c.state ≠ N.accept) (hrej : c.state ≠ N.reject) :
    step (compose M N) 0 (encodeConfigB (nsA := nsA) (ntA := ntA) N c) =
      (step N 0 c).map (encodeConfigB (nsA := nsA) (ntA := ntA) N) := by
  simp only [step, compose, encodeConfigB]
  rw [composedRule_phaseB M N c.state (c.tape c.head) hacc hrej]
  cases hrule : N.rule c.state (c.tape c.head) 0 with
  | none => simp
  | some a =>
      simp [liftActionB, writtenTape, moveHead, encodeConfigB]
      exact (encode_updateB (ntA := ntA) N c.tape c.head a.write).symm

theorem ticks_succ (n : ℕ) : ticks (n + 1) = (0 : Fin 1) :: ticks n := rfl

theorem run_phaseA (M : DeterministicMachine nsA ntA)
    (N : DeterministicMachine nsB ntB) (c : Configuration nsA ntA) (n : ℕ)
    (out : Configuration nsA ntA)
    (hrun : run M (ticks n) c = some out) :
    run (compose M N) (ticks n) (encodeConfigA (nsB := nsB) (ntB := ntB) M c) =
      some (encodeConfigA (nsB := nsB) (ntB := ntB) M out) := by
  induction n generalizing c with
  | zero =>
      have heq : c = out := Option.some.inj hrun
      subst out
      simp [ticks]
  | succ n ih =>
      rw [ticks_succ] at hrun ⊢
      have hne : c.state ≠ M.accept := by
        intro hacc
        have hnone :=
          run_accept_nonempty_none M c hacc (0 :: ticks n) (List.cons_ne_nil _ _)
        rw [hnone] at hrun
        cases hrun
      rw [run_cons] at hrun ⊢
      have hstep := step_phaseA M N c hne
      cases hs : step M 0 c with
      | none => simp [hs] at hrun
      | some middle =>
          simp [hs] at hrun
          simp [hstep, hs]
          exact ih middle hrun

theorem run_phaseB (M : DeterministicMachine nsA ntA)
    (N : DeterministicMachine nsB ntB) (c : Configuration nsB ntB) (n : ℕ)
    (out : Configuration nsB ntB)
    (hrun : run N (ticks n) c = some out) :
    run (compose M N) (ticks n) (encodeConfigB (nsA := nsA) (ntA := ntA) N c) =
      some (encodeConfigB (nsA := nsA) (ntA := ntA) N out) := by
  induction n generalizing c with
  | zero =>
      have heq : c = out := Option.some.inj hrun
      subst out
      simp [ticks]
  | succ n ih =>
      rw [ticks_succ] at hrun ⊢
      have hneA : c.state ≠ N.accept := by
        intro hacc
        have hnone :=
          run_accept_nonempty_none N c hacc (0 :: ticks n) (List.cons_ne_nil _ _)
        rw [hnone] at hrun
        cases hrun
      have hneR : c.state ≠ N.reject := by
        intro hrej
        have hnone : run N (0 :: ticks n) c = none := by
          rw [run_cons, step_reject_none N 0 c hrej]
          simp
        rw [hnone] at hrun
        cases hrun
      rw [run_cons] at hrun ⊢
      have hstep := step_phaseB M N c hneA hneR
      cases hs : step N 0 c with
      | none => simp [hs] at hrun
      | some middle =>
          simp [hs] at hrun
          simp [hstep, hs]
          exact ih middle hrun

theorem handoff_from_output (M : DeterministicMachine nsA ntA)
    (N : DeterministicMachine nsB ntB) (y : List Bool)
    (out : Configuration nsA ntA) (hout : Output M y out) :
    step (compose M N) 0 (encodeConfigA (nsB := nsB) (ntB := ntB) M out) =
      some (encodeConfigB (nsA := nsA) (ntA := ntA) N (initial N y)) := by
  have hstep := step_handoff M N out hout.1
  rw [hstep]
  apply congrArg some
  apply config_ext
  · rfl
  · exact hout.2.1
  · funext z
    have ht := hout.2.2
    simp [encodeConfigB, initial]
    rw [ht]
    exact (encodeTapeA_input M N y z).trans (encodeTapeB_input M N y z).symm

theorem compose_run (M : DeterministicMachine nsA ntA)
    (N : DeterministicMachine nsB ntB) (f g : List Bool → List Bool)
    (x : List Bool) (n m : ℕ)
    (outM : Configuration nsA ntA) (outN : Configuration nsB ntB)
    (hrunM : run M (ticks n) (initial M x) = some outM)
    (houtM : Output M (f x) outM)
    (hrunN : run N (ticks m) (initial N (f x)) = some outN)
    (_houtN : Output N (g (f x)) outN) :
    run (compose M N) (ticks (n + 1 + m)) (initial (compose M N) x) =
      some (encodeConfigB (nsA := nsA) (ntA := ntA) N outN) := by
  have hsplit : n + 1 + m = n + (1 + m) := by omega
  rw [hsplit, ticks_add, run_append]
  have hA := run_phaseA M N (initial M x) n outM hrunM
  rw [← encodeConfigA_initial M N x, hA, Option.bind_some]
  rw [ticks_add, run_append]
  have hH := handoff_from_output M N (f x) outM houtM
  have h1 : ticks 1 = [0] := rfl
  simp [h1, run_cons, hH]
  exact run_phaseB M N (initial N (f x)) m outN hrunN

theorem encodeConfigB_output (M : DeterministicMachine nsA ntA)
    (N : DeterministicMachine nsB ntB) (y : List Bool)
    (out : Configuration nsB ntB) (hout : Output N y out) :
    Output (compose M N) y (encodeConfigB (nsA := nsA) (ntA := ntA) N out) := by
  refine ⟨?_, ?_, ?_⟩
  · change encodeStateB (nsA := nsA) N out.state = (compose M N).accept
    rw [hout.1, encodeStateB_accept, compose]
  · exact hout.2.1
  · funext z
    simp [encodeConfigB, hout.2.2]
    exact encodeTapeB_input M N y z

/-- Combined run uses exactly `n+1+m` physical transitions and writes the
clean output of `g (f x)`, including zero-step and originally halting starts. -/
theorem compose_exact (M : DeterministicMachine nsA ntA)
    (N : DeterministicMachine nsB ntB) (f g : List Bool → List Bool)
    (x : List Bool) (n m : ℕ)
    (outM : Configuration nsA ntA) (outN : Configuration nsB ntB)
    (hrunM : run M (ticks n) (initial M x) = some outM)
    (houtM : Output M (f x) outM)
    (hrunN : run N (ticks m) (initial N (f x)) = some outN)
    (houtN : Output N (g (f x)) outN) :
    run (compose M N) (ticks (n + 1 + m)) (initial (compose M N) x) =
      some (encodeConfigB (nsA := nsA) (ntA := ntA) N outN) ∧
      Output (compose M N) (g (f x))
        (encodeConfigB (nsA := nsA) (ntA := ntA) N outN) :=
  ⟨compose_run M N f g x n m outM outN hrunM houtM hrunN houtN,
    encodeConfigB_output M N (g (f x)) outN houtN⟩

end PakFixedPolyomino.StandardBitMachineComposition
