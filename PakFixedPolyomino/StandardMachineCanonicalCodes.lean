import PakFixedPolyomino.StandardMachineBinaryChoices
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # Canonical numeric codes for ordinary two-slot machines

An ordinary finite two-slot machine is recoded onto reserved start/accept/reject
and zero/one/blank numbers by injecting original states and letters past the
reserved codes 0,1,2. A single genuine boot transition from start state 2
writes back the scanned letter, stays, and enters the encoded original start.
Accept/reject remain terminal. Unused numeric gaps are blocked. Every raw
target history after that unique boot is an encoded original run; accepting
leaves are exactly `0 ::` original leaves, with time bound increased by one
and identical accepting counts.
-/

namespace PakFixedPolyomino.StandardMachineCanonicalCodes

open StandardNondeterministicMachine
open FiniteOneTapeSemantics (Config moveHead writtenTape)

variable {ns nt : ℕ}

def stateCode (M : Machine ns nt 2) (q : Fin ns) : Fin (ns + 3) :=
  if q = M.accept then ⟨0, by omega⟩
  else if q = M.reject then ⟨1, by omega⟩
  else ⟨q.val + 3, by omega⟩

def letterCode (M : Machine ns nt 2) (x : Fin nt) : Fin (nt + 3) :=
  if x = M.zero then ⟨0, by omega⟩
  else if x = M.one then ⟨1, by omega⟩
  else if x = M.blank then ⟨2, by omega⟩
  else ⟨x.val + 3, by omega⟩

def lift (M : Machine ns nt 2) (c : Configuration ns nt) :
    Configuration (ns + 3) (nt + 3) :=
  { state := stateCode M c.state, head := c.head, tape := letterCode M ∘ c.tape }

def decodeStateVal (M : Machine ns nt 2) (v : ℕ) : Option (Fin ns) :=
  if v = 0 then some M.accept
  else if v = 1 then some M.reject
  else if h : 3 ≤ v ∧ v - 3 < ns then
    if v - 3 = M.accept.val ∨ v - 3 = M.reject.val then none
    else some ⟨v - 3, h.2⟩
  else none

def decodeLetterVal (M : Machine ns nt 2) (v : ℕ) : Option (Fin nt) :=
  if v = 0 then some M.zero
  else if v = 1 then some M.one
  else if v = 2 then some M.blank
  else if h : 3 ≤ v ∧ v - 3 < nt then
    if v - 3 = M.zero.val ∨ v - 3 = M.one.val ∨ v - 3 = M.blank.val then none
    else some ⟨v - 3, h.2⟩
  else none

def decodeState (M : Machine ns nt 2) (q : Fin (ns + 3)) : Option (Fin ns) :=
  decodeStateVal M q.val

def decodeLetter (M : Machine ns nt 2) (x : Fin (nt + 3)) : Option (Fin nt) :=
  decodeLetterVal M x.val

def encodeAction (M : Machine ns nt 2)
    (a : FiniteOneTapeProgram.Action (Fin ns) (Fin nt)) :
    FiniteOneTapeProgram.Action (Fin (ns + 3)) (Fin (nt + 3)) :=
  ⟨letterCode M a.write, stateCode M a.target, a.move⟩

theorem stateCode_val (M : Machine ns nt 2) (q : Fin ns) :
    (stateCode M q).val =
      if q = M.accept then 0 else if q = M.reject then 1 else q.val + 3 := by
  unfold stateCode; split_ifs <;> rfl

theorem letterCode_val (M : Machine ns nt 2) (x : Fin nt) :
    (letterCode M x).val =
      if x = M.zero then 0 else if x = M.one then 1
      else if x = M.blank then 2 else x.val + 3 := by
  unfold letterCode; split_ifs <;> rfl

theorem stateCode_ne_two (M : Machine ns nt 2) (q : Fin ns) :
    (stateCode M q).val ≠ 2 := by
  rw [stateCode_val]; split_ifs <;> omega

theorem stateCode_accept (M : Machine ns nt 2) :
    stateCode M M.accept = ⟨0, by omega⟩ := by simp [stateCode]

theorem stateCode_reject (M : Machine ns nt 2) :
    stateCode M M.reject = ⟨1, by omega⟩ := by
  have h : M.reject ≠ M.accept := M.accept_ne_reject.symm
  simp [stateCode, h]

@[simp] theorem letterCode_zero (M : Machine ns nt 2) :
    letterCode M M.zero = ⟨0, by omega⟩ := by simp [letterCode]

@[simp] theorem letterCode_one (M : Machine ns nt 2) :
    letterCode M M.one = ⟨1, by omega⟩ := by
  have h : M.one ≠ M.zero := M.zero_ne_one.symm
  simp [letterCode, h]

@[simp] theorem letterCode_blank (M : Machine ns nt 2) :
    letterCode M M.blank = ⟨2, by omega⟩ := by
  have h0 : M.blank ≠ M.zero := M.blank_ne_zero
  have h1 : M.blank ≠ M.one := M.blank_ne_one
  simp [letterCode, h0, h1]

theorem decode_stateCode (M : Machine ns nt 2) (q : Fin ns) :
    decodeState M (stateCode M q) = some q := by
  unfold stateCode
  split_ifs with hacc hrej
  · subst q; simp [decodeState, decodeStateVal]
  · subst q; simp [decodeState, decodeStateVal]
  · change decodeStateVal M (q.val + 3) = some q
    have hne0 : q.val + 3 ≠ 0 := by omega
    have hne1 : q.val + 3 ≠ 1 := by omega
    have hpos : 3 ≤ q.val + 3 ∧ q.val + 3 - 3 < ns := by omega
    have hsub : q.val + 3 - 3 = q.val := Nat.add_sub_cancel q.val 3
    have hgap : q.val ≠ M.accept.val ∧ q.val ≠ M.reject.val :=
      ⟨fun hv => hacc (Fin.ext hv), fun hv => hrej (Fin.ext hv)⟩
    simp [decodeStateVal, hne1, hpos, hsub, hgap]

theorem decode_letterCode (M : Machine ns nt 2) (x : Fin nt) :
    decodeLetter M (letterCode M x) = some x := by
  unfold letterCode
  split_ifs with hz ho hb
  · subst x; simp [decodeLetter, decodeLetterVal]
  · subst x; simp [decodeLetter, decodeLetterVal]
  · subst x; simp [decodeLetter, decodeLetterVal]
  · change decodeLetterVal M (x.val + 3) = some x
    have hne0 : x.val + 3 ≠ 0 := by omega
    have hne1 : x.val + 3 ≠ 1 := by omega
    have hne2 : x.val + 3 ≠ 2 := by omega
    have hpos : 3 ≤ x.val + 3 ∧ x.val + 3 - 3 < nt := by omega
    have hsub : x.val + 3 - 3 = x.val := Nat.add_sub_cancel x.val 3
    have hgap : x.val ≠ M.zero.val ∧ x.val ≠ M.one.val ∧ x.val ≠ M.blank.val :=
      ⟨fun hv => hz (Fin.ext hv), fun hv => ho (Fin.ext hv),
        fun hv => hb (Fin.ext hv)⟩
    simp [decodeLetterVal, hne1, hne2, hpos, hsub, hgap]

theorem stateCode_decode (M : Machine ns nt 2) (q : Fin (ns + 3)) (src : Fin ns)
    (h : decodeState M q = some src) : stateCode M src = q := by
  unfold decodeState decodeStateVal at h
  by_cases h0 : q.val = 0
  · simp [h0] at h
    subst src
    exact Fin.ext (by simp [stateCode_accept, h0])
  · by_cases h1 : q.val = 1
    · simp [h0, h1] at h
      subst src
      exact Fin.ext (by simp [stateCode_reject, h1])
    · by_cases h3 : 3 ≤ q.val ∧ q.val - 3 < ns
      · by_cases hgap : q.val - 3 = M.accept.val ∨ q.val - 3 = M.reject.val
        · simp [h0, h1, h3, hgap] at h
        · simp [h0, h1, h3, hgap] at h
          subst src
          have hneA : (⟨q.val - 3, by omega⟩ : Fin ns) ≠ M.accept := by
            intro ha; exact hgap (Or.inl (congrArg Fin.val ha))
          have hneR : (⟨q.val - 3, by omega⟩ : Fin ns) ≠ M.reject := by
            intro hr; exact hgap (Or.inr (congrArg Fin.val hr))
          apply Fin.ext
          simp [stateCode_val, hneA, hneR]
          omega
      · simp [h0, h1, h3] at h

theorem letterCode_decode (M : Machine ns nt 2) (x : Fin (nt + 3)) (src : Fin nt)
    (h : decodeLetter M x = some src) : letterCode M src = x := by
  unfold decodeLetter decodeLetterVal at h
  by_cases h0 : x.val = 0
  · simp [h0] at h
    subst src
    exact Fin.ext (by simp [letterCode_zero, h0])
  · by_cases h1 : x.val = 1
    · simp [h0, h1] at h
      subst src
      exact Fin.ext (by simp [letterCode_one, h1])
    · by_cases h2 : x.val = 2
      · simp [h0, h1, h2] at h
        subst src
        exact Fin.ext (by simp [letterCode_blank, h2])
      · by_cases h3 : 3 ≤ x.val ∧ x.val - 3 < nt
        · by_cases hgap :
              x.val - 3 = M.zero.val ∨ x.val - 3 = M.one.val ∨
                x.val - 3 = M.blank.val
          · simp [h0, h1, h2, h3, hgap] at h
          · simp [h0, h1, h2, h3, hgap] at h
            subst src
            have hz : (⟨x.val - 3, by omega⟩ : Fin nt) ≠ M.zero := by
              intro ha; exact hgap (Or.inl (congrArg Fin.val ha))
            have ho : (⟨x.val - 3, by omega⟩ : Fin nt) ≠ M.one := by
              intro ha; exact hgap (Or.inr (Or.inl (congrArg Fin.val ha)))
            have hb : (⟨x.val - 3, by omega⟩ : Fin nt) ≠ M.blank := by
              intro ha; exact hgap (Or.inr (Or.inr (congrArg Fin.val ha)))
            apply Fin.ext
            simp [letterCode_val, hz, ho, hb]
            omega
        · simp [h0, h1, h2, h3] at h

theorem stateCode_injective (M : Machine ns nt 2) :
    Function.Injective (stateCode M) := by
  intro a b h
  have hd := decode_stateCode M a
  rw [h, decode_stateCode M b] at hd
  exact Option.some.inj hd.symm

theorem letterCode_injective (M : Machine ns nt 2) :
    Function.Injective (letterCode M) := by
  intro a b h
  have hd := decode_letterCode M a
  rw [h, decode_letterCode M b] at hd
  exact Option.some.inj hd.symm

def canonicalRule (M : Machine ns nt 2)
    (q : Fin (ns + 3)) (read : Fin (nt + 3)) (slot : Fin 2) :
    Option (FiniteOneTapeProgram.Action (Fin (ns + 3)) (Fin (nt + 3))) :=
  if q.val ≤ 1 then none
  else if q.val = 2 then
    if slot = 0 then some ⟨read, stateCode M M.start, .stay⟩ else none
  else
    (decodeState M q).bind fun srcQ =>
    (decodeLetter M read).bind fun srcX =>
    (M.rule srcQ srcX slot).map (encodeAction M)

def canonicalMachine (M : Machine ns nt 2) : Machine (ns + 3) (nt + 3) 2 where
  rule := canonicalRule M
  start := ⟨2, by omega⟩
  accept := ⟨0, by omega⟩
  reject := ⟨1, by omega⟩
  accept_ne_reject := by
    intro h
    have : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  blank := ⟨2, by omega⟩
  zero := ⟨0, by omega⟩
  one := ⟨1, by omega⟩
  blank_ne_zero := by
    intro h
    have : (2 : ℕ) = 0 := congrArg Fin.val h
    omega
  blank_ne_one := by
    intro h
    have : (2 : ℕ) = 1 := congrArg Fin.val h
    omega
  zero_ne_one := by
    intro h
    have : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  accept_terminal := by
    intro read slot
    simp [canonicalRule]
  reject_terminal := by
    intro read slot
    simp [canonicalRule]

@[simp] theorem canonicalMachine_rule (M : Machine ns nt 2) :
    (canonicalMachine M).rule = canonicalRule M := rfl

@[simp] theorem canonical_start_val (M : Machine ns nt 2) :
    (canonicalMachine M).start.val = 2 := rfl
@[simp] theorem canonical_accept_val (M : Machine ns nt 2) :
    (canonicalMachine M).accept.val = 0 := rfl
@[simp] theorem canonical_reject_val (M : Machine ns nt 2) :
    (canonicalMachine M).reject.val = 1 := rfl
@[simp] theorem canonical_zero_val (M : Machine ns nt 2) :
    (canonicalMachine M).zero.val = 0 := rfl
@[simp] theorem canonical_one_val (M : Machine ns nt 2) :
    (canonicalMachine M).one.val = 1 := rfl
@[simp] theorem canonical_blank_val (M : Machine ns nt 2) :
    (canonicalMachine M).blank.val = 2 := rfl

theorem stateCode_accept' (M : Machine ns nt 2) :
    stateCode M M.accept = (canonicalMachine M).accept := stateCode_accept M

theorem stateCode_reject' (M : Machine ns nt 2) :
    stateCode M M.reject = (canonicalMachine M).reject := by
  simpa [canonicalMachine] using stateCode_reject M

theorem canonicalRule_encoded (M : Machine ns nt 2) (q : Fin ns) (x : Fin nt)
    (slot : Fin 2) :
    canonicalRule M (stateCode M q) (letterCode M x) slot =
      (M.rule q x slot).map (encodeAction M) := by
  by_cases hterm : q = M.accept ∨ q = M.reject
  · have hval : (stateCode M q).val ≤ 1 := by
      rcases hterm with h | h
      · simp [stateCode_val, h]
      · have hne : M.reject ≠ M.accept := M.accept_ne_reject.symm
        simp [stateCode_val, h, hne]
    have hL : canonicalRule M (stateCode M q) (letterCode M x) slot = none := by
      unfold canonicalRule; simp [hval]
    have hR : M.rule q x slot = none := by
      rcases hterm with h | h
      · simp [h, M.accept_terminal]
      · simp [h, M.reject_terminal]
    simp [hL, hR]
  · have hacc : q ≠ M.accept := fun h => hterm (Or.inl h)
    have hrej : q ≠ M.reject := fun h => hterm (Or.inr h)
    have hval : (stateCode M q).val = q.val + 3 := by
      simp [stateCode_val, hacc, hrej]
    have hgt : ¬ (stateCode M q).val ≤ 1 := by rw [hval]; omega
    have hne2 : (stateCode M q).val ≠ 2 := by rw [hval]; omega
    unfold canonicalRule
    simp [hgt, hne2, decode_stateCode, decode_letterCode]

theorem canonicalRule_boot (M : Machine ns nt 2) (read : Fin (nt + 3))
    (slot : Fin 2) :
    canonicalRule M (canonicalMachine M).start read slot =
      if slot = 0 then some ⟨read, stateCode M M.start, .stay⟩ else none := by
  unfold canonicalRule
  simp [canonicalMachine]

theorem inputTape_letterCode (M : Machine ns nt 2) (x : List Bool) (z : Int) :
    inputTape (canonicalMachine M) x z = letterCode M (inputTape M x z) := by
  unfold inputTape
  split_ifs with hz hi hx
  · simp [canonicalMachine, letterCode_one]
  · simp [canonicalMachine, letterCode_zero]
  · simp [canonicalMachine, letterCode_blank]
  · simp [canonicalMachine, letterCode_blank]

theorem lift_initial (M : Machine ns nt 2) (x : List Bool) :
    lift M (initial M x) =
      { state := stateCode M M.start
        head := 0
        tape := inputTape (canonicalMachine M) x } := by
  simp [lift, initial]
  funext z
  exact (inputTape_letterCode M x z).symm

theorem letterCode_writtenTape (M : Machine ns nt 2) (c : Configuration ns nt)
    (w : Fin nt) :
    letterCode M ∘ writtenTape c w =
      writtenTape (lift M c) (letterCode M w) := by
  funext z
  by_cases hz : z = c.head
  · subst z
    simp [writtenTape, Function.update, lift]
  · simp [writtenTape, Function.update, hz, lift]

theorem boot_step (M : Machine ns nt 2) (x : List Bool) :
    step (canonicalMachine M) 0 (initial (canonicalMachine M) x) =
      some (lift M (initial M x)) := by
  unfold step
  simp only [initial]
  have hrule :
      (canonicalMachine M).rule (canonicalMachine M).start
        (inputTape (canonicalMachine M) x 0) 0 =
        some ⟨inputTape (canonicalMachine M) x 0, stateCode M M.start, .stay⟩ := by
    rw [canonicalMachine_rule, canonicalRule_boot]; simp
  rw [hrule, Option.map_some]
  simp [writtenTape, moveHead, Function.update_eq_self]
  exact (lift_initial M x).symm

theorem boot_slot_one (M : Machine ns nt 2) (c : Configuration (ns + 3) (nt + 3))
    (hstate : c.state = (canonicalMachine M).start) :
    step (canonicalMachine M) 1 c = none := by
  have hrule : (canonicalMachine M).rule c.state (c.tape c.head) 1 = none := by
    rw [hstate, canonicalMachine_rule, canonicalRule_boot]
    simp
  unfold step
  simp [hrule]

theorem step_lift (M : Machine ns nt 2) (slot : Fin 2) (c : Configuration ns nt) :
    step (canonicalMachine M) slot (lift M c) =
      (step M slot c).map (lift M) := by
  cases hr : M.rule c.state (c.tape c.head) slot with
  | none =>
      have hR : step M slot c = none := by simp [step, hr]
      have hL : step (canonicalMachine M) slot (lift M c) = none := by
        unfold step
        simp [lift, canonicalRule_encoded, hr]
      simp [hL, hR]
  | some a =>
      have hR : step M slot c =
          some { state := a.target, head := moveHead a.move c.head,
                 tape := writtenTape c a.write } := by
        simp [step, hr]
      have hL : step (canonicalMachine M) slot (lift M c) =
          some { state := stateCode M a.target, head := moveHead a.move c.head,
                 tape := writtenTape (lift M c) (letterCode M a.write) } := by
        unfold step
        simp [lift, canonicalRule_encoded, hr, encodeAction]
      rw [hL, hR, Option.map_some]
      simp [lift, letterCode_writtenTape]

theorem run_lift (M : Machine ns nt 2) (slots : List (Fin 2))
    (c : Configuration ns nt) :
    run (canonicalMachine M) slots (lift M c) =
      (run M slots c).map (lift M) := by
  induction slots generalizing c with
  | nil => simp
  | cons slot slots ih =>
      rw [run_cons, run_cons, step_lift]
      cases hs : step M slot c with
      | none => simp
      | some middle => simp [ih]

theorem raw_run_from_initial (M : Machine ns nt 2) (x : List Bool)
    (bits : List (Fin 2)) (out : Configuration (ns + 3) (nt + 3))
    (hrun : run (canonicalMachine M) bits (initial (canonicalMachine M) x) =
      some out) :
    (bits = [] ∧ out = initial (canonicalMachine M) x) ∨
      ∃ slots sourceOut,
        bits = 0 :: slots ∧
          run M slots (initial M x) = some sourceOut ∧
            out = lift M sourceOut := by
  cases bits with
  | nil =>
      exact Or.inl ⟨rfl, (Option.some.inj hrun).symm⟩
  | cons bit bits =>
      by_cases hbit : bit = 0
      · subst bit
        have hboot := boot_step M x
        have htail : run (canonicalMachine M) bits (lift M (initial M x)) =
            some out := by
          simpa [run_cons, hboot] using hrun
        have hcomm := run_lift M bits (initial M x)
        rw [hcomm] at htail
        cases hs : run M bits (initial M x) with
        | none => simp [hs] at htail
        | some sourceOut =>
            refine Or.inr ⟨bits, sourceOut, rfl, hs, ?_⟩
            exact (Option.some.inj (by simpa [hs] using htail)).symm
      · have hbit1 : bit = 1 := by
          apply Fin.ext
          have hlt := bit.isLt
          have hne : bit.val ≠ 0 := by
            intro hz; exact hbit (Fin.ext hz)
          omega
        subst bit
        have hnone := boot_slot_one M (initial (canonicalMachine M) x) rfl
        simp [run_cons, hnone] at hrun

theorem accepted_boot (M : Machine ns nt 2) (x : List Bool)
    (slots : List (Fin 2)) (haccept : Accepted M x slots) :
    Accepted (canonicalMachine M) x (0 :: slots) := by
  obtain ⟨out, hrun, hstate⟩ := (accepted_iff M x slots).mp haccept
  apply (accepted_iff (canonicalMachine M) x _).mpr
  refine ⟨lift M out, ?_, ?_⟩
  · have hboot := boot_step M x
    rw [run_cons, hboot, Option.bind_some, run_lift, hrun, Option.map_some]
  · simp [lift, hstate, stateCode_accept, canonicalMachine]

theorem accepted_raw_inverse (M : Machine ns nt 2) (x : List Bool)
    (bits : List (Fin 2)) (haccept : Accepted (canonicalMachine M) x bits) :
    ∃ slots : List (Fin 2), Accepted M x slots ∧ bits = 0 :: slots := by
  obtain ⟨out, hrun, hstate⟩ :=
    (accepted_iff (canonicalMachine M) x bits).mp haccept
  rcases raw_run_from_initial M x bits out hrun with h | h
  · obtain ⟨rfl, rfl⟩ := h
    simp [initial, canonicalMachine] at hstate
  · obtain ⟨slots, sourceOut, hbits, hsource, hout⟩ := h
    refine ⟨slots, (accepted_iff M x slots).mpr ⟨sourceOut, hsource, ?_⟩, hbits⟩
    have hacc :
        stateCode M sourceOut.state = (canonicalMachine M).accept := by
      simpa [hout, lift] using hstate
    have hd := decode_stateCode M sourceOut.state
    rw [hacc] at hd
    have hdec : decodeState M (canonicalMachine M).accept = some M.accept := by
      simp [decodeState, decodeStateVal, canonicalMachine]
    rw [hdec] at hd
    exact (Option.some.inj hd).symm

def decodeCanonicalLeaf (bits : List (Fin 2)) : List (Fin 2) := bits.tail

def acceptingLeafEquiv (M : Machine ns nt 2) (x : List Bool) :
    AcceptingLeaf M x ≃ AcceptingLeaf (canonicalMachine M) x where
  toFun leaf := ⟨0 :: leaf.val, accepted_boot M x leaf.val leaf.property⟩
  invFun leaf := ⟨decodeCanonicalLeaf leaf.val, by
    obtain ⟨slots, ha, hb⟩ := accepted_raw_inverse M x leaf.val leaf.property
    simpa [decodeCanonicalLeaf, hb] using ha⟩
  left_inv leaf := by
    apply Subtype.ext
    simp [decodeCanonicalLeaf]
  right_inv leaf := by
    apply Subtype.ext
    obtain ⟨slots, _, hb⟩ := accepted_raw_inverse M x leaf.val leaf.property
    simp [decodeCanonicalLeaf, hb]

theorem canonical_runsAtMost (M : Machine ns nt 2) (x : List Bool) (bound : ℕ)
    (htime : RunsAtMost M x bound) :
    RunsAtMost (canonicalMachine M) x (bound + 1) := by
  intro bits out hrun
  rcases raw_run_from_initial M x bits out hrun with h | h
  · obtain ⟨rfl, _⟩ := h
    simp
  · obtain ⟨slots, sourceOut, rfl, hsource, _⟩ := h
    have hs := htime slots sourceOut hsource
    simp
    omega

def acceptingCodeEquiv (M : Machine ns nt 2) (x : List Bool) (bound : ℕ)
    (htime : RunsAtMost M x bound) :
    AcceptingCode M x bound ≃
      AcceptingCode (canonicalMachine M) x (bound + 1) :=
  (StandardNondeterministicMachine.acceptingLeavesEquiv M x bound htime).trans
    ((acceptingLeafEquiv M x).trans
      (StandardNondeterministicMachine.acceptingLeavesEquiv
        (canonicalMachine M) x (bound + 1)
        (canonical_runsAtMost M x bound htime)).symm)

theorem acceptingCount_canonical (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (htime : RunsAtMost M x bound) :
    acceptingCount M x bound =
      acceptingCount (canonicalMachine M) x (bound + 1) :=
  Fintype.card_congr (acceptingCodeEquiv M x bound htime)

/-- Exact public canonical-code scope: actual boot, lift-commuting runs,
unrestricted leaf equivalence, and bound+1 counts. -/
theorem canonical_exact (M : Machine ns nt 2) (x : List Bool) (bound : ℕ)
    (htime : RunsAtMost M x bound) :
    step (canonicalMachine M) 0 (initial (canonicalMachine M) x) =
        some (lift M (initial M x)) ∧
      (∀ slots c, run (canonicalMachine M) slots (lift M c) =
        (run M slots c).map (lift M)) ∧
      RunsAtMost (canonicalMachine M) x (bound + 1) ∧
      Nonempty (AcceptingLeaf M x ≃ AcceptingLeaf (canonicalMachine M) x) ∧
      acceptingCount M x bound =
        acceptingCount (canonicalMachine M) x (bound + 1) :=
  ⟨boot_step M x, fun slots c => run_lift M slots c,
    canonical_runsAtMost M x bound htime, ⟨acceptingLeafEquiv M x⟩,
    acceptingCount_canonical M x bound htime⟩

theorem canonical_exp_bound (exponent : ℕ) :
    2 ^ exponent + 1 ≤ 2 ^ (exponent + 1) := by
  have h : 2 ^ exponent + 1 ≤ 2 ^ exponent + 2 ^ exponent := by
    have : 0 < 2 ^ exponent := pow_pos (by decide) exponent
    omega
  simpa [pow_succ, two_mul] using h

/-- A binary SharpEXP witness converts to this canonical machine with one extra
exponential unit. This is the encoded ordinary source, not a zipper or
universal transducer. -/
theorem sharpEXP_to_canonical (f : List Bool → ℕ) (hf : SharpEXP f) :
    ∃ ns nt, ∃ M : Machine ns nt 2, ∃ exponent : Polynomial ℕ,
      (M.start.val = 2 ∧ M.accept.val = 0 ∧ M.reject.val = 1 ∧
        M.zero.val = 0 ∧ M.one.val = 1 ∧ M.blank.val = 2) ∧
      ∀ x : List Bool,
        RunsAtMost M x (2 ^ exponent.eval x.length) ∧
          f x = acceptingCount M x (2 ^ exponent.eval x.length) := by
  obtain ⟨ns, nt, M, exponent, hM⟩ :=
    (StandardMachineBinaryChoices.sharpEXP_iff_binary f).mp hf
  let nextExponent := exponent + Polynomial.C 1
  refine ⟨ns + 3, nt + 3, canonicalMachine M, nextExponent, ?_, ?_⟩
  · simp [canonicalMachine]
  · intro x
    obtain ⟨htime, hcount⟩ := hM x
    have hcan := canonical_runsAtMost M x (2 ^ exponent.eval x.length) htime
    have hbound : 2 ^ exponent.eval x.length + 1 ≤
        2 ^ nextExponent.eval x.length := by
      simpa [nextExponent] using canonical_exp_bound (exponent.eval x.length)
    refine ⟨fun slots out hrun => (hcan slots out hrun).trans hbound, ?_⟩
    exact hcount.trans ((acceptingCount_canonical M x _ htime).trans
      (StandardNondeterministicMachine.acceptingCount_eq_of_bounds
        (canonicalMachine M) x _ _ _ hcan (Nat.le_refl _) hbound))

end PakFixedPolyomino.StandardMachineCanonicalCodes
