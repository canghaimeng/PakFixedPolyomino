import PakFixedPolyomino.StandardMachineRunResources
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Executable finite-branch normalization

An original slot i is chosen by i continue labels followed by one commit
label. Continuing writes back the current letter and stays on its physical
cell. Committing performs exactly the original transition. The state carries
the finite choice index. This fixed machine has two slots and preserves
distinct labels even when their effects coincide. Every raw successful run
decomposes into source transitions and an unfinished choice; every accepting
run has no unfinished choice. The explicit decoder gives a leaf bijection.
-/

namespace PakFixedPolyomino.StandardMachineBinaryChoices

open StandardNondeterministicMachine
open FiniteOneTapeProgram (Action)
open FiniteOneTapeSemantics (Config moveHead writtenTape)

variable {ns nt branching : ℕ}

abbrev BinaryState (ns branching : ℕ) := Fin (ns * (branching + 1))

def encodeState (q : Fin ns) (j : Fin (branching + 1)) : BinaryState ns branching :=
  finProdFinEquiv (q, j)

@[simp] theorem decode_encodeState (q : Fin ns) (j : Fin (branching + 1)) :
    finProdFinEquiv.symm (encodeState q j) = (q, j) :=
  finProdFinEquiv.symm_apply_apply _

theorem encodeState_injective :
    Function.Injective (fun pair : Fin ns × Fin (branching + 1) =>
      encodeState pair.1 pair.2) := finProdFinEquiv.injective

def phase (c : Configuration ns nt) (j : Fin (branching + 1)) :
    Configuration (ns * (branching + 1)) nt :=
  { state := encodeState c.state j, head := c.head, tape := c.tape }

def base (c : Configuration ns nt) : Configuration (ns * (branching + 1)) nt :=
  phase c 0

def binaryRule (M : Machine ns nt branching) (q : BinaryState ns branching)
    (read : Fin nt) (slot : Fin 2) :
    Option (Action (BinaryState ns branching) (Fin nt)) :=
  let source := finProdFinEquiv.symm q
  if source.1 = M.accept ∨ source.1 = M.reject then none
  else if slot = 0 then
    if hj : source.2.val < branching then
      (M.rule source.1 read ⟨source.2.val, hj⟩).map fun a =>
        ⟨a.write, encodeState a.target 0, a.move⟩
    else none
  else if hj : source.2.val + 1 < branching then
    some ⟨read, encodeState source.1 ⟨source.2.val + 1, by omega⟩, .stay⟩
  else none

theorem binaryRule_encoded (M : Machine ns nt branching) (q : Fin ns)
    (j : Fin (branching + 1)) (read : Fin nt) (slot : Fin 2) :
    binaryRule M (encodeState q j) read slot =
      if q = M.accept ∨ q = M.reject then none
      else if slot = 0 then
        if hj : j.val < branching then
          (M.rule q read ⟨j.val, hj⟩).map fun a =>
            ⟨a.write, encodeState a.target 0, a.move⟩
        else none
      else if hj : j.val + 1 < branching then
        some ⟨read, encodeState q ⟨j.val + 1, by omega⟩, .stay⟩
      else none := by
  simp only [binaryRule, decode_encodeState]

/-- A concrete ordinary two-slot machine, without a preallocated window. -/
def binaryMachine (M : Machine ns nt branching) :
    Machine (ns * (branching + 1)) nt 2 where
  rule := binaryRule M
  start := encodeState M.start 0
  accept := encodeState M.accept 0
  reject := encodeState M.reject 0
  accept_ne_reject := by
    intro h
    have hp := finProdFinEquiv.injective h
    exact M.accept_ne_reject (congrArg Prod.fst hp)
  blank := M.blank
  zero := M.zero
  one := M.one
  blank_ne_zero := M.blank_ne_zero
  blank_ne_one := M.blank_ne_one
  zero_ne_one := M.zero_ne_one
  accept_terminal := by intro read slot; rw [binaryRule_encoded]; simp
  reject_terminal := by intro read slot; rw [binaryRule_encoded]; simp

@[simp] theorem binaryMachine_initial (M : Machine ns nt branching) (x : List Bool) :
    initial (binaryMachine M) x = base (initial M x) := by
  rfl

def choiceCode (slot : Fin branching) : List (Fin 2) :=
  List.replicate slot.val 1 ++ [0]

def choicesCode (slots : List (Fin branching)) : List (Fin 2) :=
  slots.flatMap choiceCode

@[simp] theorem choiceCode_length (slot : Fin branching) :
    (choiceCode slot).length = slot.val + 1 := by simp [choiceCode]

theorem choiceCode_length_le (slot : Fin branching) :
    (choiceCode slot).length ≤ branching := by rw [choiceCode_length]; omega

@[simp] theorem choicesCode_nil : choicesCode ([] : List (Fin branching)) = [] := rfl

@[simp] theorem choicesCode_cons (slot : Fin branching) (slots : List (Fin branching)) :
    choicesCode (slot :: slots) = choiceCode slot ++ choicesCode slots := by
  simp [choicesCode]

theorem choicesCode_length_le (slots : List (Fin branching)) :
    (choicesCode slots).length ≤ branching * slots.length := by
  induction slots with
  | nil => simp
  | cons slot slots ih =>
      have hslot := choiceCode_length_le slot
      simp only [choicesCode_cons, List.length_append, List.length_cons]
      rw [Nat.mul_add, Nat.mul_one]
      omega

theorem rule_some_nonterminal (M : Machine ns nt branching)
    (c : Configuration ns nt) (slot : Fin branching) (a : Action (Fin ns) (Fin nt))
    (hrule : M.rule c.state (c.tape c.head) slot = some a) :
    c.state ≠ M.accept ∧ c.state ≠ M.reject := by
  constructor
  · intro h
    simpa [h, M.accept_terminal] using hrule
  · intro h
    simpa [h, M.reject_terminal] using hrule

theorem continue_step (M : Machine ns nt branching) (c : Configuration ns nt)
    (j : Fin (branching + 1)) (hj : j.val + 1 < branching)
    (hstate : c.state ≠ M.accept ∧ c.state ≠ M.reject) :
    step (binaryMachine M) 1 (phase c j) =
      some (phase c ⟨j.val + 1, by omega⟩) := by
  have htape : writtenTape (phase c j) (c.tape c.head) = c.tape := by
    exact Function.update_eq_self c.head c.tape
  unfold step
  change (binaryRule M (encodeState c.state j) (c.tape c.head) 1).map _ = _
  rw [binaryRule_encoded]
  have hne : (1 : Fin 2) ≠ 0 := by decide
  simp only [hstate.1, hstate.2, or_self, if_false, hne, hj, dif_pos,
    Option.map_some]
  change some ({ state := encodeState c.state ⟨j.val + 1, by omega⟩
                 head := c.head
                 tape := writtenTape (phase c j) (c.tape c.head) } :
    Configuration (ns * (branching + 1)) nt) = _
  rw [htape]
  rfl

theorem commit_step (M : Machine ns nt branching) (c : Configuration ns nt)
    (slot : Fin branching) (a : Action (Fin ns) (Fin nt))
    (hrule : M.rule c.state (c.tape c.head) slot = some a) :
    step (binaryMachine M) 0 (phase c ⟨slot.val, by omega⟩) =
      some (base { state := a.target
                   head := moveHead a.move c.head
                   tape := writtenTape c a.write }) := by
  have hstate := rule_some_nonterminal M c slot a hrule
  unfold step
  change (binaryRule M (encodeState c.state ⟨slot.val, by omega⟩)
    (c.tape c.head) 0).map _ = _
  rw [binaryRule_encoded]
  simp [hstate.1, hstate.2, slot.isLt, hrule, writtenTape, phase, base]

theorem continue_run (M : Machine ns nt branching) (c : Configuration ns nt)
    (hstate : c.state ≠ M.accept ∧ c.state ≠ M.reject)
    (j n : ℕ) (hjn : j + n < branching) :
    run (binaryMachine M) (List.replicate n 1)
      (phase c ⟨j, by omega⟩) = some (phase c ⟨j + n, by omega⟩) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, run_cons, continue_step M c ⟨j, by omega⟩ (by dsimp; omega) hstate,
        Option.bind_some]
      simpa only [Nat.add_assoc, Nat.add_comm 1 n] using ih (j + 1) (by omega)

theorem choice_run (M : Machine ns nt branching) (c out : Configuration ns nt)
    (slot : Fin branching) (hstep : step M slot c = some out) :
    run (binaryMachine M) (choiceCode slot) (base c) = some (base out) := by
  cases hrule : M.rule c.state (c.tape c.head) slot with
  | none => simp [step, hrule] at hstep
  | some a =>
      have hout : ({ state := a.target
                     head := moveHead a.move c.head
                     tape := writtenTape c a.write } : Configuration ns nt) = out := by
        simpa [step, hrule] using hstep
      subst out
      have hstate := rule_some_nonterminal M c slot a hrule
      rw [choiceCode, run_append]
      have hpre := continue_run M c hstate 0 slot.val (by simpa using slot.isLt)
      change run (binaryMachine M) (List.replicate slot.val 1) (base c) = _ at hpre
      have hpre' : run (binaryMachine M) (List.replicate slot.val 1) (base c) =
          some (phase c ⟨slot.val, Nat.lt_succ_of_lt slot.isLt⟩) := by
        simpa only [Nat.zero_add] using hpre
      rw [hpre', Option.bind_some, run_cons, commit_step M c slot a hrule,
        Option.bind_some, run_nil]

/-- The simulation performs literal binary tape transitions, with one
commit per source transition and no changes during its finite choices. -/
theorem choices_run (M : Machine ns nt branching) (slots : List (Fin branching))
    (c out : Configuration ns nt) (hrun : run M slots c = some out) :
    run (binaryMachine M) (choicesCode slots) (base c) = some (base out) := by
  induction slots generalizing c with
  | nil =>
      have heq : c = out := Option.some.inj hrun
      subst out
      rfl
  | cons slot slots ih =>
      cases hstep : step M slot c with
      | none => simp [run_cons, hstep] at hrun
      | some middle =>
          have htail : run M slots middle = some out := by simpa [run_cons, hstep] using hrun
          rw [choicesCode_cons, run_append, choice_run M c middle slot hstep,
            Option.bind_some]
          exact ih middle htail

theorem accepted_choices (M : Machine ns nt branching) (x : List Bool)
    (slots : List (Fin branching)) (haccept : Accepted M x slots) :
    Accepted (binaryMachine M) x (choicesCode slots) := by
  obtain ⟨out, hrun, hstate⟩ := (accepted_iff M x slots).mp haccept
  apply (accepted_iff (binaryMachine M) x _).mpr
  refine ⟨base out, ?_, ?_⟩
  · rw [binaryMachine_initial]
    exact choices_run M slots (initial M x) out hrun
  · simp [base, phase, binaryMachine, hstate]

def decodeChoices (pending : ℕ) : List (Fin 2) → Option (List (Fin branching))
  | [] => if pending = 0 then some [] else none
  | bit :: bits =>
      if bit = 0 then
        if hj : pending < branching then
          (decodeChoices 0 bits).map (⟨pending, hj⟩ :: ·)
        else none
      else decodeChoices (pending + 1) bits

theorem decodeChoices_ones (pending n : ℕ) (bits : List (Fin 2)) :
    decodeChoices (branching := branching) pending (List.replicate n 1 ++ bits) =
      decodeChoices (pending + n) bits := by
  induction n generalizing pending with
  | zero => simp
  | succ n ih =>
      have hne : (1 : Fin 2) ≠ 0 := by decide
      simp only [List.replicate_succ, List.cons_append, decodeChoices, hne, if_false]
      simpa only [Nat.add_assoc, Nat.add_comm 1 n] using ih (pending + 1)

@[simp] theorem decodeChoices_choicesCode (slots : List (Fin branching)) :
    decodeChoices 0 (choicesCode slots) = some slots := by
  induction slots with
  | nil => simp [decodeChoices]
  | cons slot slots ih =>
      rw [choicesCode_cons, choiceCode, List.append_assoc, decodeChoices_ones]
      simpa [decodeChoices, slot.isLt, ih]

theorem choicesCode_injective :
    Function.Injective (choicesCode : List (Fin branching) → List (Fin 2)) := by
  intro a b h
  have hd := congrArg (decodeChoices (branching := branching) 0) h
  simpa using hd

theorem binary_step_cases (M : Machine ns nt branching) (c : Configuration ns nt)
    (j : Fin (branching + 1)) (bit : Fin 2)
    (out : Configuration (ns * (branching + 1)) nt)
    (hstep : step (binaryMachine M) bit (phase c j) = some out) :
    (∃ (slot : Fin branching) (next : Configuration ns nt),
      bit = 0 ∧ slot.val = j.val ∧ step M slot c = some next ∧ out = base next) ∨
    (∃ nextIndex : Fin (branching + 1),
      bit = 1 ∧ nextIndex.val = j.val + 1 ∧ out = phase c nextIndex) := by
  have hrule : (binaryRule M (encodeState c.state j) (c.tape c.head) bit).map
      (fun a => ({ state := a.target
                   head := moveHead a.move (phase c j).head
                   tape := writtenTape (phase c j) a.write } :
        Configuration (ns * (branching + 1)) nt)) = some out := hstep
  rw [binaryRule_encoded] at hrule
  by_cases hterminal : c.state = M.accept ∨ c.state = M.reject
  · simp [hterminal] at hrule
  rw [if_neg hterminal] at hrule
  have hstate : c.state ≠ M.accept ∧ c.state ≠ M.reject := not_or.mp hterminal
  by_cases hbit : bit = 0
  · rw [if_pos hbit] at hrule
    by_cases hj : j.val < branching
    · rw [dif_pos hj] at hrule
      let slot : Fin branching := ⟨j.val, hj⟩
      cases hsource : M.rule c.state (c.tape c.head) slot with
      | none => simp [slot, hsource] at hrule
      | some a =>
          let next : Configuration ns nt :=
            { state := a.target, head := moveHead a.move c.head, tape := writtenTape c a.write }
          have hs : step M slot c = some next := by simp [step, hsource, next]
          have hc := commit_step M c slot a hsource
          have hphase : (⟨slot.val, Nat.lt_succ_of_lt slot.isLt⟩ :
              Fin (branching + 1)) = j := Fin.ext rfl
          rw [hphase] at hc
          rw [hbit, hc] at hstep
          exact Or.inl ⟨slot, next, hbit, rfl, hs, (Option.some.inj hstep).symm⟩
    · simp [hj] at hrule
  · rw [if_neg hbit] at hrule
    by_cases hj : j.val + 1 < branching
    · have hbit1 : bit = 1 := by
        apply Fin.ext
        change bit.val = 1
        have hlt := bit.isLt
        have hzero : bit.val ≠ 0 := by
          intro hz
          exact hbit (Fin.ext hz)
        omega
      have hc := continue_step M c j hj hstate
      rw [hbit1, hc] at hstep
      exact Or.inr ⟨⟨j.val + 1, by omega⟩, hbit1, rfl, (Option.some.inj hstep).symm⟩
    · simp [hj] at hrule

/-- Every raw successful binary run is a source run followed by its actual
unfinished choice. The raw domain has no chosen-image hypothesis. -/
theorem raw_run_decomposition (M : Machine ns nt branching) (bits : List (Fin 2))
    (c : Configuration ns nt) (j : Fin (branching + 1))
    (out : Configuration (ns * (branching + 1)) nt)
    (hrun : run (binaryMachine M) bits (phase c j) = some out) :
    ∃ (slots : List (Fin branching)) (sourceOut : Configuration ns nt)
      (stage : Fin (branching + 1)),
      run M slots c = some sourceOut ∧ out = phase sourceOut stage ∧
      List.replicate j.val 1 ++ bits = choicesCode slots ++ List.replicate stage.val 1 := by
  induction bits generalizing c j with
  | nil =>
      refine ⟨[], c, j, rfl, (Option.some.inj hrun).symm, ?_⟩
      simp
  | cons bit bits ih =>
      cases hs : step (binaryMachine M) bit (phase c j) with
      | none => simp [run_cons, hs] at hrun
      | some middle =>
          have ht : run (binaryMachine M) bits middle = some out := by
            simpa [run_cons, hs] using hrun
          rcases binary_step_cases M c j bit middle hs with hc | hc
          · obtain ⟨slot, next, hbit, hslot, hsource, hmiddle⟩ := hc
            rw [hmiddle] at ht
            obtain ⟨slots, sourceOut, stage, hsourceTail, hout, hcode⟩ := ih next 0 ht
            refine ⟨slot :: slots, sourceOut, stage, ?_, hout, ?_⟩
            · simp [run_cons, hsource, hsourceTail]
            · have htailCode : bits = choicesCode slots ++ List.replicate stage.val 1 := by
                simpa using hcode
              rw [hbit, htailCode, choicesCode_cons, choiceCode, hslot]
              simp [List.append_assoc]
          · obtain ⟨nextIndex, hbit, hindex, hmiddle⟩ := hc
            rw [hmiddle] at ht
            obtain ⟨slots, sourceOut, stage, hsource, hout, hcode⟩ := ih c nextIndex ht
            refine ⟨slots, sourceOut, stage, hsource, hout, ?_⟩
            rw [hbit]
            calc
              List.replicate j.val 1 ++ 1 :: bits =
                  List.replicate (j.val + 1) 1 ++ bits := by
                    rw [List.replicate_succ']
                    simp [List.append_assoc]
              _ = choicesCode slots ++ List.replicate stage.val 1 := by
                    rw [← hindex]
                    exact hcode

theorem accepted_raw_inverse (M : Machine ns nt branching) (x : List Bool)
    (bits : List (Fin 2)) (haccept : Accepted (binaryMachine M) x bits) :
    ∃ slots : List (Fin branching), Accepted M x slots ∧ bits = choicesCode slots := by
  obtain ⟨out, hrun, hstate⟩ := (accepted_iff (binaryMachine M) x bits).mp haccept
  rw [binaryMachine_initial] at hrun
  obtain ⟨slots, sourceOut, stage, hsource, hout, hcode⟩ :=
    raw_run_decomposition M bits (initial M x) 0 out hrun
  have heq : encodeState sourceOut.state stage = encodeState M.accept 0 := by
    simpa [hout, phase, binaryMachine] using hstate
  have hp := finProdFinEquiv.injective heq
  have hacceptSource : sourceOut.state = M.accept := congrArg Prod.fst hp
  have hstage : stage = 0 := congrArg Prod.snd hp
  refine ⟨slots, (accepted_iff M x slots).mpr ⟨sourceOut, hsource, hacceptSource⟩, ?_⟩
  simpa [hstage] using hcode

theorem binary_runsAtMost (M : Machine ns nt branching) (x : List Bool)
    (bound : ℕ) (htime : RunsAtMost M x bound) :
    RunsAtMost (binaryMachine M) x (branching * (bound + 1)) := by
  intro bits out hrun
  rw [binaryMachine_initial] at hrun
  obtain ⟨slots, sourceOut, stage, hsource, _, hcode⟩ :=
    raw_run_decomposition M bits (initial M x) 0 out hrun
  have hsourceTime := htime slots sourceOut hsource
  have hlength := congrArg List.length hcode
  simp only [List.length_append, List.length_replicate, Fin.val_zero,
    Nat.zero_add] at hlength
  have hencoded := choicesCode_length_le slots
  have hmul := Nat.mul_le_mul_left branching hsourceTime
  have hstage := stage.isLt
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- An explicit executable inverse decodes every raw accepting binary leaf. -/
def acceptingLeafEquiv (M : Machine ns nt branching) (x : List Bool) :
    AcceptingLeaf M x ≃ AcceptingLeaf (binaryMachine M) x where
  toFun leaf := ⟨choicesCode leaf.val, accepted_choices M x leaf.val leaf.property⟩
  invFun leaf := ⟨(decodeChoices 0 leaf.val).getD [], by
    obtain ⟨slots, ha, hb⟩ := accepted_raw_inverse M x leaf.val leaf.property
    simpa [hb] using ha⟩
  left_inv leaf := by
    apply Subtype.ext
    simp
  right_inv leaf := by
    apply Subtype.ext
    obtain ⟨slots, _, hb⟩ := accepted_raw_inverse M x leaf.val leaf.property
    simp [hb]

def acceptingCodeEquiv (M : Machine ns nt branching) (x : List Bool)
    (bound : ℕ) (htime : RunsAtMost M x bound) :
    AcceptingCode M x bound ≃
      AcceptingCode (binaryMachine M) x (branching * (bound + 1)) :=
  (StandardNondeterministicMachine.acceptingLeavesEquiv M x bound htime).trans
    ((acceptingLeafEquiv M x).trans
      (StandardNondeterministicMachine.acceptingLeavesEquiv (binaryMachine M) x
        (branching * (bound + 1)) (binary_runsAtMost M x bound htime)).symm)

theorem acceptingCount_binary (M : Machine ns nt branching) (x : List Bool)
    (bound : ℕ) (htime : RunsAtMost M x bound) :
    acceptingCount M x bound =
      acceptingCount (binaryMachine M) x (branching * (bound + 1)) :=
  Fintype.card_congr (acceptingCodeEquiv M x bound htime)

theorem binary_exp_bound (branching exponent : ℕ) :
    branching * (2 ^ exponent + 1) ≤ 2 ^ (exponent + (branching + 1)) := by
  have hb : branching ≤ 2 ^ branching :=
    (Nat.lt_two_pow_self : branching < 2 ^ branching).le
  have hp : 0 < (2 : ℕ) ^ exponent := pow_pos (by decide) exponent
  calc
    branching * (2 ^ exponent + 1) ≤ 2 ^ branching * (2 ^ exponent * 2) :=
      Nat.mul_le_mul hb (by omega)
    _ = 2 ^ (exponent + (branching + 1)) := by
      rw [pow_add, pow_succ]
      ring

/-- Arbitrary finite branching and binary branching give the SAME source
class, using the actual compiled machine and all its raw accepting leaves.
This does not yet compile the tape alphabet to the fixed universal scanner. -/
theorem sharpEXP_iff_binary (f : List Bool → ℕ) :
    SharpEXP f ↔
      ∃ ns nt, ∃ M : Machine ns nt 2, ∃ exponent : Polynomial ℕ,
        ∀ x : List Bool, RunsAtMost M x (2 ^ exponent.eval x.length) ∧
          f x = acceptingCount M x (2 ^ exponent.eval x.length) := by
  constructor
  · rintro ⟨ns, nt, branching, M, exponent, hf⟩
    let nextExponent := exponent + Polynomial.C (branching + 1)
    refine ⟨ns * (branching + 1), nt, binaryMachine M, nextExponent, ?_⟩
    intro x
    obtain ⟨htime, hcount⟩ := hf x
    have hbinary := binary_runsAtMost M x (2 ^ exponent.eval x.length) htime
    have hbound : branching * (2 ^ exponent.eval x.length + 1) ≤
        2 ^ nextExponent.eval x.length := by
      simpa [nextExponent] using binary_exp_bound branching (exponent.eval x.length)
    refine ⟨fun slots out hrun => (hbinary slots out hrun).trans hbound, ?_⟩
    exact hcount.trans ((acceptingCount_binary M x _ htime).trans
      (StandardNondeterministicMachine.acceptingCount_eq_of_bounds (binaryMachine M) x
        _ _ _ hbinary (Nat.le_refl _) hbound))
  · rintro ⟨ns, nt, M, exponent, hf⟩
    exact ⟨ns, nt, 2, M, exponent, hf⟩

/-- Exact public normalization scope: actual time and counts, with the
literal unrestricted leaf equivalence rather than a chosen subset. -/
theorem normalization_exact (M : Machine ns nt branching) (x : List Bool)
    (bound : ℕ) (htime : RunsAtMost M x bound) :
    RunsAtMost (binaryMachine M) x (branching * (bound + 1)) ∧
    Nonempty (AcceptingLeaf M x ≃ AcceptingLeaf (binaryMachine M) x) ∧
    acceptingCount M x bound =
      acceptingCount (binaryMachine M) x (branching * (bound + 1)) :=
  ⟨binary_runsAtMost M x bound htime, ⟨acceptingLeafEquiv M x⟩,
    acceptingCount_binary M x bound htime⟩

end PakFixedPolyomino.StandardMachineBinaryChoices
