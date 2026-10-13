import PakFixedPolyomino.StandardBitTime
import PakFixedPolyomino.StandardBitMachineComposition
import PakFixedPolyomino.StandardMachineDeterministicDuration

/-! Deterministic initializer followed by a nondeterministic continuation.
Source core uses only slot 0. One stay hands the entire source-accept tape
to N.start. Target executes every N slot. One stay finalizes N terminals.
The physical rule is independent of duration and of ComputesWithin. -/
set_option maxHeartbeats 0
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace PakFixedPolyomino.StandardMachineDeterministicNondeterministicSequence
noncomputable section
open StandardNondeterministicMachine StandardBitTime
open FiniteOneTapeSemantics (moveHead writtenTape)
open StandardBitMachineComposition (config_ext)
open StandardMachineDeterministicDuration (duration duration_spec accepted_run_unique)

variable {nsA nsB nt nb : Nat}

def SameCodes (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb) : Prop :=
  M.blank = N.blank ∧ M.zero = N.zero ∧ M.one = N.one

def acceptC : Fin (nsA + nsB + 2) := ⟨0, by omega⟩
def rejectC : Fin (nsA + nsB + 2) := ⟨1, by omega⟩
def encodeLeft (q : Fin nsA) : Fin (nsA + nsB + 2) :=
  ⟨2 + q.val, by have := q.isLt; omega⟩
def encodeRight (q : Fin nsB) : Fin (nsA + nsB + 2) :=
  ⟨2 + nsA + q.val, by have := q.isLt; omega⟩
def zeroSlot (hnb : 0 < nb) : Fin nb := ⟨0, hnb⟩

def liftA (c : Configuration nsA nt) : Configuration (nsA + nsB + 2) nt :=
  { state := encodeLeft c.state, head := c.head, tape := c.tape }
def liftB (c : Configuration nsB nt) : Configuration (nsA + nsB + 2) nt :=
  { state := encodeRight c.state, head := c.head, tape := c.tape }

theorem encodeLeft_val (q : Fin nsA) : (encodeLeft (nsB := nsB) q).val = 2 + q.val := rfl
theorem encodeRight_val (q : Fin nsB) : (encodeRight (nsA := nsA) q).val = 2 + nsA + q.val := rfl
theorem encodeLeft_range (q : Fin nsA) :
    2 ≤ (encodeLeft (nsB := nsB) q).val ∧ (encodeLeft (nsB := nsB) q).val - 2 < nsA := by
  have := q.isLt; simp [encodeLeft]
theorem encodeRight_range (q : Fin nsB) :
    2 + nsA ≤ (encodeRight (nsA := nsA) q).val ∧
      (encodeRight (nsA := nsA) q).val - (2 + nsA) < nsB := by
  have := q.isLt; simp [encodeRight]
theorem encodeLeft_ne_zero (q : Fin nsA) : (encodeLeft (nsB := nsB) q).val ≠ 0 := by
  simp [encodeLeft]
theorem encodeLeft_ne_one (q : Fin nsA) : (encodeLeft (nsB := nsB) q).val ≠ 1 := by
  simp [encodeLeft]; omega
theorem encodeRight_ne_zero (q : Fin nsB) : (encodeRight (nsA := nsA) q).val ≠ 0 := by
  simp [encodeRight]
theorem encodeRight_ne_one (q : Fin nsB) : (encodeRight (nsA := nsA) q).val ≠ 1 := by
  simp [encodeRight]; omega

def ruleLeft (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (qa : Fin nsA) (read : Fin nt) (slot : Fin nb) :
    Option (FiniteOneTapeProgram.Action (Fin (nsA + nsB + 2)) (Fin nt)) :=
  if qa = M.accept then
    if slot = zeroSlot hnb then some ⟨read, encodeRight N.start, .stay⟩ else none
  else if qa = M.reject then
    if slot = zeroSlot hnb then some ⟨read, rejectC, .stay⟩ else none
  else if slot = zeroSlot hnb then
    (M.rule qa read 0).map fun a => ⟨a.write, encodeLeft a.target, a.move⟩
  else none

def ruleRight (N : Machine nsB nt nb) (hnb : 0 < nb)
    (qb : Fin nsB) (read : Fin nt) (slot : Fin nb) :
    Option (FiniteOneTapeProgram.Action (Fin (nsA + nsB + 2)) (Fin nt)) :=
  if qb = N.accept then
    if slot = zeroSlot hnb then some ⟨read, acceptC, .stay⟩ else none
  else if qb = N.reject then
    if slot = zeroSlot hnb then some ⟨read, rejectC, .stay⟩ else none
  else
    (N.rule qb read slot).map fun a => ⟨a.write, encodeRight a.target, a.move⟩

def ndRule (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (q : Fin (nsA + nsB + 2)) (read : Fin nt) (slot : Fin nb) :
    Option (FiniteOneTapeProgram.Action (Fin (nsA + nsB + 2)) (Fin nt)) :=
  if q.val = 0 ∨ q.val = 1 then none
  else if hA : 2 ≤ q.val ∧ q.val - 2 < nsA then
    ruleLeft M N hnb ⟨q.val - 2, hA.2⟩ read slot
  else if hB : 2 + nsA ≤ q.val ∧ q.val - (2 + nsA) < nsB then
    ruleRight N hnb ⟨q.val - (2 + nsA), hB.2⟩ read slot
  else none

def machine (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N) : Machine (nsA + nsB + 2) nt nb where
  rule := ndRule M N hnb
  start := encodeLeft M.start
  accept := acceptC
  reject := rejectC
  accept_ne_reject := by
    intro h; have hv := congrArg Fin.val h; simp [acceptC, rejectC] at hv
  blank := M.blank
  zero := M.zero
  one := M.one
  blank_ne_zero := M.blank_ne_zero
  blank_ne_one := M.blank_ne_one
  zero_ne_one := M.zero_ne_one
  accept_terminal := by intro x slot; simp [ndRule, acceptC]
  reject_terminal := by intro x slot; simp [ndRule, rejectC]

theorem machine_rule (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N) :
    (machine M N hnb hcodes).rule = ndRule M N hnb := rfl
theorem machine_start (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N) :
    (machine M N hnb hcodes).start = encodeLeft M.start := rfl
theorem machine_accept (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N) :
    (machine M N hnb hcodes).accept = acceptC := rfl
theorem machine_reject (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N) :
    (machine M N hnb hcodes).reject = rejectC := rfl

theorem ndRule_left (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (qa : Fin nsA) (read : Fin nt) (slot : Fin nb) :
    ndRule M N hnb (encodeLeft qa) read slot = ruleLeft M N hnb qa read slot := by
  have hterm : ¬ ((encodeLeft (nsB := nsB) qa).val = 0 ∨
      (encodeLeft (nsB := nsB) qa).val = 1) := by
    intro h; rcases h with h | h
    · exact encodeLeft_ne_zero (nsB := nsB) qa h
    · exact encodeLeft_ne_one (nsB := nsB) qa h
  have hA := encodeLeft_range (nsB := nsB) qa
  have hq : (⟨(encodeLeft (nsB := nsB) qa).val - 2, hA.2⟩ : Fin nsA) = qa := by
    apply Fin.ext; simp [encodeLeft]
  unfold ndRule
  rw [if_neg hterm, dif_pos hA]
  simp [hq]

theorem ndRule_right (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (qb : Fin nsB) (read : Fin nt) (slot : Fin nb) :
    ndRule M N hnb (encodeRight qb) read slot = ruleRight N hnb qb read slot := by
  have hterm : ¬ ((encodeRight (nsA := nsA) qb).val = 0 ∨
      (encodeRight (nsA := nsA) qb).val = 1) := by
    intro h; rcases h with h | h
    · exact encodeRight_ne_zero (nsA := nsA) qb h
    · exact encodeRight_ne_one (nsA := nsA) qb h
  have hA : ¬ (2 ≤ (encodeRight (nsA := nsA) qb).val ∧
      (encodeRight (nsA := nsA) qb).val - 2 < nsA) := by
    intro h; have := qb.isLt; simp [encodeRight] at h; omega
  have hB := encodeRight_range (nsA := nsA) qb
  have hq : (⟨(encodeRight (nsA := nsA) qb).val - (2 + nsA), hB.2⟩ : Fin nsB) = qb := by
    apply Fin.ext; simp [encodeRight]
  unfold ndRule
  rw [if_neg hterm, dif_neg hA, dif_pos hB]
  simp [hq]

theorem inputTape_machine (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N) (x : List Bool) :
    inputTape (machine M N hnb hcodes) x = inputTape M x := by
  funext z; simp [inputTape, machine]

theorem inputTape_N (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hcodes : SameCodes M N) (x : List Bool) : inputTape N x = inputTape M x := by
  funext z
  rcases hcodes with ⟨hb, hz, ho⟩
  simp [inputTape, hb, hz, ho]

theorem initial_liftA (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N) (raw : List Bool) :
    initial (machine M N hnb hcodes) raw = liftA (initial M raw) := by
  apply config_ext
  · rfl
  · rfl
  · exact inputTape_machine M N hnb hcodes raw

theorem step_M_nonterminal (M : DeterministicMachine nsA nt)
    (c c' : Configuration nsA nt) (h : step M 0 c = some c') :
    c.state ≠ M.accept ∧ c.state ≠ M.reject := by
  constructor
  · intro hs; simp [step, hs, M.accept_terminal] at h
  · intro hs; simp [step, hs, M.reject_terminal] at h

theorem step_N_nonterminal (N : Machine nsB nt nb)
    (c c' : Configuration nsB nt) (slot : Fin nb) (h : step N slot c = some c') :
    c.state ≠ N.accept ∧ c.state ≠ N.reject := by
  constructor
  · intro hs; simp [step, hs, N.accept_terminal] at h
  · intro hs; simp [step, hs, N.reject_terminal] at h

theorem lift_step_A (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c c' : Configuration nsA nt) (h : step M 0 c = some c') :
    step (machine M N hnb hcodes) (zeroSlot hnb) (liftA c) = some (liftA c') := by
  have hsrc := step_M_nonterminal M c c' h
  simp only [step, liftA, machine_rule] at h ⊢
  cases hrule : M.rule c.state (c.tape c.head) 0 with
  | none => simp [hrule] at h
  | some a =>
      simp [hrule] at h
      subst c'
      rw [ndRule_left, ruleLeft, if_neg hsrc.1, if_neg hsrc.2, if_pos rfl, hrule]
      simp [liftA, writtenTape]

theorem lift_run_A (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (n : Nat) (c out : Configuration nsA nt) (h : run M (ticks n) c = some out) :
    run (machine M N hnb hcodes) (List.replicate n (zeroSlot hnb)) (liftA c) =
      some (liftA out) := by
  induction n generalizing c with
  | zero => simp [ticks] at h; subst out; simp
  | succ n ih =>
      change run M (0 :: ticks n) c = some out at h
      rw [run_cons] at h
      cases hstep : step M 0 c with
      | none => simp [hstep] at h
      | some mid =>
          simp [hstep] at h
          rw [List.replicate_succ, run_cons, lift_step_A (h := hstep), Option.bind_some]
          exact ih mid h

theorem handoff_accept (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c : Configuration nsA nt) (hs : c.state = M.accept) :
    step (machine M N hnb hcodes) (zeroSlot hnb) (liftA c) =
      some (liftB { state := N.start, head := c.head, tape := c.tape }) := by
  simp only [step, liftA, machine_rule]
  rw [ndRule_left, ruleLeft, if_pos hs, if_pos rfl]
  simp [moveHead, writtenTape, Function.update_eq_self, liftB]

theorem handoff_reject (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c : Configuration nsA nt) (hs : c.state = M.reject) :
    step (machine M N hnb hcodes) (zeroSlot hnb) (liftA c) =
      some { state := rejectC, head := c.head, tape := c.tape } := by
  have hne : c.state ≠ M.accept := fun h => M.accept_ne_reject (h.symm.trans hs)
  simp only [step, liftA, machine_rule]
  rw [ndRule_left, ruleLeft, if_neg hne, if_pos hs, if_pos rfl]
  simp [moveHead, writtenTape, Function.update_eq_self]

theorem lift_step_B (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c c' : Configuration nsB nt) (slot : Fin nb) (h : step N slot c = some c') :
    step (machine M N hnb hcodes) slot (liftB c) = some (liftB c') := by
  have hsrc := step_N_nonterminal N c c' slot h
  simp only [step, liftB, machine_rule] at h ⊢
  cases hrule : N.rule c.state (c.tape c.head) slot with
  | none => simp [hrule] at h
  | some a =>
      simp [hrule] at h
      subst c'
      rw [ndRule_right, ruleRight, if_neg hsrc.1, if_neg hsrc.2, hrule]
      simp [liftB, writtenTape]

theorem lift_run_B (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (v : List (Fin nb)) (c out : Configuration nsB nt) (h : run N v c = some out) :
    run (machine M N hnb hcodes) v (liftB c) = some (liftB out) := by
  induction v generalizing c with
  | nil => simp at h; subst out; simp
  | cons slot v ih =>
      rw [run_cons] at h
      cases hstep : step N slot c with
      | none => simp [hstep] at h
      | some mid =>
          simp [hstep] at h
          rw [run_cons, lift_step_B (h := hstep), Option.bind_some]
          exact ih mid h

theorem finalize_accept (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c : Configuration nsB nt) (hs : c.state = N.accept) :
    step (machine M N hnb hcodes) (zeroSlot hnb) (liftB c) =
      some { state := acceptC, head := c.head, tape := c.tape } := by
  simp only [step, liftB, machine_rule]
  rw [ndRule_right, ruleRight, if_pos hs, if_pos rfl]
  simp [moveHead, writtenTape, Function.update_eq_self]

theorem finalize_reject (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c : Configuration nsB nt) (hs : c.state = N.reject) :
    step (machine M N hnb hcodes) (zeroSlot hnb) (liftB c) =
      some { state := rejectC, head := c.head, tape := c.tape } := by
  have hne : c.state ≠ N.accept := fun h => N.accept_ne_reject (h.symm.trans hs)
  simp only [step, liftB, machine_rule]
  rw [ndRule_right, ruleRight, if_neg hne, if_pos hs, if_pos rfl]
  simp [moveHead, writtenTape, Function.update_eq_self]

theorem sequence_run (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N) (raw : List Bool)
    (a : Nat) (v : List (Fin nb))
    (c : Configuration nsA nt) (d : Configuration nsB nt)
    (hu : run M (ticks a) (initial M raw) = some c) (hacc : c.state = M.accept)
    (hv : run N v { state := N.start, head := c.head, tape := c.tape } = some d)
    (hd : d.state = N.accept) :
    run (machine M N hnb hcodes)
        (List.replicate a (zeroSlot hnb) ++ [zeroSlot hnb] ++ v ++ [zeroSlot hnb])
        (initial (machine M N hnb hcodes) raw) =
      some { state := acceptC, head := d.head, tape := d.tape } := by
  have hArun : run (machine M N hnb hcodes) (List.replicate a (zeroSlot hnb))
      (initial (machine M N hnb hcodes) raw) = some (liftA c) := by
    rw [initial_liftA, lift_run_A (h := hu)]
  have hHand : run (machine M N hnb hcodes)
      (List.replicate a (zeroSlot hnb) ++ [zeroSlot hnb])
      (initial (machine M N hnb hcodes) raw) =
      some (liftB { state := N.start, head := c.head, tape := c.tape }) := by
    rw [run_append, hArun, Option.bind_some, run_cons, handoff_accept (hs := hacc),
      Option.bind_some, run_nil]
  have hBrun : run (machine M N hnb hcodes)
      (List.replicate a (zeroSlot hnb) ++ [zeroSlot hnb] ++ v)
      (initial (machine M N hnb hcodes) raw) = some (liftB d) := by
    rw [run_append, hHand, Option.bind_some, lift_run_B (h := hv)]
  rw [run_append, hBrun, Option.bind_some, run_cons, finalize_accept (hs := hd),
    Option.bind_some, run_nil]

theorem accepted_of_split (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N) (raw : List Bool)
    (a : Nat) (v : List (Fin nb))
    (c : Configuration nsA nt) (d : Configuration nsB nt)
    (hu : run M (ticks a) (initial M raw) = some c) (hacc : c.state = M.accept)
    (hv : run N v { state := N.start, head := c.head, tape := c.tape } = some d)
    (hd : d.state = N.accept) :
    Accepted (machine M N hnb hcodes) raw
      (List.replicate a (zeroSlot hnb) ++ [zeroSlot hnb] ++ v ++ [zeroSlot hnb]) := by
  refine (accepted_iff (machine M N hnb hcodes) raw _).mpr ?_
  refine ⟨_, sequence_run M N hnb hcodes raw a v c d hu hacc hv hd, ?_⟩
  rfl

theorem step_left_inv (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c : Configuration nsA nt) (slot : Fin nb)
    (mid : Configuration (nsA + nsB + 2) nt)
    (h : step (machine M N hnb hcodes) slot (liftA c) = some mid) :
    (c.state = M.accept ∧ slot = zeroSlot hnb ∧
      mid = liftB { state := N.start, head := c.head, tape := c.tape }) ∨
    (c.state = M.reject ∧ slot = zeroSlot hnb ∧
      mid = { state := rejectC, head := c.head, tape := c.tape }) ∨
    (c.state ≠ M.accept ∧ c.state ≠ M.reject ∧ slot = zeroSlot hnb ∧
      ∃ c', step M 0 c = some c' ∧ mid = liftA c') := by
  simp only [step, liftA, machine_rule] at h
  rw [ndRule_left] at h
  by_cases hacc : c.state = M.accept
  · rw [ruleLeft, if_pos hacc] at h
    by_cases hs0 : slot = zeroSlot hnb
    · rw [if_pos hs0] at h
      simp [moveHead, writtenTape, Function.update_eq_self] at h
      subst mid
      exact Or.inl ⟨hacc, hs0, by simp [liftB]⟩
    · rw [if_neg hs0] at h; simp at h
  · by_cases hrej : c.state = M.reject
    · rw [ruleLeft, if_neg hacc, if_pos hrej] at h
      by_cases hs0 : slot = zeroSlot hnb
      · rw [if_pos hs0] at h
        simp [moveHead, writtenTape, Function.update_eq_self] at h
        subst mid
        exact Or.inr (Or.inl ⟨hrej, hs0, rfl⟩)
      · rw [if_neg hs0] at h; simp at h
    · rw [ruleLeft, if_neg hacc, if_neg hrej] at h
      by_cases hs0 : slot = zeroSlot hnb
      · rw [if_pos hs0] at h
        cases hrule : M.rule c.state (c.tape c.head) 0 with
        | none => simp [hrule] at h
        | some a =>
            simp [hrule] at h
            subst mid
            refine Or.inr (Or.inr ⟨hacc, hrej, hs0, ?_⟩)
            let c' : Configuration nsA nt :=
              { state := a.target, head := moveHead a.move c.head,
                tape := writtenTape c a.write }
            refine ⟨c', ?_⟩
            constructor
            · simp [step, hrule, c']
            · simp [liftA, c', writtenTape]
      · rw [if_neg hs0] at h; simp at h

theorem step_right_inv (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c : Configuration nsB nt) (slot : Fin nb)
    (mid : Configuration (nsA + nsB + 2) nt)
    (h : step (machine M N hnb hcodes) slot (liftB c) = some mid) :
    (c.state = N.accept ∧ slot = zeroSlot hnb ∧
      mid = { state := acceptC, head := c.head, tape := c.tape }) ∨
    (c.state = N.reject ∧ slot = zeroSlot hnb ∧
      mid = { state := rejectC, head := c.head, tape := c.tape }) ∨
    (c.state ≠ N.accept ∧ c.state ≠ N.reject ∧
      ∃ c', step N slot c = some c' ∧ mid = liftB c') := by
  simp only [step, liftB, machine_rule] at h
  rw [ndRule_right] at h
  by_cases hacc : c.state = N.accept
  · rw [ruleRight, if_pos hacc] at h
    by_cases hs0 : slot = zeroSlot hnb
    · rw [if_pos hs0] at h
      simp [moveHead, writtenTape, Function.update_eq_self] at h
      subst mid
      exact Or.inl ⟨hacc, hs0, rfl⟩
    · rw [if_neg hs0] at h; simp at h
  · by_cases hrej : c.state = N.reject
    · rw [ruleRight, if_neg hacc, if_pos hrej] at h
      by_cases hs0 : slot = zeroSlot hnb
      · rw [if_pos hs0] at h
        simp [moveHead, writtenTape, Function.update_eq_self] at h
        subst mid
        exact Or.inr (Or.inl ⟨hrej, hs0, rfl⟩)
      · rw [if_neg hs0] at h; simp at h
    · rw [ruleRight, if_neg hacc, if_neg hrej] at h
      cases hrule : N.rule c.state (c.tape c.head) slot with
      | none => simp [hrule] at h
      | some a =>
          simp [hrule] at h
          subst mid
          refine Or.inr (Or.inr ⟨hacc, hrej, ?_⟩)
          let c' : Configuration nsB nt :=
            { state := a.target, head := moveHead a.move c.head,
              tape := writtenTape c a.write }
          refine ⟨c', ?_⟩
          constructor
          · simp [step, hrule, c']
          · simp [liftB, c', writtenTape]

theorem run_reject_nonempty_none {ns br : Nat} (S : Machine ns nt br)
    (c : Configuration ns nt) (hstate : c.state = S.reject)
    (slots : List (Fin br)) (hne : slots ≠ []) : run S slots c = none := by
  cases slots with
  | nil => contradiction
  | cons slot rest => simp [run_cons, step_reject_none S slot c hstate]

theorem rest_nil_of_accept (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c : Configuration (nsA + nsB + 2) nt) (hacc : c.state = acceptC)
    (rest : List (Fin nb)) (out : Configuration (nsA + nsB + 2) nt)
    (h : run (machine M N hnb hcodes) rest c = some out) : rest = [] := by
  cases rest with
  | nil => rfl
  | cons s rest =>
      have hst : c.state = (machine M N hnb hcodes).accept := by
        simpa [machine_accept] using hacc
      have hnone := run_accept_nonempty_none (machine M N hnb hcodes)
        c hst (s :: rest) (by simp)
      simp [hnone] at h

theorem rest_nil_of_reject (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c : Configuration (nsA + nsB + 2) nt) (hrej : c.state = rejectC)
    (rest : List (Fin nb)) (out : Configuration (nsA + nsB + 2) nt)
    (h : run (machine M N hnb hcodes) rest c = some out) : rest = [] := by
  cases rest with
  | nil => rfl
  | cons s rest =>
      have hst : c.state = (machine M N hnb hcodes).reject := by
        simpa [machine_reject] using hrej
      have hnone := run_reject_nonempty_none (machine M N hnb hcodes)
        c hst (s :: rest) (by simp)
      simp [hnone] at h

theorem ticks_succ (n : Nat) : ticks (n + 1) = ticks n ++ [0] := by
  rw [ticks_add n 1]; rfl

theorem run_ticks_succ {ns : Nat} (S : DeterministicMachine ns nt)
    (origin c c' : Configuration ns nt) (t : Nat)
    (hpre : run S (ticks t) origin = some c) (hstep : step S 0 c = some c') :
    run S (ticks (t + 1)) origin = some c' := by
  rw [ticks_succ, run_append, hpre, Option.bind_some, run_cons, hstep,
    Option.bind_some, run_nil]

theorem run_ticks_cons {ns : Nat} (S : DeterministicMachine ns nt)
    (origin mid out : Configuration ns nt) (a : Nat)
    (hstep : step S 0 origin = some mid) (htail : run S (ticks a) mid = some out) :
    run S (ticks (a + 1)) origin = some out := by
  have htick : ticks (a + 1) = 0 :: ticks a := by
    rw [Nat.add_comm, ticks_add]; simp [ticks]
  rw [htick, run_cons, hstep, Option.bind_some, htail]

theorem run_snoc (S : Machine nsB nt nb) (start c c' : Configuration nsB nt)
    (u0 : List (Fin nb)) (slot : Fin nb)
    (hpre : run S u0 start = some c) (hstep : step S slot c = some c') :
    run S (u0 ++ [slot]) start = some c' := by
  rw [run_append, hpre, Option.bind_some, run_cons, hstep, Option.bind_some, run_nil]

theorem accepted_from_right (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (cB : Configuration nsB nt) (slots : List (Fin nb))
    (out : Configuration (nsA + nsB + 2) nt)
    (h : run (machine M N hnb hcodes) slots (liftB cB) = some out)
    (hacc : out.state = acceptC) :
    ∃ v d, slots = v ++ [zeroSlot hnb] ∧
      run N v cB = some d ∧ d.state = N.accept := by
  induction slots generalizing cB with
  | nil =>
      simp at h; subst out
      have hval : (encodeRight (nsA := nsA) cB.state).val = 0 := by
        simpa [liftB, acceptC] using congrArg Fin.val hacc
      exact (encodeRight_ne_zero (nsA := nsA) cB.state hval).elim
  | cons slot rest ih =>
      rw [run_cons] at h
      cases hstep : step (machine M N hnb hcodes) slot (liftB cB) with
      | none => simp [hstep] at h
      | some mid =>
          simp [hstep] at h
          have hinv := step_right_inv M N hnb hcodes cB slot mid hstep
          rcases hinv with hFinA | hFinR | hOrd
          · rcases hFinA with ⟨hs, hs0, hmid⟩
            subst slot; rw [hmid] at h
            have hnil := rest_nil_of_accept M N hnb hcodes
              { state := acceptC, head := cB.head, tape := cB.tape } rfl rest out h
            subst rest
            refine ⟨[], cB, ?_, ?_, hs⟩
            · simp
            · simp
          · rcases hFinR with ⟨_, hs0, hmid⟩
            subst slot; rw [hmid] at h
            have hnil := rest_nil_of_reject M N hnb hcodes
              { state := rejectC, head := cB.head, tape := cB.tape } rfl rest out h
            subst rest
            simp at h
            subst out
            simp [acceptC, rejectC] at hacc
          · rcases hOrd with ⟨_, _, cB', hN, hmid⟩
            subst mid
            obtain ⟨v, d, hrest, hrun, hd⟩ := ih cB' h
            refine ⟨slot :: v, d, ?_, ?_, hd⟩
            · simp [hrest]
            · rw [run_cons, hN, Option.bind_some, hrun]

theorem accepted_from_left (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c : Configuration nsA nt) (slots : List (Fin nb))
    (out : Configuration (nsA + nsB + 2) nt)
    (h : run (machine M N hnb hcodes) slots (liftA c) = some out)
    (hacc : out.state = acceptC) :
    ∃ a v cAcc d,
      slots = List.replicate a (zeroSlot hnb) ++ [zeroSlot hnb] ++ v ++ [zeroSlot hnb] ∧
      run M (ticks a) c = some cAcc ∧ cAcc.state = M.accept ∧
      run N v { state := N.start, head := cAcc.head, tape := cAcc.tape } = some d ∧
      d.state = N.accept := by
  induction slots generalizing c with
  | nil =>
      simp at h; subst out
      have hval : (encodeLeft (nsB := nsB) c.state).val = 0 := by
        simpa [liftA, acceptC] using congrArg Fin.val hacc
      exact (encodeLeft_ne_zero (nsB := nsB) c.state hval).elim
  | cons slot rest ih =>
      rw [run_cons] at h
      cases hstep : step (machine M N hnb hcodes) slot (liftA c) with
      | none => simp [hstep] at h
      | some mid =>
          simp [hstep] at h
          have hinv := step_left_inv M N hnb hcodes c slot mid hstep
          rcases hinv with hHand | hRej | hOrd
          · rcases hHand with ⟨hs, hs0, hmid⟩
            subst slot; rw [hmid] at h
            obtain ⟨v, d, hrest, hN, hd⟩ :=
              accepted_from_right M N hnb hcodes
                { state := N.start, head := c.head, tape := c.tape } rest out h hacc
            refine ⟨0, v, c, d, ?_, ?_, hs, hN, hd⟩
            · simp [hrest]
            · simp [ticks]
          · rcases hRej with ⟨_, hs0, hmid⟩
            subst slot; rw [hmid] at h
            have hnil := rest_nil_of_reject M N hnb hcodes
              { state := rejectC, head := c.head, tape := c.tape } rfl rest out h
            subst rest
            simp at h; subst out
            simp [acceptC, rejectC] at hacc
          · rcases hOrd with ⟨_, _, hs0, c', hM, hmid⟩
            subst slot; subst mid
            obtain ⟨a, v, cAcc, d, hrest, hu, ha, hv, hd⟩ := ih c' h
            refine ⟨a + 1, v, cAcc, d, ?_, ?_, ha, hv, hd⟩
            · simp [hrest, List.replicate_succ, List.cons_append]
            · exact run_ticks_cons M c c' cAcc a hM hu

theorem accepted_iff_split (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N) (raw : List Bool) (slots : List (Fin nb)) :
    Accepted (machine M N hnb hcodes) raw slots ↔
      ∃ (a : Nat) (v : List (Fin nb)) (c : Configuration nsA nt)
        (d : Configuration nsB nt),
        slots = List.replicate a (zeroSlot hnb) ++ [zeroSlot hnb] ++ v ++
          [zeroSlot hnb] ∧
        run M (ticks a) (initial M raw) = some c ∧ c.state = M.accept ∧
        run N v { state := N.start, head := c.head, tape := c.tape } = some d ∧
        d.state = N.accept := by
  constructor
  · intro hAcc
    obtain ⟨out, hrun, hst⟩ := (accepted_iff (machine M N hnb hcodes) raw slots).mp hAcc
    have hstC : out.state = acceptC := by simpa [machine_accept] using hst
    rw [initial_liftA] at hrun
    exact accepted_from_left M N hnb hcodes (initial M raw) slots out hrun hstC
  · intro h
    rcases h with ⟨a, v, c, d, hs, hu, ha, hv, hd⟩
    rw [hs]
    exact accepted_of_split M N hnb hcodes raw a v c d hu ha hv hd

theorem split_unique (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (raw : List Bool) (slots : List (Fin nb))
    (a1 a2 : Nat) (v1 v2 : List (Fin nb))
    (c1 c2 : Configuration nsA nt) (d1 d2 : Configuration nsB nt)
    (hs1 : slots = List.replicate a1 (zeroSlot hnb) ++ [zeroSlot hnb] ++ v1 ++
      [zeroSlot hnb])
    (hu1 : run M (ticks a1) (initial M raw) = some c1) (ha1 : c1.state = M.accept)
    (hs2 : slots = List.replicate a2 (zeroSlot hnb) ++ [zeroSlot hnb] ++ v2 ++
      [zeroSlot hnb])
    (hu2 : run M (ticks a2) (initial M raw) = some c2) (ha2 : c2.state = M.accept)
    (hn1 : run N v1 { state := N.start, head := c1.head, tape := c1.tape } = some d1)
    (hn2 : run N v2 { state := N.start, head := c2.head, tape := c2.tape } = some d2) :
    a1 = a2 ∧ v1 = v2 ∧ c1 = c2 ∧ d1 = d2 := by
  have ⟨heq, hc⟩ := halting_run_unique M raw a1 a2 c1 c2 hu1 ha1 hu2 ha2
  subst a2; subst c2
  have e1 : slots =
      (List.replicate a1 (zeroSlot hnb) ++ [zeroSlot hnb]) ++
        (v1 ++ [zeroSlot hnb]) := by
    simp [hs1, List.append_assoc]
  have e2 : slots =
      (List.replicate a1 (zeroSlot hnb) ++ [zeroSlot hnb]) ++
        (v2 ++ [zeroSlot hnb]) := by
    simp [hs2, List.append_assoc]
  have hmid : v1 ++ [zeroSlot hnb] = v2 ++ [zeroSlot hnb] :=
    List.append_cancel_left (e1.symm.trans e2)
  have hv : v1 = v2 := List.append_cancel_right hmid
  subst v2
  have hd : d1 = d2 := Option.some.inj (hn1.symm.trans hn2)
  exact ⟨rfl, rfl, rfl, hd⟩

theorem det_fuel_pred {ns : Nat} (S : DeterministicMachine ns nt)
    (c c' : Configuration ns nt) (fuel : Nat)
    (hstep : step S 0 c = some c')
    (hfuel : ∀ t d, run S (ticks t) c = some d → t ≤ fuel) :
    1 ≤ fuel ∧ ∀ t d, run S (ticks t) c' = some d → t ≤ fuel - 1 := by
  constructor
  · have : run S (ticks 1) c = some c' := by
      change run S [0] c = some c'; simp [run_cons, hstep]
    exact hfuel 1 c' this
  · intro t d hk
    have : run S (ticks (t + 1)) c = some d := by
      change run S (0 :: ticks t) c = some d
      rw [run_cons, hstep, Option.bind_some, hk]
    have ht : t + 1 ≤ fuel := hfuel (t + 1) d this
    omega

theorem nd_fuel_pred (S : Machine nsB nt nb) (c c' : Configuration nsB nt)
    (slot : Fin nb) (fuel : Nat) (hstep : step S slot c = some c')
    (hfuel : ∀ u d, run S u c = some d → u.length ≤ fuel) :
    1 ≤ fuel ∧ ∀ u d, run S u c' = some d → u.length ≤ fuel - 1 := by
  constructor
  · have : run S [slot] c = some c' := by simp [run_cons, hstep]
    simpa using hfuel [slot] c' this
  · intro u d hk
    have : run S (slot :: u) c = some d := by
      rw [run_cons, hstep, Option.bind_some, hk]
    have ht : (slot :: u).length ≤ fuel := hfuel (slot :: u) d this
    simp at ht; omega

theorem prefix_len_right (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c : Configuration nsB nt) (fuel : Nat) (slots : List (Fin nb))
    (out : Configuration (nsA + nsB + 2) nt)
    (hfuel : ∀ v d, run N v c = some d → v.length ≤ fuel)
    (h : run (machine M N hnb hcodes) slots (liftB c) = some out) :
    slots.length ≤ fuel + 1 := by
  induction slots generalizing c fuel with
  | nil => simp
  | cons slot rest ih =>
      rw [run_cons] at h
      cases hstep : step (machine M N hnb hcodes) slot (liftB c) with
      | none => simp [hstep] at h
      | some mid =>
          simp [hstep] at h
          have hinv := step_right_inv M N hnb hcodes c slot mid hstep
          rcases hinv with hFinA | hFinR | hOrd
          · rcases hFinA with ⟨_, hs0, hmid⟩
            subst slot; rw [hmid] at h
            have hnil := rest_nil_of_accept M N hnb hcodes
              { state := acceptC, head := c.head, tape := c.tape } rfl rest out h
            subst rest
            simpa using (Nat.le_add_right 1 fuel)
          · rcases hFinR with ⟨_, hs0, hmid⟩
            subst slot; rw [hmid] at h
            have hnil := rest_nil_of_reject M N hnb hcodes
              { state := rejectC, head := c.head, tape := c.tape } rfl rest out h
            subst rest
            simpa using (Nat.le_add_right 1 fuel)
          · rcases hOrd with ⟨_, _, c', hN, hmid⟩
            subst mid
            have hf := nd_fuel_pred N c c' slot fuel hN hfuel
            have := ih c' (fuel - 1) hf.2 h
            simp at this ⊢; omega

theorem prefix_from_left (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N) (raw : List Bool) (A B : Nat)
    (htA : RunsAtMost M raw A)
    (htB : ∀ (u : List (Fin 1)) (c : Configuration nsA nt),
      run M u (initial M raw) = some c → c.state = M.accept →
      ∀ (v : List (Fin nb)) (d : Configuration nsB nt),
        run N v { state := N.start, head := c.head, tape := c.tape } = some d →
        v.length ≤ B)
    (c : Configuration nsA nt) (t fuel : Nat) (slots : List (Fin nb))
    (out : Configuration (nsA + nsB + 2) nt)
    (hpre : run M (ticks t) (initial M raw) = some c)
    (hfuel : ∀ s d, run M (ticks s) c = some d → s ≤ fuel)
    (h : run (machine M N hnb hcodes) slots (liftA c) = some out) :
    slots.length ≤ fuel + B + 2 := by
  induction slots generalizing c t fuel with
  | nil => exact Nat.zero_le _
  | cons slot rest ih =>
      rw [run_cons] at h
      cases hstep : step (machine M N hnb hcodes) slot (liftA c) with
      | none => simp [hstep] at h
      | some mid =>
          simp [hstep] at h
          have hinv := step_left_inv M N hnb hcodes c slot mid hstep
          rcases hinv with hHand | hRej | hOrd
          · rcases hHand with ⟨hs, hs0, hmid⟩
            subst slot; rw [hmid] at h
            have hBf : ∀ v d,
                run N v { state := N.start, head := c.head, tape := c.tape } =
                  some d → v.length ≤ B :=
              fun v d hk => htB (ticks t) c hpre hs v d hk
            have hrest := prefix_len_right M N hnb hcodes
              { state := N.start, head := c.head, tape := c.tape } B rest out hBf h
            simp at hrest ⊢; omega
          · rcases hRej with ⟨_, hs0, hmid⟩
            subst slot; rw [hmid] at h
            have hnil := rest_nil_of_reject M N hnb hcodes
              { state := rejectC, head := c.head, tape := c.tape } rfl rest out h
            subst rest
            simpa using (show 1 ≤ fuel + B + 2 from Nat.le_add_left 1 _)
          · rcases hOrd with ⟨_, _, hs0, c', hM, hmid⟩
            subst slot; subst mid
            have hpre' := run_ticks_succ M (initial M raw) c c' t hpre hM
            have hf := det_fuel_pred M c c' fuel hM hfuel
            have := ih c' (t + 1) (fuel - 1) hpre' hf.2 h
            simp at this ⊢; omega

theorem sequence_runsAtMost (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N) (raw : List Bool) (A B : Nat)
    (htA : RunsAtMost M raw A)
    (htB : ∀ (u : List (Fin 1)) (c : Configuration nsA nt),
      run M u (initial M raw) = some c → c.state = M.accept →
      ∀ (v : List (Fin nb)) (d : Configuration nsB nt),
        run N v { state := N.start, head := c.head, tape := c.tape } = some d →
        v.length ≤ B) :
    RunsAtMost (machine M N hnb hcodes) raw (A + B + 2) := by
  intro slots out hrun
  have hpre : run M (ticks 0) (initial M raw) = some (initial M raw) := by
    simp [ticks]
  have hfuel : ∀ s d, run M (ticks s) (initial M raw) = some d → s ≤ A := by
    intro s d hk
    simpa [ticks_length] using htA (ticks s) d hk
  rw [initial_liftA] at hrun
  have := prefix_from_left M N hnb hcodes raw A B htA htB (initial M raw) 0 A
    slots out hpre hfuel hrun
  omega

theorem sequence_spec (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N) (raw : List Bool) (A B : Nat)
    (htA : RunsAtMost M raw A)
    (htB : ∀ (u : List (Fin 1)) (c : Configuration nsA nt),
      run M u (initial M raw) = some c → c.state = M.accept →
      ∀ (v : List (Fin nb)) (d : Configuration nsB nt),
        run N v { state := N.start, head := c.head, tape := c.tape } = some d →
        v.length ≤ B) :
    (∀ (a : Nat) (v : List (Fin nb)) (c : Configuration nsA nt)
        (d : Configuration nsB nt),
      run M (ticks a) (initial M raw) = some c → c.state = M.accept →
      run N v { state := N.start, head := c.head, tape := c.tape } = some d →
      d.state = N.accept →
      Accepted (machine M N hnb hcodes) raw
        (List.replicate a (zeroSlot hnb) ++ [zeroSlot hnb] ++ v ++
          [zeroSlot hnb])) ∧
    (∀ slots, Accepted (machine M N hnb hcodes) raw slots ↔
      ∃ (a : Nat) (v : List (Fin nb)) (c : Configuration nsA nt)
        (d : Configuration nsB nt),
        slots = List.replicate a (zeroSlot hnb) ++ [zeroSlot hnb] ++ v ++
          [zeroSlot hnb] ∧
        run M (ticks a) (initial M raw) = some c ∧ c.state = M.accept ∧
        run N v { state := N.start, head := c.head, tape := c.tape } = some d ∧
        d.state = N.accept) ∧
    RunsAtMost (machine M N hnb hcodes) raw (A + B + 2) := by
  refine ⟨?fwd, ?iff, sequence_runsAtMost M N hnb hcodes raw A B htA htB⟩
  · intro a v c d hu ha hv hd
    exact accepted_of_split M N hnb hcodes raw a v c d hu ha hv hd
  · intro slots
    exact accepted_iff_split M N hnb hcodes raw slots

def pad (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (f : List Bool → List Bool) (p : Nat → Nat)
    (hf : ComputesWithin M f p) (raw : List Bool) : List (Fin nb) :=
  List.replicate (duration M f p hf raw) (zeroSlot hnb) ++ [zeroSlot hnb]

theorem restart_eq_initial (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hcodes : SameCodes M N) (f : List Bool → List Bool) (p : Nat → Nat)
    (hf : ComputesWithin M f p) (raw : List Bool) :
    { state := N.start,
      head := (⟨M.accept, 0, inputTape M (f raw)⟩ : Configuration nsA nt).head,
      tape := (⟨M.accept, 0, inputTape M (f raw)⟩ : Configuration nsA nt).tape } =
      initial N (f raw) := by
  apply config_ext
  · rfl
  · rfl
  · exact (inputTape_N M N hcodes (f raw)).symm

theorem targetBound_of_runs (M : DeterministicMachine nsA nt)
    (N : Machine nsB nt nb) (hcodes : SameCodes M N)
    (f : List Bool → List Bool) (p : Nat → Nat)
    (hf : ComputesWithin M f p) (raw : List Bool) (B : Nat)
    (hB : RunsAtMost N (f raw) B) :
    ∀ (u : List (Fin 1)) (c : Configuration nsA nt),
      run M u (initial M raw) = some c → c.state = M.accept →
      ∀ (v : List (Fin nb)) (d : Configuration nsB nt),
        run N v { state := N.start, head := c.head, tape := c.tape } = some d →
        v.length ≤ B := by
  intro u c hu ha v d hv
  have ⟨hs, hout⟩ := accepted_run_unique M f p hf raw u c hu ha
  subst u
  have hc : c = ⟨M.accept, 0, inputTape M (f raw)⟩ := hout
  subst c
  have hv' : run N v (initial N (f raw)) = some d := by
    simpa [restart_eq_initial M N hcodes f p hf raw] using hv
  exact hB v d hv'

theorem accepted_iff_duration (M : DeterministicMachine nsA nt)
    (N : Machine nsB nt nb) (hnb : 0 < nb) (hcodes : SameCodes M N)
    (f : List Bool → List Bool) (p : Nat → Nat) (hf : ComputesWithin M f p)
    (raw : List Bool) (slots : List (Fin nb)) :
    Accepted (machine M N hnb hcodes) raw slots ↔
      ∃ v, Accepted N (f raw) v ∧
        slots = pad M N hnb f p hf raw ++ v ++ [zeroSlot hnb] := by
  constructor
  · intro hAcc
    obtain ⟨a, v, c, d, hs, hu, ha, hv, hd⟩ :=
      (accepted_iff_split M N hnb hcodes raw slots).mp hAcc
    have ⟨heq, hout⟩ :=
      accepted_run_unique M f p hf raw (ticks a) c (by simpa using hu) ha
    have haeq : a = duration M f p hf raw := by
      have := congrArg List.length heq
      simpa [ticks_length] using this
    subst a
    have hc : c = ⟨M.accept, 0, inputTape M (f raw)⟩ := hout
    subst c
    refine ⟨v, ?_, ?_⟩
    · refine (accepted_iff N (f raw) v).mpr ⟨d, ?_, hd⟩
      simpa [restart_eq_initial M N hcodes f p hf raw] using hv
    · simp [pad, hs]
  · intro h
    rcases h with ⟨v, hN, hs⟩
    obtain ⟨d, hv, hd⟩ := (accepted_iff N (f raw) v).mp hN
    have hdur := (duration_spec M f p hf raw).2
    let c0 : Configuration nsA nt := ⟨M.accept, 0, inputTape M (f raw)⟩
    have hacc : c0.state = M.accept := rfl
    have hv' : run N v { state := N.start, head := c0.head, tape := c0.tape } =
        some d := by
      simpa [c0, restart_eq_initial M N hcodes f p hf raw] using hv
    rw [hs, pad]
    exact accepted_of_split M N hnb hcodes raw (duration M f p hf raw) v
      c0 d hdur hacc hv' hd

theorem pad_inj (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (f : List Bool → List Bool) (p : Nat → Nat)
    (hf : ComputesWithin M f p) (raw : List Bool)
    (v1 v2 : List (Fin nb))
    (h : pad M N hnb f p hf raw ++ v1 ++ [zeroSlot hnb] =
      pad M N hnb f p hf raw ++ v2 ++ [zeroSlot hnb]) : v1 = v2 := by
  have hmid : pad M N hnb f p hf raw ++ v1 =
      pad M N hnb f p hf raw ++ v2 := List.append_cancel_right h
  exact List.append_cancel_left hmid

def leafEquiv (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (f : List Bool → List Bool) (p : Nat → Nat) (hf : ComputesWithin M f p)
    (raw : List Bool) :
    AcceptingLeaf N (f raw) ≃ AcceptingLeaf (machine M N hnb hcodes) raw where
  toFun w :=
    ⟨pad M N hnb f p hf raw ++ w.val ++ [zeroSlot hnb],
      (accepted_iff_duration M N hnb hcodes f p hf raw _).mpr ⟨w.val, w.property, rfl⟩⟩
  invFun w :=
    ⟨Classical.choose ((accepted_iff_duration M N hnb hcodes f p hf raw w.val).mp
        w.property),
      (Classical.choose_spec ((accepted_iff_duration M N hnb hcodes f p hf raw
          w.val).mp w.property)).1⟩
  left_inv w := by
    apply Subtype.ext
    have hspec := Classical.choose_spec
      ((accepted_iff_duration M N hnb hcodes f p hf raw
          (pad M N hnb f p hf raw ++ w.val ++ [zeroSlot hnb])).mp
        ((accepted_iff_duration M N hnb hcodes f p hf raw _).mpr
          ⟨w.val, w.property, rfl⟩))
    exact (pad_inj M N hnb f p hf raw _ _ (by simpa [List.append_assoc] using hspec.2)).symm
  right_inv w := by
    apply Subtype.ext
    exact (Classical.choose_spec
      ((accepted_iff_duration M N hnb hcodes f p hf raw w.val).mp w.property)).2.symm

def codeEquiv (M : DeterministicMachine nsA nt) (N : Machine nsB nt nb)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (f : List Bool → List Bool) (p : Nat → Nat) (hf : ComputesWithin M f p)
    (raw : List Bool) (B : Nat) (hB : RunsAtMost N (f raw) B) :
    AcceptingCode N (f raw) B ≃
      AcceptingCode (machine M N hnb hcodes) raw (p raw.length + B + 2) where
  toFun w :=
    ⟨WordCode.ofList
      (pad M N hnb f p hf raw ++ w.val.toList ++ [zeroSlot hnb])
      (by
        have hv : w.val.toList.length ≤ B :=
          accepting_length_le N (f raw) B hB w.val.toList w.property
        have hd : duration M f p hf raw ≤ p raw.length :=
          (duration_spec M f p hf raw).1
        simp [pad, WordCode.toList_length] at hv ⊢
        omega),
      by
        simpa using
          (accepted_iff_duration M N hnb hcodes f p hf raw _).mpr
            ⟨w.val.toList, w.property, rfl⟩⟩
  invFun w :=
    ⟨WordCode.ofList
      (Classical.choose
        ((accepted_iff_duration M N hnb hcodes f p hf raw w.val.toList).mp
          (by simpa using w.property)))
      (by
        have hspec := Classical.choose_spec
          ((accepted_iff_duration M N hnb hcodes f p hf raw w.val.toList).mp
            (by simpa using w.property))
        have : (Classical.choose
            ((accepted_iff_duration M N hnb hcodes f p hf raw w.val.toList).mp
              (by simpa using w.property))).length ≤ B :=
          accepting_length_le N (f raw) B hB _ hspec.1
        simpa using this),
      by
        have hspec := Classical.choose_spec
          ((accepted_iff_duration M N hnb hcodes f p hf raw w.val.toList).mp
            (by simpa using w.property))
        simpa using hspec.1⟩
  left_inv w := by
    apply Subtype.ext
    apply WordCode.toList_injective
    simp
    have hspec := Classical.choose_spec
      ((accepted_iff_duration M N hnb hcodes f p hf raw
          (pad M N hnb f p hf raw ++ w.val.toList ++ [zeroSlot hnb])).mp
        (by
          simpa using
            (accepted_iff_duration M N hnb hcodes f p hf raw _).mpr
              ⟨w.val.toList, w.property, rfl⟩))
    exact (pad_inj M N hnb f p hf raw _ _ (by
      simpa [List.append_assoc] using hspec.2)).symm
  right_inv w := by
    apply Subtype.ext
    apply WordCode.toList_injective
    simp
    have hspec := Classical.choose_spec
      ((accepted_iff_duration M N hnb hcodes f p hf raw w.val.toList).mp
        (by simpa using w.property))
    simpa [List.append_assoc] using hspec.2.symm

theorem acceptingCount_eq (M : DeterministicMachine nsA nt)
    (N : Machine nsB nt nb) (hnb : 0 < nb) (hcodes : SameCodes M N)
    (f : List Bool → List Bool) (p : Nat → Nat) (hf : ComputesWithin M f p)
    (raw : List Bool) (B : Nat) (hB : RunsAtMost N (f raw) B) :
    acceptingCount (machine M N hnb hcodes) raw (p raw.length + B + 2) =
      acceptingCount N (f raw) B :=
  (Fintype.card_congr (codeEquiv M N hnb hcodes f p hf raw B hB)).symm

theorem initializer_spec (M : DeterministicMachine nsA nt)
    (N : Machine nsB nt nb) (hnb : 0 < nb) (hcodes : SameCodes M N)
    (f : List Bool → List Bool) (p : Nat → Nat) (hf : ComputesWithin M f p)
    (raw : List Bool) (B : Nat) (hB : RunsAtMost N (f raw) B) :
    (∀ slots, Accepted (machine M N hnb hcodes) raw slots ↔
      ∃ v, Accepted N (f raw) v ∧
        slots = pad M N hnb f p hf raw ++ v ++ [zeroSlot hnb]) ∧
    RunsAtMost (machine M N hnb hcodes) raw (p raw.length + B + 2) ∧
    acceptingCount (machine M N hnb hcodes) raw (p raw.length + B + 2) =
      acceptingCount N (f raw) B := by
  refine ⟨accepted_iff_duration M N hnb hcodes f p hf raw, ?_,
    acceptingCount_eq M N hnb hcodes f p hf raw B hB⟩
  exact sequence_runsAtMost M N hnb hcodes raw (p raw.length) B
    (ComputesWithin.actual_bounds M f p hf raw).1
    (targetBound_of_runs M N hcodes f p hf raw B hB)

end
end PakFixedPolyomino.StandardMachineDeterministicNondeterministicSequence
