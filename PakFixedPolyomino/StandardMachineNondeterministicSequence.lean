import PakFixedPolyomino.StandardBitTime
import PakFixedPolyomino.StandardBitMachineComposition

/-! Common-alphabet sequencer: an arbitrary finite-branch source phase
followed by a deterministic continuation. One slot-0 stay hands the
source accept configuration (head and every tape cell) to the
continuation start. One slot-0 stay finalizes continuation accept/reject
to the global codes. No runtime/count certificate premises. -/
set_option maxHeartbeats 0
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace PakFixedPolyomino.StandardMachineNondeterministicSequence
noncomputable section
open StandardNondeterministicMachine StandardBitTime
open FiniteOneTapeSemantics (moveHead writtenTape)
open StandardBitMachineComposition (config_ext)

variable {nsA nsB nt nb : Nat}

def SameCodes (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt) : Prop :=
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
    2 ≤ (encodeLeft (nsB := nsB) q).val ∧
      (encodeLeft (nsB := nsB) q).val - 2 < nsA := by
  have := q.isLt
  simp [encodeLeft]

theorem encodeRight_range (q : Fin nsB) :
    2 + nsA ≤ (encodeRight (nsA := nsA) q).val ∧
      (encodeRight (nsA := nsA) q).val - (2 + nsA) < nsB := by
  have := q.isLt
  simp [encodeRight]

theorem encodeLeft_ne_zero (q : Fin nsA) : (encodeLeft (nsB := nsB) q).val ≠ 0 := by
  simp [encodeLeft]
theorem encodeLeft_ne_one (q : Fin nsA) : (encodeLeft (nsB := nsB) q).val ≠ 1 := by
  simp [encodeLeft]; omega
theorem encodeRight_ne_zero (q : Fin nsB) : (encodeRight (nsA := nsA) q).val ≠ 0 := by
  simp [encodeRight]
theorem encodeRight_ne_one (q : Fin nsB) : (encodeRight (nsA := nsA) q).val ≠ 1 := by
  simp [encodeRight]; omega

theorem encodeLeft_not_right (qa : Fin nsA) (qb : Fin nsB) :
    encodeLeft (nsB := nsB) qa ≠ encodeRight (nsA := nsA) qb := by
  intro h
  have hv := congrArg Fin.val h
  have := qa.isLt
  have := qb.isLt
  simp [encodeLeft, encodeRight] at hv
  omega

def ruleLeft (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (qa : Fin nsA) (read : Fin nt) (slot : Fin nb) :
    Option (FiniteOneTapeProgram.Action (Fin (nsA + nsB + 2)) (Fin nt)) :=
  if qa = M.accept then
    if slot = zeroSlot hnb then
      some ⟨read, encodeRight N.start, .stay⟩
    else none
  else if qa = M.reject then
    if slot = zeroSlot hnb then
      some ⟨read, rejectC, .stay⟩
    else none
  else
    (M.rule qa read slot).map fun a =>
      ⟨a.write, encodeLeft a.target, a.move⟩

def ruleRight (N : DeterministicMachine nsB nt) (hnb : 0 < nb)
    (qb : Fin nsB) (read : Fin nt) (slot : Fin nb) :
    Option (FiniteOneTapeProgram.Action (Fin (nsA + nsB + 2)) (Fin nt)) :=
  if qb = N.accept then
    if slot = zeroSlot hnb then
      some ⟨read, acceptC, .stay⟩
    else none
  else if qb = N.reject then
    if slot = zeroSlot hnb then
      some ⟨read, rejectC, .stay⟩
    else none
  else if slot = zeroSlot hnb then
    (N.rule qb read 0).map fun a =>
      ⟨a.write, encodeRight a.target, a.move⟩
  else none

def ndRule (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (q : Fin (nsA + nsB + 2)) (read : Fin nt) (slot : Fin nb) :
    Option (FiniteOneTapeProgram.Action (Fin (nsA + nsB + 2)) (Fin nt)) :=
  if q.val = 0 ∨ q.val = 1 then none
  else if hA : 2 ≤ q.val ∧ q.val - 2 < nsA then
    ruleLeft M N hnb ⟨q.val - 2, hA.2⟩ read slot
  else if hB : 2 + nsA ≤ q.val ∧ q.val - (2 + nsA) < nsB then
    ruleRight N hnb ⟨q.val - (2 + nsA), hB.2⟩ read slot
  else none

def machine (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N) : Machine (nsA + nsB + 2) nt nb where
  rule := ndRule M N hnb
  start := encodeLeft M.start
  accept := acceptC
  reject := rejectC
  accept_ne_reject := by
    intro h
    have hv := congrArg Fin.val h
    simp [acceptC, rejectC] at hv
  blank := M.blank
  zero := M.zero
  one := M.one
  blank_ne_zero := M.blank_ne_zero
  blank_ne_one := M.blank_ne_one
  zero_ne_one := M.zero_ne_one
  accept_terminal := by intro x slot; simp [ndRule, acceptC]
  reject_terminal := by intro x slot; simp [ndRule, rejectC]

theorem machine_rule (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N) :
    (machine M N hnb hcodes).rule = ndRule M N hnb := rfl
theorem machine_start (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N) :
    (machine M N hnb hcodes).start = encodeLeft M.start := rfl
theorem machine_accept (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N) :
    (machine M N hnb hcodes).accept = acceptC := rfl
theorem machine_reject (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N) :
    (machine M N hnb hcodes).reject = rejectC := rfl

theorem ndRule_left (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (qa : Fin nsA) (read : Fin nt) (slot : Fin nb) :
    ndRule M N hnb (encodeLeft qa) read slot = ruleLeft M N hnb qa read slot := by
  have hterm : ¬ ((encodeLeft (nsB := nsB) qa).val = 0 ∨
      (encodeLeft (nsB := nsB) qa).val = 1) := by
    intro h; rcases h with h | h
    · exact encodeLeft_ne_zero (nsB := nsB) qa h
    · exact encodeLeft_ne_one (nsB := nsB) qa h
  have hA := encodeLeft_range (nsB := nsB) qa
  have hq : (⟨(encodeLeft (nsB := nsB) qa).val - 2, hA.2⟩ : Fin nsA) = qa := by
    apply Fin.ext
    simp [encodeLeft]
  unfold ndRule
  rw [if_neg hterm, dif_pos hA]
  simp [hq]

theorem ndRule_right (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (qb : Fin nsB) (read : Fin nt) (slot : Fin nb) :
    ndRule M N hnb (encodeRight qb) read slot = ruleRight N hnb qb read slot := by
  have hterm : ¬ ((encodeRight (nsA := nsA) qb).val = 0 ∨
      (encodeRight (nsA := nsA) qb).val = 1) := by
    intro h; rcases h with h | h
    · exact encodeRight_ne_zero (nsA := nsA) qb h
    · exact encodeRight_ne_one (nsA := nsA) qb h
  have hA : ¬ (2 ≤ (encodeRight (nsA := nsA) qb).val ∧
      (encodeRight (nsA := nsA) qb).val - 2 < nsA) := by
    intro h
    have := qb.isLt
    simp [encodeRight] at h
    omega
  have hB := encodeRight_range (nsA := nsA) qb
  have hq : (⟨(encodeRight (nsA := nsA) qb).val - (2 + nsA), hB.2⟩ : Fin nsB) = qb := by
    apply Fin.ext
    simp [encodeRight]
  unfold ndRule
  rw [if_neg hterm, dif_neg hA, dif_pos hB]
  simp [hq]

theorem inputTape_machine (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N) (x : List Bool) :
    inputTape (machine M N hnb hcodes) x = inputTape M x := by
  funext z
  simp [inputTape, machine]

theorem inputTape_N (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hcodes : SameCodes M N) (x : List Bool) :
    inputTape N x = inputTape M x := by
  funext z
  rcases hcodes with ⟨hb, hz, ho⟩
  simp [inputTape, hb, hz, ho]

theorem initial_liftA (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N) (raw : List Bool) :
    initial (machine M N hnb hcodes) raw = liftA (initial M raw) := by
  apply config_ext
  · rfl
  · rfl
  · exact inputTape_machine M N hnb hcodes raw

theorem step_M_nonterminal (M : Machine nsA nt nb)
    (c c' : Configuration nsA nt) (slot : Fin nb)
    (h : step M slot c = some c') :
    c.state ≠ M.accept ∧ c.state ≠ M.reject := by
  constructor
  · intro hs; simp [step, hs, M.accept_terminal] at h
  · intro hs; simp [step, hs, M.reject_terminal] at h

theorem step_N_nonterminal (N : DeterministicMachine nsB nt)
    (c c' : Configuration nsB nt)
    (h : step N 0 c = some c') :
    c.state ≠ N.accept ∧ c.state ≠ N.reject := by
  constructor
  · intro hs; simp [step, hs, N.accept_terminal] at h
  · intro hs; simp [step, hs, N.reject_terminal] at h

theorem lift_step_A (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c c' : Configuration nsA nt) (slot : Fin nb)
    (h : step M slot c = some c') :
    step (machine M N hnb hcodes) slot (liftA c) = some (liftA c') := by
  have hsrc := step_M_nonterminal M c c' slot h
  simp only [step, liftA, machine_rule] at h ⊢
  cases hrule : M.rule c.state (c.tape c.head) slot with
  | none => simp [hrule] at h
  | some a =>
      simp [hrule] at h
      subst c'
      rw [ndRule_left, ruleLeft, if_neg hsrc.1, if_neg hsrc.2, hrule]
      simp [liftA, writtenTape]

theorem lift_run_A (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (u : List (Fin nb)) (c out : Configuration nsA nt)
    (h : run M u c = some out) :
    run (machine M N hnb hcodes) u (liftA c) = some (liftA out) := by
  induction u generalizing c with
  | nil =>
      simp at h; subst out; simp
  | cons slot u ih =>
      rw [run_cons] at h
      cases hstep : step M slot c with
      | none => simp [hstep] at h
      | some mid =>
          simp [hstep] at h
          rw [run_cons, lift_step_A (h := hstep), Option.bind_some]
          exact ih mid h

theorem handoff_accept (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c : Configuration nsA nt) (hs : c.state = M.accept) :
    step (machine M N hnb hcodes) (zeroSlot hnb) (liftA c) =
      some (liftB { state := N.start, head := c.head, tape := c.tape }) := by
  simp only [step, liftA, machine_rule]
  rw [ndRule_left, ruleLeft, if_pos hs, if_pos rfl]
  simp [moveHead, writtenTape, Function.update_eq_self, liftB]

theorem handoff_reject (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c : Configuration nsA nt) (hs : c.state = M.reject) :
    step (machine M N hnb hcodes) (zeroSlot hnb) (liftA c) =
      some { state := rejectC, head := c.head, tape := c.tape } := by
  have hne : c.state ≠ M.accept := fun h => M.accept_ne_reject (h.symm.trans hs)
  simp only [step, liftA, machine_rule]
  rw [ndRule_left, ruleLeft, if_neg hne, if_pos hs, if_pos rfl]
  simp [moveHead, writtenTape, Function.update_eq_self]

theorem lift_step_B (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c c' : Configuration nsB nt)
    (h : step N 0 c = some c') :
    step (machine M N hnb hcodes) (zeroSlot hnb) (liftB c) = some (liftB c') := by
  have hsrc := step_N_nonterminal N c c' h
  simp only [step, liftB, machine_rule] at h ⊢
  cases hrule : N.rule c.state (c.tape c.head) 0 with
  | none => simp [hrule] at h
  | some a =>
      simp [hrule] at h
      subst c'
      rw [ndRule_right, ruleRight, if_neg hsrc.1, if_neg hsrc.2, if_pos rfl, hrule]
      simp [liftB, writtenTape]

theorem lift_run_B (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (n : Nat) (c out : Configuration nsB nt)
    (h : run N (ticks n) c = some out) :
    run (machine M N hnb hcodes) (List.replicate n (zeroSlot hnb)) (liftB c) =
      some (liftB out) := by
  induction n generalizing c with
  | zero =>
      simp [ticks] at h; subst out; simp
  | succ n ih =>
      change run N (0 :: ticks n) c = some out at h
      rw [run_cons] at h
      cases hstep : step N 0 c with
      | none => simp [hstep] at h
      | some mid =>
          simp [hstep] at h
          rw [List.replicate_succ, run_cons, lift_step_B (h := hstep), Option.bind_some]
          exact ih mid h

theorem finalize_accept (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c : Configuration nsB nt) (hs : c.state = N.accept) :
    step (machine M N hnb hcodes) (zeroSlot hnb) (liftB c) =
      some { state := acceptC, head := c.head, tape := c.tape } := by
  simp only [step, liftB, machine_rule]
  rw [ndRule_right, ruleRight, if_pos hs, if_pos rfl]
  simp [moveHead, writtenTape, Function.update_eq_self]

theorem finalize_reject (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c : Configuration nsB nt) (hs : c.state = N.reject) :
    step (machine M N hnb hcodes) (zeroSlot hnb) (liftB c) =
      some { state := rejectC, head := c.head, tape := c.tape } := by
  have hne : c.state ≠ N.accept := fun h => N.accept_ne_reject (h.symm.trans hs)
  simp only [step, liftB, machine_rule]
  rw [ndRule_right, ruleRight, if_neg hne, if_pos hs, if_pos rfl]
  simp [moveHead, writtenTape, Function.update_eq_self]

theorem sequence_run (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N) (raw : List Bool)
    (u : List (Fin nb)) (n : Nat)
    (c : Configuration nsA nt) (d : Configuration nsB nt)
    (hu : run M u (initial M raw) = some c) (hacc : c.state = M.accept)
    (hv : run N (ticks n) { state := N.start, head := c.head, tape := c.tape } = some d)
    (hd : d.state = N.accept) :
    run (machine M N hnb hcodes)
        (u ++ [zeroSlot hnb] ++ List.replicate n (zeroSlot hnb) ++ [zeroSlot hnb])
        (initial (machine M N hnb hcodes) raw) =
      some { state := acceptC, head := d.head, tape := d.tape } := by
  have hArun : run (machine M N hnb hcodes) u
      (initial (machine M N hnb hcodes) raw) = some (liftA c) := by
    rw [initial_liftA, lift_run_A (h := hu)]
  have hHand : run (machine M N hnb hcodes) (u ++ [zeroSlot hnb])
      (initial (machine M N hnb hcodes) raw) =
      some (liftB { state := N.start, head := c.head, tape := c.tape }) := by
    rw [run_append, hArun, Option.bind_some, run_cons, handoff_accept (hs := hacc),
      Option.bind_some, run_nil]
  have hBrun : run (machine M N hnb hcodes)
      (u ++ [zeroSlot hnb] ++ List.replicate n (zeroSlot hnb))
      (initial (machine M N hnb hcodes) raw) = some (liftB d) := by
    rw [run_append, hHand, Option.bind_some, lift_run_B (h := hv)]
  rw [run_append, hBrun, Option.bind_some, run_cons, finalize_accept (hs := hd),
    Option.bind_some, run_nil]

theorem accepted_of_split (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N) (raw : List Bool)
    (u : List (Fin nb)) (n : Nat)
    (c : Configuration nsA nt) (d : Configuration nsB nt)
    (hu : run M u (initial M raw) = some c) (hacc : c.state = M.accept)
    (hv : run N (ticks n) { state := N.start, head := c.head, tape := c.tape } = some d)
    (hd : d.state = N.accept) :
    Accepted (machine M N hnb hcodes) raw
      (u ++ [zeroSlot hnb] ++ List.replicate n (zeroSlot hnb) ++ [zeroSlot hnb]) := by
  refine (accepted_iff (machine M N hnb hcodes) raw _).mpr ?_
  refine ⟨_, sequence_run M N hnb hcodes raw u n c d hu hacc hv hd, ?_⟩
  rfl

theorem step_left_inv (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c : Configuration nsA nt) (slot : Fin nb)
    (mid : Configuration (nsA + nsB + 2) nt)
    (h : step (machine M N hnb hcodes) slot (liftA c) = some mid) :
    (c.state = M.accept ∧ slot = zeroSlot hnb ∧
      mid = liftB { state := N.start, head := c.head, tape := c.tape }) ∨
    (c.state = M.reject ∧ slot = zeroSlot hnb ∧
      mid = { state := rejectC, head := c.head, tape := c.tape }) ∨
    (c.state ≠ M.accept ∧ c.state ≠ M.reject ∧
      ∃ c', step M slot c = some c' ∧ mid = liftA c') := by
  simp only [step, liftA, machine_rule] at h
  rw [ndRule_left] at h
  by_cases hacc : c.state = M.accept
  · rw [ruleLeft, if_pos hacc] at h
    by_cases hs0 : slot = zeroSlot hnb
    · rw [if_pos hs0] at h
      simp [moveHead, writtenTape, Function.update_eq_self] at h
      subst mid
      exact Or.inl ⟨hacc, hs0, by simp [liftB]⟩
    · rw [if_neg hs0] at h
      simp at h
  · by_cases hrej : c.state = M.reject
    · rw [ruleLeft, if_neg hacc, if_pos hrej] at h
      by_cases hs0 : slot = zeroSlot hnb
      · rw [if_pos hs0] at h
        simp [moveHead, writtenTape, Function.update_eq_self] at h
        subst mid
        exact Or.inr (Or.inl ⟨hrej, hs0, rfl⟩)
      · rw [if_neg hs0] at h
        simp at h
    · rw [ruleLeft, if_neg hacc, if_neg hrej] at h
      cases hrule : M.rule c.state (c.tape c.head) slot with
      | none => simp [hrule] at h
      | some a =>
          simp [hrule] at h
          subst mid
          refine Or.inr (Or.inr ⟨hacc, hrej, ?_⟩)
          let c' : Configuration nsA nt :=
            { state := a.target, head := moveHead a.move c.head,
              tape := writtenTape c a.write }
          refine ⟨c', ?_⟩
          constructor
          · simp [step, hrule, c']
          · simp [liftA, c', writtenTape]

theorem step_right_inv (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c : Configuration nsB nt) (slot : Fin nb)
    (mid : Configuration (nsA + nsB + 2) nt)
    (h : step (machine M N hnb hcodes) slot (liftB c) = some mid) :
    (c.state = N.accept ∧ slot = zeroSlot hnb ∧
      mid = { state := acceptC, head := c.head, tape := c.tape }) ∨
    (c.state = N.reject ∧ slot = zeroSlot hnb ∧
      mid = { state := rejectC, head := c.head, tape := c.tape }) ∨
    (c.state ≠ N.accept ∧ c.state ≠ N.reject ∧ slot = zeroSlot hnb ∧
      ∃ c', step N 0 c = some c' ∧ mid = liftB c') := by
  simp only [step, liftB, machine_rule] at h
  rw [ndRule_right] at h
  by_cases hacc : c.state = N.accept
  · rw [ruleRight, if_pos hacc] at h
    by_cases hs0 : slot = zeroSlot hnb
    · rw [if_pos hs0] at h
      simp [moveHead, writtenTape, Function.update_eq_self] at h
      subst mid
      exact Or.inl ⟨hacc, hs0, rfl⟩
    · rw [if_neg hs0] at h
      simp at h
  · by_cases hrej : c.state = N.reject
    · rw [ruleRight, if_neg hacc, if_pos hrej] at h
      by_cases hs0 : slot = zeroSlot hnb
      · rw [if_pos hs0] at h
        simp [moveHead, writtenTape, Function.update_eq_self] at h
        subst mid
        exact Or.inr (Or.inl ⟨hrej, hs0, rfl⟩)
      · rw [if_neg hs0] at h
        simp at h
    · rw [ruleRight, if_neg hacc, if_neg hrej] at h
      by_cases hs0 : slot = zeroSlot hnb
      · rw [if_pos hs0] at h
        cases hrule : N.rule c.state (c.tape c.head) 0 with
        | none => simp [hrule] at h
        | some a =>
            simp [hrule] at h
            subst mid
            refine Or.inr (Or.inr ⟨hacc, hrej, hs0, ?_⟩)
            let c' : Configuration nsB nt :=
              { state := a.target, head := moveHead a.move c.head,
                tape := writtenTape c a.write }
            refine ⟨c', ?_⟩
            constructor
            · simp [step, hrule, c']
            · simp [liftB, c', writtenTape]
      · simp [hs0] at h

theorem run_reject_nonempty_none {ns nt br : Nat}
    (M : Machine ns nt br) (c : Configuration ns nt)
    (hstate : c.state = M.reject) (slots : List (Fin br)) (hne : slots ≠ []) :
    run M slots c = none := by
  cases slots with
  | nil => contradiction
  | cons slot rest => simp [run_cons, step_reject_none M slot c hstate]

theorem accepted_from_right (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (cB : Configuration nsB nt) (slots : List (Fin nb))
    (out : Configuration (nsA + nsB + 2) nt)
    (h : run (machine M N hnb hcodes) slots (liftB cB) = some out)
    (hacc : out.state = acceptC) :
    ∃ n d, slots = List.replicate n (zeroSlot hnb) ++ [zeroSlot hnb] ∧
      run N (ticks n) cB = some d ∧ d.state = N.accept := by
  induction slots generalizing cB with
  | nil =>
      simp at h
      subst out
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
            subst slot
            rw [hmid] at h
            cases rest with
            | nil =>
                simp at h
                subst out
                refine ⟨0, cB, ?_, ?_, hs⟩
                · simp
                · simp [ticks]
            | cons s rest =>
                have hst :
                    ({ state := acceptC, head := cB.head, tape := cB.tape } :
                      Configuration (nsA + nsB + 2) nt).state =
                      (machine M N hnb hcodes).accept := by
                  simp [machine_accept]
                have hnone := run_accept_nonempty_none (machine M N hnb hcodes)
                    { state := acceptC, head := cB.head, tape := cB.tape } hst
                    (s :: rest) (by simp)
                simp [hnone] at h
          · rcases hFinR with ⟨_, hs0, hmid⟩
            subst slot
            rw [hmid] at h
            cases rest with
            | nil =>
                simp at h
                subst out
                simp [acceptC, rejectC] at hacc
            | cons s rest =>
                have hst :
                    ({ state := rejectC, head := cB.head, tape := cB.tape } :
                      Configuration (nsA + nsB + 2) nt).state =
                      (machine M N hnb hcodes).reject := by
                  simp [machine_reject]
                have hnone := run_reject_nonempty_none (machine M N hnb hcodes)
                    { state := rejectC, head := cB.head, tape := cB.tape } hst
                    (s :: rest) (by simp)
                simp [hnone] at h
          · rcases hOrd with ⟨_, _, hs0, cB', hN, hmid⟩
            subst slot
            subst mid
            obtain ⟨n, d, hrest, hrun, hd⟩ := ih cB' h
            refine ⟨n + 1, d, ?_, ?_, hd⟩
            · simp [hrest, List.replicate_succ, List.cons_append]
            · change run N (0 :: ticks n) cB = some d
              rw [run_cons, hN, Option.bind_some, hrun]

theorem accepted_from_left (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (c : Configuration nsA nt) (slots : List (Fin nb))
    (out : Configuration (nsA + nsB + 2) nt)
    (h : run (machine M N hnb hcodes) slots (liftA c) = some out)
    (hacc : out.state = acceptC) :
    ∃ u n cAcc d,
      slots = u ++ [zeroSlot hnb] ++ List.replicate n (zeroSlot hnb) ++ [zeroSlot hnb] ∧
      run M u c = some cAcc ∧ cAcc.state = M.accept ∧
      run N (ticks n) { state := N.start, head := cAcc.head, tape := cAcc.tape } =
        some d ∧ d.state = N.accept := by
  induction slots generalizing c with
  | nil =>
      simp at h
      subst out
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
            subst slot
            rw [hmid] at h
            obtain ⟨n, d, hrest, hN, hd⟩ :=
              accepted_from_right M N hnb hcodes
                { state := N.start, head := c.head, tape := c.tape } rest out h hacc
            refine ⟨[], n, c, d, ?_, ?_, hs, hN, hd⟩
            · simp [hrest]
            · simp
          · rcases hRej with ⟨_, hs0, hmid⟩
            subst slot
            rw [hmid] at h
            cases rest with
            | nil =>
                simp at h
                subst out
                simp [acceptC, rejectC] at hacc
            | cons s rest =>
                have hst :
                    ({ state := rejectC, head := c.head, tape := c.tape } :
                      Configuration (nsA + nsB + 2) nt).state =
                      (machine M N hnb hcodes).reject := by
                  simp [machine_reject]
                have hnone := run_reject_nonempty_none (machine M N hnb hcodes)
                    { state := rejectC, head := c.head, tape := c.tape } hst
                    (s :: rest) (by simp)
                simp [hnone] at h
          · rcases hOrd with ⟨_, _, c', hM, hmid⟩
            subst mid
            obtain ⟨u, n, cAcc, d, hrest, hu, ha, hv, hd⟩ := ih c' h
            refine ⟨slot :: u, n, cAcc, d, ?_, ?_, ha, hv, hd⟩
            · simp [hrest]
            · rw [run_cons, hM, Option.bind_some, hu]

theorem accepted_iff_split (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N) (raw : List Bool) (slots : List (Fin nb)) :
    Accepted (machine M N hnb hcodes) raw slots ↔
      ∃ (u v : List (Fin nb)) (c : Configuration nsA nt) (d : Configuration nsB nt),
        slots = u ++ [zeroSlot hnb] ++ v ++ [zeroSlot hnb] ∧
        run M u (initial M raw) = some c ∧ c.state = M.accept ∧
        v = List.replicate v.length (zeroSlot hnb) ∧
        run N (ticks v.length) { state := N.start, head := c.head, tape := c.tape } =
          some d ∧ d.state = N.accept := by
  constructor
  · intro hAcc
    obtain ⟨out, hrun, hst⟩ := (accepted_iff (machine M N hnb hcodes) raw slots).mp hAcc
    have hstC : out.state = acceptC := by simpa [machine_accept] using hst
    rw [initial_liftA] at hrun
    obtain ⟨u, n, c, d, hs, hu, ha, hv, hd⟩ :=
      accepted_from_left M N hnb hcodes (initial M raw) slots out hrun hstC
    refine ⟨u, List.replicate n (zeroSlot hnb), c, d, hs, hu, ha, ?_, ?_, hd⟩
    · simp
    · simpa using hv
  · intro h
    rcases h with ⟨u, v, c, d, hs, hu, ha, hv, hN, hd⟩
    rw [hs, hv]
    exact accepted_of_split M N hnb hcodes raw u v.length c d hu ha hN hd

theorem split_unique (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (raw : List Bool) (slots : List (Fin nb))
    (u1 u2 v1 v2 : List (Fin nb))
    (c1 c2 : Configuration nsA nt) (d1 d2 : Configuration nsB nt)
    (hs1 : slots = u1 ++ [zeroSlot hnb] ++ v1 ++ [zeroSlot hnb])
    (hu1 : run M u1 (initial M raw) = some c1) (ha1 : c1.state = M.accept)
    (hs2 : slots = u2 ++ [zeroSlot hnb] ++ v2 ++ [zeroSlot hnb])
    (hu2 : run M u2 (initial M raw) = some c2) (ha2 : c2.state = M.accept)
    (hv1eq : v1 = List.replicate v1.length (zeroSlot hnb))
    (hv2eq : v2 = List.replicate v2.length (zeroSlot hnb))
    (hn1 : run N (ticks v1.length)
      { state := N.start, head := c1.head, tape := c1.tape } = some d1)
    (hn2 : run N (ticks v2.length)
      { state := N.start, head := c2.head, tape := c2.tape } = some d2) :
    u1 = u2 ∧ v1 = v2 ∧ c1 = c2 ∧ d1 = d2 := by
  have e1 : slots = u1 ++ ([zeroSlot hnb] ++ v1 ++ [zeroSlot hnb]) := by
    simp [hs1, List.append_assoc]
  have e2 : slots = u2 ++ ([zeroSlot hnb] ++ v2 ++ [zeroSlot hnb]) := by
    simp [hs2, List.append_assoc]
  have tu1 : slots.take u1.length = u1 := by rw [e1, List.take_left]
  have tu2 : slots.take u2.length = u2 := by rw [e2, List.take_left]
  have hlen : u1.length = u2.length := by
    by_contra hne
    have hord : u1.length < u2.length ∨ u2.length < u1.length :=
      Nat.lt_or_gt_of_ne hne
    rcases hord with hlt | hlt
    · let extra :=
        ([zeroSlot hnb] ++ v1 ++ [zeroSlot hnb]).take (u2.length - u1.length)
      have hx : extra ≠ [] := by
        intro he
        have := List.take_eq_nil_iff.mp he
        rcases this with hz | hempty
        · omega
        · simp at hempty
      have hu2eq : u2 = u1 ++ extra := by
        calc
          u2 = slots.take u2.length := tu2.symm
          _ = (u1 ++ ([zeroSlot hnb] ++ v1 ++ [zeroSlot hnb])).take u2.length := by
            rw [e1]
          _ = u1.take u2.length ++ extra := List.take_append
          _ = u1 ++ extra := by
            rw [List.take_of_length_le (Nat.le_of_lt hlt)]
      have hnone : run M u2 (initial M raw) = none := by
        rw [hu2eq, run_append, hu1, Option.bind_some]
        exact run_accept_nonempty_none M c1 ha1 extra hx
      simp [hnone] at hu2
    · let extra :=
        ([zeroSlot hnb] ++ v2 ++ [zeroSlot hnb]).take (u1.length - u2.length)
      have hx : extra ≠ [] := by
        intro he
        have := List.take_eq_nil_iff.mp he
        rcases this with hz | hempty
        · omega
        · simp at hempty
      have hu1eq : u1 = u2 ++ extra := by
        calc
          u1 = slots.take u1.length := tu1.symm
          _ = (u2 ++ ([zeroSlot hnb] ++ v2 ++ [zeroSlot hnb])).take u1.length := by
            rw [e2]
          _ = u2.take u1.length ++ extra := List.take_append
          _ = u2 ++ extra := by
            rw [List.take_of_length_le (Nat.le_of_lt hlt)]
      have hnone : run M u1 (initial M raw) = none := by
        rw [hu1eq, run_append, hu2, Option.bind_some]
        exact run_accept_nonempty_none M c2 ha2 extra hx
      simp [hnone] at hu1
  have hu : u1 = u2 := by
    rw [← tu1, ← tu2, hlen]
  subst u2
  have hc : c1 = c2 := Option.some.inj (hu1.symm.trans hu2)
  subst c2
  have hr : [zeroSlot hnb] ++ v1 ++ [zeroSlot hnb] =
      [zeroSlot hnb] ++ v2 ++ [zeroSlot hnb] :=
    List.append_cancel_left (e1.symm.trans e2)
  have hlenv : v1.length = v2.length := by
    have := congrArg List.length hr
    simp [List.length_append] at this
    omega
  have hv : v1 = v2 := by
    rw [hv1eq, hv2eq, hlenv]
  subst v2
  have hd : d1 = d2 := Option.some.inj (hn1.symm.trans hn2)
  exact ⟨rfl, rfl, rfl, hd⟩

theorem prefix_len_right (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N)
    (cB : Configuration nsB nt) (B : Nat) (slots : List (Fin nb))
    (out : Configuration (nsA + nsB + 2) nt)
    (hB : ∀ k d, run N (ticks k) cB = some d → k ≤ B)
    (h : run (machine M N hnb hcodes) slots (liftB cB) = some out) :
    slots.length ≤ B + 1 := by
  induction slots generalizing cB B with
  | nil => simp
  | cons slot rest ih =>
      rw [run_cons] at h
      cases hstep : step (machine M N hnb hcodes) slot (liftB cB) with
      | none => simp [hstep] at h
      | some mid =>
          simp [hstep] at h
          have hinv := step_right_inv M N hnb hcodes cB slot mid hstep
          rcases hinv with hFinA | hFinR | hOrd
          · rcases hFinA with ⟨_, hs0, hmid⟩
            subst slot
            rw [hmid] at h
            cases rest with
            | nil => simp
            | cons s rest =>
                have hst :
                    ({ state := acceptC, head := cB.head, tape := cB.tape } :
                      Configuration (nsA + nsB + 2) nt).state =
                      (machine M N hnb hcodes).accept := by
                  simp [machine_accept]
                have hnone := run_accept_nonempty_none (machine M N hnb hcodes)
                    { state := acceptC, head := cB.head, tape := cB.tape } hst
                    (s :: rest) (by simp)
                simp [hnone] at h
          · rcases hFinR with ⟨_, hs0, hmid⟩
            subst slot
            rw [hmid] at h
            cases rest with
            | nil => simp
            | cons s rest =>
                have hst :
                    ({ state := rejectC, head := cB.head, tape := cB.tape } :
                      Configuration (nsA + nsB + 2) nt).state =
                      (machine M N hnb hcodes).reject := by
                  simp [machine_reject]
                have hnone := run_reject_nonempty_none (machine M N hnb hcodes)
                    { state := rejectC, head := cB.head, tape := cB.tape } hst
                    (s :: rest) (by simp)
                simp [hnone] at h
          · rcases hOrd with ⟨_, _, hs0, cB', hN, hmid⟩
            subst slot
            subst mid
            have h1 : 1 ≤ B := by
              have : run N (ticks 1) cB = some cB' := by
                change run N [0] cB = some cB'
                simp [run_cons, hN]
              exact hB 1 cB' this
            have hB' : ∀ k d, run N (ticks k) cB' = some d → k ≤ B - 1 := by
              intro k d hk
              have : run N (ticks (k + 1)) cB = some d := by
                change run N (0 :: ticks k) cB = some d
                rw [run_cons, hN, Option.bind_some, hk]
              have hkB : k + 1 ≤ B := hB (k + 1) d this
              omega
            have := ih cB' (B - 1) hB' h
            simp at this ⊢
            omega

theorem prefix_from_left (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N) (raw : List Bool) (A B : Nat)
    (htA : RunsAtMost M raw A)
    (htB : ∀ (u : List (Fin nb)) (c : Configuration nsA nt),
      run M u (initial M raw) = some c → c.state = M.accept →
      ∀ (v : List (Fin nb)) (d : Configuration nsB nt),
        run N (ticks v.length)
          { state := N.start, head := c.head, tape := c.tape } = some d →
        v.length ≤ B)
    (u0 : List (Fin nb)) (c : Configuration nsA nt) (slots : List (Fin nb))
    (out : Configuration (nsA + nsB + 2) nt)
    (hu0 : run M u0 (initial M raw) = some c)
    (h : run (machine M N hnb hcodes) slots (liftA c) = some out) :
    u0.length + slots.length ≤ A + B + 2 := by
  induction slots generalizing c u0 with
  | nil =>
      have hlen : u0.length ≤ A := htA u0 c hu0
      have hpad : A ≤ A + B + 2 := Nat.le_add_right A (B + 2)
      exact Nat.le_trans (by simpa using hlen) hpad
  | cons slot rest ih =>
      rw [run_cons] at h
      cases hstep : step (machine M N hnb hcodes) slot (liftA c) with
      | none => simp [hstep] at h
      | some mid =>
          simp [hstep] at h
          have hinv := step_left_inv M N hnb hcodes c slot mid hstep
          rcases hinv with hHand | hRej | hOrd
          · rcases hHand with ⟨hs, hs0, hmid⟩
            subst slot
            rw [hmid] at h
            have hBk : ∀ k d,
                run N (ticks k)
                  { state := N.start, head := c.head, tape := c.tape } = some d →
                k ≤ B := by
              intro k d hk
              simpa using htB u0 c hu0 hs (List.replicate k (zeroSlot hnb)) d
                (by simpa using hk)
            have hrest := prefix_len_right M N hnb hcodes
              { state := N.start, head := c.head, tape := c.tape } B rest out hBk h
            have hAu : u0.length ≤ A := htA u0 c hu0
            have : rest.length ≤ B + 1 := hrest
            simp
            omega
          · rcases hRej with ⟨_, hs0, hmid⟩
            subst slot
            rw [hmid] at h
            cases rest with
            | nil =>
                have hAu : u0.length ≤ A := htA u0 c hu0
                simp
                exact Nat.le_trans hAu (Nat.le_add_right A (B + 1))
            | cons s rest =>
                have hst :
                    ({ state := rejectC, head := c.head, tape := c.tape } :
                      Configuration (nsA + nsB + 2) nt).state =
                      (machine M N hnb hcodes).reject := by
                  simp [machine_reject]
                have hnone := run_reject_nonempty_none (machine M N hnb hcodes)
                    { state := rejectC, head := c.head, tape := c.tape } hst
                    (s :: rest) (by simp)
                simp [hnone] at h
          · rcases hOrd with ⟨_, _, c', hM, hmid⟩
            subst mid
            have hu0' : run M (u0 ++ [slot]) (initial M raw) = some c' := by
              rw [run_append, hu0, Option.bind_some, run_cons, hM, Option.bind_some,
                run_nil]
            have := ih (u0 ++ [slot]) c' hu0' h
            simp [List.length_append] at this ⊢
            omega

theorem sequence_runsAtMost (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N) (raw : List Bool) (A B : Nat)
    (htA : RunsAtMost M raw A)
    (htB : ∀ (u : List (Fin nb)) (c : Configuration nsA nt),
      run M u (initial M raw) = some c → c.state = M.accept →
      ∀ (v : List (Fin nb)) (d : Configuration nsB nt),
        run N (ticks v.length)
          { state := N.start, head := c.head, tape := c.tape } = some d →
        v.length ≤ B) :
    RunsAtMost (machine M N hnb hcodes) raw (A + B + 2) := by
  intro slots out hrun
  have hnil : run M [] (initial M raw) = some (initial M raw) := by simp
  rw [initial_liftA] at hrun
  have := prefix_from_left M N hnb hcodes raw A B htA htB [] (initial M raw) slots
    out hnil hrun
  simpa using this

theorem sequence_spec (M : Machine nsA nt nb) (N : DeterministicMachine nsB nt)
    (hnb : 0 < nb) (hcodes : SameCodes M N) (raw : List Bool) (A B : Nat)
    (htA : RunsAtMost M raw A)
    (htB : ∀ (u : List (Fin nb)) (c : Configuration nsA nt),
      run M u (initial M raw) = some c → c.state = M.accept →
      ∀ (v : List (Fin nb)) (d : Configuration nsB nt),
        run N (ticks v.length)
          { state := N.start, head := c.head, tape := c.tape } = some d →
        v.length ≤ B) :
    (∀ (u : List (Fin nb)) (n : Nat) (c : Configuration nsA nt)
        (d : Configuration nsB nt),
      run M u (initial M raw) = some c → c.state = M.accept →
      run N (ticks n) { state := N.start, head := c.head, tape := c.tape } =
        some d → d.state = N.accept →
      Accepted (machine M N hnb hcodes) raw
        (u ++ [zeroSlot hnb] ++ List.replicate n (zeroSlot hnb) ++
          [zeroSlot hnb])) ∧
    (∀ slots, Accepted (machine M N hnb hcodes) raw slots ↔
      ∃ (u v : List (Fin nb)) (c : Configuration nsA nt) (d : Configuration nsB nt),
        slots = u ++ [zeroSlot hnb] ++ v ++ [zeroSlot hnb] ∧
        run M u (initial M raw) = some c ∧ c.state = M.accept ∧
        v = List.replicate v.length (zeroSlot hnb) ∧
        run N (ticks v.length)
          { state := N.start, head := c.head, tape := c.tape } = some d ∧
        d.state = N.accept) ∧
    RunsAtMost (machine M N hnb hcodes) raw (A + B + 2) := by
  refine ⟨?fwd, ?iff, sequence_runsAtMost M N hnb hcodes raw A B htA htB⟩
  · intro u n c d hu ha hv hd
    exact accepted_of_split M N hnb hcodes raw u n c d hu ha hv hd
  · intro slots
    exact accepted_iff_split M N hnb hcodes raw slots

end
end PakFixedPolyomino.StandardMachineNondeterministicSequence
