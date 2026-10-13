import PakFixedPolyomino.StandardBitTime
import PakFixedPolyomino.StandardBitMachineComposition

/-! Prepare / flag-strip / nondeterministic branch / flag-strip feedback.
Four tagged phases, slot-0 deterministic cores, every source M slot retained.
Accepting words are the inductive component-run grammar AcceptTrace. -/
set_option maxHeartbeats 0
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace PakFixedPolyomino.StandardMachineNondeterministicFeedback
noncomputable section
open StandardNondeterministicMachine StandardBitTime
open FiniteOneTapeSemantics (moveHead writtenTape)
open StandardBitMachineComposition (config_ext)

variable {nsP nsM nsH nt nb : Nat}

def SameCodes (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) : Prop :=
  P.blank = M.blank ∧ P.zero = M.zero ∧ P.one = M.one ∧
    P.blank = H.blank ∧ P.zero = H.zero ∧ P.one = H.one

def acceptC : Fin (nsP + nsM + 2 * nsH + 2) := ⟨0, by omega⟩
def rejectC : Fin (nsP + nsM + 2 * nsH + 2) := ⟨1, by omega⟩
def encodeP (q : Fin nsP) : Fin (nsP + nsM + 2 * nsH + 2) :=
  ⟨2 + q.val, by have := q.isLt; omega⟩
def encodeHM (q : Fin nsH) : Fin (nsP + nsM + 2 * nsH + 2) :=
  ⟨2 + nsP + q.val, by have := q.isLt; omega⟩
def encodeM (q : Fin nsM) : Fin (nsP + nsM + 2 * nsH + 2) :=
  ⟨2 + nsP + nsH + q.val, by have := q.isLt; omega⟩
def encodeHP (q : Fin nsH) : Fin (nsP + nsM + 2 * nsH + 2) :=
  ⟨2 + nsP + nsH + nsM + q.val, by have := q.isLt; omega⟩
def zeroSlot (hnb : 0 < nb) : Fin nb := ⟨0, hnb⟩

def liftP (c : Configuration nsP nt) : Configuration (nsP + nsM + 2 * nsH + 2) nt :=
  { state := encodeP c.state, head := c.head, tape := c.tape }
def liftHM (c : Configuration nsH nt) : Configuration (nsP + nsM + 2 * nsH + 2) nt :=
  { state := encodeHM c.state, head := c.head, tape := c.tape }
def liftM (c : Configuration nsM nt) : Configuration (nsP + nsM + 2 * nsH + 2) nt :=
  { state := encodeM c.state, head := c.head, tape := c.tape }
def liftHP (c : Configuration nsH nt) : Configuration (nsP + nsM + 2 * nsH + 2) nt :=
  { state := encodeHP c.state, head := c.head, tape := c.tape }

def restartP (P : DeterministicMachine nsP nt) {ns : Nat}
    (c : Configuration ns nt) : Configuration nsP nt :=
  { state := P.start, head := c.head, tape := c.tape }
def restartH (H : DeterministicMachine nsH nt) {ns : Nat}
    (c : Configuration ns nt) : Configuration nsH nt :=
  { state := H.start, head := c.head, tape := c.tape }
def restartM (M : Machine nsM nt nb) {ns : Nat}
    (c : Configuration ns nt) : Configuration nsM nt :=
  { state := M.start, head := c.head, tape := c.tape }

theorem encodeP_val (q : Fin nsP) :
    (encodeP (nsM := nsM) (nsH := nsH) q).val = 2 + q.val := rfl
theorem encodeHM_val (q : Fin nsH) :
    (encodeHM (nsP := nsP) (nsM := nsM) q).val = 2 + nsP + q.val := rfl
theorem encodeM_val (q : Fin nsM) :
    (encodeM (nsP := nsP) (nsH := nsH) q).val = 2 + nsP + nsH + q.val := rfl
theorem encodeHP_val (q : Fin nsH) :
    (encodeHP (nsP := nsP) (nsM := nsM) q).val = 2 + nsP + nsH + nsM + q.val := rfl

theorem encodeP_range (q : Fin nsP) :
    2 ≤ (encodeP (nsM := nsM) (nsH := nsH) q).val ∧
      (encodeP (nsM := nsM) (nsH := nsH) q).val - 2 < nsP := by
  have := q.isLt; simp [encodeP_val]
theorem encodeHM_range (q : Fin nsH) :
    2 + nsP ≤ (encodeHM (nsP := nsP) (nsM := nsM) q).val ∧
      (encodeHM (nsP := nsP) (nsM := nsM) q).val - (2 + nsP) < nsH := by
  have := q.isLt; simp [encodeHM_val]
theorem encodeM_range (q : Fin nsM) :
    2 + nsP + nsH ≤ (encodeM (nsP := nsP) (nsH := nsH) q).val ∧
      (encodeM (nsP := nsP) (nsH := nsH) q).val - (2 + nsP + nsH) < nsM := by
  have := q.isLt; simp [encodeM_val]
theorem encodeHP_range (q : Fin nsH) :
    2 + nsP + nsH + nsM ≤ (encodeHP (nsP := nsP) (nsM := nsM) q).val ∧
      (encodeHP (nsP := nsP) (nsM := nsM) q).val - (2 + nsP + nsH + nsM) < nsH := by
  have := q.isLt; simp [encodeHP_val]

theorem encodeP_ne_zero (q : Fin nsP) :
    (encodeP (nsM := nsM) (nsH := nsH) q).val ≠ 0 := by simp [encodeP_val]
theorem encodeP_ne_one (q : Fin nsP) :
    (encodeP (nsM := nsM) (nsH := nsH) q).val ≠ 1 := by simp [encodeP_val]; omega
theorem encodeHM_ne_zero (q : Fin nsH) :
    (encodeHM (nsP := nsP) (nsM := nsM) q).val ≠ 0 := by simp [encodeHM_val]
theorem encodeHM_ne_one (q : Fin nsH) :
    (encodeHM (nsP := nsP) (nsM := nsM) q).val ≠ 1 := by simp [encodeHM_val]; omega
theorem encodeM_ne_zero (q : Fin nsM) :
    (encodeM (nsP := nsP) (nsH := nsH) q).val ≠ 0 := by simp [encodeM_val]
theorem encodeM_ne_one (q : Fin nsM) :
    (encodeM (nsP := nsP) (nsH := nsH) q).val ≠ 1 := by simp [encodeM_val]; omega
theorem encodeHP_ne_zero (q : Fin nsH) :
    (encodeHP (nsP := nsP) (nsM := nsM) q).val ≠ 0 := by simp [encodeHP_val]
theorem encodeHP_ne_one (q : Fin nsH) :
    (encodeHP (nsP := nsP) (nsM := nsM) q).val ≠ 1 := by simp [encodeHP_val]; omega

def ruleP (P : DeterministicMachine nsP nt) (H : DeterministicMachine nsH nt)
    (hnb : 0 < nb) (qa : Fin nsP) (read : Fin nt) (slot : Fin nb) :
    Option (FiniteOneTapeProgram.Action (Fin (nsP + nsM + 2 * nsH + 2)) (Fin nt)) :=
  if qa = P.accept then
    if slot = zeroSlot hnb then
      if read = P.one then some ⟨read, encodeHM H.start, .stay⟩
      else some ⟨read, acceptC, .stay⟩
    else none
  else if qa = P.reject then
    if slot = zeroSlot hnb then some ⟨read, rejectC, .stay⟩ else none
  else if slot = zeroSlot hnb then
    (P.rule qa read 0).map fun a => ⟨a.write, encodeP a.target, a.move⟩
  else none

def ruleHM (M : Machine nsM nt nb) (H : DeterministicMachine nsH nt)
    (hnb : 0 < nb) (qh : Fin nsH) (read : Fin nt) (slot : Fin nb) :
    Option (FiniteOneTapeProgram.Action (Fin (nsP + nsM + 2 * nsH + 2)) (Fin nt)) :=
  if qh = H.accept then
    if slot = zeroSlot hnb then some ⟨read, encodeM M.start, .stay⟩ else none
  else if qh = H.reject then
    if slot = zeroSlot hnb then some ⟨read, rejectC, .stay⟩ else none
  else if slot = zeroSlot hnb then
    (H.rule qh read 0).map fun a => ⟨a.write, encodeHM a.target, a.move⟩
  else none

def ruleM (M : Machine nsM nt nb) (H : DeterministicMachine nsH nt)
    (hnb : 0 < nb) (qm : Fin nsM) (read : Fin nt) (slot : Fin nb) :
    Option (FiniteOneTapeProgram.Action (Fin (nsP + nsM + 2 * nsH + 2)) (Fin nt)) :=
  if qm = M.accept then
    if slot = zeroSlot hnb then
      if read = M.one then some ⟨read, encodeHP H.start, .stay⟩
      else some ⟨read, rejectC, .stay⟩
    else none
  else if qm = M.reject then
    if slot = zeroSlot hnb then some ⟨read, rejectC, .stay⟩ else none
  else
    (M.rule qm read slot).map fun a => ⟨a.write, encodeM a.target, a.move⟩

def ruleHP (P : DeterministicMachine nsP nt) (H : DeterministicMachine nsH nt)
    (hnb : 0 < nb) (qh : Fin nsH) (read : Fin nt) (slot : Fin nb) :
    Option (FiniteOneTapeProgram.Action (Fin (nsP + nsM + 2 * nsH + 2)) (Fin nt)) :=
  if qh = H.accept then
    if slot = zeroSlot hnb then some ⟨read, encodeP P.start, .stay⟩ else none
  else if qh = H.reject then
    if slot = zeroSlot hnb then some ⟨read, rejectC, .stay⟩ else none
  else if slot = zeroSlot hnb then
    (H.rule qh read 0).map fun a => ⟨a.write, encodeHP a.target, a.move⟩
  else none

def ndRule (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb)
    (q : Fin (nsP + nsM + 2 * nsH + 2)) (read : Fin nt) (slot : Fin nb) :
    Option (FiniteOneTapeProgram.Action (Fin (nsP + nsM + 2 * nsH + 2)) (Fin nt)) :=
  if q.val = 0 ∨ q.val = 1 then none
  else if hP : 2 ≤ q.val ∧ q.val - 2 < nsP then
    ruleP P H hnb ⟨q.val - 2, hP.2⟩ read slot
  else if hHM : 2 + nsP ≤ q.val ∧ q.val - (2 + nsP) < nsH then
    ruleHM M H hnb ⟨q.val - (2 + nsP), hHM.2⟩ read slot
  else if hM : 2 + nsP + nsH ≤ q.val ∧ q.val - (2 + nsP + nsH) < nsM then
    ruleM M H hnb ⟨q.val - (2 + nsP + nsH), hM.2⟩ read slot
  else if hHP : 2 + nsP + nsH + nsM ≤ q.val ∧ q.val - (2 + nsP + nsH + nsM) < nsH then
    ruleHP P H hnb ⟨q.val - (2 + nsP + nsH + nsM), hHP.2⟩ read slot
  else none

def machine (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (_hcodes : SameCodes P M H) :
    Machine (nsP + nsM + 2 * nsH + 2) nt nb where
  rule := ndRule P M H hnb
  start := encodeP P.start
  accept := acceptC
  reject := rejectC
  accept_ne_reject := by
    intro h; have hv := congrArg Fin.val h; simp [acceptC, rejectC] at hv
  blank := P.blank
  zero := P.zero
  one := P.one
  blank_ne_zero := P.blank_ne_zero
  blank_ne_one := P.blank_ne_one
  zero_ne_one := P.zero_ne_one
  accept_terminal := by intro x slot; simp [ndRule, acceptC]
  reject_terminal := by intro x slot; simp [ndRule, rejectC]

theorem machine_rule (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H) :
    (machine P M H hnb hcodes).rule = ndRule P M H hnb := rfl
theorem machine_accept (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H) :
    (machine P M H hnb hcodes).accept = acceptC := rfl
theorem machine_reject (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H) :
    (machine P M H hnb hcodes).reject = rejectC := rfl

theorem ndRule_P (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb)
    (qa : Fin nsP) (read : Fin nt) (slot : Fin nb) :
    ndRule P M H hnb (encodeP qa) read slot = ruleP P H hnb qa read slot := by
  have hterm : ¬ ((encodeP (nsM := nsM) (nsH := nsH) qa).val = 0 ∨
      (encodeP (nsM := nsM) (nsH := nsH) qa).val = 1) := by
    intro h; rcases h with h | h
    · exact encodeP_ne_zero (nsM := nsM) (nsH := nsH) qa h
    · exact encodeP_ne_one (nsM := nsM) (nsH := nsH) qa h
  have hA := encodeP_range (nsM := nsM) (nsH := nsH) qa
  have hq : (⟨(encodeP (nsM := nsM) (nsH := nsH) qa).val - 2, hA.2⟩ : Fin nsP) = qa := by
    apply Fin.ext; simp [encodeP_val]
  unfold ndRule
  rw [if_neg hterm, dif_pos hA]
  simp [hq]

theorem ndRule_HM (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb)
    (qh : Fin nsH) (read : Fin nt) (slot : Fin nb) :
    ndRule P M H hnb (encodeHM qh) read slot = ruleHM M H hnb qh read slot := by
  have hterm : ¬ ((encodeHM (nsP := nsP) (nsM := nsM) qh).val = 0 ∨
      (encodeHM (nsP := nsP) (nsM := nsM) qh).val = 1) := by
    intro h; rcases h with h | h
    · exact encodeHM_ne_zero (nsP := nsP) (nsM := nsM) qh h
    · exact encodeHM_ne_one (nsP := nsP) (nsM := nsM) qh h
  have hP : ¬ (2 ≤ (encodeHM (nsP := nsP) (nsM := nsM) qh).val ∧
      (encodeHM (nsP := nsP) (nsM := nsM) qh).val - 2 < nsP) := by
    intro h; have := qh.isLt; simp [encodeHM_val] at h; omega
  have hA := encodeHM_range (nsP := nsP) (nsM := nsM) qh
  have hq : (⟨(encodeHM (nsP := nsP) (nsM := nsM) qh).val - (2 + nsP), hA.2⟩ : Fin nsH) =
      qh := by
    apply Fin.ext; simp [encodeHM_val]
  unfold ndRule
  rw [if_neg hterm, dif_neg hP, dif_pos hA]
  simp [hq]

theorem ndRule_M (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb)
    (qm : Fin nsM) (read : Fin nt) (slot : Fin nb) :
    ndRule P M H hnb (encodeM qm) read slot = ruleM M H hnb qm read slot := by
  have hterm : ¬ ((encodeM (nsP := nsP) (nsH := nsH) qm).val = 0 ∨
      (encodeM (nsP := nsP) (nsH := nsH) qm).val = 1) := by
    intro h; rcases h with h | h
    · exact encodeM_ne_zero (nsP := nsP) (nsH := nsH) qm h
    · exact encodeM_ne_one (nsP := nsP) (nsH := nsH) qm h
  have hP : ¬ (2 ≤ (encodeM (nsP := nsP) (nsH := nsH) qm).val ∧
      (encodeM (nsP := nsP) (nsH := nsH) qm).val - 2 < nsP) := by
    intro h; have := qm.isLt; simp [encodeM_val] at h; omega
  have hHM : ¬ (2 + nsP ≤ (encodeM (nsP := nsP) (nsH := nsH) qm).val ∧
      (encodeM (nsP := nsP) (nsH := nsH) qm).val - (2 + nsP) < nsH) := by
    intro h; have := qm.isLt; simp [encodeM_val] at h; omega
  have hA := encodeM_range (nsP := nsP) (nsH := nsH) qm
  have hq : (⟨(encodeM (nsP := nsP) (nsH := nsH) qm).val - (2 + nsP + nsH), hA.2⟩ : Fin nsM) =
      qm := by
    apply Fin.ext; simp [encodeM_val]
  unfold ndRule
  rw [if_neg hterm, dif_neg hP, dif_neg hHM, dif_pos hA]
  simp [hq]

theorem ndRule_HP (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb)
    (qh : Fin nsH) (read : Fin nt) (slot : Fin nb) :
    ndRule P M H hnb (encodeHP qh) read slot = ruleHP P H hnb qh read slot := by
  have hterm : ¬ ((encodeHP (nsP := nsP) (nsM := nsM) qh).val = 0 ∨
      (encodeHP (nsP := nsP) (nsM := nsM) qh).val = 1) := by
    intro h; rcases h with h | h
    · exact encodeHP_ne_zero (nsP := nsP) (nsM := nsM) qh h
    · exact encodeHP_ne_one (nsP := nsP) (nsM := nsM) qh h
  have hP : ¬ (2 ≤ (encodeHP (nsP := nsP) (nsM := nsM) qh).val ∧
      (encodeHP (nsP := nsP) (nsM := nsM) qh).val - 2 < nsP) := by
    intro h; have := qh.isLt; simp [encodeHP_val] at h; omega
  have hHM : ¬ (2 + nsP ≤ (encodeHP (nsP := nsP) (nsM := nsM) qh).val ∧
      (encodeHP (nsP := nsP) (nsM := nsM) qh).val - (2 + nsP) < nsH) := by
    intro h; have := qh.isLt; simp [encodeHP_val] at h; omega
  have hM : ¬ (2 + nsP + nsH ≤ (encodeHP (nsP := nsP) (nsM := nsM) qh).val ∧
      (encodeHP (nsP := nsP) (nsM := nsM) qh).val - (2 + nsP + nsH) < nsM) := by
    intro h; have := qh.isLt; simp [encodeHP_val] at h; omega
  have hA := encodeHP_range (nsP := nsP) (nsM := nsM) qh
  have hq : (⟨(encodeHP (nsP := nsP) (nsM := nsM) qh).val - (2 + nsP + nsH + nsM), hA.2⟩ :
      Fin nsH) = qh := by
    apply Fin.ext; simp [encodeHP_val]
  unfold ndRule
  rw [if_neg hterm, dif_neg hP, dif_neg hHM, dif_neg hM, dif_pos hA]
  simp [hq]

theorem inputTape_machine (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (x : List Bool) :
    inputTape (machine P M H hnb hcodes) x = inputTape P x := by
  funext z
  simp [inputTape, machine]

theorem initial_liftP (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (raw : List Bool) :
    initial (machine P M H hnb hcodes) raw = liftP (initial P raw) := by
  apply config_ext
  · rfl
  · rfl
  · exact inputTape_machine P M H hnb hcodes raw

theorem step_det_nonterminal {ns : Nat} (S : DeterministicMachine ns nt)
    (c c' : Configuration ns nt) (h : step S 0 c = some c') :
    c.state ≠ S.accept ∧ c.state ≠ S.reject := by
  constructor
  · intro hs; simp [step, hs, S.accept_terminal] at h
  · intro hs; simp [step, hs, S.reject_terminal] at h

theorem step_M_nonterminal (M : Machine nsM nt nb)
    (c c' : Configuration nsM nt) (slot : Fin nb) (h : step M slot c = some c') :
    c.state ≠ M.accept ∧ c.state ≠ M.reject := by
  constructor
  · intro hs; simp [step, hs, M.accept_terminal] at h
  · intro hs; simp [step, hs, M.reject_terminal] at h

theorem lift_step_P (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (c c' : Configuration nsP nt) (h : step P 0 c = some c') :
    step (machine P M H hnb hcodes) (zeroSlot hnb) (liftP c) = some (liftP c') := by
  have hsrc := step_det_nonterminal P c c' h
  simp only [step, liftP, machine_rule] at h ⊢
  cases hrule : P.rule c.state (c.tape c.head) 0 with
  | none => simp [hrule] at h
  | some a =>
      simp [hrule] at h
      subst c'
      rw [ndRule_P, ruleP, if_neg hsrc.1, if_neg hsrc.2, if_pos rfl, hrule]
      simp [liftP, writtenTape]

theorem lift_run_P (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (n : Nat) (c out : Configuration nsP nt) (h : run P (ticks n) c = some out) :
    run (machine P M H hnb hcodes) (List.replicate n (zeroSlot hnb)) (liftP c) =
      some (liftP out) := by
  induction n generalizing c with
  | zero => simp [ticks] at h; subst out; simp
  | succ n ih =>
      change run P (0 :: ticks n) c = some out at h
      rw [run_cons] at h
      cases hstep : step P 0 c with
      | none => simp [hstep] at h
      | some mid =>
          simp [hstep] at h
          rw [List.replicate_succ, run_cons, lift_step_P (h := hstep), Option.bind_some]
          exact ih mid h

theorem lift_step_HM (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (c c' : Configuration nsH nt) (h : step H 0 c = some c') :
    step (machine P M H hnb hcodes) (zeroSlot hnb) (liftHM c) = some (liftHM c') := by
  have hsrc := step_det_nonterminal H c c' h
  simp only [step, liftHM, machine_rule] at h ⊢
  cases hrule : H.rule c.state (c.tape c.head) 0 with
  | none => simp [hrule] at h
  | some a =>
      simp [hrule] at h
      subst c'
      rw [ndRule_HM, ruleHM, if_neg hsrc.1, if_neg hsrc.2, if_pos rfl, hrule]
      simp [liftHM, writtenTape]

theorem lift_run_HM (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (n : Nat) (c out : Configuration nsH nt) (h : run H (ticks n) c = some out) :
    run (machine P M H hnb hcodes) (List.replicate n (zeroSlot hnb)) (liftHM c) =
      some (liftHM out) := by
  induction n generalizing c with
  | zero => simp [ticks] at h; subst out; simp
  | succ n ih =>
      change run H (0 :: ticks n) c = some out at h
      rw [run_cons] at h
      cases hstep : step H 0 c with
      | none => simp [hstep] at h
      | some mid =>
          simp [hstep] at h
          rw [List.replicate_succ, run_cons, lift_step_HM (h := hstep), Option.bind_some]
          exact ih mid h

theorem lift_step_M (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (c c' : Configuration nsM nt) (slot : Fin nb) (h : step M slot c = some c') :
    step (machine P M H hnb hcodes) slot (liftM c) = some (liftM c') := by
  have hsrc := step_M_nonterminal M c c' slot h
  simp only [step, liftM, machine_rule] at h ⊢
  cases hrule : M.rule c.state (c.tape c.head) slot with
  | none => simp [hrule] at h
  | some a =>
      simp [hrule] at h
      subst c'
      rw [ndRule_M, ruleM, if_neg hsrc.1, if_neg hsrc.2, hrule]
      simp [liftM, writtenTape]

theorem lift_run_M (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (u : List (Fin nb)) (c out : Configuration nsM nt) (h : run M u c = some out) :
    run (machine P M H hnb hcodes) u (liftM c) = some (liftM out) := by
  induction u generalizing c with
  | nil => simp at h; subst out; simp
  | cons slot u ih =>
      rw [run_cons] at h
      cases hstep : step M slot c with
      | none => simp [hstep] at h
      | some mid =>
          simp [hstep] at h
          rw [run_cons, lift_step_M (h := hstep), Option.bind_some]
          exact ih mid h

theorem lift_step_HP (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (c c' : Configuration nsH nt) (h : step H 0 c = some c') :
    step (machine P M H hnb hcodes) (zeroSlot hnb) (liftHP c) = some (liftHP c') := by
  have hsrc := step_det_nonterminal H c c' h
  simp only [step, liftHP, machine_rule] at h ⊢
  cases hrule : H.rule c.state (c.tape c.head) 0 with
  | none => simp [hrule] at h
  | some a =>
      simp [hrule] at h
      subst c'
      rw [ndRule_HP, ruleHP, if_neg hsrc.1, if_neg hsrc.2, if_pos rfl, hrule]
      simp [liftHP, writtenTape]

theorem lift_run_HP (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (n : Nat) (c out : Configuration nsH nt) (h : run H (ticks n) c = some out) :
    run (machine P M H hnb hcodes) (List.replicate n (zeroSlot hnb)) (liftHP c) =
      some (liftHP out) := by
  induction n generalizing c with
  | zero => simp [ticks] at h; subst out; simp
  | succ n ih =>
      change run H (0 :: ticks n) c = some out at h
      rw [run_cons] at h
      cases hstep : step H 0 c with
      | none => simp [hstep] at h
      | some mid =>
          simp [hstep] at h
          rw [List.replicate_succ, run_cons, lift_step_HP (h := hstep), Option.bind_some]
          exact ih mid h

theorem handoff_P_stop (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (c : Configuration nsP nt) (hs : c.state = P.accept) (hstop : c.tape c.head ≠ P.one) :
    step (machine P M H hnb hcodes) (zeroSlot hnb) (liftP c) =
      some { state := acceptC, head := c.head, tape := c.tape } := by
  simp only [step, liftP, machine_rule]
  rw [ndRule_P, ruleP, if_pos hs, if_pos rfl, if_neg hstop]
  simp [moveHead, writtenTape, Function.update_eq_self]

theorem handoff_P_continue (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (c : Configuration nsP nt) (hs : c.state = P.accept) (hone : c.tape c.head = P.one) :
    step (machine P M H hnb hcodes) (zeroSlot hnb) (liftP c) =
      some (liftHM (restartH H c)) := by
  simp only [step, liftP, machine_rule]
  rw [ndRule_P, ruleP, if_pos hs, if_pos rfl, if_pos hone]
  simp [moveHead, writtenTape, Function.update_eq_self, liftHM, restartH]

theorem handoff_P_reject (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (c : Configuration nsP nt) (hs : c.state = P.reject) :
    step (machine P M H hnb hcodes) (zeroSlot hnb) (liftP c) =
      some { state := rejectC, head := c.head, tape := c.tape } := by
  have hne : c.state ≠ P.accept := fun h => P.accept_ne_reject (h.symm.trans hs)
  simp only [step, liftP, machine_rule]
  rw [ndRule_P, ruleP, if_neg hne, if_pos hs, if_pos rfl]
  simp [moveHead, writtenTape, Function.update_eq_self]

theorem handoff_HM_accept (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (c : Configuration nsH nt) (hs : c.state = H.accept) :
    step (machine P M H hnb hcodes) (zeroSlot hnb) (liftHM c) =
      some (liftM (restartM M c)) := by
  simp only [step, liftHM, machine_rule]
  rw [ndRule_HM, ruleHM, if_pos hs, if_pos rfl]
  simp [moveHead, writtenTape, Function.update_eq_self, liftM, restartM]

theorem handoff_HM_reject (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (c : Configuration nsH nt) (hs : c.state = H.reject) :
    step (machine P M H hnb hcodes) (zeroSlot hnb) (liftHM c) =
      some { state := rejectC, head := c.head, tape := c.tape } := by
  have hne : c.state ≠ H.accept := fun h => H.accept_ne_reject (h.symm.trans hs)
  simp only [step, liftHM, machine_rule]
  rw [ndRule_HM, ruleHM, if_neg hne, if_pos hs, if_pos rfl]
  simp [moveHead, writtenTape, Function.update_eq_self]

theorem handoff_M_continue (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (c : Configuration nsM nt) (hs : c.state = M.accept) (hone : c.tape c.head = M.one) :
    step (machine P M H hnb hcodes) (zeroSlot hnb) (liftM c) =
      some (liftHP (restartH H c)) := by
  simp only [step, liftM, machine_rule]
  rw [ndRule_M, ruleM, if_pos hs, if_pos rfl, if_pos hone]
  simp [moveHead, writtenTape, Function.update_eq_self, liftHP, restartH]

theorem handoff_M_bad (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (c : Configuration nsM nt) (hs : c.state = M.accept) (hbad : c.tape c.head ≠ M.one) :
    step (machine P M H hnb hcodes) (zeroSlot hnb) (liftM c) =
      some { state := rejectC, head := c.head, tape := c.tape } := by
  simp only [step, liftM, machine_rule]
  rw [ndRule_M, ruleM, if_pos hs, if_pos rfl, if_neg hbad]
  simp [moveHead, writtenTape, Function.update_eq_self]

theorem handoff_M_reject (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (c : Configuration nsM nt) (hs : c.state = M.reject) :
    step (machine P M H hnb hcodes) (zeroSlot hnb) (liftM c) =
      some { state := rejectC, head := c.head, tape := c.tape } := by
  have hne : c.state ≠ M.accept := fun h => M.accept_ne_reject (h.symm.trans hs)
  simp only [step, liftM, machine_rule]
  rw [ndRule_M, ruleM, if_neg hne, if_pos hs, if_pos rfl]
  simp [moveHead, writtenTape, Function.update_eq_self]

theorem handoff_HP_accept (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (c : Configuration nsH nt) (hs : c.state = H.accept) :
    step (machine P M H hnb hcodes) (zeroSlot hnb) (liftHP c) =
      some (liftP (restartP P c)) := by
  simp only [step, liftHP, machine_rule]
  rw [ndRule_HP, ruleHP, if_pos hs, if_pos rfl]
  simp [moveHead, writtenTape, Function.update_eq_self, liftP, restartP]

theorem handoff_HP_reject (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (c : Configuration nsH nt) (hs : c.state = H.reject) :
    step (machine P M H hnb hcodes) (zeroSlot hnb) (liftHP c) =
      some { state := rejectC, head := c.head, tape := c.tape } := by
  have hne : c.state ≠ H.accept := fun h => H.accept_ne_reject (h.symm.trans hs)
  simp only [step, liftHP, machine_rule]
  rw [ndRule_HP, ruleHP, if_neg hne, if_pos hs, if_pos rfl]
  simp [moveHead, writtenTape, Function.update_eq_self]

theorem run_reject_nonempty_none {ns br : Nat} (S : Machine ns nt br)
    (c : Configuration ns nt) (hstate : c.state = S.reject)
    (slots : List (Fin br)) (hne : slots ≠ []) : run S slots c = none := by
  cases slots with
  | nil => contradiction
  | cons slot rest => simp [run_cons, step_reject_none S slot c hstate]

inductive AcceptTrace (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) :
    Configuration nsP nt → List (Fin nb) → Prop where
  | stop (cP p : Configuration nsP nt) (a : Nat)
      (hp : run P (ticks a) cP = some p) (hpa : p.state = P.accept)
      (hstop : p.tape p.head ≠ P.one) :
      AcceptTrace P M H hnb cP (List.replicate a (zeroSlot hnb) ++ [zeroSlot hnb])
  | next (cP p : Configuration nsP nt) (h1 : Configuration nsH nt)
      (m : Configuration nsM nt) (h2 : Configuration nsH nt)
      (u rest : List (Fin nb)) (a b d : Nat)
      (hp : run P (ticks a) cP = some p) (hpa : p.state = P.accept)
      (hone : p.tape p.head = P.one)
      (hh : run H (ticks b) (restartH H p) = some h1) (hha : h1.state = H.accept)
      (hm : run M u (restartM M h1) = some m) (hma : m.state = M.accept)
      (hmone : m.tape m.head = M.one)
      (hh2 : run H (ticks d) (restartH H m) = some h2) (hh2a : h2.state = H.accept)
      (ih : AcceptTrace P M H hnb (restartP P h2) rest) :
      AcceptTrace P M H hnb cP
        (List.replicate a (zeroSlot hnb) ++ [zeroSlot hnb] ++
          List.replicate b (zeroSlot hnb) ++ [zeroSlot hnb] ++
          u ++ [zeroSlot hnb] ++
          List.replicate d (zeroSlot hnb) ++ [zeroSlot hnb] ++ rest)

theorem sequence_stop (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (cP p : Configuration nsP nt) (a : Nat)
    (hp : run P (ticks a) cP = some p) (hpa : p.state = P.accept)
    (hstop : p.tape p.head ≠ P.one) :
    run (machine P M H hnb hcodes) (List.replicate a (zeroSlot hnb) ++ [zeroSlot hnb])
      (liftP cP) = some { state := acceptC, head := p.head, tape := p.tape } := by
  have hA : run (machine P M H hnb hcodes) (List.replicate a (zeroSlot hnb)) (liftP cP) =
      some (liftP p) := lift_run_P P M H hnb hcodes a cP p hp
  rw [run_append, hA, Option.bind_some, run_cons, handoff_P_stop (hs := hpa) (hstop := hstop),
    Option.bind_some, run_nil]

theorem cycle_run (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (cP p : Configuration nsP nt) (h1 : Configuration nsH nt)
    (m : Configuration nsM nt) (h2 : Configuration nsH nt)
    (u : List (Fin nb)) (a b d : Nat)
    (hp : run P (ticks a) cP = some p) (hpa : p.state = P.accept)
    (hone : p.tape p.head = P.one)
    (hh : run H (ticks b) (restartH H p) = some h1) (hha : h1.state = H.accept)
    (hm : run M u (restartM M h1) = some m) (hma : m.state = M.accept)
    (hmone : m.tape m.head = M.one)
    (hh2 : run H (ticks d) (restartH H m) = some h2) (hh2a : h2.state = H.accept) :
    run (machine P M H hnb hcodes)
      (List.replicate a (zeroSlot hnb) ++ [zeroSlot hnb] ++
        List.replicate b (zeroSlot hnb) ++ [zeroSlot hnb] ++
        u ++ [zeroSlot hnb] ++
        List.replicate d (zeroSlot hnb) ++ [zeroSlot hnb])
      (liftP cP) = some (liftP (restartP P h2)) := by
  have hA := lift_run_P P M H hnb hcodes a cP p hp
  have hP : run (machine P M H hnb hcodes)
      (List.replicate a (zeroSlot hnb) ++ [zeroSlot hnb]) (liftP cP) =
      some (liftHM (restartH H p)) := by
    rw [run_append, hA, Option.bind_some, run_cons,
      handoff_P_continue (hs := hpa) (hone := hone), Option.bind_some, run_nil]
  have hB := lift_run_HM P M H hnb hcodes b (restartH H p) h1 hh
  have hHM : run (machine P M H hnb hcodes)
      ((List.replicate a (zeroSlot hnb) ++ [zeroSlot hnb]) ++
        (List.replicate b (zeroSlot hnb) ++ [zeroSlot hnb])) (liftP cP) =
      some (liftM (restartM M h1)) := by
    rw [run_append, hP, Option.bind_some, run_append, hB, Option.bind_some, run_cons,
      handoff_HM_accept (hs := hha), Option.bind_some, run_nil]
  have hU := lift_run_M P M H hnb hcodes u (restartM M h1) m hm
  have hMc : run (machine P M H hnb hcodes)
      (((List.replicate a (zeroSlot hnb) ++ [zeroSlot hnb]) ++
        (List.replicate b (zeroSlot hnb) ++ [zeroSlot hnb])) ++
        (u ++ [zeroSlot hnb])) (liftP cP) =
      some (liftHP (restartH H m)) := by
    rw [run_append, hHM, Option.bind_some, run_append, hU, Option.bind_some, run_cons,
      handoff_M_continue (hs := hma) (hone := hmone), Option.bind_some, run_nil]
  have hD := lift_run_HP P M H hnb hcodes d (restartH H m) h2 hh2
  have hs :
      List.replicate a (zeroSlot hnb) ++ [zeroSlot hnb] ++
        List.replicate b (zeroSlot hnb) ++ [zeroSlot hnb] ++
        u ++ [zeroSlot hnb] ++
        List.replicate d (zeroSlot hnb) ++ [zeroSlot hnb] =
      (((List.replicate a (zeroSlot hnb) ++ [zeroSlot hnb]) ++
        (List.replicate b (zeroSlot hnb) ++ [zeroSlot hnb])) ++
        (u ++ [zeroSlot hnb])) ++
        (List.replicate d (zeroSlot hnb) ++ [zeroSlot hnb]) := by
    simp [List.append_assoc]
  rw [hs, run_append, hMc, Option.bind_some, run_append, hD, Option.bind_some, run_cons,
    handoff_HP_accept (hs := hh2a), Option.bind_some, run_nil]

theorem accepted_of_trace (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (cP : Configuration nsP nt) (slots : List (Fin nb))
    (h : AcceptTrace P M H hnb cP slots) :
    ∃ out, run (machine P M H hnb hcodes) slots (liftP cP) = some out ∧
      out.state = acceptC := by
  induction h with
  | stop cP p a hp hpa hstop =>
      refine ⟨_, sequence_stop P M H hnb hcodes cP p a hp hpa hstop, rfl⟩
  | next cP p h1 m h2 u rest a b d hp hpa hone hh hha hm hma hmone hh2 hh2a ih ih_ih =>
      obtain ⟨out, hrest, hacc⟩ := ih_ih
      have hcyc := cycle_run P M H hnb hcodes cP p h1 m h2 u a b d hp hpa hone hh hha
        hm hma hmone hh2 hh2a
      refine ⟨out, ?_, hacc⟩
      rw [run_append, hcyc, Option.bind_some, hrest]

theorem acceptTrace_cons_P (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb)
    (c c' : Configuration nsP nt) (rest : List (Fin nb))
    (hst : step P 0 c = some c') (h : AcceptTrace P M H hnb c' rest) :
    AcceptTrace P M H hnb c (zeroSlot hnb :: rest) := by
  cases h with
  | stop _ p a hp hpa hstop =>
      have hp' : run P (ticks (a + 1)) c = some p := by
        change run P (0 :: ticks a) c = some p
        rw [run_cons, hst, Option.bind_some, hp]
      have hs : zeroSlot hnb :: (List.replicate a (zeroSlot hnb) ++ [zeroSlot hnb]) =
          List.replicate (a + 1) (zeroSlot hnb) ++ [zeroSlot hnb] := by
        simp [List.replicate_succ]
      exact hs ▸ AcceptTrace.stop c p (a + 1) hp' hpa hstop
  | next _ p h1 m h2 u rest a b d hp hpa hone hh hha hm hma hmone hh2 hh2a ih =>
      have hp' : run P (ticks (a + 1)) c = some p := by
        change run P (0 :: ticks a) c = some p
        rw [run_cons, hst, Option.bind_some, hp]
      have hs : zeroSlot hnb ::
          (List.replicate a (zeroSlot hnb) ++ [zeroSlot hnb] ++
            List.replicate b (zeroSlot hnb) ++ [zeroSlot hnb] ++
            u ++ [zeroSlot hnb] ++
            List.replicate d (zeroSlot hnb) ++ [zeroSlot hnb] ++ rest) =
          List.replicate (a + 1) (zeroSlot hnb) ++ [zeroSlot hnb] ++
            List.replicate b (zeroSlot hnb) ++ [zeroSlot hnb] ++
            u ++ [zeroSlot hnb] ++
            List.replicate d (zeroSlot hnb) ++ [zeroSlot hnb] ++ rest := by
        simp [List.replicate_succ, List.cons_append]
      exact hs ▸ AcceptTrace.next c p h1 m h2 u rest (a + 1) b d hp' hpa hone hh hha
        hm hma hmone hh2 hh2a ih

theorem step_P_inv (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (c : Configuration nsP nt) (slot : Fin nb)
    (mid : Configuration (nsP + nsM + 2 * nsH + 2) nt)
    (h : step (machine P M H hnb hcodes) slot (liftP c) = some mid) :
    (c.state = P.accept ∧ slot = zeroSlot hnb ∧ c.tape c.head = P.one ∧
      mid = liftHM (restartH H c)) ∨
    (c.state = P.accept ∧ slot = zeroSlot hnb ∧ c.tape c.head ≠ P.one ∧
      mid = { state := acceptC, head := c.head, tape := c.tape }) ∨
    (c.state = P.reject ∧ slot = zeroSlot hnb ∧
      mid = { state := rejectC, head := c.head, tape := c.tape }) ∨
    (c.state ≠ P.accept ∧ c.state ≠ P.reject ∧ slot = zeroSlot hnb ∧
      ∃ c', step P 0 c = some c' ∧ mid = liftP c') := by
  simp only [step, liftP, machine_rule] at h
  rw [ndRule_P] at h
  by_cases hacc : c.state = P.accept
  · rw [ruleP, if_pos hacc] at h
    by_cases hs0 : slot = zeroSlot hnb
    · rw [if_pos hs0] at h
      by_cases hone : c.tape c.head = P.one
      · rw [if_pos hone] at h
        simp [moveHead, writtenTape, Function.update_eq_self] at h
        subst mid
        exact Or.inl ⟨hacc, hs0, hone, by simp [liftHM, restartH]⟩
      · rw [if_neg hone] at h
        simp [moveHead, writtenTape, Function.update_eq_self] at h
        subst mid
        exact Or.inr (Or.inl ⟨hacc, hs0, hone, rfl⟩)
    · rw [if_neg hs0] at h; simp at h
  · by_cases hrej : c.state = P.reject
    · rw [ruleP, if_neg hacc, if_pos hrej] at h
      by_cases hs0 : slot = zeroSlot hnb
      · rw [if_pos hs0] at h
        simp [moveHead, writtenTape, Function.update_eq_self] at h
        subst mid
        exact Or.inr (Or.inr (Or.inl ⟨hrej, hs0, rfl⟩))
      · rw [if_neg hs0] at h; simp at h
    · rw [ruleP, if_neg hacc, if_neg hrej] at h
      by_cases hs0 : slot = zeroSlot hnb
      · rw [if_pos hs0] at h
        cases hrule : P.rule c.state (c.tape c.head) 0 with
        | none => simp [hrule] at h
        | some a =>
            simp [hrule] at h
            subst mid
            refine Or.inr (Or.inr (Or.inr ⟨hacc, hrej, hs0, ?_⟩))
            let c' : Configuration nsP nt :=
              { state := a.target, head := moveHead a.move c.head,
                tape := writtenTape c a.write }
            refine ⟨c', ?_⟩
            constructor
            · simp [step, hrule, c']
            · simp [liftP, c', writtenTape]
      · rw [if_neg hs0] at h; simp at h

theorem step_HM_inv (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (c : Configuration nsH nt) (slot : Fin nb)
    (mid : Configuration (nsP + nsM + 2 * nsH + 2) nt)
    (h : step (machine P M H hnb hcodes) slot (liftHM c) = some mid) :
    (c.state = H.accept ∧ slot = zeroSlot hnb ∧ mid = liftM (restartM M c)) ∨
    (c.state = H.reject ∧ slot = zeroSlot hnb ∧
      mid = { state := rejectC, head := c.head, tape := c.tape }) ∨
    (c.state ≠ H.accept ∧ c.state ≠ H.reject ∧ slot = zeroSlot hnb ∧
      ∃ c', step H 0 c = some c' ∧ mid = liftHM c') := by
  simp only [step, liftHM, machine_rule] at h
  rw [ndRule_HM] at h
  by_cases hacc : c.state = H.accept
  · rw [ruleHM, if_pos hacc] at h
    by_cases hs0 : slot = zeroSlot hnb
    · rw [if_pos hs0] at h
      simp [moveHead, writtenTape, Function.update_eq_self] at h
      subst mid
      exact Or.inl ⟨hacc, hs0, by simp [liftM, restartM]⟩
    · rw [if_neg hs0] at h; simp at h
  · by_cases hrej : c.state = H.reject
    · rw [ruleHM, if_neg hacc, if_pos hrej] at h
      by_cases hs0 : slot = zeroSlot hnb
      · rw [if_pos hs0] at h
        simp [moveHead, writtenTape, Function.update_eq_self] at h
        subst mid
        exact Or.inr (Or.inl ⟨hrej, hs0, rfl⟩)
      · rw [if_neg hs0] at h; simp at h
    · rw [ruleHM, if_neg hacc, if_neg hrej] at h
      by_cases hs0 : slot = zeroSlot hnb
      · rw [if_pos hs0] at h
        cases hrule : H.rule c.state (c.tape c.head) 0 with
        | none => simp [hrule] at h
        | some a =>
            simp [hrule] at h
            subst mid
            refine Or.inr (Or.inr ⟨hacc, hrej, hs0, ?_⟩)
            let c' : Configuration nsH nt :=
              { state := a.target, head := moveHead a.move c.head,
                tape := writtenTape c a.write }
            refine ⟨c', ?_⟩
            constructor
            · simp [step, hrule, c']
            · simp [liftHM, c', writtenTape]
      · rw [if_neg hs0] at h; simp at h

theorem step_M_inv (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (c : Configuration nsM nt) (slot : Fin nb)
    (mid : Configuration (nsP + nsM + 2 * nsH + 2) nt)
    (h : step (machine P M H hnb hcodes) slot (liftM c) = some mid) :
    (c.state = M.accept ∧ slot = zeroSlot hnb ∧ c.tape c.head = M.one ∧
      mid = liftHP (restartH H c)) ∨
    (c.state = M.accept ∧ slot = zeroSlot hnb ∧ c.tape c.head ≠ M.one ∧
      mid = { state := rejectC, head := c.head, tape := c.tape }) ∨
    (c.state = M.reject ∧ slot = zeroSlot hnb ∧
      mid = { state := rejectC, head := c.head, tape := c.tape }) ∨
    (c.state ≠ M.accept ∧ c.state ≠ M.reject ∧
      ∃ c', step M slot c = some c' ∧ mid = liftM c') := by
  simp only [step, liftM, machine_rule] at h
  rw [ndRule_M] at h
  by_cases hacc : c.state = M.accept
  · rw [ruleM, if_pos hacc] at h
    by_cases hs0 : slot = zeroSlot hnb
    · rw [if_pos hs0] at h
      by_cases hone : c.tape c.head = M.one
      · rw [if_pos hone] at h
        simp [moveHead, writtenTape, Function.update_eq_self] at h
        subst mid
        exact Or.inl ⟨hacc, hs0, hone, by simp [liftHP, restartH]⟩
      · rw [if_neg hone] at h
        simp [moveHead, writtenTape, Function.update_eq_self] at h
        subst mid
        exact Or.inr (Or.inl ⟨hacc, hs0, hone, rfl⟩)
    · rw [if_neg hs0] at h; simp at h
  · by_cases hrej : c.state = M.reject
    · rw [ruleM, if_neg hacc, if_pos hrej] at h
      by_cases hs0 : slot = zeroSlot hnb
      · rw [if_pos hs0] at h
        simp [moveHead, writtenTape, Function.update_eq_self] at h
        subst mid
        exact Or.inr (Or.inr (Or.inl ⟨hrej, hs0, rfl⟩))
      · rw [if_neg hs0] at h; simp at h
    · rw [ruleM, if_neg hacc, if_neg hrej] at h
      cases hrule : M.rule c.state (c.tape c.head) slot with
      | none => simp [hrule] at h
      | some a =>
          simp [hrule] at h
          subst mid
          refine Or.inr (Or.inr (Or.inr ⟨hacc, hrej, ?_⟩))
          let c' : Configuration nsM nt :=
            { state := a.target, head := moveHead a.move c.head,
              tape := writtenTape c a.write }
          refine ⟨c', ?_⟩
          constructor
          · simp [step, hrule, c']
          · simp [liftM, c', writtenTape]

theorem step_HP_inv (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (c : Configuration nsH nt) (slot : Fin nb)
    (mid : Configuration (nsP + nsM + 2 * nsH + 2) nt)
    (h : step (machine P M H hnb hcodes) slot (liftHP c) = some mid) :
    (c.state = H.accept ∧ slot = zeroSlot hnb ∧ mid = liftP (restartP P c)) ∨
    (c.state = H.reject ∧ slot = zeroSlot hnb ∧
      mid = { state := rejectC, head := c.head, tape := c.tape }) ∨
    (c.state ≠ H.accept ∧ c.state ≠ H.reject ∧ slot = zeroSlot hnb ∧
      ∃ c', step H 0 c = some c' ∧ mid = liftHP c') := by
  simp only [step, liftHP, machine_rule] at h
  rw [ndRule_HP] at h
  by_cases hacc : c.state = H.accept
  · rw [ruleHP, if_pos hacc] at h
    by_cases hs0 : slot = zeroSlot hnb
    · rw [if_pos hs0] at h
      simp [moveHead, writtenTape, Function.update_eq_self] at h
      subst mid
      exact Or.inl ⟨hacc, hs0, by simp [liftP, restartP]⟩
    · rw [if_neg hs0] at h; simp at h
  · by_cases hrej : c.state = H.reject
    · rw [ruleHP, if_neg hacc, if_pos hrej] at h
      by_cases hs0 : slot = zeroSlot hnb
      · rw [if_pos hs0] at h
        simp [moveHead, writtenTape, Function.update_eq_self] at h
        subst mid
        exact Or.inr (Or.inl ⟨hrej, hs0, rfl⟩)
      · rw [if_neg hs0] at h; simp at h
    · rw [ruleHP, if_neg hacc, if_neg hrej] at h
      by_cases hs0 : slot = zeroSlot hnb
      · rw [if_pos hs0] at h
        cases hrule : H.rule c.state (c.tape c.head) 0 with
        | none => simp [hrule] at h
        | some a =>
            simp [hrule] at h
            subst mid
            refine Or.inr (Or.inr ⟨hacc, hrej, hs0, ?_⟩)
            let c' : Configuration nsH nt :=
              { state := a.target, head := moveHead a.move c.head,
                tape := writtenTape c a.write }
            refine ⟨c', ?_⟩
            constructor
            · simp [step, hrule, c']
            · simp [liftHP, c', writtenTape]
      · rw [if_neg hs0] at h; simp at h

def HMTrace (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb)
    (cH : Configuration nsH nt) (slots : List (Fin nb)) : Prop :=
  ∃ (b d : Nat) (h1 : Configuration nsH nt) (m : Configuration nsM nt)
    (h2 : Configuration nsH nt) (u rest : List (Fin nb)),
    slots = List.replicate b (zeroSlot hnb) ++ [zeroSlot hnb] ++
      u ++ [zeroSlot hnb] ++ List.replicate d (zeroSlot hnb) ++ [zeroSlot hnb] ++ rest ∧
    run H (ticks b) cH = some h1 ∧ h1.state = H.accept ∧
    run M u (restartM M h1) = some m ∧ m.state = M.accept ∧ m.tape m.head = M.one ∧
    run H (ticks d) (restartH H m) = some h2 ∧ h2.state = H.accept ∧
    AcceptTrace P M H hnb (restartP P h2) rest

def MTrace (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb)
    (cM : Configuration nsM nt) (slots : List (Fin nb)) : Prop :=
  ∃ (d : Nat) (m : Configuration nsM nt) (h2 : Configuration nsH nt)
    (u rest : List (Fin nb)),
    slots = u ++ [zeroSlot hnb] ++ List.replicate d (zeroSlot hnb) ++ [zeroSlot hnb] ++
      rest ∧
    run M u cM = some m ∧ m.state = M.accept ∧ m.tape m.head = M.one ∧
    run H (ticks d) (restartH H m) = some h2 ∧ h2.state = H.accept ∧
    AcceptTrace P M H hnb (restartP P h2) rest

def HPTrace (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb)
    (cH : Configuration nsH nt) (slots : List (Fin nb)) : Prop :=
  ∃ (d : Nat) (h2 : Configuration nsH nt) (rest : List (Fin nb)),
    slots = List.replicate d (zeroSlot hnb) ++ [zeroSlot hnb] ++ rest ∧
    run H (ticks d) cH = some h2 ∧ h2.state = H.accept ∧
    AcceptTrace P M H hnb (restartP P h2) rest

theorem invert (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (slots : List (Fin nb)) :
    (∀ (c : Configuration nsP nt) (out : Configuration (nsP + nsM + 2 * nsH + 2) nt),
      run (machine P M H hnb hcodes) slots (liftP c) = some out →
        out.state = acceptC → AcceptTrace P M H hnb c slots) ∧
    (∀ (c : Configuration nsH nt) (out : Configuration (nsP + nsM + 2 * nsH + 2) nt),
      run (machine P M H hnb hcodes) slots (liftHM c) = some out →
        out.state = acceptC → HMTrace P M H hnb c slots) ∧
    (∀ (c : Configuration nsM nt) (out : Configuration (nsP + nsM + 2 * nsH + 2) nt),
      run (machine P M H hnb hcodes) slots (liftM c) = some out →
        out.state = acceptC → MTrace P M H hnb c slots) ∧
    (∀ (c : Configuration nsH nt) (out : Configuration (nsP + nsM + 2 * nsH + 2) nt),
      run (machine P M H hnb hcodes) slots (liftHP c) = some out →
        out.state = acceptC → HPTrace P M H hnb c slots) := by
  induction slots with
  | nil =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro c out h hacc
        simp at h; subst out
        have hval : (encodeP (nsM := nsM) (nsH := nsH) c.state).val = 0 := by
          simpa [liftP, acceptC] using congrArg Fin.val hacc
        exact (encodeP_ne_zero (nsM := nsM) (nsH := nsH) c.state hval).elim
      · intro c out h hacc
        simp at h; subst out
        have hval : (encodeHM (nsP := nsP) (nsM := nsM) c.state).val = 0 := by
          simpa [liftHM, acceptC] using congrArg Fin.val hacc
        exact (encodeHM_ne_zero (nsP := nsP) (nsM := nsM) c.state hval).elim
      · intro c out h hacc
        simp at h; subst out
        have hval : (encodeM (nsP := nsP) (nsH := nsH) c.state).val = 0 := by
          simpa [liftM, acceptC] using congrArg Fin.val hacc
        exact (encodeM_ne_zero (nsP := nsP) (nsH := nsH) c.state hval).elim
      · intro c out h hacc
        simp at h; subst out
        have hval : (encodeHP (nsP := nsP) (nsM := nsM) c.state).val = 0 := by
          simpa [liftHP, acceptC] using congrArg Fin.val hacc
        exact (encodeHP_ne_zero (nsP := nsP) (nsM := nsM) c.state hval).elim
  | cons slot rest ih =>
      rcases ih with ⟨ihP, ihHM, ihM, ihHP⟩
      refine ⟨?fromP, ?fromHM, ?fromM, ?fromHP⟩
      · intro c out h hacc
        rw [run_cons] at h
        cases hstep : step (machine P M H hnb hcodes) slot (liftP c) with
        | none => simp [hstep] at h
        | some mid =>
            simp [hstep] at h
            have hinv := step_P_inv P M H hnb hcodes c slot mid hstep
            rcases hinv with hC | hS | hR | hO
            · rcases hC with ⟨hs, hs0, hone, hmid⟩
              subst slot; rw [hmid] at h
              obtain ⟨b, d, h1, m, h2, u, rest', hs', hh, hha, hm, hma, hmone, hh2, hh2a, ihT⟩ :=
                ihHM (restartH H c) out h hacc
              have hp : run P (ticks 0) c = some c := by simp [ticks]
              rw [hs']
              exact AcceptTrace.next c c h1 m h2 u rest' 0 b d hp hs hone hh hha hm hma
                hmone hh2 hh2a ihT
            · rcases hS with ⟨hs, hs0, hstop, hmid⟩
              subst slot; rw [hmid] at h
              cases rest with
              | nil =>
                  simp at h; subst out
                  have hp : run P (ticks 0) c = some c := by simp [ticks]
                  exact AcceptTrace.stop c c 0 hp hs hstop
              | cons s rest =>
                  have hst :
                      ({ state := acceptC, head := c.head, tape := c.tape } :
                        Configuration (nsP + nsM + 2 * nsH + 2) nt).state =
                        (machine P M H hnb hcodes).accept := by
                    simp [machine_accept]
                  have hnone := run_accept_nonempty_none (machine P M H hnb hcodes)
                      { state := acceptC, head := c.head, tape := c.tape } hst
                      (s :: rest) (by simp)
                  simp [hnone] at h
            · rcases hR with ⟨_, hs0, hmid⟩
              subst slot; rw [hmid] at h
              cases rest with
              | nil =>
                  simp at h; subst out; simp [acceptC, rejectC] at hacc
              | cons s rest =>
                  have hst :
                      ({ state := rejectC, head := c.head, tape := c.tape } :
                        Configuration (nsP + nsM + 2 * nsH + 2) nt).state =
                        (machine P M H hnb hcodes).reject := by
                    simp [machine_reject]
                  have hnone := run_reject_nonempty_none (machine P M H hnb hcodes)
                      { state := rejectC, head := c.head, tape := c.tape } hst
                      (s :: rest) (by simp)
                  simp [hnone] at h
            · rcases hO with ⟨_, _, hs0, c', hPstep, hmid⟩
              subst slot; subst mid
              exact acceptTrace_cons_P P M H hnb c c' rest hPstep (ihP c' out h hacc)
      · intro c out h hacc
        rw [run_cons] at h
        cases hstep : step (machine P M H hnb hcodes) slot (liftHM c) with
        | none => simp [hstep] at h
        | some mid =>
            simp [hstep] at h
            have hinv := step_HM_inv P M H hnb hcodes c slot mid hstep
            rcases hinv with hA | hR | hO
            · rcases hA with ⟨hs, hs0, hmid⟩
              subst slot; rw [hmid] at h
              obtain ⟨d, m, h2, u, rest', hs', hm, hma, hmone, hh2, hh2a, ihT⟩ :=
                ihM (restartM M c) out h hacc
              refine ⟨0, d, c, m, h2, u, rest', ?_, ?_, hs, hm, hma, hmone, hh2, hh2a, ihT⟩
              · simp [hs']
              · simp [ticks]
            · rcases hR with ⟨_, hs0, hmid⟩
              subst slot; rw [hmid] at h
              cases rest with
              | nil => simp at h; subst out; simp [acceptC, rejectC] at hacc
              | cons s rest =>
                  have hst :
                      ({ state := rejectC, head := c.head, tape := c.tape } :
                        Configuration (nsP + nsM + 2 * nsH + 2) nt).state =
                        (machine P M H hnb hcodes).reject := by
                    simp [machine_reject]
                  have hnone := run_reject_nonempty_none (machine P M H hnb hcodes)
                      { state := rejectC, head := c.head, tape := c.tape } hst
                      (s :: rest) (by simp)
                  simp [hnone] at h
            · rcases hO with ⟨_, _, hs0, c', hH, hmid⟩
              subst slot; subst mid
              obtain ⟨b, d, h1, m, h2, u, rest', hs', hh, hha, hm, hma, hmone, hh2, hh2a, ihT⟩ :=
                ihHM c' out h hacc
              refine ⟨b + 1, d, h1, m, h2, u, rest', ?_, ?_, hha, hm, hma, hmone, hh2, hh2a, ihT⟩
              · simp [hs', List.replicate_succ, List.cons_append]
              · change run H (0 :: ticks b) c = some h1
                rw [run_cons, hH, Option.bind_some, hh]
      · intro c out h hacc
        rw [run_cons] at h
        cases hstep : step (machine P M H hnb hcodes) slot (liftM c) with
        | none => simp [hstep] at h
        | some mid =>
            simp [hstep] at h
            have hinv := step_M_inv P M H hnb hcodes c slot mid hstep
            rcases hinv with hC | hBad | hR | hO
            · rcases hC with ⟨hs, hs0, hone, hmid⟩
              subst slot; rw [hmid] at h
              obtain ⟨d, h2, rest', hs', hh2, hh2a, ihT⟩ := ihHP (restartH H c) out h hacc
              refine ⟨d, c, h2, [], rest', ?_, ?_, hs, hone, hh2, hh2a, ihT⟩
              · simp [hs']
              · simp
            · rcases hBad with ⟨_, hs0, _, hmid⟩
              subst slot; rw [hmid] at h
              cases rest with
              | nil => simp at h; subst out; simp [acceptC, rejectC] at hacc
              | cons s rest =>
                  have hst :
                      ({ state := rejectC, head := c.head, tape := c.tape } :
                        Configuration (nsP + nsM + 2 * nsH + 2) nt).state =
                        (machine P M H hnb hcodes).reject := by
                    simp [machine_reject]
                  have hnone := run_reject_nonempty_none (machine P M H hnb hcodes)
                      { state := rejectC, head := c.head, tape := c.tape } hst
                      (s :: rest) (by simp)
                  simp [hnone] at h
            · rcases hR with ⟨_, hs0, hmid⟩
              subst slot; rw [hmid] at h
              cases rest with
              | nil => simp at h; subst out; simp [acceptC, rejectC] at hacc
              | cons s rest =>
                  have hst :
                      ({ state := rejectC, head := c.head, tape := c.tape } :
                        Configuration (nsP + nsM + 2 * nsH + 2) nt).state =
                        (machine P M H hnb hcodes).reject := by
                    simp [machine_reject]
                  have hnone := run_reject_nonempty_none (machine P M H hnb hcodes)
                      { state := rejectC, head := c.head, tape := c.tape } hst
                      (s :: rest) (by simp)
                  simp [hnone] at h
            · rcases hO with ⟨_, _, c', hMstep, hmid⟩
              subst mid
              obtain ⟨d, m, h2, u, rest', hs', hm, hma, hmone, hh2, hh2a, ihT⟩ :=
                ihM c' out h hacc
              refine ⟨d, m, h2, slot :: u, rest', ?_, ?_, hma, hmone, hh2, hh2a, ihT⟩
              · simp [hs']
              · rw [run_cons, hMstep, Option.bind_some, hm]
      · intro c out h hacc
        rw [run_cons] at h
        cases hstep : step (machine P M H hnb hcodes) slot (liftHP c) with
        | none => simp [hstep] at h
        | some mid =>
            simp [hstep] at h
            have hinv := step_HP_inv P M H hnb hcodes c slot mid hstep
            rcases hinv with hA | hR | hO
            · rcases hA with ⟨hs, hs0, hmid⟩
              subst slot; rw [hmid] at h
              have ihT := ihP (restartP P c) out h hacc
              refine ⟨0, c, rest, ?_, ?_, hs, ihT⟩
              · simp
              · simp [ticks]
            · rcases hR with ⟨_, hs0, hmid⟩
              subst slot; rw [hmid] at h
              cases rest with
              | nil => simp at h; subst out; simp [acceptC, rejectC] at hacc
              | cons s rest =>
                  have hst :
                      ({ state := rejectC, head := c.head, tape := c.tape } :
                        Configuration (nsP + nsM + 2 * nsH + 2) nt).state =
                        (machine P M H hnb hcodes).reject := by
                    simp [machine_reject]
                  have hnone := run_reject_nonempty_none (machine P M H hnb hcodes)
                      { state := rejectC, head := c.head, tape := c.tape } hst
                      (s :: rest) (by simp)
                  simp [hnone] at h
            · rcases hO with ⟨_, _, hs0, c', hH, hmid⟩
              subst slot; subst mid
              obtain ⟨d, h2, rest', hs', hh2, hh2a, ihT⟩ := ihHP c' out h hacc
              refine ⟨d + 1, h2, rest', ?_, ?_, hh2a, ihT⟩
              · simp [hs', List.replicate_succ, List.cons_append]
              · change run H (0 :: ticks d) c = some h2
                rw [run_cons, hH, Option.bind_some, hh2]

theorem accepted_iff_trace (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (cP : Configuration nsP nt) (slots : List (Fin nb)) :
    (∃ out, run (machine P M H hnb hcodes) slots (liftP cP) = some out ∧
      out.state = acceptC) ↔ AcceptTrace P M H hnb cP slots := by
  constructor
  · intro h
    obtain ⟨out, hrun, hst⟩ := h
    exact (invert P M H hnb hcodes slots).1 cP out hrun hst
  · exact accepted_of_trace P M H hnb hcodes cP slots

theorem accepted_iff_init (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (raw : List Bool) (slots : List (Fin nb)) :
    Accepted (machine P M H hnb hcodes) raw slots ↔
      AcceptTrace P M H hnb (initial P raw) slots := by
  rw [accepted_iff]
  constructor
  · intro h
    obtain ⟨out, hrun, hst⟩ := h
    have hstC : out.state = acceptC := by simpa [machine_accept] using hst
    rw [initial_liftP] at hrun
    exact (accepted_iff_trace P M H hnb hcodes (initial P raw) slots).mp ⟨out, hrun, hstC⟩
  · intro h
    obtain ⟨out, hrun, hst⟩ :=
      (accepted_iff_trace P M H hnb hcodes (initial P raw) slots).mpr h
    refine ⟨out, ?_, ?_⟩
    · rw [initial_liftP]; exact hrun
    · simpa [machine_accept] using hst

def cycleBound (A B C : Nat) : Nat := A + B + 2 * C + 4

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

theorem nd_fuel_pred (S : Machine nsM nt nb) (c c' : Configuration nsM nt)
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

theorem prefix_len (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (I : Configuration nsP nt → Prop) (r : Configuration nsP nt → Nat)
    (A B C : Nat)
    (hP : ∀ c, I c → ∀ t d, run P (ticks t) c = some d → t ≤ A)
    (hHfromP : ∀ c, c.state = P.accept → c.tape c.head = P.one →
      ∀ t d, run H (ticks t) (restartH H c) = some d → t ≤ C)
    (hMfromH : ∀ c, c.state = H.accept →
      ∀ u d, run M u (restartM M c) = some d → u.length ≤ B)
    (hHfromM : ∀ c, c.state = M.accept → c.tape c.head = M.one →
      ∀ t d, run H (ticks t) (restartH H c) = some d → t ≤ C)
    (hret : ∀ cP cH, I cP → cH.state = H.accept →
      I (restartP P cH) ∧ r (restartP P cH) < r cP)
    (slots : List (Fin nb)) (out : Configuration (nsP + nsM + 2 * nsH + 2) nt) :
    (∀ (c cP : Configuration nsP nt) (fuel k : Nat),
      I cP → r cP ≤ k → (∀ t d, run P (ticks t) c = some d → t ≤ fuel) →
      run (machine P M H hnb hcodes) slots (liftP c) = some out →
      slots.length ≤ fuel + 1 + B + 2 * C + 3 + k * cycleBound A B C) ∧
    (∀ (c : Configuration nsH nt) (cP : Configuration nsP nt) (fuel k : Nat),
      I cP → r cP ≤ k → (∀ t d, run H (ticks t) c = some d → t ≤ fuel) →
      run (machine P M H hnb hcodes) slots (liftHM c) = some out →
      slots.length ≤ fuel + 1 + B + C + 2 + k * cycleBound A B C) ∧
    (∀ (c : Configuration nsM nt) (cP : Configuration nsP nt) (fuel k : Nat),
      I cP → r cP ≤ k → (∀ u d, run M u c = some d → u.length ≤ fuel) →
      run (machine P M H hnb hcodes) slots (liftM c) = some out →
      slots.length ≤ fuel + 1 + C + 1 + k * cycleBound A B C) ∧
    (∀ (c : Configuration nsH nt) (cP : Configuration nsP nt) (fuel k : Nat),
      I cP → r cP ≤ k → (∀ t d, run H (ticks t) c = some d → t ≤ fuel) →
      run (machine P M H hnb hcodes) slots (liftHP c) = some out →
      slots.length ≤ fuel + 1 + k * cycleBound A B C) := by
  induction slots with
  | nil =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro c cP fuel k hI hr hfuel h; simp at h ⊢
      · intro c cP fuel k hI hr hfuel h; simp at h ⊢
      · intro c cP fuel k hI hr hfuel h; simp at h ⊢
      · intro c cP fuel k hI hr hfuel h; simp at h ⊢
  | cons slot rest ih =>
      rcases ih with ⟨ihP, ihHM, ihM, ihHP⟩
      refine ⟨?fromP, ?fromHM, ?fromM, ?fromHP⟩
      · intro c cP fuel k hI hr hfuel h
        rw [run_cons] at h
        cases hstep : step (machine P M H hnb hcodes) slot (liftP c) with
        | none => simp [hstep] at h
        | some mid =>
            simp [hstep] at h
            have hinv := step_P_inv P M H hnb hcodes c slot mid hstep
            rcases hinv with hC | hS | hR | hO
            · rcases hC with ⟨hs, hs0, hone, hmid⟩
              subst slot; rw [hmid] at h
              have hHf := hHfromP c hs hone
              have := ihHM (restartH H c) cP C k hI hr hHf h
              simp [cycleBound] at this ⊢; omega
            · rcases hS with ⟨_, hs0, _, hmid⟩
              subst slot; rw [hmid] at h
              cases rest with
              | nil => simp; omega
              | cons s rest =>
                  have hst :
                      ({ state := acceptC, head := c.head, tape := c.tape } :
                        Configuration (nsP + nsM + 2 * nsH + 2) nt).state =
                        (machine P M H hnb hcodes).accept := by
                    simp [machine_accept]
                  have hnone := run_accept_nonempty_none (machine P M H hnb hcodes)
                      { state := acceptC, head := c.head, tape := c.tape } hst
                      (s :: rest) (by simp)
                  simp [hnone] at h
            · rcases hR with ⟨_, hs0, hmid⟩
              subst slot; rw [hmid] at h
              cases rest with
              | nil => simp; omega
              | cons s rest =>
                  have hst :
                      ({ state := rejectC, head := c.head, tape := c.tape } :
                        Configuration (nsP + nsM + 2 * nsH + 2) nt).state =
                        (machine P M H hnb hcodes).reject := by
                    simp [machine_reject]
                  have hnone := run_reject_nonempty_none (machine P M H hnb hcodes)
                      { state := rejectC, head := c.head, tape := c.tape } hst
                      (s :: rest) (by simp)
                  simp [hnone] at h
            · rcases hO with ⟨_, _, hs0, c', hPstep, hmid⟩
              subst slot; subst mid
              have hf := det_fuel_pred P c c' fuel hPstep hfuel
              have := ihP c' cP (fuel - 1) k hI hr hf.2 h
              simp at this ⊢; omega
      · intro c cP fuel k hI hr hfuel h
        rw [run_cons] at h
        cases hstep : step (machine P M H hnb hcodes) slot (liftHM c) with
        | none => simp [hstep] at h
        | some mid =>
            simp [hstep] at h
            have hinv := step_HM_inv P M H hnb hcodes c slot mid hstep
            rcases hinv with hA | hR | hO
            · rcases hA with ⟨hs, hs0, hmid⟩
              subst slot; rw [hmid] at h
              have hMf := hMfromH c hs
              have := ihM (restartM M c) cP B k hI hr hMf h
              simp [cycleBound] at this ⊢; omega
            · rcases hR with ⟨_, hs0, hmid⟩
              subst slot; rw [hmid] at h
              cases rest with
              | nil => simp; omega
              | cons s rest =>
                  have hst :
                      ({ state := rejectC, head := c.head, tape := c.tape } :
                        Configuration (nsP + nsM + 2 * nsH + 2) nt).state =
                        (machine P M H hnb hcodes).reject := by
                    simp [machine_reject]
                  have hnone := run_reject_nonempty_none (machine P M H hnb hcodes)
                      { state := rejectC, head := c.head, tape := c.tape } hst
                      (s :: rest) (by simp)
                  simp [hnone] at h
            · rcases hO with ⟨_, _, hs0, c', hH, hmid⟩
              subst slot; subst mid
              have hf := det_fuel_pred H c c' fuel hH hfuel
              have := ihHM c' cP (fuel - 1) k hI hr hf.2 h
              simp at this ⊢; omega
      · intro c cP fuel k hI hr hfuel h
        rw [run_cons] at h
        cases hstep : step (machine P M H hnb hcodes) slot (liftM c) with
        | none => simp [hstep] at h
        | some mid =>
            simp [hstep] at h
            have hinv := step_M_inv P M H hnb hcodes c slot mid hstep
            rcases hinv with hC | hBad | hR | hO
            · rcases hC with ⟨hs, hs0, hone, hmid⟩
              subst slot; rw [hmid] at h
              have hHf := hHfromM c hs hone
              have := ihHP (restartH H c) cP C k hI hr hHf h
              simp [cycleBound] at this ⊢; omega
            · rcases hBad with ⟨_, hs0, _, hmid⟩
              subst slot; rw [hmid] at h
              cases rest with
              | nil => simp; omega
              | cons s rest =>
                  have hst :
                      ({ state := rejectC, head := c.head, tape := c.tape } :
                        Configuration (nsP + nsM + 2 * nsH + 2) nt).state =
                        (machine P M H hnb hcodes).reject := by
                    simp [machine_reject]
                  have hnone := run_reject_nonempty_none (machine P M H hnb hcodes)
                      { state := rejectC, head := c.head, tape := c.tape } hst
                      (s :: rest) (by simp)
                  simp [hnone] at h
            · rcases hR with ⟨_, hs0, hmid⟩
              subst slot; rw [hmid] at h
              cases rest with
              | nil => simp; omega
              | cons s rest =>
                  have hst :
                      ({ state := rejectC, head := c.head, tape := c.tape } :
                        Configuration (nsP + nsM + 2 * nsH + 2) nt).state =
                        (machine P M H hnb hcodes).reject := by
                    simp [machine_reject]
                  have hnone := run_reject_nonempty_none (machine P M H hnb hcodes)
                      { state := rejectC, head := c.head, tape := c.tape } hst
                      (s :: rest) (by simp)
                  simp [hnone] at h
            · rcases hO with ⟨_, _, c', hMstep, hmid⟩
              subst mid
              have hf := nd_fuel_pred M c c' slot fuel hMstep hfuel
              have := ihM c' cP (fuel - 1) k hI hr hf.2 h
              simp at this ⊢; omega
      · intro c cP fuel k hI hr hfuel h
        rw [run_cons] at h
        cases hstep : step (machine P M H hnb hcodes) slot (liftHP c) with
        | none => simp [hstep] at h
        | some mid =>
            simp [hstep] at h
            have hinv := step_HP_inv P M H hnb hcodes c slot mid hstep
            rcases hinv with hA | hR | hO
            · rcases hA with ⟨hs, hs0, hmid⟩
              subst slot; rw [hmid] at h
              have hrt := hret cP c hI hs
              have hlt : r (restartP P c) < k ∨ k = 0 := by omega
              cases hlt with
              | inl hlt =>
                  have hkpos : 0 < k := Nat.zero_lt_of_lt hlt
                  have hr' : r (restartP P c) ≤ k - 1 := Nat.le_pred_of_lt hlt
                  have hPf := hP (restartP P c) hrt.1
                  have hrest :=
                    ihP (restartP P c) (restartP P c) A (k - 1) hrt.1 hr' hPf h
                  have hkeq : (k - 1) + 1 = k := Nat.succ_pred_eq_of_pos hkpos
                  have hmul : k * cycleBound A B C =
                      (k - 1) * cycleBound A B C + cycleBound A B C := by
                    conv => lhs; rw [← hkeq]
                    rw [Nat.succ_mul]
                  have hpad : A + 1 + B + 2 * C + 3 = cycleBound A B C := by
                    simp [cycleBound]; omega
                  rw [hpad] at hrest
                  have hrest' : rest.length ≤ k * cycleBound A B C := by
                    rw [hmul, Nat.add_comm]; exact hrest
                  simp; omega
              | inr hk =>
                  subst k
                  have : r (restartP P c) < 0 := Nat.lt_of_lt_of_le hrt.2 (by omega)
                  exact (Nat.not_lt_zero _ this).elim
            · rcases hR with ⟨_, hs0, hmid⟩
              subst slot; rw [hmid] at h
              cases rest with
              | nil => simp; omega
              | cons s rest =>
                  have hst :
                      ({ state := rejectC, head := c.head, tape := c.tape } :
                        Configuration (nsP + nsM + 2 * nsH + 2) nt).state =
                        (machine P M H hnb hcodes).reject := by
                    simp [machine_reject]
                  have hnone := run_reject_nonempty_none (machine P M H hnb hcodes)
                      { state := rejectC, head := c.head, tape := c.tape } hst
                      (s :: rest) (by simp)
                  simp [hnone] at h
            · rcases hO with ⟨_, _, hs0, c', hH, hmid⟩
              subst slot; subst mid
              have hf := det_fuel_pred H c c' fuel hH hfuel
              have := ihHP c' cP (fuel - 1) k hI hr hf.2 h
              simp at this ⊢; omega

theorem prefix_from_P (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (I : Configuration nsP nt → Prop) (r : Configuration nsP nt → Nat)
    (A B C K : Nat) (cP : Configuration nsP nt) (slots : List (Fin nb))
    (out : Configuration (nsP + nsM + 2 * nsH + 2) nt)
    (hI : I cP) (hr : r cP ≤ K)
    (hP : ∀ c, I c → ∀ t d, run P (ticks t) c = some d → t ≤ A)
    (hHfromP : ∀ c, c.state = P.accept → c.tape c.head = P.one →
      ∀ t d, run H (ticks t) (restartH H c) = some d → t ≤ C)
    (hMfromH : ∀ c, c.state = H.accept →
      ∀ u d, run M u (restartM M c) = some d → u.length ≤ B)
    (hHfromM : ∀ c, c.state = M.accept → c.tape c.head = M.one →
      ∀ t d, run H (ticks t) (restartH H c) = some d → t ≤ C)
    (hret : ∀ cP cH, I cP → cH.state = H.accept →
      I (restartP P cH) ∧ r (restartP P cH) < r cP)
    (h : run (machine P M H hnb hcodes) slots (liftP cP) = some out) :
    slots.length ≤ (K + 1) * cycleBound A B C := by
  have hfuel : ∀ t d, run P (ticks t) cP = some d → t ≤ A := hP cP hI
  have := (prefix_len P M H hnb hcodes I r A B C hP hHfromP hMfromH hHfromM hret
    slots out).1 cP cP A K hI hr hfuel h
  have hpad : A + 1 + B + 2 * C + 3 = cycleBound A B C := by
    simp [cycleBound]; omega
  rw [hpad] at this
  have hmul : cycleBound A B C + K * cycleBound A B C =
      (K + 1) * cycleBound A B C := by rw [Nat.add_comm, Nat.succ_mul]
  omega

theorem feedback_spec (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (I : Configuration nsP nt → Prop) (r : Configuration nsP nt → Nat)
    (A B C K : Nat)
    (hP : ∀ c, I c → ∀ t d, run P (ticks t) c = some d → t ≤ A)
    (hHfromP : ∀ c, c.state = P.accept → c.tape c.head = P.one →
      ∀ t d, run H (ticks t) (restartH H c) = some d → t ≤ C)
    (hMfromH : ∀ c, c.state = H.accept →
      ∀ u d, run M u (restartM M c) = some d → u.length ≤ B)
    (hHfromM : ∀ c, c.state = M.accept → c.tape c.head = M.one →
      ∀ t d, run H (ticks t) (restartH H c) = some d → t ≤ C)
    (hret : ∀ cP cH, I cP → cH.state = H.accept →
      I (restartP P cH) ∧ r (restartP P cH) < r cP) :
    (∀ raw slots, Accepted (machine P M H hnb hcodes) raw slots ↔
      AcceptTrace P M H hnb (initial P raw) slots) ∧
    (∀ (cP : Configuration nsP nt) (slots : List (Fin nb))
        (out : Configuration (nsP + nsM + 2 * nsH + 2) nt),
      I cP → r cP ≤ K →
        run (machine P M H hnb hcodes) slots (liftP cP) = some out →
        slots.length ≤ (K + 1) * cycleBound A B C) := by
  refine ⟨accepted_iff_init P M H hnb hcodes, ?_⟩
  intro cP slots out hI hr hrun
  exact prefix_from_P P M H hnb hcodes I r A B C K cP slots out hI hr
    hP hHfromP hMfromH hHfromM hret hrun

end
end PakFixedPolyomino.StandardMachineNondeterministicFeedback
