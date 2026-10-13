import PakFixedPolyomino.StandardBitTime

/-! Embed an ordinary deterministic machine into a fixed positive branching
alphabet without adding any choices or transitions. Only literal slot zero
is enabled. The full arbitrary-word inverse and physical time are proved. -/
namespace PakFixedPolyomino.StandardMachineDeterministicBranchEmbedding
open StandardNondeterministicMachine StandardBitTime
variable {ns nt nb : Nat}

def zeroSlot (hnb : 0<nb) : Fin nb := ⟨0,hnb⟩

def machine (M : DeterministicMachine ns nt) (hnb : 0<nb) : Machine ns nt nb where
  rule q a slot := if slot=zeroSlot hnb then M.rule q a 0 else none
  start := M.start
  accept := M.accept
  reject := M.reject
  accept_ne_reject := M.accept_ne_reject
  blank := M.blank
  zero := M.zero
  one := M.one
  blank_ne_zero := M.blank_ne_zero
  blank_ne_one := M.blank_ne_one
  zero_ne_one := M.zero_ne_one
  accept_terminal a slot := by simp only [M.accept_terminal,ite_self]
  reject_terminal a slot := by simp only [M.reject_terminal,ite_self]

theorem initial_eq (M : DeterministicMachine ns nt) (hnb : 0<nb) (raw : List Bool) :
    initial (machine M hnb) raw=initial M raw := rfl

theorem step_zero (M : DeterministicMachine ns nt) (hnb : 0<nb) (c : Configuration ns nt) :
    step (machine M hnb) (zeroSlot hnb) c=step M 0 c := by
  simp only [step,machine,if_true]

theorem step_other (M : DeterministicMachine ns nt) (hnb : 0<nb)
    (c : Configuration ns nt) (s : Fin nb) (h : s≠zeroSlot hnb) :
    step (machine M hnb) s c=none := by
  simp only [step,machine,if_neg h,Option.map_none]

theorem run_zeroes (M : DeterministicMachine ns nt) (hnb : 0<nb)
    (k : Nat) (c : Configuration ns nt) :
    run (machine M hnb) (List.replicate k (zeroSlot hnb)) c=run M (ticks k) c := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ,ticks,run_cons,step_zero]
    cases hs : step M 0 c with
    | none => rfl
    | some next => exact ih next

theorem run_some_iff (M : DeterministicMachine ns nt) (hnb : 0<nb)
    (slots : List (Fin nb)) (c d : Configuration ns nt) :
    run (machine M hnb) slots c=some d ↔
      slots=List.replicate slots.length (zeroSlot hnb) ∧ run M (ticks slots.length) c=some d := by
  induction slots generalizing c with
  | nil => simp only [List.length_nil,List.replicate_zero,ticks,run_nil,true_and]
  | cons s slots ih =>
    by_cases hz : s=zeroSlot hnb
    · subst s
      simp only [run_cons,step_zero,List.length_cons,List.replicate_succ,List.cons.injEq,true_and]
      change (step M 0 c).bind (run (machine M hnb) slots)=some d ↔
        slots=List.replicate slots.length (zeroSlot hnb) ∧
          (step M 0 c).bind (run M (ticks slots.length))=some d
      cases hs : step M 0 c with
      | none => simp
      | some next => simpa only [Option.bind_some] using ih next
    · rw [run_cons,step_other M hnb c s hz,Option.bind_none]
      have hn : s::slots≠List.replicate (s::slots).length (zeroSlot hnb) := by
        intro he
        simp only [List.length_cons,List.replicate_succ,List.cons.injEq] at he
        exact hz he.1
      constructor
      · intro he
        cases he
      · rintro ⟨he,_⟩
        exact (hn he).elim

theorem accepted_iff (M : DeterministicMachine ns nt) (hnb : 0<nb)
    (raw : List Bool) (slots : List (Fin nb)) :
    Accepted (machine M hnb) raw slots ↔
      slots=List.replicate slots.length (zeroSlot hnb) ∧ Accepted M raw (ticks slots.length) := by
  rw [StandardNondeterministicMachine.accepted_iff,StandardNondeterministicMachine.accepted_iff]
  simp only [initial_eq]
  constructor
  · rintro ⟨d,hr,ha⟩
    obtain ⟨hz,ht⟩ := (run_some_iff M hnb slots _ d).mp hr
    exact ⟨hz,d,ht,ha⟩
  · rintro ⟨hz,d,hr,ha⟩
    exact ⟨d,(run_some_iff M hnb slots _ d).mpr ⟨hz,hr⟩,ha⟩

theorem prefix_bound (M : DeterministicMachine ns nt) (hnb : 0<nb)
    (raw : List Bool) (bound : Nat) (h : RunsAtMost M raw bound) :
    RunsAtMost (machine M hnb) raw bound := by
  intro slots d hr
  rw [initial_eq] at hr
  have ht := (run_some_iff M hnb slots _ d).mp hr
  have hb := h (ticks slots.length) d ht.2
  simpa only [ticks,List.length_replicate] using hb

theorem deterministic_branch_embedding_spec (M : DeterministicMachine ns nt) (hnb : 0<nb) :
    (∀ raw slots,Accepted (machine M hnb) raw slots ↔
      slots=List.replicate slots.length (zeroSlot hnb) ∧ Accepted M raw (ticks slots.length)) ∧
    (∀ raw bound,RunsAtMost M raw bound → RunsAtMost (machine M hnb) raw bound) :=
  ⟨accepted_iff M hnb,prefix_bound M hnb⟩

end PakFixedPolyomino.StandardMachineDeterministicBranchEmbedding
