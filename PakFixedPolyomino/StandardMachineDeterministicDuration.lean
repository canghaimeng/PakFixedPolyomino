import PakFixedPolyomino.StandardMachineCleanWordReadback

/-! The unique physical accepting word of a deterministic clean transducer.
Duration is selected from an already proved computation, and is not an
additional machine operation or a premise about the composite runtime. -/
namespace PakFixedPolyomino.StandardMachineDeterministicDuration
noncomputable section
open StandardNondeterministicMachine StandardBitTime
variable {ns nt : Nat}

def duration (M : DeterministicMachine ns nt) (f : List Bool → List Bool)
    (p : Nat → Nat) (hf : ComputesWithin M f p) (x : List Bool) : Nat :=
  Classical.choose (hf x)

theorem duration_spec (M : DeterministicMachine ns nt) (f : List Bool → List Bool)
    (p : Nat → Nat) (hf : ComputesWithin M f p) (x : List Bool) :
    duration M f p hf x≤p x.length ∧
      run M (ticks (duration M f p hf x)) (initial M x)=
        some ⟨M.accept,0,inputTape M (f x)⟩ := by
  obtain ⟨out,hn,hr,ha,hh,ht⟩ := Classical.choose_spec (hf x)
  refine ⟨hn,?_⟩
  have he : out=⟨M.accept,0,inputTape M (f x)⟩ := by
    cases out
    simp_all
  exact hr.trans (congrArg some he)

theorem accepted_iff_ticks (M : DeterministicMachine ns nt) (f : List Bool → List Bool)
    (p : Nat → Nat) (hf : ComputesWithin M f p) (x : List Bool) (slots : List (Fin 1)) :
    Accepted M x slots ↔ slots=ticks (duration M f p hf x) := by
  constructor
  · intro h
    obtain ⟨out,hr,ha⟩ := (accepted_iff M x slots).mp h
    have hc := (duration_spec M f p hf x).2
    rw [deterministic_word slots] at hr
    have he := (halting_run_unique M x _ _ _ out hc rfl hr ha).1
    exact (deterministic_word slots).trans (congrArg ticks he.symm)
  · intro he
    subst slots
    exact (accepted_iff M x _).mpr ⟨_,(duration_spec M f p hf x).2,rfl⟩

theorem accepted_run_unique (M : DeterministicMachine ns nt) (f : List Bool → List Bool)
    (p : Nat → Nat) (hf : ComputesWithin M f p) (x : List Bool) (slots : List (Fin 1))
    (out : Configuration ns nt) (hr : run M slots (initial M x)=some out) (ha : out.state=M.accept) :
    slots=ticks (duration M f p hf x) ∧ out=⟨M.accept,0,inputTape M (f x)⟩ := by
  have hs := (accepted_iff_ticks M f p hf x slots).mp ((accepted_iff M x slots).mpr ⟨out,hr,ha⟩)
  refine ⟨hs,?_⟩
  rw [hs,(duration_spec M f p hf x).2] at hr
  exact (Option.some.inj hr).symm

theorem head_one_iff (M : Machine ns nt 1) (x : List Bool) :
    inputTape M x 0=M.one ↔ x.headD false=true := by
  cases x with
  | nil =>
    simp only [List.headD_nil,Bool.false_eq_true,iff_false]
    exact M.blank_ne_one
  | cons b bs =>
    cases b <;> simp [inputTape,M.zero_ne_one]

end
end PakFixedPolyomino.StandardMachineDeterministicDuration
