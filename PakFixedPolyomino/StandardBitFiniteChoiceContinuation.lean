import PakFixedPolyomino.StandardMachineNondeterministicSequence
import PakFixedPolyomino.StandardMachineNondeterministicCommonAlphabet
import PakFixedPolyomino.StandardBitFiniteChoicePrefix
import PakFixedPolyomino.StandardBitTimeComposition

/-! Actual finite choice followed by an ordinary deterministic bit transducer.
All raw accepted slot words are recovered, with clean whole-tape output.
The finite machine depends only on L and N; witness times are proof data. -/
set_option maxHeartbeats 1000000
namespace PakFixedPolyomino.StandardBitFiniteChoiceContinuation
noncomputable section
open StandardNondeterministicMachine StandardBitTime StandardBitMetric
variable {ns nt : Nat}

theorem positive (L : Nat) : 0 < L+1 := Nat.zero_lt_succ L
def left (N : DeterministicMachine ns nt) (L : Nat) := StandardMachineNondeterministicCommonAlphabet.left (ntB:=nt) (StandardBitFiniteChoicePrefix.machine L) (positive L)
def right (N : DeterministicMachine ns nt) := StandardMachineNondeterministicCommonAlphabet.right (ntA:=3) N
theorem codes (N : DeterministicMachine ns nt) (L : Nat) : StandardMachineNondeterministicSequence.SameCodes (left N L) (right N) :=
  StandardMachineNondeterministicCommonAlphabet.same_codes (StandardBitFiniteChoicePrefix.machine L) N (positive L)
def machine (N : DeterministicMachine ns nt) (L : Nat) := StandardMachineNondeterministicSequence.machine (left N L) (right N) (positive L) (codes N L)
def input (L : Nat) (raw : List Bool) (i : Fin L) := pairBits (StandardBitFiniteChoicePrefix.labelCode L i) raw
def choiceFinal (N : DeterministicMachine ns nt) (L : Nat) (raw : List Bool) (i : Fin L) :
    Configuration (StandardBitFiniteChoicePrefix.ns L) (3+nt+3) := ⟨(left N L).accept,0,inputTape (left N L) (input L raw i)⟩

theorem left_word (N : DeterministicMachine ns nt) (L : Nat) (raw : List Bool) (i : Fin L) :
    run (left N L) (StandardBitFiniteChoicePrefix.word L raw i) (initial (left N L) raw)=some (choiceFinal N L raw i) := by
  apply (StandardMachineNondeterministicCommonAlphabet.left_all_raw_inverse (StandardBitFiniteChoicePrefix.machine L) (positive L) raw _ _).mpr
  exact ⟨_,StandardBitFiniteChoicePrefix.word_output L raw i,(StandardMachineNondeterministicCommonAlphabet.left_clean (ntB:=nt) (StandardBitFiniteChoicePrefix.machine L) (positive L) (input L raw i)).symm⟩

theorem restart_eq (N : DeterministicMachine ns nt) (L : Nat) (raw : List Bool) (i : Fin L) :
    (⟨(right N).start,(choiceFinal N L raw i).head,(choiceFinal N L raw i).tape⟩ :
      Configuration ns (3+nt+3))=initial (right N) (input L raw i) := by
  apply StandardBitMachineComposition.config_ext
  · rfl
  · rfl
  · exact (StandardMachineNondeterministicSequence.inputTape_N (left N L) (right N) (codes N L) (input L raw i)).symm

def duration (N : DeterministicMachine ns nt) (f : List Bool → List Bool) (p : Polynomial Nat)
    (hf : ComputesWithin N f (fun n => p.eval n)) (x : List Bool) : Nat :=
  Classical.choose (StandardMachineNondeterministicCommonAlphabet.right_computes (ntA:=3) N f _ hf x)

theorem duration_spec (N : DeterministicMachine ns nt) (f : List Bool → List Bool) (p : Polynomial Nat)
    (hf : ComputesWithin N f (fun n => p.eval n)) (x : List Bool) :
    ∃ out, duration N f p hf x ≤ p.eval x.length ∧
      run (right N) (ticks (duration N f p hf x)) (initial (right N) x)=some out ∧
      Output (right N) (f x) out :=
  Classical.choose_spec (StandardMachineNondeterministicCommonAlphabet.right_computes (ntA:=3) N f _ hf x)

def path (N : DeterministicMachine ns nt) (L : Nat) (f : List Bool → List Bool) (p : Polynomial Nat)
    (hf : ComputesWithin N f (fun n => p.eval n)) (raw : List Bool) (i : Fin L) : List (Fin (L+1)) :=
  StandardBitFiniteChoicePrefix.word L raw i ++ [StandardMachineNondeterministicSequence.zeroSlot (positive L)] ++
    List.replicate (duration N f p hf (input L raw i)) (StandardMachineNondeterministicSequence.zeroSlot (positive L)) ++ [StandardMachineNondeterministicSequence.zeroSlot (positive L)]

theorem path_run (N : DeterministicMachine ns nt) (L : Nat) (f : List Bool → List Bool) (p : Polynomial Nat)
    (hf : ComputesWithin N f (fun n => p.eval n)) (raw : List Bool) (i : Fin L) :
    run (machine N L) (path N L f p hf raw i) (initial (machine N L) raw)=
      some ⟨(machine N L).accept,0,inputTape (machine N L) (f (input L raw i))⟩ := by
  obtain ⟨out,_,hr,ho⟩ := duration_spec N f p hf (input L raw i)
  have hr' : run (right N) (ticks (duration N f p hf (input L raw i)))
      ⟨(right N).start,(choiceFinal N L raw i).head,(choiceFinal N L raw i).tape⟩=some out := by
    rw [restart_eq];exact hr
  have h := StandardMachineNondeterministicSequence.sequence_run (left N L) (right N) (positive L) (codes N L) raw
    (StandardBitFiniteChoicePrefix.word L raw i) _ _ out (left_word N L raw i) rfl hr' ho.1
  change run (machine N L) (path N L f p hf raw i) (initial (machine N L) raw)=
    some ⟨(machine N L).accept,0,inputTape (machine N L) (f (input L raw i))⟩
  change run (machine N L) (path N L f p hf raw i) (initial (machine N L) raw)=
    some ⟨(machine N L).accept,out.head,out.tape⟩ at h
  rw [h]
  congr 1
  apply StandardBitMachineComposition.config_ext
  · rfl
  · exact ho.2.1
  · exact ho.2.2.trans ((StandardMachineNondeterministicSequence.inputTape_N (left N L) (right N) (codes N L) _).trans
      (StandardMachineNondeterministicSequence.inputTape_machine (left N L) (right N) (positive L) (codes N L) _).symm)

theorem accepted_path (N : DeterministicMachine ns nt) (L : Nat) (f : List Bool → List Bool) (p : Polynomial Nat)
    (hf : ComputesWithin N f (fun n => p.eval n)) (raw : List Bool) (i : Fin L) :
    Accepted (machine N L) raw (path N L f p hf raw i) :=
  (accepted_iff _ _ _).mpr ⟨_,path_run N L f p hf raw i,rfl⟩

theorem accepted_iff_path (N : DeterministicMachine ns nt) (L : Nat) (f : List Bool → List Bool) (p : Polynomial Nat)
    (hf : ComputesWithin N f (fun n => p.eval n)) (raw : List Bool) (slots : List (Fin (L+1))) :
    Accepted (machine N L) raw slots ↔ ∃ i : Fin L, slots=path N L f p hf raw i := by
  constructor
  · intro h
    obtain ⟨u,v,c,d,hs,hu,ha,hv,hn,hd⟩ := (StandardMachineNondeterministicSequence.accepted_iff_split (left N L) (right N)
      (positive L) (codes N L) raw slots).mp h
    have hleft : Accepted (left N L) raw u := (accepted_iff _ _ _).mpr ⟨c,hu,ha⟩
    obtain ⟨i,hi⟩ := (StandardBitFiniteChoicePrefix.accepted_iff_word L raw u).mp
      ((StandardMachineNondeterministicCommonAlphabet.left_accepted_iff (ntB:=nt) (StandardBitFiniteChoicePrefix.machine L) (positive L) raw u).mp hleft)
    subst u
    have hc : c=choiceFinal N L raw i := Option.some.inj (hu.symm.trans (left_word N L raw i))
    subst c
    rw [restart_eq] at hn
    obtain ⟨out,_,hr,ho⟩ := duration_spec N f p hf (input L raw i)
    have ht := (halting_run_unique (right N) (input L raw i) _ v.length out d hr ho.1 hn hd).1
    refine ⟨i,?_⟩
    rw [hs,hv,← ht]
    rfl
  · rintro ⟨i,rfl⟩
    exact accepted_path N L f p hf raw i

def bound (L : Nat) (p : Polynomial Nat) : Polynomial Nat :=
  StandardBitFiniteChoicePrefix.boundPoly L + p.comp (Polynomial.X + Polynomial.C (2*L+1)) + 2

theorem bound_eval (L : Nat) (p : Polynomial Nat) (n : Nat) :
    (bound L p).eval n=(StandardBitFiniteChoicePrefix.boundPoly L).eval n+p.eval (2*L+1+n)+2 := by
  simp [bound,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_X,Polynomial.eval_C,Nat.add_comm]

theorem input_length (L : Nat) (raw : List Bool) (i : Fin L) :
    (input L raw i).length=2*L+1+raw.length := by
  simp [input,pairBits,StandardBitFiniteChoicePrefix.labelCode_length]
  omega

theorem all_prefix_bound (N : DeterministicMachine ns nt) (L : Nat) (f : List Bool → List Bool) (p : Polynomial Nat)
    (hf : ComputesWithin N f (fun n => p.eval n)) (raw : List Bool) :
    RunsAtMost (machine N L) raw ((bound L p).eval raw.length) := by
  rw [bound_eval]
  apply StandardMachineNondeterministicSequence.sequence_runsAtMost (left N L) (right N) (positive L) (codes N L)
  · exact StandardMachineNondeterministicCommonAlphabet.left_prefix_bound (ntB:=nt) (StandardBitFiniteChoicePrefix.machine L) (positive L) raw _ (StandardBitFiniteChoicePrefix.choose_runsAtMost L raw)
  · intro u c hu ha v d hn
    have hleft : Accepted (left N L) raw u := (accepted_iff _ _ _).mpr ⟨c,hu,ha⟩
    obtain ⟨i,hi⟩ := (StandardBitFiniteChoicePrefix.accepted_iff_word L raw u).mp
      ((StandardMachineNondeterministicCommonAlphabet.left_accepted_iff (ntB:=nt) (StandardBitFiniteChoicePrefix.machine L) (positive L) raw u).mp hleft)
    subst u
    have hc : c=choiceFinal N L raw i := Option.some.inj (hu.symm.trans (left_word N L raw i))
    subst c
    rw [restart_eq] at hn
    have hb := (ComputesWithin.actual_bounds (right N) f (fun n => p.eval n)
      (StandardMachineNondeterministicCommonAlphabet.right_computes (ntA:=3) N f _ hf) (input L raw i)).1 (ticks v.length) d hn
    simpa only [ticks_length,input_length] using hb

theorem path_injective (N : DeterministicMachine ns nt) (L : Nat) (f : List Bool → List Bool)
    (p : Polynomial Nat) (hf : ComputesWithin N f (fun n => p.eval n)) (raw : List Bool) :
    Function.Injective (path N L f p hf raw) := by
  intro i j he
  have hh : i.castSucc=j.castSucc := by
    have h := congrArg List.head? he
    simpa [path,StandardBitFiniteChoicePrefix.word,List.cons_append] using h
  exact Fin.castSucc_injective _ hh

theorem accepted_clean (N : DeterministicMachine ns nt) (L : Nat) (f : List Bool → List Bool)
    (p : Polynomial Nat) (hf : ComputesWithin N f (fun n => p.eval n)) (raw : List Bool)
    (slots : List (Fin (L+1))) (out : Configuration (StandardBitFiniteChoicePrefix.ns L+ns+2) (3+nt+3))
    (hr : run (machine N L) slots (initial (machine N L) raw)=some out)
    (ha : out.state=(machine N L).accept) :
    ∃ i : Fin L,slots=path N L f p hf raw i ∧ out.head=0 ∧
      out.tape=inputTape (machine N L) (f (input L raw i)) := by
  obtain ⟨i,hi⟩ := (accepted_iff_path N L f p hf raw slots).mp ((accepted_iff _ _ _).mpr ⟨out,hr,ha⟩)
  rw [hi,path_run] at hr
  have he := Option.some.inj hr
  subst out
  exact ⟨i,hi,rfl,rfl⟩

def acceptingOf (N : DeterministicMachine ns nt) (L : Nat) (f : List Bool → List Bool)
    (p : Polynomial Nat) (hf : ComputesWithin N f (fun n => p.eval n)) (raw : List Bool) (i : Fin L) :
    AcceptingCode (machine N L) raw ((bound L p).eval raw.length) :=
  ⟨WordCode.ofList (path N L f p hf raw i)
    (accepting_length_le _ _ _ (all_prefix_bound N L f p hf raw) _ (accepted_path N L f p hf raw i)),
    by simpa using accepted_path N L f p hf raw i⟩

theorem acceptingOf_bijective (N : DeterministicMachine ns nt) (L : Nat) (f : List Bool → List Bool)
    (p : Polynomial Nat) (hf : ComputesWithin N f (fun n => p.eval n)) (raw : List Bool) :
    Function.Bijective (acceptingOf N L f p hf raw) := by
  constructor
  · intro i j he
    apply path_injective N L f p hf raw
    have h := congrArg (fun c : AcceptingCode (machine N L) raw _ => c.val.toList) he
    simpa [acceptingOf] using h
  · intro code
    obtain ⟨i,hi⟩ := (accepted_iff_path N L f p hf raw code.val.toList).mp code.property
    refine ⟨i,?_⟩
    apply Subtype.ext
    apply WordCode.toList_injective
    simpa [acceptingOf] using hi.symm

def acceptingEquiv (N : DeterministicMachine ns nt) (L : Nat) (f : List Bool → List Bool)
    (p : Polynomial Nat) (hf : ComputesWithin N f (fun n => p.eval n)) (raw : List Bool) :
    Fin L ≃ AcceptingCode (machine N L) raw ((bound L p).eval raw.length) :=
  Equiv.ofBijective (acceptingOf N L f p hf raw) (acceptingOf_bijective N L f p hf raw)

theorem count_eq (N : DeterministicMachine ns nt) (L : Nat) (f : List Bool → List Bool)
    (p : Polynomial Nat) (hf : ComputesWithin N f (fun n => p.eval n)) (raw : List Bool) :
    acceptingCount (machine N L) raw ((bound L p).eval raw.length)=L := by
  rw [acceptingCount,← Fintype.card_congr (acceptingEquiv N L f p hf raw),Fintype.card_fin]

theorem finite_choice_continuation_spec (N : DeterministicMachine ns nt) (L : Nat)
    (f : List Bool → List Bool) (p : Polynomial Nat) (hf : ComputesWithin N f (fun n => p.eval n)) :
    (∀ raw, RunsAtMost (machine N L) raw ((bound L p).eval raw.length)) ∧
    (∀ raw slots, Accepted (machine N L) raw slots ↔ ∃ i : Fin L, slots=path N L f p hf raw i) ∧
    (∀ raw, acceptingCount (machine N L) raw ((bound L p).eval raw.length)=L) ∧
    (∀ raw i, run (machine N L) (path N L f p hf raw i) (initial (machine N L) raw)=
      some ⟨(machine N L).accept,0,inputTape (machine N L) (f (input L raw i))⟩) :=
  ⟨all_prefix_bound N L f p hf,accepted_iff_path N L f p hf,count_eq N L f p hf,path_run N L f p hf⟩
end
end PakFixedPolyomino.StandardBitFiniteChoiceContinuation
