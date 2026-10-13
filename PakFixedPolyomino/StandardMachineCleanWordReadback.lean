import PakFixedPolyomino.StandardBitTime

/-! Proof-only readback of a clean whole binary tape. It is not a machine
primitive or a time certificate. Literal input tapes determine their words
uniquely, including empty words and redundant zero bits. -/
namespace PakFixedPolyomino.StandardMachineCleanWordReadback
noncomputable section
open StandardNondeterministicMachine StandardBitTime
variable {ns nt nb : Nat}

theorem input_length_le (M : Machine ns nt nb) (x y : List Bool)
    (he : inputTape M x=inputTape M y) : x.length≤y.length := by
  by_contra h
  have hy : y.length<x.length := by omega
  have hc := congrFun he (y.length : Int)
  rw [inputTape_ofNat M x y.length hy,inputTape_ge M y _ (by rfl)] at hc
  cases hbit : x[y.length] <;> simp only [hbit,if_false,if_true,Bool.false_eq_true] at hc
  · exact M.blank_ne_zero hc.symm
  · exact M.blank_ne_one hc.symm

theorem inputTape_injective (M : Machine ns nt nb) : Function.Injective (inputTape M) := by
  intro x y he
  have hl : x.length=y.length := Nat.le_antisymm (input_length_le M x y he) (input_length_le M y x he.symm)
  apply List.ext_getElem hl
  intro k hx hy
  have hc := congrFun he (k : Int)
  rw [inputTape_ofNat M x k hx,inputTape_ofNat M y k hy] at hc
  cases hb : x[k] <;> cases hd : y[k] <;> simp only [hb,hd,if_false,if_true,Bool.false_eq_true] at hc ⊢
  · exact (M.zero_ne_one hc).elim
  · exact (M.zero_ne_one hc.symm).elim

def word (M : Machine ns nt nb) (tape : Int → Fin nt) : List Bool := by
  classical
  exact if h : ∃ x : List Bool,inputTape M x=tape then Classical.choose h else []

theorem word_inputTape (M : Machine ns nt nb) (x : List Bool) : word M (inputTape M x)=x := by
  have h : ∃ y : List Bool,inputTape M y=inputTape M x := ⟨x,rfl⟩
  rw [word,dif_pos h]
  exact inputTape_injective M (Classical.choose_spec h)

theorem inputTape_codes {ns' nb' : Nat} (M : Machine ns nt nb) (N : Machine ns' nt nb')
    (hb : M.blank=N.blank) (hz : M.zero=N.zero) (ho : M.one=N.one) (x : List Bool) :
    inputTape M x=inputTape N x := by
  funext z
  simp only [inputTape,hb,hz,ho]

theorem word_same_codes {ns' nb' : Nat} (M : Machine ns nt nb) (N : Machine ns' nt nb')
    (hb : M.blank=N.blank) (hz : M.zero=N.zero) (ho : M.one=N.one) (x : List Bool) :
    word M (inputTape N x)=x := by
  rw [← inputTape_codes M N hb hz ho]
  exact word_inputTape M x

theorem computes_accepted_output (M : DeterministicMachine ns nt) (f : List Bool → List Bool)
    (p : Nat → Nat) (hf : ComputesWithin M f p) (x : List Bool) (slots : List (Fin 1))
    (out : Configuration ns nt) (hr : run M slots (initial M x)=some out) (ha : out.state=M.accept) :
    Output M (f x) out := by
  obtain ⟨n,final,_,hfinal,ho⟩ := hf x
  rw [deterministic_word slots] at hr
  have he := (halting_run_unique M x n slots.length final out hfinal ho.1 hr ha).2
  exact he ▸ ho
end
end PakFixedPolyomino.StandardMachineCleanWordReadback
