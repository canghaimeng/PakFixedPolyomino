import PakFixedPolyomino.StandardBitVariableAddTape

/-! Actual states36–38 of the frozen64/32 adder normalize the shifted
literal result and erase its left sentinel on the entire integer tape. -/
namespace PakFixedPolyomino.StandardBitVariableAddNormalize
open Computability StandardBinaryWordNormalization
open StandardNondeterministicMachine StandardBitTime
open StandardBitVariableAdd (machine machine_zero machine_one machine_blank enc)
open StandardBitVariableAddTape
open StandardBitNormalize (low_get high_get normalized_last)
open FiniteOneTapeSemantics (moveHead writtenTape)
abbrev bit (b : Bool) : Fin 32 := enc b

theorem rule_scan_bit (b : Bool) : machine.rule 36 (bit b) 0 =
    some ⟨bit b,36,.right⟩ := by cases b <;> rfl

theorem rule_scan_blank : machine.rule 36 2 0 = some ⟨2,37,.left⟩ := rfl

theorem rule_trim_zero : machine.rule 37 0 0 = some ⟨2,37,.left⟩ := rfl

theorem rule_trim_one : machine.rule 37 1 0 = some ⟨1,38,.left⟩ := rfl

theorem rule_return_bit (b : Bool) : machine.rule 38 (bit b) 0 =
    some ⟨bit b,38,.left⟩ := by cases b <;> rfl

theorem rule_finish (q : Fin 64) (hq : q=37 ∨ q=38) :
    machine.rule q 3 0 = some ⟨2,0,.right⟩ := by
  rcases hq with rfl | rfl <;> rfl

def scanConfig (x : List Bool) (k : Nat) : Configuration 64 32 :=
  ⟨36,k,blockTape x 0⟩

/-- Only cells at or to the right of the sweep boundary have been finalized. -/
def reverseTape (x : List Bool) (k : Nat) (z : Int) : Fin 32 :=
  if (k : Int) ≤ z then blockTape (normalizeBits x) 0 z
  else blockTape x 0 z

def returnConfig (x : List Bool) (k : Nat) : Configuration 64 32 :=
  ⟨if (normalizeBits x).length ≤ k then 37 else 38,(k : Int)-1,reverseTape x k⟩

def finalConfig (x : List Bool) : Configuration 64 32 :=
  ⟨0,0,inputTape machine (normalizeBits x)⟩

theorem scan_run (x : List Bool) (k : Nat) (hk : k ≤ x.length) :
    run machine (ticks k) (scanConfig x 0) = some (scanConfig x k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ticks_add k 1,run_append,ih (by omega),Option.bind_some,run_ticks_one]
    have hread : inputTape machine x (k:Int)=bit x[k] :=
      inputTape_ofNat machine x k (by omega : k < x.length)
    simp only [step,scanConfig,block_zero_nat,hread,rule_scan_bit,Option.map_some,moveHead,writtenTape]
    rw [←hread,←block_zero_nat x k,Function.update_eq_self]
    congr 2

theorem reverseTape_at_head (x : List Bool) (k : Nat) :
    reverseTape x (k+1) (k : Int) = inputTape machine x (k : Int) := by
  simp only [reverseTape,if_neg (show ¬((k+1:Nat):Int) ≤ (k:Int) from by omega),block_zero_nat]

theorem output_low (x : List Bool) (k : Nat) (hk : k < (normalizeBits x).length) :
    inputTape machine (normalizeBits x) (k : Int) = inputTape machine x (k : Int) := by
  have hx : k < x.length := lt_of_lt_of_le hk (normalize_length x)
  rw [inputTape_ofNat machine (normalizeBits x) k hk,inputTape_ofNat machine x k hx]
  have he := low_get x k hk
  rw [List.getElem?_eq_getElem hx,List.getElem?_eq_getElem hk] at he
  rw [Option.some.inj he]

theorem reverseTape_write (x : List Bool) (k : Nat) :
    Function.update (reverseTape x (k+1)) (k : Int)
      (inputTape machine (normalizeBits x) (k : Int)) = reverseTape x k := by
  funext z
  by_cases hz : z=(k:Int)
  · subst z; simp [reverseTape,block_zero_nat]
  · have hc : (((k+1:Nat):Int) ≤ z) ↔ ((k:Int) ≤ z) := by omega
    simp only [Function.update_of_ne hz,reverseTape,hc]

theorem reverseTape_zero (x : List Bool) : reverseTape x 0 = blockTape (normalizeBits x) 0 := by
  funext z
  by_cases hz : 0 ≤ z
  · simp [reverseTape,hz]
  · have hn : z<0 := by omega
    simp [reverseTape,hz,blockTape,inputTape_neg machine x z hn,
      inputTape_neg machine (normalizeBits x) z hn]

theorem reverseTape_length (x : List Bool) : reverseTape x x.length = blockTape x 0 := by
  funext z
  by_cases hz : (x.length:Int) ≤ z
  · have hn : ((normalizeBits x).length:Int) ≤ z := by
      have := normalize_length x; omega
    have hL : z≠-1 := by omega
    simp only [reverseTape,if_pos hz,blockTape,if_neg hL,Int.natCast_zero,sub_zero]
    rw [inputTape_ge machine x z hz,inputTape_ge machine (normalizeBits x) z hn]
  · simp [reverseTape,hz]

theorem scan_turn (x : List Bool) : step machine 0 (scanConfig x x.length) =
    some (returnConfig x x.length) := by
  have hread : inputTape machine x (x.length:Int)=2 :=
    inputTape_ge machine x (x.length:Int) le_rfl
  simp only [step,scanConfig,block_zero_nat,hread,rule_scan_blank,Option.map_some,writtenTape,moveHead]
  rw [←hread,←block_zero_nat x x.length,Function.update_eq_self]
  simp only [returnConfig,if_pos (normalize_length x),reverseTape_length]

theorem return_step (x : List Bool) (k : Nat) (hk : k < x.length) :
    step machine 0 (returnConfig x (k+1)) = some (returnConfig x k) := by
  have hhead : ((k+1:Nat):Int)-1=(k:Int) := by omega
  have hread : inputTape machine x (k:Int)=bit x[k] := inputTape_ofNat machine x k hk
  have hlow := normalize_length x
  by_cases hge : (normalizeBits x).length ≤ k
  · have hstate : (normalizeBits x).length ≤ k+1 := by omega
    have hb : x[k]=false := by
      have h := high_get x k hge hk
      rw [List.getElem?_eq_getElem hk] at h
      exact Option.some.inj h
    have hr0 : inputTape machine x (k:Int)=0 := by rw [hread,hb]; rfl
    have hout : inputTape machine (normalizeBits x) (k:Int)=2 :=
      inputTape_ge machine (normalizeBits x) (k:Int) (by omega)
    simp only [step,returnConfig,if_pos hstate,hhead,reverseTape_at_head,hr0,
      machine_zero,rule_trim_zero,Option.map_some,writtenTape,moveHead]
    rw [←hout,reverseTape_write]
    simp only [if_pos hge]
  · have hlt : k < (normalizeBits x).length := by omega
    have hout := output_low x k hlt
    by_cases he : (normalizeBits x).length=k+1
    · have hstate : (normalizeBits x).length ≤ k+1 := by omega
      have hb : x[k]=true := by
        have hl : (normalizeBits x)[k]? = some true := by
          have h := normalized_last x (by omega)
          rw [he,Nat.add_sub_cancel] at h
          exact h
        have h := (low_get x k hlt).trans hl
        rw [List.getElem?_eq_getElem hk] at h
        exact Option.some.inj h
      have hr1 : inputTape machine x (k:Int)=1 := by rw [hread,hb]; rfl
      simp only [step,returnConfig,if_pos hstate,hhead,reverseTape_at_head,hr1,
        machine_one,rule_trim_one,Option.map_some,writtenTape,moveHead]
      rw [←hr1,←hout,reverseTape_write]
      simp only [if_neg hge]
    · have hstate : ¬(normalizeBits x).length ≤ k+1 := by omega
      simp only [step,returnConfig,if_neg hstate,hhead,reverseTape_at_head,hread,
        rule_return_bit,Option.map_some,writtenTape,moveHead]
      rw [←hread,←hout,reverseTape_write]
      simp only [if_neg hge]

theorem return_run (x : List Bool) (k : Nat) (hk : k ≤ x.length) :
    run machine (ticks k) (returnConfig x k) = some (returnConfig x 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change run machine (0::ticks k) (returnConfig x (k+1)) = _
    rw [run_cons,return_step x k (by omega),Option.bind_some]
    exact ih (by omega)

theorem return_finish (x : List Bool) : step machine 0 (returnConfig x 0) =
    some (finalConfig x) := by
  have hq : (if (normalizeBits x).length ≤ 0 then 37 else 38 : Fin 64)=37 ∨
      (if (normalizeBits x).length ≤ 0 then 37 else 38 : Fin 64)=38 := by split <;> simp
  simp only [step,returnConfig,Nat.cast_zero,zero_sub,reverseTape_zero,block_L,
    rule_finish _ hq,Option.map_some,writtenTape,moveHead]
  rw [block_zero_erase]
  rfl

theorem normalize_run (x : List Bool) : run machine (ticks (2*x.length+2))
    (scanConfig x 0) = some (finalConfig x) := by
  have ht : 2*x.length+2=x.length+1+x.length+1 := by omega
  rw [ht,ticks_add,ticks_add,ticks_add,run_append,run_append,run_append,
    scan_run x x.length le_rfl,Option.bind_some,run_ticks_one,scan_turn,
    Option.bind_some,return_run x x.length le_rfl,Option.bind_some,run_ticks_one]
  exact return_finish x

theorem normalization_spec (x : List Bool) :
    run machine (ticks (2*x.length+2)) (scanConfig x 0)=some (finalConfig x) ∧
    Output machine (normalizeBits x) (finalConfig x) ∧
    normalizeBits x=encodeNat (PakFixedWeightedStandardBinaryCount.value x) :=
  ⟨normalize_run x,⟨rfl,rfl,rfl⟩,normalize_eq_encodeNat x⟩

end PakFixedPolyomino.StandardBitVariableAddNormalize
