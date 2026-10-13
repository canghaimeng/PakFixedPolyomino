import PakFixedPolyomino.StandardBinaryWordNormalization
import PakFixedPolyomino.StandardBitTime

/-! Literal fixed finite-tape normalization: scan right, erase high zeros,
then return over retained bits. Every raw word has the same 2*n+2 bound. -/
namespace PakFixedPolyomino.StandardBitNormalize
open Computability StandardBinaryWordNormalization
open StandardNondeterministicMachine StandardBitTime
open FiniteOneTapeSemantics (moveHead writtenTape)

def machine : DeterministicMachine 5 3 where
  rule q a _ :=
    if q = 2 then
      if a = 2 then some ⟨2,3,.left⟩ else some ⟨a,2,.right⟩
    else if q = 3 then
      if a = 2 then some ⟨2,0,.right⟩
      else if a = 0 then some ⟨2,3,.left⟩ else some ⟨a,4,.left⟩
    else if q = 4 then
      if a = 2 then some ⟨2,0,.right⟩ else some ⟨a,4,.left⟩
    else none
  start := 2
  accept := 0
  reject := 1
  accept_ne_reject := by decide
  blank := 2
  zero := 0
  one := 1
  blank_ne_zero := by decide
  blank_ne_one := by decide
  zero_ne_one := by decide
  accept_terminal := by intros; simp
  reject_terminal := by intros; simp

@[simp] theorem machine_zero : machine.zero = 0 := rfl
@[simp] theorem machine_one : machine.one = 1 := rfl
@[simp] theorem machine_blank : machine.blank = 2 := rfl

abbrev bit (b : Bool) : Fin 3 := if b then 1 else 0

theorem rule_scan_bit (b : Bool) : machine.rule 2 (bit b) 0 =
    some ⟨bit b,2,.right⟩ := by cases b <;> rfl

theorem rule_scan_blank : machine.rule 2 2 0 = some ⟨2,3,.left⟩ := rfl

theorem rule_trim_zero : machine.rule 3 0 0 = some ⟨2,3,.left⟩ := rfl

theorem rule_trim_one : machine.rule 3 1 0 = some ⟨1,4,.left⟩ := rfl

theorem rule_return_bit (b : Bool) : machine.rule 4 (bit b) 0 =
    some ⟨bit b,4,.left⟩ := by cases b <;> rfl

theorem rule_finish (q : Fin 5) (hq : q=3 ∨ q=4) :
    machine.rule q 2 0 = some ⟨2,0,.right⟩ := by
  rcases hq with rfl | rfl <;> rfl

theorem low_get (x : List Bool) (i : Nat) (hi : i < (normalizeBits x).length) :
    x[i]? = (normalizeBits x)[i]? := by
  obtain ⟨k,hk⟩ := normalize_zero_suffix x
  conv_lhs => rw [hk]
  rw [List.getElem?_append_left hi]

theorem high_get (x : List Bool) (i : Nat)
    (hi : (normalizeBits x).length ≤ i) (hx : i < x.length) : x[i]? = some false := by
  obtain ⟨k,hk⟩ := normalize_zero_suffix x
  have hlen := congrArg List.length hk
  simp only [List.length_append,List.length_replicate] at hlen
  conv_lhs => rw [hk]
  rw [List.getElem?_append_right hi, List.getElem?_replicate]
  simp [show i - (normalizeBits x).length < k from by omega]

theorem encodePosNum_last (n : PosNum) : ∃ y, encodePosNum n = y ++ [true] := by
  induction n with
  | one => exact ⟨[],rfl⟩
  | bit0 n ih => obtain ⟨y,hy⟩ := ih; exact ⟨false::y,congrArg (List.cons false) hy⟩
  | bit1 n ih => obtain ⟨y,hy⟩ := ih; exact ⟨true::y,congrArg (List.cons true) hy⟩

theorem normalized_last (x : List Bool) (h : 0 < (normalizeBits x).length) :
    (normalizeBits x)[(normalizeBits x).length-1]? = some true := by
  rw [normalize_eq_encodeNum] at h ⊢
  cases hn : rawNum x with
  | zero => simp [hn, encodeNum] at h
  | pos n =>
    obtain ⟨y,hy⟩ := encodePosNum_last n
    simp only [hn,encodeNum,hy,List.length_append,List.length_singleton,
      Nat.add_sub_cancel]
    rw [List.getElem?_append_right (by omega)]
    simp

def scanConfig (x : List Bool) (k : Nat) : Configuration 5 3 :=
  ⟨2,k,inputTape machine x⟩

/-- Only cells at or to the right of the sweep boundary have been finalized. -/
def reverseTape (x : List Bool) (k : Nat) (z : Int) : Fin 3 :=
  if (k : Int) ≤ z then inputTape machine (normalizeBits x) z
  else inputTape machine x z

def returnConfig (x : List Bool) (k : Nat) : Configuration 5 3 :=
  ⟨if (normalizeBits x).length ≤ k then 3 else 4,(k : Int)-1,reverseTape x k⟩

def finalConfig (x : List Bool) : Configuration 5 3 :=
  ⟨0,0,inputTape machine (normalizeBits x)⟩

theorem scan_run (x : List Bool) (k : Nat) (hk : k ≤ x.length) :
    run machine (ticks k) (initial machine x) = some (scanConfig x k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ticks_add k 1,run_append,ih (by omega),Option.bind_some,run_ticks_one]
    have hread : inputTape machine x (k:Int)=bit x[k] :=
      inputTape_ofNat machine x k (by omega : k < x.length)
    simp only [step,scanConfig,hread,rule_scan_bit,Option.map_some,moveHead,writtenTape]
    rw [←hread,Function.update_eq_self]
    congr 2

theorem reverseTape_at_head (x : List Bool) (k : Nat) :
    reverseTape x (k+1) (k : Int) = inputTape machine x (k : Int) := by
  simp [reverseTape,show ¬((k+1:Nat):Int) ≤ (k:Int) from by omega]

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
  · subst z; simp [reverseTape]
  · have hc : (((k+1:Nat):Int) ≤ z) ↔ ((k:Int) ≤ z) := by omega
    simp only [Function.update_of_ne hz,reverseTape,hc]

theorem reverseTape_zero (x : List Bool) : reverseTape x 0 =
    inputTape machine (normalizeBits x) := by
  funext z
  by_cases hz : 0 ≤ z
  · simp [reverseTape,hz]
  · have hn : z<0 := by omega
    simp [reverseTape,hz,inputTape_neg machine x z hn,
      inputTape_neg machine (normalizeBits x) z hn]

theorem reverseTape_length (x : List Bool) : reverseTape x x.length = inputTape machine x := by
  funext z
  by_cases hz : (x.length:Int) ≤ z
  · have hn : ((normalizeBits x).length:Int) ≤ z := by
      have := normalize_length x; omega
    simp [reverseTape,hz,inputTape_ge machine x z hz,
      inputTape_ge machine (normalizeBits x) z hn]
  · simp [reverseTape,hz]

theorem scan_turn (x : List Bool) : step machine 0 (scanConfig x x.length) =
    some (returnConfig x x.length) := by
  have hread : inputTape machine x (x.length:Int)=2 :=
    inputTape_ge machine x (x.length:Int) le_rfl
  simp only [step,scanConfig,hread,rule_scan_blank,Option.map_some,writtenTape,moveHead]
  rw [←hread,Function.update_eq_self]
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
  have hq : (if (normalizeBits x).length ≤ 0 then 3 else 4 : Fin 5)=3 ∨
      (if (normalizeBits x).length ≤ 0 then 3 else 4 : Fin 5)=4 := by split <;> simp
  have hread : inputTape machine (normalizeBits x) (-1)=2 :=
    inputTape_neg machine (normalizeBits x) (-1) (by omega)
  simp only [step,returnConfig,Nat.cast_zero,zero_sub,reverseTape_zero,hread,
    rule_finish _ hq,Option.map_some,writtenTape,moveHead]
  rw [←hread,Function.update_eq_self]
  rfl

theorem normalize_run (x : List Bool) : run machine (ticks (2*x.length+2))
    (initial machine x) = some (finalConfig x) := by
  have ht : 2*x.length+2=x.length+1+x.length+1 := by omega
  rw [ht,ticks_add,ticks_add,ticks_add,run_append,run_append,run_append,
    scan_run x x.length le_rfl,Option.bind_some,run_ticks_one,scan_turn,
    Option.bind_some,return_run x x.length le_rfl,Option.bind_some,run_ticks_one]
  exact return_finish x

theorem normalize_computes : ComputesWithin machine normalizeBits (fun n=>2*n+2) := by
  intro x
  exact ⟨2*x.length+2,finalConfig x,le_rfl,normalize_run x,rfl,rfl,rfl⟩

theorem normalize_polyBitTime : PolyBitTime normalizeBits := by
  refine ⟨5,3,machine,Polynomial.C 2*Polynomial.X+Polynomial.C 2,?_⟩
  simpa using normalize_computes

theorem normalization_exact :
    (∀ x, normalizeBits x = encodeNat (PakFixedWeightedStandardBinaryCount.value x)) ∧
    (∀ x, run machine (ticks (2*x.length+2)) (initial machine x)=some (finalConfig x)) ∧
    ComputesWithin machine normalizeBits (fun n=>2*n+2) ∧ PolyBitTime normalizeBits :=
  ⟨normalize_eq_encodeNat,normalize_run,normalize_computes,normalize_polyBitTime⟩

end PakFixedPolyomino.StandardBitNormalize
