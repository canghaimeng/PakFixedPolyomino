import PakFixedPolyomino.StandardBitVariableAddShift

/-! Entire-tape erasure, left shifting and normalization from the exact
ripple boundary of the frozen64/32 adder. -/
namespace PakFixedPolyomino.StandardBitVariableAddCleanup
open StandardNondeterministicMachine StandardBitTime
open StandardBitVariableAdd (machine Epos D)
open StandardBitVariableAddRippleInterface (resultTape resultTape_L resultTape_E)
open StandardBitVariableAddTape
open StandardBitVariableAddShift (keep_step inspect_empty inspect_normalize)
open FiniteOneTapeSemantics (moveHead writtenTape)

theorem input_not_E (v : List Bool) (z : Int) : inputTape machine v z≠5 := by
  simp only [inputTape]
  split_ifs <;> decide

theorem result_not_L (x y v : List Bool) (i : Nat) : resultTape x y v (i : Int)≠3 := by
  simp only [resultTape,if_neg (show (i : Int)≠-1 by omega),
    if_pos (show (0 : Int)≤(i : Int) by omega),Int.toNat_natCast]
  split_ifs <;> first | decide | exact input_not_L v _

theorem result_not_E (x y v : List Bool) (i : Nat) (hi : i≠Epos x y) :
    resultTape x y v (i : Int)≠5 := by
  simp only [resultTape,if_neg (show (i : Int)≠-1 by omega),
    if_pos (show (0 : Int)≤(i : Int) by omega),Int.toNat_natCast,if_neg hi]
  split_ifs <;> first | decide | exact input_not_E v _

theorem result_neg (x y v : List Bool) (z : Int) (hz : z<0) (hL : z≠-1) :
    resultTape x y v z=2 := by simp only [resultTape,if_neg hL,if_neg (show ¬0≤z by omega)]

theorem result_ge (x y v : List Bool) (z : Int) (hz : (Epos x y+1 : Nat)≤z) :
    resultTape x y v z=blockTape v (Epos x y+1) z := by
  have hE : 2*x.length<Epos x y := by simp [Epos,D];omega
  have hL : z≠-1 := by omega
  have hpos : 0≤z := by omega
  have h2l : ¬z.toNat<2*x.length := by omega
  have h2e : z.toNat≠2*x.length := by omega
  have hel : ¬z.toNat<Epos x y := by omega
  have hee : z.toNat≠Epos x y := by omega
  simp only [resultTape,if_neg hL,if_pos hpos,if_neg h2l,if_neg h2e,if_neg hel,if_neg hee,
    blockTape]

def wipeTape (x y v : List Bool) (k : Nat) (z : Int) : Fin 32 :=
  if 0≤z ∧ z.toNat<k then 2 else resultTape x y v z

theorem wipe_zero (x y v : List Bool) : wipeTape x y v 0=resultTape x y v := by
  funext z;simp [wipeTape]

theorem wipe_read (x y v : List Bool) (k : Nat) :
    wipeTape x y v k (k : Int)=resultTape x y v (k : Int) := by
  simp only [wipeTape,Int.toNat_natCast,Nat.lt_irrefl,and_false,if_false]

theorem wipe_write (x y v : List Bool) (k : Nat) :
    Function.update (wipeTape x y v k) (k : Int) 2=wipeTape x y v (k+1) := by
  funext z
  by_cases hz : z=(k : Int)
  · subst z;simp [wipeTape]
  · rw [Function.update_of_ne hz]
    have he : (0≤z ∧ z.toNat<k) ↔ (0≤z ∧ z.toNat<k+1) := by
      by_cases hp : 0≤z
      · have ht := Int.toNat_of_nonneg hp
        have hn : z.toNat≠k := by intro h;apply hz;omega
        omega
      · simp [hp]
    simp only [wipeTape,he]

theorem wipe_final (x y v : List Bool) :
    wipeTape x y v (Epos x y+1)=blockTape v (Epos x y+1) := by
  funext z
  by_cases hL : z=-1
  · subst z;simp [wipeTape,resultTape_L,block_L]
  · by_cases hz : 0≤z
    · by_cases hk : z.toNat<Epos x y+1
      · rw [wipeTape,if_pos ⟨hz,hk⟩,block_before v _ z hL (by omega)]
      · rw [wipeTape,if_neg (by omega : ¬(0≤z ∧ z.toNat<Epos x y+1))]
        exact result_ge x y v z (by omega)
    · rw [wipeTape,if_neg (by omega : ¬(0≤z ∧ z.toNat<Epos x y+1)),
        result_neg x y v z (by omega) hL,block_before v _ z hL (by omega)]

def wipeConfig (x y v : List Bool) (k : Nat) : Configuration 64 32 :=
  ⟨27,(k : Int),wipeTape x y v k⟩

theorem wipe_step (x y v : List Bool) (k : Nat) (hk : k<Epos x y) :
    step machine 0 (wipeConfig x y v k)=some (wipeConfig x y v (k+1)) := by
  have ht : wipeTape x y v k (k : Int)≠5 := by rw [wipe_read];exact result_not_E x y v k (by omega)
  have hr := StandardBitVariableAdd.rule_wipe_notE _ ht
  simp only [step,wipeConfig,hr,Option.map_some,writtenTape,moveHead]
  rw [wipe_write]
  congr 2

theorem wipe_run (x y v : List Bool) (k : Nat) (hk : k≤Epos x y) :
    run machine (ticks k) (wipeConfig x y v 0)=some (wipeConfig x y v k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ticks_add,run_append,ih (by omega),Option.bind_some,run_ticks_one]
    exact wipe_step x y v k (by omega)

theorem wipe_end (x y v : List Bool) :
    step machine 0 (wipeConfig x y v (Epos x y))=
      some ⟨28,(Epos x y+1 : Nat),blockTape v (Epos x y+1)⟩ := by
  simp only [step,wipeConfig,wipe_read,resultTape_E,StandardBitVariableAdd.rule_wipe_E,
    Option.map_some,writtenTape,moveHead]
  rw [wipe_write,wipe_final]
  congr 2

theorem seek_result (x y v : List Bool) :
    run machine (ticks (Epos x y+2)) ⟨26,(Epos x y : Int),resultTape x y v⟩=
      some ⟨27,0,resultTape x y v⟩ := by
  have hs := StandardBitMarkedCompaction.scan_left machine 26 (resultTape x y v)
    (Epos x y : Int) (Epos x y+1) (by
      intro i hi
      have hh : (Epos x y : Int)-(i : Int)=((Epos x y-i : Nat) : Int) := by omega
      rw [hh]
      exact StandardBitVariableAdd.rule_wipeSeek_notL _ (result_not_L x y v _))
  rw [show (Epos x y : Int)-((Epos x y+1 : Nat) : Int)=(-1 : Int) by omega] at hs
  have hh := keep_step 26 27 (resultTape x y v) (-1) .right (by
    rw [resultTape_L];rfl)
  have hf : Epos x y+2=(Epos x y+1)+1 := by omega
  rw [hf,ticks_add,run_append,hs,Option.bind_some,run_ticks_one]
  exact hh

theorem wipe_result (x y v : List Bool) :
    run machine (ticks (2*Epos x y+3)) ⟨26,(Epos x y : Int),resultTape x y v⟩=
      some ⟨28,(Epos x y+1 : Nat),blockTape v (Epos x y+1)⟩ := by
  have hf : 2*Epos x y+3=(Epos x y+2)+Epos x y+1 := by omega
  have hr := wipe_run x y v (Epos x y) (by rfl)
  simp only [wipeConfig,Nat.cast_zero,wipe_zero] at hr
  rw [hf,ticks_add,ticks_add,run_append,run_append,seek_result,Option.bind_some,hr,
    Option.bind_some,run_ticks_one]
  exact wipe_end x y v

def cleanupFuel (x y v : List Bool) : Nat :=
  2*Epos x y+3 + if v=[] then Epos x y+3 else 1+(Epos x y+2)*(2*v.length+3)

theorem cleanup_run (x y v : List Bool) :
    run machine (ticks (cleanupFuel x y v)) ⟨26,(Epos x y : Int),resultTape x y v⟩=
      some (StandardBitVariableAddNormalize.finalConfig v) := by
  induction v using List.reverseRecOn with
  | nil =>
    rw [cleanupFuel,if_pos rfl,ticks_add,run_append,wipe_result,Option.bind_some]
    simpa only [Nat.add_assoc] using inspect_empty (Epos x y+1)
  | append_singleton u b ih =>
    have hn : u++[b]≠[] := by simp
    rw [cleanupFuel,if_neg hn,ticks_add,run_append,wipe_result,Option.bind_some]
    simpa only [Nat.add_assoc] using inspect_normalize u b (Epos x y+1)

theorem cleanupFuel_le (x y v : List Bool) :
    cleanupFuel x y v ≤
      64*((StandardBitMetric.pairBits x y).length+v.length+1)*
        ((StandardBitMetric.pairBits x y).length+v.length+1) := by
  have he : Epos x y=(StandardBitMetric.pairBits x y).length := by
    simp [Epos,D,StandardBitMetric.pairBits_length]
  unfold cleanupFuel
  rw [he]
  split_ifs <;>
    nlinarith [Nat.zero_le ((StandardBitMetric.pairBits x y).length^2),
      Nat.zero_le (v.length^2),Nat.zero_le ((StandardBitMetric.pairBits x y).length*v.length)]

theorem cleanup_spec (x y v : List Bool) :
    run machine (ticks (cleanupFuel x y v)) ⟨26,(Epos x y : Int),resultTape x y v⟩=
      some (StandardBitVariableAddNormalize.finalConfig v) ∧
    cleanupFuel x y v ≤
      64*((StandardBitMetric.pairBits x y).length+v.length+1)*
        ((StandardBitMetric.pairBits x y).length+v.length+1) ∧
    Output machine (StandardBinaryWordNormalization.normalizeBits v)
      (StandardBitVariableAddNormalize.finalConfig v) ∧
    StandardBinaryWordNormalization.normalizeBits v=
      Computability.encodeNat (PakFixedWeightedStandardBinaryCount.value v) :=
  ⟨cleanup_run x y v,cleanupFuel_le x y v,
    (StandardBitVariableAddNormalize.normalization_spec v).2⟩

end PakFixedPolyomino.StandardBitVariableAddCleanup
