import PakFixedPolyomino.StandardBitRetainedPairAnswer

/-! Entire-tape cleanup of the completed physical pairing stage. -/
namespace PakFixedPolyomino.StandardBitRetainedPairCleanup
open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open StandardBitRetainedPairStage StandardBitRetainedPairCounter
open StandardBitRetainedPairSeparator StandardBitRetainedPairAnswer
open StandardBitProtectedCleanup (rawTape rawBit)
open StandardBitMarkedCompaction (scan_left)
open FiniteOneTapeSemantics (moveHead writtenTape)
variable {ns nt : Nat}

set_option maxHeartbeats 800000

def dirtyTape (M : DeterministicMachine ns nt) (x y u : List Bool) : Int → Alphabet nt :=
  answerTape M x y u y.length
def cleanupWidth (x y u : List Bool) : Nat :=
  max (pairBits x y).length (pairBits u y).length

theorem dirty_phase (M : DeterministicMachine ns nt) (x y u : List Bool) :
    dirtyTape M x y u=answerPhaseTape M x y u y.length (pairBits u y) := by
  simp only [dirtyTape,answerTape,List.take_length]

theorem raw_ge (v : List Bool) (i : Nat) (hi : v.length ≤ i) : rawTape v (i : Int)=2 := by
  simp only [rawTape,Int.natCast_nonneg,Int.toNat_natCast,Nat.not_lt.mpr hi,dite_true,dite_false]

theorem inputTape_joint (M : DeterministicMachine ns nt) (v : List Bool) (z : Int) :
    inputTape (machine M) v z=joint 2 (inputTape M v z) 0 2 := by
  simp only [inputTape,machine]
  split_ifs <;> rfl

theorem raw_decode (M : DeterministicMachine ns nt) (v : List Bool) (z : Int) :
    (if rawTape v z=0 then M.zero else if rawTape v z=1 then M.one else M.blank)=
      inputTape M v z := by
  by_cases hz : 0≤z
  · by_cases hi : z.toNat<v.length
    · simp only [rawTape,inputTape,hz,hi,dite_true]
      cases v[z.toNat] <;> rfl
    · simp [rawTape,inputTape,hz,hi]
  · simp [rawTape,inputTape,hz]

theorem cleanCell_answer (M : DeterministicMachine ns nt) (x y u v : List Bool)
    (j : Nat) (z : Int) (hL : z≠-1) :
    cleanCell M (answerPhaseTape M x y u j v z)=inputTape (machine M) v z := by
  rw [cleanCell,answer_output,phase_output M _ u v u.length z hL,raw_decode,inputTape_joint]

theorem dirty_L (M : DeterministicMachine ns nt) (x y u : List Bool) :
    dirtyTape M x y u (-1)=joint 2 M.blank 0 3 := by rw [dirty_phase,answer_L]

theorem dirty_neg (M : DeterministicMachine ns nt) (x y u : List Bool)
    (z : Int) (hz : z<0) (hL : z≠-1) : dirtyTape M x y u z=blank M := by
  have hmask : ¬ (((2*x.length : Nat) : Int)≤z ∧
    z<((2*x.length+1+y.length : Nat) : Int)) := by omega
  rw [dirty_phase]
  simp only [answerPhaseTape,if_neg hmask,phaseTape,if_neg hL,rawTape,
    show ¬ 0≤z by omega,dite_false,false_and,if_false,inputTape_neg M u z hz]
  rfl

theorem dirty_ge (M : DeterministicMachine ns nt) (x y u : List Bool)
    (i : Nat) (hi : cleanupWidth x y u ≤ i) : dirtyTape M x y u (i : Int)=blank M := by
  have hr : (pairBits x y).length ≤ i := (Nat.le_max_left _ _).trans hi
  have hv : (pairBits u y).length ≤ i := (Nat.le_max_right _ _).trans hi
  have hu : u.length ≤ i := by have hlen := pairBits_length u y;omega
  have hmask : ¬ (((2*x.length : Nat) : Int)≤(i : Int) ∧
    (i : Int)<((2*x.length+1+y.length : Nat) : Int)) := by
    have hlen := pairBits_length x y;omega
  rw [dirty_phase]
  simp only [answerPhaseTape,if_neg hmask,phaseTape,if_neg (show (i : Int)≠-1 by omega),
    raw_ge _ i hr,raw_ge _ i hv,inputTape_ge M u i (by omega),
    Int.natCast_nonneg,Int.toNat_natCast,true_and,if_neg (Nat.not_lt.mpr hu)]
  rfl

theorem dirty_nonblank (M : DeterministicMachine ns nt) (x y u : List Bool)
    (i : Nat) (hi : i<cleanupWidth x y u) : dirtyTape M x y u (i : Int)≠blank M := by
  by_cases hr : i<(pairBits x y).length
  · have hn : raw (dirtyTape M x y u (i : Int))≠2 := by
      rw [dirty_phase]
      by_cases hm : ((2*x.length : Nat) : Int)≤(i : Int) ∧
        (i : Int)<((2*x.length+1+y.length : Nat) : Int)
      · rw [answer_raw_marked M x y u _ y.length _ hm];decide
      · rw [answer_raw_unmarked M x y u _ y.length i hm]
        simp only [rawTape,Int.natCast_nonneg,Int.toNat_natCast,hr,dite_true]
        exact StandardBitProtectedCleanup.rawBit_ne_blank _
    intro he
    apply hn
    simpa only [blank,raw_joint] using congrArg raw he
  · have hv : i<(pairBits u y).length := by unfold cleanupWidth at hi;omega
    have hn : output (dirtyTape M x y u (i : Int))≠2 := by
      rw [dirty_phase,answer_output,phase_output M _ u _ u.length _ (by omega)]
      simp only [rawTape,Int.natCast_nonneg,Int.toNat_natCast,hv,dite_true]
      exact StandardBitProtectedCleanup.rawBit_ne_blank _
    intro he
    apply hn
    simpa only [blank,output_joint] using congrArg output he

def sweepTape (M : DeterministicMachine ns nt) (x y u : List Bool) (k : Nat)
    (z : Int) : Alphabet nt :=
  if 0≤z ∧ z.toNat<k then inputTape (machine M) (pairBits u y) z else dirtyTape M x y u z
def sweepConfig (M : DeterministicMachine ns nt) (x y u : List Bool) (k : Nat) :
    Configuration 30 (4*(2*(4*nt))) := ⟨27,(k : Int),sweepTape M x y u k⟩

theorem sweep_zero (M : DeterministicMachine ns nt) (x y u : List Bool) :
    sweepTape M x y u 0=dirtyTape M x y u := by funext z;simp [sweepTape]

theorem sweep_read (M : DeterministicMachine ns nt) (x y u : List Bool) (k : Nat) :
    sweepTape M x y u k (k : Int)=dirtyTape M x y u (k : Int) := by simp [sweepTape]

theorem sweep_write (M : DeterministicMachine ns nt) (x y u : List Bool) (k : Nat) :
    Function.update (sweepTape M x y u k) (k : Int)
      (cleanCell M (sweepTape M x y u k (k : Int)))=sweepTape M x y u (k+1) := by
  funext z
  by_cases hz : z=(k : Int)
  · subst z
    rw [Function.update_self,sweep_read,dirty_phase,cleanCell_answer M x y u _ y.length _ (by omega)]
    simp [sweepTape]
  · rw [Function.update_of_ne hz]
    have he : (0≤z ∧ z.toNat<k) ↔ (0≤z ∧ z.toNat<k+1) := by
      by_cases hp : 0≤z
      · have ht := Int.toNat_of_nonneg hp
        have hn : z.toNat≠k := by intro h;apply hz;omega
        omega
      · simp [hp]
    simp only [sweepTape,he]

theorem sweep_step (M : DeterministicMachine ns nt) (x y u : List Bool)
    (k : Nat) (hk : k<cleanupWidth x y u) :
    step (machine M) 0 (sweepConfig M x y u k)=some (sweepConfig M x y u (k+1)) := by
  have hn : sweepTape M x y u k (k : Int)≠blank M := by
    rw [sweep_read];exact dirty_nonblank M x y u k hk
  have hr : (machine M).rule 27 (sweepTape M x y u k (k : Int)) 0=
      some ⟨cleanCell M (sweepTape M x y u k (k : Int)),27,.right⟩ := by simp [machine,hn]
  simp only [sweepConfig,step,hr,Option.map_some,writtenTape,moveHead]
  rw [sweep_write]
  simp only [Nat.cast_add,Nat.cast_one]

theorem sweep_run (M : DeterministicMachine ns nt) (x y u : List Bool)
    (k : Nat) (hk : k≤cleanupWidth x y u) :
    run (machine M) (ticks k) (sweepConfig M x y u 0)=some (sweepConfig M x y u k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ticks_add,run_append,ih (by omega),Option.bind_some,run_ticks_one]
    exact sweep_step M x y u k (by omega)

def sentinelCleanTape (M : DeterministicMachine ns nt) (v : List Bool) : Int → Alphabet nt :=
  Function.update (inputTape (machine M) v) (-1) (joint 2 M.blank 0 3)

theorem sweep_final (M : DeterministicMachine ns nt) (x y u : List Bool) :
    sweepTape M x y u (cleanupWidth x y u)=sentinelCleanTape M (pairBits u y) := by
  funext z
  by_cases hL : z=(-1 : Int)
  · subst z;simp [sweepTape,sentinelCleanTape,dirty_L]
  · rw [sentinelCleanTape,Function.update_of_ne hL]
    by_cases hz : 0≤z
    · by_cases hk : z.toNat<cleanupWidth x y u
      · simp only [sweepTape,hz,hk,and_self,if_true]
      · have he : (z.toNat : Int)=z := Int.toNat_of_nonneg hz
        have hn : cleanupWidth x y u≤z.toNat := by omega
        have hv : (pairBits u y).length≤z.toNat := (Nat.le_max_right _ _).trans hn
        simp only [sweepTape,hz,hk,true_and,if_false]
        rw [← he,dirty_ge M x y u z.toNat hn,inputTape_ge (machine M) (pairBits u y) z.toNat (by omega)]
        rfl
    · simp only [sweepTape,hz,false_and,if_false]
      rw [dirty_neg M x y u z (by omega) hL,inputTape_neg (machine M) _ z (by omega)]
      rfl

theorem sentinel_output (M : DeterministicMachine ns nt) (v : List Bool) (i : Nat) :
    output (sentinelCleanTape M v (i : Int))=2 := by
  rw [sentinelCleanTape,Function.update_of_ne (show (i : Int)≠-1 by omega),inputTape_joint,output_joint]

theorem sentinel_erase (M : DeterministicMachine ns nt) (v : List Bool) :
    Function.update (sentinelCleanTape M v) (-1) (blank M)=inputTape (machine M) v := by
  rw [sentinelCleanTape,Function.update_idem]
  apply Function.update_eq_self_iff.mpr
  rw [inputTape_neg (machine M) v (-1) (by omega)]
  rfl

theorem cleanup_return (M : DeterministicMachine ns nt) (v : List Bool) (a : Nat) :
    run (machine M) (ticks (a+1)) ⟨28,(a : Int)-1,sentinelCleanTape M v⟩=
      some (finalConfig M v) := by
  have hs := scan_left (M:=machine M) (q:=28) (t:=sentinelCleanTape M v)
    (h:=(a : Int)-1) (n:=a) (by
      intro i hi
      have hz : (a : Int)-1-(i : Int)=((a-1-i : Nat) : Int) := by omega
      rw [hz]
      simp [machine,sentinel_output])
  rw [show (a : Int)-1-(a : Int)=(-1 : Int) by omega] at hs
  rw [ticks_add,run_append,hs,Option.bind_some,run_ticks_one]
  have hr : (machine M).rule 28 (sentinelCleanTape M v (-1)) 0=
      some ⟨blank M,0,.right⟩ := by simp [machine,sentinelCleanTape,output_joint]
  simp only [step,hr,Option.map_some,writtenTape,moveHead,finalConfig]
  rw [sentinel_erase]
  rfl

theorem sweep_halt (M : DeterministicMachine ns nt) (x y u : List Bool) :
    step (machine M) 0 (sweepConfig M x y u (cleanupWidth x y u))=
      some ⟨28,(cleanupWidth x y u : Int)-1,sentinelCleanTape M (pairBits u y)⟩ := by
  have he : sweepTape M x y u (cleanupWidth x y u) (cleanupWidth x y u : Int)=blank M := by
    rw [sweep_read];exact dirty_ge M x y u _ (by rfl)
  have hs := stage_preserve M 27 28 (sweepTape M x y u (cleanupWidth x y u))
    (cleanupWidth x y u : Int) .left (by simp [machine,he])
  simpa only [sweepConfig,moveHead,sweep_final] using hs

theorem cleanup_sweep_run (M : DeterministicMachine ns nt) (x y u : List Bool) :
    run (machine M) (ticks (2*cleanupWidth x y u+2)) ⟨27,0,dirtyTape M x y u⟩=
      some (finalConfig M (pairBits u y)) := by
  have ht : ticks (2*cleanupWidth x y u+2)=ticks (cleanupWidth x y u)++ticks 1++
      ticks (cleanupWidth x y u+1) := by
    rw [show 2*cleanupWidth x y u+2=cleanupWidth x y u+1+(cleanupWidth x y u+1) by omega]
    simp only [ticks_add,List.append_assoc]
  rw [ht,run_append,run_append]
  have hs := sweep_run M x y u (cleanupWidth x y u) (by rfl)
  simp only [sweepConfig,Nat.cast_zero,sweep_zero] at hs
  have hh := sweep_halt M x y u
  simp only [sweepConfig] at hh
  rw [hs,Option.bind_some,run_ticks_one,hh,Option.bind_some,cleanup_return]

theorem answer_done (M : DeterministicMachine ns nt) (x y u : List Bool) :
    step (machine M) 0 ⟨18,((pairBits x y).length : Int),dirtyTape M x y u⟩=
      some ⟨25,((pairBits x y).length : Int)-1,dirtyTape M x y u⟩ := by
  have hr : raw (dirtyTape M x y u ((pairBits x y).length : Int))=2 := by
    rw [dirty_phase,answer_raw_unmarked M x y u _ y.length _ (by
      have hlen := pairBits_length x y;omega),raw_ge _ _ (by rfl)]
  simp only [pairBits_length,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] at hr
  apply stage_preserve M 18 25 _ _ .left (by simp [machine,hr])

theorem return_answer_done (M : DeterministicMachine ns nt) (x y u : List Bool) (a : Nat) :
    run (machine M) (ticks (a+1)) ⟨25,(a : Int)-1,dirtyTape M x y u⟩=
      some ⟨27,0,dirtyTape M x y u⟩ := by
  have hs := scan_left (M:=machine M) (q:=25) (t:=dirtyTape M x y u)
    (h:=(a : Int)-1) (n:=a) (by
      intro i hi
      have hz : (a : Int)-1-(i : Int)=((a-1-i : Nat) : Int) := by omega
      rw [hz]
      have ho : output (dirtyTape M x y u ((a-1-i : Nat) : Int))≠3 := by
        rw [dirty_phase];exact answer_output_ne_L M x y u _ y.length _
      simp [machine,ho])
  rw [show (a : Int)-1-(a : Int)=(-1 : Int) by omega] at hs
  rw [ticks_add,run_append,hs,Option.bind_some,run_ticks_one]
  apply stage_preserve M 25 27 (dirtyTape M x y u) (-1) .right
    (by simp [machine,dirty_L,output_joint])

theorem answer_cleanup_setup (M : DeterministicMachine ns nt) (x y u : List Bool) :
    run (machine M) (ticks (y.length+(pairBits x y).length+2))
      (answerConfig M x y u y.length)=some ⟨27,0,dirtyTape M x y u⟩ := by
  have hs := skip_answer M x y u (pairBits u y) y.length
  rw [← dirty_phase,show 2*x.length+1+y.length=(pairBits x y).length by rw [pairBits_length]] at hs
  have ht : ticks (y.length+(pairBits x y).length+2)=
      ticks y.length++ticks 1++ticks ((pairBits x y).length+1) := by
    rw [show y.length+(pairBits x y).length+2=y.length+1+((pairBits x y).length+1) by omega]
    simp only [ticks_add,List.append_assoc]
  change run (machine M) (ticks (y.length+(pairBits x y).length+2))
      ⟨18,((2*x.length+1 : Nat) : Int),dirtyTape M x y u⟩=_
  rw [ht,run_append,run_append,hs,Option.bind_some,run_ticks_one,answer_done,
    Option.bind_some,return_answer_done]

theorem answer_cleanup_run (M : DeterministicMachine ns nt) (x y u : List Bool) :
    run (machine M) (ticks (2*x.length+2*y.length+2*cleanupWidth x y u+5))
      (answerConfig M x y u y.length)=some (finalConfig M (pairBits u y)) := by
  have hf : 2*x.length+2*y.length+2*cleanupWidth x y u+5=
      (y.length+(pairBits x y).length+2)+(2*cleanupWidth x y u+2) := by
    rw [pairBits_length];omega
  rw [hf,ticks_add,run_append,answer_cleanup_setup,Option.bind_some,cleanup_sweep_run]

def stageFuel (x y u : List Bool) : Nat :=
  2+counterFuel u.length+(6*u.length+2*x.length+5)+answerFuel x.length u.length y.length+
    (2*x.length+2*y.length+2*cleanupWidth x y u+5)

theorem stage_run (M : DeterministicMachine ns nt) (x y u : List Bool) :
    run (machine M) (ticks (stageFuel x y u)) (startConfig M (pairBits x y) u)=
      some (finalConfig M (pairBits u y)) := by
  rw [stageFuel,ticks_add,run_append,start_answer_run,Option.bind_some,answer_cleanup_run]

theorem stageFuel_le (x y u : List Bool) :
    stageFuel x y u≤64*(x.length+y.length+u.length+1)*(x.length+y.length+u.length+1) := by
  have hw : cleanupWidth x y u≤2*(x.length+y.length+u.length)+1 := by
    unfold cleanupWidth
    rw [max_le_iff,pairBits_length,pairBits_length]
    constructor <;> omega
  unfold stageFuel counterFuel answerFuel
  nlinarith [Nat.zero_le (x.length*x.length),Nat.zero_le (y.length*y.length),
    Nat.zero_le (u.length*u.length),Nat.zero_le (x.length*y.length),
    Nat.zero_le (x.length*u.length),Nat.zero_le (y.length*u.length)]

theorem stage_spec (M : DeterministicMachine ns nt) (x y u : List Bool) :
    run (machine M) (ticks (stageFuel x y u)) (startConfig M (pairBits x y) u)=
      some (finalConfig M (pairBits u y)) ∧
    stageFuel x y u≤64*(x.length+y.length+u.length+1)*(x.length+y.length+u.length+1) ∧
    Output (machine M) (pairBits u y) (finalConfig M (pairBits u y)) :=
  ⟨stage_run M x y u,stageFuel_le x y u,final_output M _⟩

end PakFixedPolyomino.StandardBitRetainedPairCleanup
