import PakFixedPolyomino.StandardBitRetainedFirstCounter
import PakFixedPolyomino.StandardBitPairProjection

/-! Exact physical separator phase for retaining the FIRST field. It returns
to head0 directly, leaving the original separator intact. This begins at
the explicit two-track stage; ordinary loading remains separate. -/
namespace PakFixedPolyomino.StandardBitRetainedFirstSeparator
open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open StandardBitRetainedPairStage hiding machine counter_zero_setup
open StandardBitRetainedFirstStage StandardBitRetainedFirstCounter
open StandardBitProtectedCleanup (rawTape rawBit)
open StandardBitMarkedCompaction (scan_left scan_right)
open StandardBitPairProjection (pairBits_marker pairBits_payload pairBits_sep)
open FiniteOneTapeSemantics (moveHead)
variable {ns nt : Nat}

set_option maxHeartbeats 800000

theorem phase_return (M : DeterministicMachine ns nt) (r u v : List Bool)
    (p a : Nat) (q q' : Fin 30)
    (hr : ∀ i : Nat, (machine M).rule q (phaseTape M r u p v (i : Int)) 0=
      some ⟨phaseTape M r u p v (i : Int),q,.left⟩)
    (hL : (machine M).rule q (phaseTape M r u p v (-1)) 0=
      some ⟨phaseTape M r u p v (-1),q',.right⟩) :
    run (machine M) (ticks (a+1)) ⟨q,(a : Int)-1,phaseTape M r u p v⟩=
      some ⟨q',0,phaseTape M r u p v⟩ := by
  have hs := scan_left (M:=machine M) (q:=q) (t:=phaseTape M r u p v)
    (h:=(a : Int)-1) (n:=a) (by
      intro i hi
      have hz : (a : Int)-1-(i : Int)=((a-1-i : Nat) : Int) := by omega
      rw [hz]
      exact hr _)
  rw [show (a : Int)-1-(a : Int)=(-1 : Int) by omega] at hs
  rw [ticks_add,run_append,hs,Option.bind_some,run_ticks_one]
  simpa [moveHead] using stage_preserve M q q' (phaseTape M r u p v) (-1) .right hL

theorem counter_done (M : DeterministicMachine ns nt) (r u v : List Bool) :
    step (machine M) 0 ⟨4,(u.length : Int),phaseTape M r u u.length v⟩=
      some ⟨13,(u.length : Int)-1,phaseTape M r u u.length v⟩ := by
  apply stage_preserve M 4 13 _ _ .left
  have hp : seen (phaseTape M r u u.length v (u.length : Int))=0 := by
    rw [phase_seen];simp
  have hw : work (phaseTape M r u u.length v (u.length : Int))=M.blank := by
    rw [phase_work];simp [inputTape]
  simp [machine,StandardBitRetainedPairStage.machine,hp,hw]

theorem return_counter_done (M : DeterministicMachine ns nt) (r u v : List Bool)
    (p a : Nat) :
    run (machine M) (ticks (a+1)) ⟨13,(a : Int)-1,phaseTape M r u p v⟩=
      some ⟨14,0,phaseTape M r u p v⟩ := by
  apply phase_return
  · intro i;simp [machine,StandardBitRetainedPairStage.machine,phase_output_ne_L]
  · simp [machine,StandardBitRetainedPairStage.machine,phase_L,output_joint]

theorem seek_separator (M : DeterministicMachine ns nt) (r u v : List Bool)
    (p : Nat) :
    run (machine M) (ticks v.length) ⟨14,0,phaseTape M r u p v⟩=
      some ⟨14,(v.length : Int),phaseTape M r u p v⟩ := by
  have hs := scan_right (M:=machine M) (q:=14) (t:=phaseTape M r u p v)
    (h:=0) (n:=v.length) (by
      intro i hi
      rw [Int.zero_add]
      have ho : output (phaseTape M r u p v (i : Int))≠2 := by
        rw [phase_output M r u v p _ (by omega)]
        simp only [rawTape,show (0 : Int)≤(i : Int) by omega,
          Int.toNat_natCast,hi,dite_true]
        exact StandardBitProtectedCleanup.rawBit_ne_blank _
      simp [machine,StandardBitRetainedPairStage.machine,ho])
  simpa only [Int.zero_add] using hs

theorem write_separator (M : DeterministicMachine ns nt) (r u v : List Bool)
    (p : Nat) :
    step (machine M) 0 ⟨14,(v.length : Int),phaseTape M r u p v⟩=
      some ⟨15,(v.length : Int)-1,phaseTape M r u p (v++[false])⟩ := by
  have ho : output (phaseTape M r u p v (v.length : Int))=2 := by
    rw [phase_output M r u v p _ (by omega)];simp [rawTape]
  have hr : (machine M).rule 14 (phaseTape M r u p v (v.length : Int)) 0=
      some ⟨setOutput (phaseTape M r u p v (v.length : Int)) 0,15,.left⟩ := by
    simp [machine,StandardBitRetainedPairStage.machine,ho]
  simp only [step,hr,Option.map_some,FiniteOneTapeSemantics.writtenTape,moveHead]
  have hw := phase_output_write M r u v p false
  simp [rawBit] at hw
  rw [hw]

theorem return_separator (M : DeterministicMachine ns nt) (r u v : List Bool)
    (p a : Nat) :
    run (machine M) (ticks (a+1)) ⟨15,(a : Int)-1,phaseTape M r u p v⟩=
      some ⟨18,0,phaseTape M r u p v⟩ := by
  apply phase_return
  · intro i;simp [machine,StandardBitRetainedPairStage.machine,phase_output_ne_L]
  · simp [machine,StandardBitRetainedPairStage.machine,phase_L,output_joint]

theorem counter_separator_run (M : DeterministicMachine ns nt) (r u : List Bool) :
    run (machine M) (ticks (6*u.length+4)) (counterConfig M r u u.length)=
      some ⟨18,0,phaseTape M r u u.length (pairBits u [])⟩ := by
  let m := u.length
  have hn : (prefixOutput u m).length=2*m := prefixOutput_length u m (by rfl)
  have hv : prefixOutput u m++[false]=pairBits u [] := by
    simp [prefixOutput,pairBits,m]
  have hseek := seek_separator M r u (prefixOutput u m) m
  rw [hn] at hseek
  have hwrite := write_separator M r u (prefixOutput u m) m
  rw [hn,hv] at hwrite
  have hback := return_separator M r u (pairBits u []) m (2*m)
  have ht : ticks (6*m+4)=ticks m++ticks 1++ticks (m+1)++ticks (2*m)++
      ticks 1++ticks (2*m+1) := by
    rw [show 6*m+4=m+1+(m+1)+2*m+1+(2*m+1) by omega]
    simp only [ticks_add,List.append_assoc]
  change run (machine M) (ticks (6*m+4)) ⟨4,0,phaseTape M r u m (prefixOutput u m)⟩=_
  rw [ht,run_append,run_append,run_append,run_append,run_append,counter_skip,
    Option.bind_some,run_ticks_one,counter_done,Option.bind_some,return_counter_done,
    Option.bind_some,hseek,Option.bind_some,run_ticks_one,hwrite,Option.bind_some,hback]

theorem phase_raw (M : DeterministicMachine ns nt) (r u v : List Bool) (p i : Nat) :
    raw (phaseTape M r u p v (i : Int))=rawTape r (i : Int) := by
  simp [phaseTape,show (i : Int)≠-1 by omega,raw_joint]

theorem raw_pair_marker (x y : List Bool) (i : Nat) (hi : i<x.length) :
    rawTape (pairBits x y) ((2*i : Nat) : Int)=1 := by
  have hl : 2*i<(pairBits x y).length := by rw [pairBits_length];omega
  simp only [rawTape,show (0 : Int)≤((2*i : Nat) : Int) by omega,
    Int.toNat_natCast,hl,dite_true]
  rw [pairBits_marker x y i hi]
  rfl

theorem raw_pair_payload (x y : List Bool) (i : Nat) (hi : i<x.length) :
    rawTape (pairBits x y) ((2*i+1 : Nat) : Int)=rawBit x[i] := by
  have hl : 2*i+1<(pairBits x y).length := by rw [pairBits_length];omega
  simp only [rawTape,show (0 : Int)≤((2*i+1 : Nat) : Int) by omega,
    Int.toNat_natCast,hl,dite_true]
  rw [pairBits_payload x y i hi]

theorem raw_pair_separator (x y : List Bool) :
    rawTape (pairBits x y) ((2*x.length : Nat) : Int)=0 := by
  have hl : 2*x.length<(pairBits x y).length := by rw [pairBits_length];omega
  simp only [rawTape,show (0 : Int)≤((2*x.length : Nat) : Int) by omega,
    Int.toNat_natCast,hl,dite_true]
  rw [pairBits_sep]
  rfl

def separatorTape (M : DeterministicMachine ns nt) (x y u : List Bool) : Int → Alphabet nt :=
  phaseTape M (pairBits x y) u u.length (pairBits u [])

theorem separator_run (M : DeterministicMachine ns nt) (x y u : List Bool) :
    run (machine M) (ticks (6*u.length+4))
      (counterConfig M (pairBits x y) u u.length)=some ⟨18,0,separatorTape M x y u⟩ :=
  counter_separator_run M (pairBits x y) u

theorem start_separator_run (M : DeterministicMachine ns nt) (x y u : List Bool) :
    run (machine M) (ticks (2+counterFuel u.length+(6*u.length+4)))
      (startConfig M (pairBits x y) u)=some ⟨18,0,separatorTape M x y u⟩ := by
  rw [ticks_add,run_append,ticks_add,run_append,counter_zero_setup,Option.bind_some,
    counter_run M _ u u.length (by rfl),Option.bind_some,separator_run]

end PakFixedPolyomino.StandardBitRetainedFirstSeparator
