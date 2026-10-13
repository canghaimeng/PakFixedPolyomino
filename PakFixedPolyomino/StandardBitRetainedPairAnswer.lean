import PakFixedPolyomino.StandardBitRetainedPairSeparator

/-! Copy the literal retained answer, including every high zero, onto the
separate output track. Only already consumed raw cells are marked. -/
namespace PakFixedPolyomino.StandardBitRetainedPairAnswer
open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open StandardBitRetainedPairStage StandardBitRetainedPairCounter
open StandardBitRetainedPairSeparator
open StandardBitProtectedCleanup (rawTape rawBit)
open StandardBitMarkedCompaction (scan_left scan_right)
open StandardBitPairProjection (pairBits_y)
open FiniteOneTapeSemantics (moveHead writtenTape)
variable {ns nt : Nat}

set_option maxHeartbeats 800000

def answerPhaseTape (M : DeterministicMachine ns nt) (x y u : List Bool)
    (j : Nat) (v : List Bool) (z : Int) : Alphabet nt :=
  let t := phaseTape M (pairBits x y) u u.length v
  if ((2*x.length : Nat) : Int)≤z ∧ z<((2*x.length+1+j : Nat) : Int) then
    setRaw (t z) 3 else t z

theorem answer_L (M : DeterministicMachine ns nt) (x y u v : List Bool) (j : Nat) :
    answerPhaseTape M x y u j v (-1)=joint 2 M.blank 0 3 := by
  have h : ¬ ((2*x.length : Nat) : Int)≤(-1 : Int) := by omega
  simp only [answerPhaseTape,h,false_and,if_false,phase_L]

theorem answer_output (M : DeterministicMachine ns nt) (x y u v : List Bool)
    (j : Nat) (z : Int) :
    output (answerPhaseTape M x y u j v z)=output (phaseTape M (pairBits x y) u u.length v z) := by
  unfold answerPhaseTape
  split <;> simp only [setRaw,output_joint]

theorem answer_output_ne_L (M : DeterministicMachine ns nt) (x y u v : List Bool)
    (j i : Nat) : output (answerPhaseTape M x y u j v (i : Int))≠3 := by
  rw [answer_output];exact phase_output_ne_L M _ u v u.length i

theorem answer_raw_marked (M : DeterministicMachine ns nt) (x y u v : List Bool)
    (j : Nat) (z : Int)
    (h : ((2*x.length : Nat) : Int)≤z ∧ z<((2*x.length+1+j : Nat) : Int)) :
    raw (answerPhaseTape M x y u j v z)=3 := by
  simp only [answerPhaseTape,if_pos h,setRaw,raw_joint]

theorem answer_raw_unmarked (M : DeterministicMachine ns nt) (x y u v : List Bool)
    (j i : Nat)
    (h : ¬ (((2*x.length : Nat) : Int)≤(i : Int) ∧
      (i : Int)<((2*x.length+1+j : Nat) : Int))) :
    raw (answerPhaseTape M x y u j v (i : Int))=rawTape (pairBits x y) (i : Int) := by
  simp only [answerPhaseTape,if_neg h,phase_raw]

theorem raw_pair_answer (x y : List Bool) (j : Nat) (hj : j<y.length) :
    rawTape (pairBits x y) ((2*x.length+1+j : Nat) : Int)=rawBit y[j] := by
  have hl : 2*x.length+1+j<(pairBits x y).length := by rw [pairBits_length];omega
  simp only [rawTape,show (0 : Int)≤((2*x.length+1+j : Nat) : Int) by omega,
    Int.toNat_natCast,hl,dite_true]
  rw [pairBits_y x y j hj]

theorem answer_read (M : DeterministicMachine ns nt) (x y u v : List Bool)
    (j : Nat) (hj : j<y.length) :
    raw (answerPhaseTape M x y u j v ((2*x.length+1+j : Nat) : Int))=rawBit y[j] := by
  rw [answer_raw_unmarked M x y u v j _ (by omega)]
  exact raw_pair_answer x y j hj

theorem answer_mark_write (M : DeterministicMachine ns nt) (x y u v : List Bool)
    (j : Nat) :
    Function.update (answerPhaseTape M x y u j v) ((2*x.length+1+j : Nat) : Int)
      (setRaw (answerPhaseTape M x y u j v ((2*x.length+1+j : Nat) : Int)) 3)=
        answerPhaseTape M x y u (j+1) v := by
  funext z
  by_cases hz : z=((2*x.length+1+j : Nat) : Int)
  · subst z
    have hprev : ¬ (((2*x.length : Nat) : Int)≤((2*x.length+1+j : Nat) : Int) ∧
      ((2*x.length+1+j : Nat) : Int)<((2*x.length+1+j : Nat) : Int)) := by omega
    have hnext : ((2*x.length : Nat) : Int)≤((2*x.length+1+j : Nat) : Int) ∧
      ((2*x.length+1+j : Nat) : Int)<((2*x.length+1+(j+1) : Nat) : Int) := by omega
    simp only [Function.update_self,answerPhaseTape,if_neg hprev,if_pos hnext]
  · rw [Function.update_of_ne hz]
    have he : (((2*x.length : Nat) : Int)≤z ∧ z<((2*x.length+1+j : Nat) : Int)) ↔
      (((2*x.length : Nat) : Int)≤z ∧ z<((2*x.length+1+(j+1) : Nat) : Int)) := by omega
    simp only [answerPhaseTape,he]

theorem answer_output_write (M : DeterministicMachine ns nt) (x y u v : List Bool)
    (j : Nat) (b : Bool) :
    Function.update (answerPhaseTape M x y u j v) (v.length : Int)
      (setOutput (answerPhaseTape M x y u j v (v.length : Int)) (rawBit b))=
        answerPhaseTape M x y u j (v++[b]) := by
  funext z
  have hr := congrFun (phase_output_write M (pairBits x y) u v u.length b) z
  by_cases hz : z=(v.length : Int)
  · subst z
    rw [Function.update_self] at hr ⊢
    unfold answerPhaseTape
    dsimp only
    split
    · rw [← hr]
      simp only [setRaw,setOutput,raw_joint,work_joint,seen_joint,output_joint]
    · exact hr
  · rw [Function.update_of_ne hz] at hr ⊢
    simp only [answerPhaseTape,hr]

theorem separator_answer_zero (M : DeterministicMachine ns nt) (x y u : List Bool) :
    separatorTape M x y u=answerPhaseTape M x y u 0 (pairBits u []) := by
  funext z
  by_cases hz : z=((2*x.length : Nat) : Int)
  · subst z
    have h : ((2*x.length : Nat) : Int)≤((2*x.length : Nat) : Int) ∧
      ((2*x.length : Nat) : Int)<((2*x.length+1+0 : Nat) : Int) := by omega
    simp only [separatorTape,Function.update_self,answerPhaseTape,if_pos h]
  · have h : ¬ (((2*x.length : Nat) : Int)≤z ∧ z<((2*x.length+1+0 : Nat) : Int)) := by omega
    simp only [separatorTape,Function.update_of_ne hz,answerPhaseTape,if_neg h]

def answerTape (M : DeterministicMachine ns nt) (x y u : List Bool) (j : Nat) :
    Int → Alphabet nt := answerPhaseTape M x y u j (pairBits u (y.take j))
def answerConfig (M : DeterministicMachine ns nt) (x y u : List Bool) (j : Nat) :
    Configuration 30 (4*(2*(4*nt))) := ⟨18,((2*x.length+1 : Nat) : Int),answerTape M x y u j⟩

theorem answer_zero (M : DeterministicMachine ns nt) (x y u : List Bool) :
    answerTape M x y u 0=separatorTape M x y u := by
  simp only [answerTape,List.take_zero,← separator_answer_zero]

def answerBack (b : Bool) : Fin 30 := if b then 22 else 19
def answerSeek (b : Bool) : Fin 30 := if b then 23 else 20

theorem skip_answer (M : DeterministicMachine ns nt) (x y u v : List Bool) (j : Nat) :
    run (machine M) (ticks j)
      ⟨18,((2*x.length+1 : Nat) : Int),answerPhaseTape M x y u j v⟩=
      some ⟨18,((2*x.length+1+j : Nat) : Int),answerPhaseTape M x y u j v⟩ := by
  have hs := scan_right (M:=machine M) (q:=18) (t:=answerPhaseTape M x y u j v)
    (h:=((2*x.length+1 : Nat) : Int)) (n:=j) (by
      intro i hi
      have hr := answer_raw_marked M x y u v j
        (((2*x.length+1 : Nat) : Int)+(i : Int)) (by omega)
      simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] at hr
      simp [machine,hr])
  have hh : ((2*x.length+1 : Nat) : Int)+(j : Int)=((2*x.length+1+j : Nat) : Int) := by omega
  rw [hh] at hs
  exact hs

theorem take_answer (M : DeterministicMachine ns nt) (x y u v : List Bool)
    (j : Nat) (hj : j<y.length) :
    step (machine M) 0
      ⟨18,((2*x.length+1+j : Nat) : Int),answerPhaseTape M x y u j v⟩=
      some ⟨answerBack y[j],((2*x.length+1+j : Nat) : Int)-1,
        answerPhaseTape M x y u (j+1) v⟩ := by
  have hb := answer_read M x y u v j hj
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] at hb
  have hr : (machine M).rule 18
      (answerPhaseTape M x y u j v ((2*x.length+1+j : Nat) : Int)) 0=
      some ⟨setRaw (answerPhaseTape M x y u j v ((2*x.length+1+j : Nat) : Int)) 3,
        answerBack y[j],.left⟩ := by
    cases hbit : y[j] <;> simp [machine,hb,hbit,rawBit,answerBack]
  simp only [step,hr,Option.map_some,writtenTape,moveHead]
  rw [answer_mark_write]

theorem return_answer (M : DeterministicMachine ns nt) (x y u v : List Bool)
    (j a : Nat) (b : Bool) :
    run (machine M) (ticks (a+1))
      ⟨answerBack b,(a : Int)-1,answerPhaseTape M x y u j v⟩=
      some ⟨answerSeek b,0,answerPhaseTape M x y u j v⟩ := by
  have hs := scan_left (M:=machine M) (q:=answerBack b)
    (t:=answerPhaseTape M x y u j v) (h:=(a : Int)-1) (n:=a) (by
      intro i hi
      have hz : (a : Int)-1-(i : Int)=((a-1-i : Nat) : Int) := by omega
      rw [hz]
      have ho := answer_output_ne_L M x y u v j (a-1-i)
      cases b <;> simp [machine,answerBack,ho])
  rw [show (a : Int)-1-(a : Int)=(-1 : Int) by omega] at hs
  rw [ticks_add,run_append,hs,Option.bind_some,run_ticks_one]
  have hr : (machine M).rule (answerBack b) (answerPhaseTape M x y u j v (-1)) 0=
      some ⟨answerPhaseTape M x y u j v (-1),answerSeek b,.right⟩ := by
    cases b <;> simp [machine,answerBack,answerSeek,answer_L,output_joint]
  simpa [moveHead] using stage_preserve M (answerBack b) (answerSeek b)
    (answerPhaseTape M x y u j v) (-1) .right hr

theorem seek_answer (M : DeterministicMachine ns nt) (x y u v : List Bool)
    (j : Nat) (b : Bool) :
    run (machine M) (ticks v.length) ⟨answerSeek b,0,answerPhaseTape M x y u j v⟩=
      some ⟨answerSeek b,(v.length : Int),answerPhaseTape M x y u j v⟩ := by
  have hs := scan_right (M:=machine M) (q:=answerSeek b) (t:=answerPhaseTape M x y u j v)
    (h:=0) (n:=v.length) (by
      intro i hi
      rw [Int.zero_add]
      have ho : output (answerPhaseTape M x y u j v (i : Int))≠2 := by
        rw [answer_output,phase_output M _ u v u.length _ (by omega)]
        simp only [rawTape,show (0 : Int)≤(i : Int) by omega,
          Int.toNat_natCast,hi,dite_true]
        exact StandardBitProtectedCleanup.rawBit_ne_blank _
      cases b <;> simp [machine,answerSeek,ho])
  simpa only [Int.zero_add] using hs

theorem write_answer (M : DeterministicMachine ns nt) (x y u v : List Bool)
    (j : Nat) (b : Bool) :
    step (machine M) 0 ⟨answerSeek b,(v.length : Int),answerPhaseTape M x y u j v⟩=
      some ⟨24,(v.length : Int)-1,answerPhaseTape M x y u j (v++[b])⟩ := by
  have ho : output (answerPhaseTape M x y u j v (v.length : Int))=2 := by
    rw [answer_output,phase_output M _ u v u.length _ (by omega)];simp [rawTape]
  have hr : (machine M).rule (answerSeek b) (answerPhaseTape M x y u j v (v.length : Int)) 0=
      some ⟨setOutput (answerPhaseTape M x y u j v (v.length : Int)) (rawBit b),24,.left⟩ := by
    cases b <;> simp [machine,answerSeek,ho,rawBit]
  simp only [step,hr,Option.map_some,writtenTape,moveHead]
  rw [answer_output_write]

theorem return_answer_output (M : DeterministicMachine ns nt) (x y u v : List Bool)
    (j a : Nat) :
    run (machine M) (ticks (a+1)) ⟨24,(a : Int)-1,answerPhaseTape M x y u j v⟩=
      some ⟨26,0,answerPhaseTape M x y u j v⟩ := by
  have hs := scan_left (M:=machine M) (q:=24) (t:=answerPhaseTape M x y u j v)
    (h:=(a : Int)-1) (n:=a) (by
      intro i hi
      have hz : (a : Int)-1-(i : Int)=((a-1-i : Nat) : Int) := by omega
      rw [hz]
      have ho := answer_output_ne_L M x y u v j (a-1-i)
      simp [machine,ho])
  rw [show (a : Int)-1-(a : Int)=(-1 : Int) by omega] at hs
  rw [ticks_add,run_append,hs,Option.bind_some,run_ticks_one]
  apply stage_preserve M 24 26 (answerPhaseTape M x y u j v) (-1) .right
    (by simp [machine,answer_L,output_joint])

theorem seek_original_separator (M : DeterministicMachine ns nt) (x y u v : List Bool)
    (j : Nat) :
    run (machine M) (ticks (2*x.length)) ⟨26,0,answerPhaseTape M x y u j v⟩=
      some ⟨26,((2*x.length : Nat) : Int),answerPhaseTape M x y u j v⟩ := by
  have hs := scan_right (M:=machine M) (q:=26) (t:=answerPhaseTape M x y u j v)
    (h:=0) (n:=2*x.length) (by
      intro i hi
      rw [Int.zero_add]
      have hr : raw (answerPhaseTape M x y u j v (i : Int))≠3 := by
        rw [answer_raw_unmarked M x y u v j i (by omega)]
        exact raw_ne_L _ _
      simp [machine,hr])
  simpa only [Int.zero_add] using hs

theorem leave_original_separator (M : DeterministicMachine ns nt) (x y u v : List Bool)
    (j : Nat) :
    step (machine M) 0 ⟨26,((2*x.length : Nat) : Int),answerPhaseTape M x y u j v⟩=
      some ⟨18,((2*x.length+1 : Nat) : Int),answerPhaseTape M x y u j v⟩ := by
  have hr := answer_raw_marked M x y u v j ((2*x.length : Nat) : Int) (by omega)
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hr
  have hs := stage_preserve M 26 18 (answerPhaseTape M x y u j v)
    ((2*x.length : Nat) : Int) .right (by simp [machine,hr])
  simpa only [moveHead,Nat.cast_add,Nat.cast_one] using hs

theorem pair_take_succ (u y : List Bool) (j : Nat) (hj : j<y.length) :
    pairBits u (y.take (j+1))=pairBits u (y.take j)++[y[j]] := by
  rw [List.take_succ_eq_append_getElem hj]
  simp [pairBits,List.append_assoc]

theorem answer_cycle (M : DeterministicMachine ns nt) (x y u : List Bool)
    (j : Nat) (hj : j<y.length) :
    run (machine M) (ticks (4*j+4*u.length+4*x.length+8)) (answerConfig M x y u j)=
      some (answerConfig M x y u (j+1)) := by
  let a := 2*x.length+1+j
  let v := pairBits u (y.take j)
  let l := 2*u.length+1+j
  have hn : v.length=l := by
    simp only [v,pairBits_length,List.length_take,Nat.min_eq_left (show j≤y.length by omega),l]
  have hv : v++[y[j]]=pairBits u (y.take (j+1)) := (pair_take_succ u y j hj).symm
  have hseek := seek_answer M x y u v (j+1) y[j]
  rw [hn] at hseek
  have hwrite := write_answer M x y u v (j+1) y[j]
  rw [hn,hv] at hwrite
  have hback := return_answer_output M x y u (pairBits u (y.take (j+1))) (j+1) l
  have hscan := seek_original_separator M x y u (pairBits u (y.take (j+1))) (j+1)
  have hleave := leave_original_separator M x y u (pairBits u (y.take (j+1))) (j+1)
  have ht : ticks (4*j+4*u.length+4*x.length+8)=ticks j++ticks 1++ticks (a+1)++
      ticks l++ticks 1++ticks (l+1)++ticks (2*x.length)++ticks 1 := by
    rw [show 4*j+4*u.length+4*x.length+8=j+1+(a+1)+l+1+(l+1)+2*x.length+1 by dsimp [a,l];omega]
    simp only [ticks_add,List.append_assoc]
  change run (machine M) (ticks (4*j+4*u.length+4*x.length+8))
      ⟨18,((2*x.length+1 : Nat) : Int),answerPhaseTape M x y u j v⟩=
    some ⟨18,((2*x.length+1 : Nat) : Int),answerPhaseTape M x y u (j+1) (pairBits u (y.take (j+1)))⟩
  rw [ht,run_append,run_append,run_append,run_append,run_append,run_append,run_append,
    skip_answer,Option.bind_some,run_ticks_one,take_answer M x y u v j hj,Option.bind_some,
    return_answer,Option.bind_some,hseek,Option.bind_some,run_ticks_one,hwrite,
    Option.bind_some,hback,Option.bind_some,hscan,Option.bind_some,run_ticks_one,hleave]

def answerFuel (xlen ulen j : Nat) : Nat := 2*j*j+(4*ulen+4*xlen+6)*j

theorem answer_run (M : DeterministicMachine ns nt) (x y u : List Bool)
    (j : Nat) (hj : j≤y.length) :
    run (machine M) (ticks (answerFuel x.length u.length j)) (answerConfig M x y u 0)=
      some (answerConfig M x y u j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hf : answerFuel x.length u.length (j+1)=answerFuel x.length u.length j+
        (4*j+4*u.length+4*x.length+8) := by unfold answerFuel;ring
    rw [hf,ticks_add,run_append,ih (by omega),Option.bind_some]
    exact answer_cycle M x y u j (by omega)

theorem start_answer_run (M : DeterministicMachine ns nt) (x y u : List Bool) :
    run (machine M) (ticks (2+counterFuel u.length+(6*u.length+2*x.length+5)+
      answerFuel x.length u.length y.length)) (startConfig M (pairBits x y) u)=
      some (answerConfig M x y u y.length) := by
  have hstart := start_separator_run M x y u
  rw [← answer_zero] at hstart
  rw [ticks_add,run_append,hstart,Option.bind_some]
  exact answer_run M x y u y.length (by rfl)

end PakFixedPolyomino.StandardBitRetainedPairAnswer
