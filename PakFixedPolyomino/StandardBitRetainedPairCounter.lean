import PakFixedPolyomino.StandardBitRetainedPairStage
import PakFixedPolyomino.StandardBitMarkedCompaction

/-! Whole-tape counter-prefix phases of the retained-answer pairing stage. -/
namespace PakFixedPolyomino.StandardBitRetainedPairCounter
open StandardNondeterministicMachine StandardBitTime
open StandardBitRetainedPairStage
open StandardBitProtectedCleanup (rawTape rawBit)
open StandardBitMarkedCompaction (scan_left scan_right preserve_step)
open FiniteOneTapeSemantics (moveHead writtenTape)
variable {ns nt : Nat}

set_option maxHeartbeats 800000

def phaseTape (M : DeterministicMachine ns nt) (r u : List Bool) (p : Nat)
    (v : List Bool) (z : Int) : Alphabet nt :=
  if z=-1 then joint 2 M.blank 0 3 else
    joint (rawTape r z) (inputTape M u z)
      (if 0≤z ∧ z.toNat<p then 1 else 0) (rawTape v z)

theorem counter_phase (M : DeterministicMachine ns nt) (r u : List Bool) (k : Nat) :
    counterTape M r u k=phaseTape M r u k (prefixOutput u k) := rfl

theorem phase_L (M : DeterministicMachine ns nt) (r u v : List Bool) (p : Nat) :
    phaseTape M r u p v (-1)=joint 2 M.blank 0 3 := by simp [phaseTape]

theorem phase_seen (M : DeterministicMachine ns nt) (r u v : List Bool) (p i : Nat) :
    seen (phaseTape M r u p v (i : Int))=(if i<p then 1 else 0) := by
  simp [phaseTape,show (i : Int)≠-1 by omega,seen_joint]

theorem phase_work (M : DeterministicMachine ns nt) (r u v : List Bool) (p i : Nat) :
    work (phaseTape M r u p v (i : Int))=inputTape M u (i : Int) := by
  simp [phaseTape,show (i : Int)≠-1 by omega,work_joint]

theorem phase_output (M : DeterministicMachine ns nt) (r u v : List Bool) (p : Nat)
    (z : Int) (hL : z≠-1) : output (phaseTape M r u p v z)=rawTape v z := by
  simp only [phaseTape,if_neg hL,output_joint]

theorem raw_ne_L (v : List Bool) (z : Int) : rawTape v z≠(3 : Fin 4) := by
  unfold rawTape
  split_ifs <;> try decide
  unfold rawBit
  split_ifs <;> decide

theorem phase_output_ne_L (M : DeterministicMachine ns nt) (r u v : List Bool) (p i : Nat) :
    output (phaseTape M r u p v (i : Int))≠(3 : Fin 4) := by
  rw [phase_output M r u v p _ (by omega)]
  exact raw_ne_L v _

theorem phase_seen_write (M : DeterministicMachine ns nt) (r u v : List Bool) (p : Nat) :
    Function.update (phaseTape M r u p v) (p : Int)
      (setSeen (phaseTape M r u p v (p : Int)) 1)=phaseTape M r u (p+1) v := by
  funext z
  by_cases hz : z=(p : Int)
  · subst z
    rw [Function.update_self]
    have hL : (p : Int)≠-1 := by omega
    simp [phaseTape,hL,setSeen,raw_joint,work_joint,output_joint]
  · rw [Function.update_of_ne hz]
    by_cases hL : z=(-1 : Int)
    · subst z;rw [phase_L,phase_L]
    · have he : (0≤z ∧ z.toNat<p) ↔ (0≤z ∧ z.toNat<p+1) := by
        by_cases hp : 0≤z
        · have ht := Int.toNat_of_nonneg hp
          have hn : z.toNat≠p := by intro h;apply hz;omega
          omega
        · simp [hp]
      simp only [phaseTape,if_neg hL,he]

theorem raw_append_write (v : List Bool) (b : Bool) :
    Function.update (rawTape v) (v.length : Int) (rawBit b)=rawTape (v++[b]) := by
  funext z
  by_cases hz : z=(v.length : Int)
  · subst z
    simp [rawTape]
  · rw [Function.update_of_ne hz]
    by_cases hp : 0≤z
    · have ht := Int.toNat_of_nonneg hp
      have hn : z.toNat≠v.length := by intro h;apply hz;omega
      by_cases hi : z.toNat<v.length
      · have ha : z.toNat<(v++[b]).length := by simp;omega
        simp only [rawTape,hp,hi,ha,dite_true,List.getElem_append_left]
      · have ha : ¬ z.toNat<(v++[b]).length := by simp;omega
        simp only [rawTape,hp,hi,ha,dite_true,dite_false]
    · simp [rawTape,hp]

theorem phase_output_write (M : DeterministicMachine ns nt) (r u v : List Bool)
    (p : Nat) (b : Bool) :
    Function.update (phaseTape M r u p v) (v.length : Int)
      (setOutput (phaseTape M r u p v (v.length : Int)) (rawBit b))=
        phaseTape M r u p (v++[b]) := by
  funext z
  have hr := congrFun (raw_append_write v b) z
  by_cases hz : z=(v.length : Int)
  · subst z
    rw [Function.update_self] at hr ⊢
    have hL : (v.length : Int)≠-1 := by omega
    simp only [phaseTape,if_neg hL,setOutput,raw_joint,work_joint,seen_joint]
    rw [← hr]
  · rw [Function.update_of_ne hz] at hr ⊢
    simp only [phaseTape,hr]

theorem prefixOutput_succ (u : List Bool) (k : Nat) (hk : k<u.length) :
    prefixOutput u (k+1)=prefixOutput u k++[true,u[k]] := by
  unfold prefixOutput
  rw [List.take_succ_eq_append_getElem hk,List.flatMap_append]
  rfl

def backState (b : Bool) : Fin 30 := if b then 8 else 5
def seekState (b : Bool) : Fin 30 := if b then 9 else 6
def emitState (b : Bool) : Fin 30 := if b then 10 else 7

theorem rule_back (M : DeterministicMachine ns nt) (b : Bool) (s : Alphabet nt)
    (h : output s≠3) :
    (machine M).rule (backState b) s 0=some ⟨s,backState b,.left⟩ := by
  cases b <;> simp [machine,backState,h]

theorem rule_back_L (M : DeterministicMachine ns nt) (b : Bool) (s : Alphabet nt)
    (h : output s=3) :
    (machine M).rule (backState b) s 0=some ⟨s,seekState b,.right⟩ := by
  cases b <;> simp [machine,backState,seekState,h]

theorem rule_seek (M : DeterministicMachine ns nt) (b : Bool) (s : Alphabet nt)
    (h : output s≠2) :
    (machine M).rule (seekState b) s 0=some ⟨s,seekState b,.right⟩ := by
  cases b <;> simp [machine,seekState,h]

theorem rule_seek_end (M : DeterministicMachine ns nt) (b : Bool) (s : Alphabet nt)
    (h : output s=2) :
    (machine M).rule (seekState b) s 0=some ⟨setOutput s 1,emitState b,.right⟩ := by
  cases b <;> simp [machine,seekState,emitState,h]

theorem rule_emit (M : DeterministicMachine ns nt) (b : Bool) (s : Alphabet nt) :
    (machine M).rule (emitState b) s 0=some ⟨setOutput s (rawBit b),12,.left⟩ := by
  cases b <;> simp [machine,emitState,rawBit]

theorem counter_skip (M : DeterministicMachine ns nt) (r u v : List Bool) (k : Nat) :
    run (machine M) (ticks k) ⟨4,0,phaseTape M r u k v⟩=
      some ⟨4,(k : Int),phaseTape M r u k v⟩ := by
  have hs := scan_right (M:=machine M) (q:=4) (t:=phaseTape M r u k v) (h:=0) (n:=k)
  simpa only [Int.zero_add] using hs (by
    intro i hi
    rw [Int.zero_add]
    simp [machine,phase_seen,hi])

theorem stage_preserve (M : DeterministicMachine ns nt) (q q' : Fin 30)
    (t : Int → Alphabet nt) (h : Int) (d : OneTapeTableau.Move)
    (hr : (machine M).rule q (t h) 0=some ⟨t h,q',d⟩) :
    step (machine M) 0 ⟨q,h,t⟩=some ⟨q',moveHead d h,t⟩ := by
  simp [step,hr,writtenTape,Function.update_eq_self_iff]

theorem counter_take (M : DeterministicMachine ns nt) (r u v : List Bool)
    (k : Nat) (hk : k<u.length) :
    step (machine M) 0 ⟨4,(k : Int),phaseTape M r u k v⟩=
      some ⟨backState u[k],(k : Int)-1,phaseTape M r u (k+1) v⟩ := by
  have hp : seen (phaseTape M r u k v (k : Int))=0 := by rw [phase_seen];simp
  have hw : work (phaseTape M r u k v (k : Int))=(if u[k] then M.one else M.zero) := by
    rw [phase_work,inputTape_ofNat M u k hk]
  have hr : (machine M).rule 4 (phaseTape M r u k v (k : Int)) 0=
      some ⟨setSeen (phaseTape M r u k v (k : Int)) 1,backState u[k],.left⟩ := by
    cases hb : u[k] <;> simp [machine,hp,hw,hb,backState,
      Ne.symm M.blank_ne_zero,Ne.symm M.blank_ne_one,Ne.symm M.zero_ne_one]
  simp only [step,hr,Option.map_some,writtenTape,moveHead]
  rw [phase_seen_write]

theorem counter_return (M : DeterministicMachine ns nt) (r u v : List Bool)
    (p a : Nat) (b : Bool) :
    run (machine M) (ticks (a+1)) ⟨backState b,(a : Int)-1,phaseTape M r u p v⟩=
      some ⟨seekState b,0,phaseTape M r u p v⟩ := by
  have hs := scan_left (M:=machine M) (q:=backState b) (t:=phaseTape M r u p v)
    (h:=(a : Int)-1) (n:=a) (by
      intro i hi
      have hz : (a : Int)-1-(i : Int)=((a-1-i : Nat) : Int) := by omega
      rw [hz]
      exact rule_back M b _ (phase_output_ne_L M r u v p _))
  have he : (a : Int)-1-(a : Int)=(-1 : Int) := by omega
  rw [he] at hs
  rw [ticks_add,run_append,hs,Option.bind_some,run_ticks_one]
  have hr := rule_back_L M b (phaseTape M r u p v (-1)) (by rw [phase_L,output_joint])
  simpa [moveHead] using
    stage_preserve M (backState b) (seekState b) (phaseTape M r u p v) (-1) .right hr

theorem seek_output (M : DeterministicMachine ns nt) (r u v : List Bool)
    (p : Nat) (b : Bool) :
    run (machine M) (ticks v.length) ⟨seekState b,0,phaseTape M r u p v⟩=
      some ⟨seekState b,(v.length : Int),phaseTape M r u p v⟩ := by
  have hs := scan_right (M:=machine M) (q:=seekState b) (t:=phaseTape M r u p v)
    (h:=0) (n:=v.length) (by
      intro i hi
      rw [Int.zero_add]
      apply rule_seek M b
      rw [phase_output M r u v p _ (by omega)]
      have hr : rawTape v (i : Int)=rawBit v[i] := by simp [rawTape,hi]
      rw [hr]
      exact StandardBitProtectedCleanup.rawBit_ne_blank _)
  simpa only [Int.zero_add] using hs

theorem write_marker (M : DeterministicMachine ns nt) (r u v : List Bool)
    (p : Nat) (b : Bool) :
    step (machine M) 0 ⟨seekState b,(v.length : Int),phaseTape M r u p v⟩=
      some ⟨emitState b,(v.length : Int)+1,phaseTape M r u p (v++[true])⟩ := by
  have ho : output (phaseTape M r u p v (v.length : Int))=2 := by
    rw [phase_output M r u v p _ (by omega)];simp [rawTape]
  have hr := rule_seek_end M b _ ho
  simp only [step,hr,Option.map_some,writtenTape,moveHead]
  have hw := phase_output_write M r u v p true
  simp only [rawBit,if_true] at hw
  rw [hw]

theorem write_counter_bit (M : DeterministicMachine ns nt) (r u v : List Bool)
    (p : Nat) (b : Bool) :
    step (machine M) 0 ⟨emitState b,(v.length : Int),phaseTape M r u p v⟩=
      some ⟨12,(v.length : Int)-1,phaseTape M r u p (v++[b])⟩ := by
  simp only [step,rule_emit,Option.map_some,writtenTape,moveHead]
  rw [phase_output_write M r u v p b]

theorem append_counter_pair (M : DeterministicMachine ns nt) (r u v : List Bool)
    (p : Nat) (b : Bool) :
    run (machine M) (ticks 2) ⟨seekState b,(v.length : Int),phaseTape M r u p v⟩=
      some ⟨12,(v.length : Int),phaseTape M r u p (v++[true,b])⟩ := by
  have hc : ((v++[true]).length : Int)=(v.length : Int)+1 := by simp
  rw [show ticks 2=ticks 1++ticks 1 by rfl,run_append,run_ticks_one,write_marker,
    Option.bind_some,run_ticks_one,← hc,write_counter_bit]
  simp [List.append_assoc]

theorem return_after_pair (M : DeterministicMachine ns nt) (r u v : List Bool)
    (p a : Nat) :
    run (machine M) (ticks (a+1)) ⟨12,(a : Int)-1,phaseTape M r u p v⟩=
      some ⟨4,0,phaseTape M r u p v⟩ := by
  have hs := scan_left (M:=machine M) (q:=12) (t:=phaseTape M r u p v)
    (h:=(a : Int)-1) (n:=a) (by
      intro i hi
      have hz : (a : Int)-1-(i : Int)=((a-1-i : Nat) : Int) := by omega
      rw [hz]
      have ho := phase_output_ne_L M r u v p (a-1-i)
      simp [machine,ho])
  have he : (a : Int)-1-(a : Int)=(-1 : Int) := by omega
  rw [he] at hs
  rw [ticks_add,run_append,hs,Option.bind_some,run_ticks_one]
  apply stage_preserve M 12 4 (phaseTape M r u p v) (-1) .right
    (by simp [machine,phase_L,output_joint])

theorem counter_cycle (M : DeterministicMachine ns nt) (r u : List Bool)
    (k : Nat) (hk : k<u.length) :
    run (machine M) (ticks (6*k+6)) (counterConfig M r u k)=
      some (counterConfig M r u (k+1)) := by
  have hn : (prefixOutput u k).length=2*k := prefixOutput_length u k (by omega)
  have hf : 6*k+6=k+1+(k+1)+2*k+2+(2*k+2) := by omega
  have hh : ((2*k+1 : Nat) : Int)-1=((2*k : Nat) : Int) := by omega
  change run (machine M) (ticks (6*k+6)) ⟨4,0,phaseTape M r u k (prefixOutput u k)⟩=
    some ⟨4,0,phaseTape M r u (k+1) (prefixOutput u (k+1))⟩
  have ht : ticks (6*k+6)=ticks k++ticks 1++ticks (k+1)++ticks (2*k)++
      ticks 2++ticks (2*k+2) := by rw [hf];simp only [ticks_add,List.append_assoc]
  have hseek := seek_output M r u (prefixOutput u k) (k+1) u[k]
  rw [hn] at hseek
  have hwrite := append_counter_pair M r u (prefixOutput u k) (k+1) u[k]
  rw [hn,← prefixOutput_succ u k hk] at hwrite
  have hback := return_after_pair M r u (prefixOutput u (k+1)) (k+1) (2*k+1)
  rw [show 2*k+1+1=2*k+2 by omega,hh] at hback
  rw [ht,run_append,run_append,run_append,run_append,run_append,counter_skip,
    Option.bind_some,run_ticks_one,counter_take M r u _ k hk,Option.bind_some,
    counter_return,Option.bind_some,hseek,Option.bind_some,hwrite,Option.bind_some,hback]

def counterFuel (k : Nat) : Nat := 3*k*k+3*k

theorem counter_run (M : DeterministicMachine ns nt) (r u : List Bool)
    (k : Nat) (hk : k≤u.length) :
    run (machine M) (ticks (counterFuel k)) (counterConfig M r u 0)=
      some (counterConfig M r u k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hf : counterFuel (k+1)=counterFuel k+(6*k+6) := by unfold counterFuel;ring
    rw [hf,ticks_add,run_append,ih (by omega),Option.bind_some]
    exact counter_cycle M r u k (by omega)

end PakFixedPolyomino.StandardBitRetainedPairCounter
