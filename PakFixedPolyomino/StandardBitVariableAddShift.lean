import PakFixedPolyomino.StandardBitVariableAddNormalize

/-! Rolling left shift of a binary block in the frozen adder. -/
namespace PakFixedPolyomino.StandardBitVariableAddShift
open StandardNondeterministicMachine StandardBitTime
open StandardBitVariableAdd (machine enc)
open StandardBitVariableAddTape
open FiniteOneTapeSemantics (moveHead writtenTape)

def cell : Option Bool → Fin 32 | none => 2 | some b => enc b

theorem input_nat_option (v : List Bool) (i : Nat) :
    inputTape machine v (i : Int)=cell v[i]? := by
  by_cases hi : i<v.length
  · rw [StandardBitVariableAdd.read_bit v i hi,List.getElem?_eq_getElem hi]
    rfl
  · rw [inputTape_ge machine v (i : Int) (by omega)]
    have hnone : v[i]?=none := List.getElem?_eq_none (by omega)
    rw [hnone]
    rfl

theorem input_cons (b : Bool) (v : List Bool) (i : Nat) :
    inputTape machine (b::v) (i+1 : Nat)=inputTape machine v (i : Int) := by
  rw [input_nat_option,input_nat_option,List.getElem?_cons_succ]

theorem input_replace (u v : List Bool) (a b : Bool) :
    Function.update (inputTape machine (u++a::v)) (u.length : Int) (enc b)=
      inputTape machine (u++b::v) := by
  funext z
  by_cases hz : z=(u.length : Int)
  · subst z
    rw [Function.update_self,input_nat_option,List.getElem?_append_right (by omega)]
    simp [cell]
  · rw [Function.update_of_ne hz]
    by_cases hn : z<0
    · rw [inputTape_neg machine _ z hn,inputTape_neg machine _ z hn]
    · have he : z=(z.toNat : Int) := by omega
      rw [he,input_nat_option,input_nat_option]
      by_cases hi : z.toNat<u.length
      · rw [List.getElem?_append_left hi,List.getElem?_append_left hi]
      · have hge : u.length≤z.toNat := by omega
        have hne : z.toNat-u.length≠0 := by omega
        rw [List.getElem?_append_right hge,List.getElem?_append_right hge,
          List.getElem?_cons,List.getElem?_cons,if_neg hne,if_neg hne]

theorem block_replace (u v : List Bool) (a b : Bool) (p : Nat) :
    Function.update (blockTape (u++a::v) p) (p+u.length : Nat) (enc b)=
      blockTape (u++b::v) p := by
  funext z
  by_cases hz : z=((p+u.length : Nat) : Int)
  · subst z
    rw [Function.update_self,block_at _ p u.length (by simp)]
    simp
  · rw [Function.update_of_ne hz]
    by_cases hL : z=-1
    · subst z;rw [block_L,block_L]
    · simp only [blockTape,if_neg hL]
      have hne : z-(p : Int)≠(u.length : Int) := by omega
      have he := congrFun (input_replace u v a b) (z-(p : Int))
      rw [Function.update_of_ne hne] at he
      exact he

theorem block_prepend (v : List Bool) (b : Bool) (p : Nat) (hp : 0<p) :
    Function.update (blockTape v p) ((p : Int)-1) (enc b)=blockTape (b::v) (p-1) := by
  funext z
  by_cases hz : z=(p : Int)-1
  · subst z
    rw [Function.update_self]
    have he : (p : Int)-1=((p-1+0 : Nat) : Int) := by omega
    rw [he,block_at _ (p-1) 0 (by simp)]
    rfl
  · rw [Function.update_of_ne hz]
    by_cases hL : z=-1
    · subst z;rw [block_L,block_L]
    · by_cases hn : z<(p : Int)
      · rw [block_before v p z hL hn,block_before (b::v) (p-1) z hL (by omega)]
      · have he0 : z-(p : Int)=((z-(p : Int)).toNat : Int) := by omega
        have he1 : z-((p-1 : Nat) : Int)=(((z-(p : Int)).toNat+1 : Nat) : Int) := by omega
        simp only [blockTape,if_neg hL]
        rw [he0,he1]
        exact (input_cons b v _).symm

def holdState (b : Bool) : Fin 64 := if b then 32 else 31

theorem keep_step (q q' : Fin 64) (t : Int → Fin 32) (h : Int)
    (d : OneTapeTableau.Move)
    (hr : machine.rule q (t h) 0=some ⟨t h,q',d⟩) :
    step machine 0 ⟨q,h,t⟩=some ⟨q',moveHead d h,t⟩ := by
  simp [step,hr,writtenTape,Function.update_eq_self_iff]

theorem rule_hold_bit (b a : Bool) : machine.rule (holdState b) (enc a) 0=
    some ⟨enc b,holdState a,.left⟩ := by cases b <;> cases a <;> rfl

theorem rule_hold_blank (b : Bool) : machine.rule (holdState b) 2 0=
    some ⟨enc b,34,.left⟩ := by cases b <;> rfl

theorem roll_return (u v : List Bool) (b : Bool) (p : Nat) (hp : 0<p) :
    run machine (ticks (u.length+1))
      ⟨holdState b,(p+u.length : Nat)- (1 : Int),blockTape (u++v) p⟩ =
      some ⟨34,(p : Int)-2,blockTape ((u++[b])++v) (p-1)⟩ := by
  induction u using List.reverseRecOn generalizing b v with
  | nil =>
    simp only [List.nil_append,List.length_nil,Nat.add_zero]
    rw [run_ticks_one]
    have ht : blockTape v p ((p : Int)-1)=2 := block_before v p _ (by omega) (by omega)
    simp only [step,ht,rule_hold_blank,Option.map_some,writtenTape,moveHead]
    rw [block_prepend v b p hp]
    congr 2
    omega
  | append_singleton u a ih =>
    have he : (u++[a])++v=u++a::v := by simp
    have hhead : ((p+(u++[a]).length : Nat) : Int)-1=((p+u.length : Nat) : Int) := by simp;omega
    have ht : blockTape (u++a::v) p (p+u.length : Nat)=enc a := by
      rw [block_at _ p u.length (by simp)]
      simp
    have hs : step machine 0 ⟨holdState b,(p+u.length : Nat),blockTape (u++a::v) p⟩=
        some ⟨holdState a,((p+u.length : Nat) : Int)-1,blockTape (u++b::v) p⟩ := by
      simp only [step,ht,rule_hold_bit,Option.map_some,writtenTape,moveHead]
      rw [block_replace u v a b p]
    have hf : (u++[a]).length+1=1+(u.length+1) := by simp;omega
    rw [hf,ticks_add,run_append,he,hhead,run_ticks_one,hs,Option.bind_some,ih (b::v) a]
    simp only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append]

theorem input_erase_last (u : List Bool) (b : Bool) :
    Function.update (inputTape machine (u++[b])) (u.length : Int) 2=inputTape machine u := by
  funext z
  by_cases hz : z=(u.length : Int)
  · subst z;rw [Function.update_self,inputTape_ge machine u _ (by rfl)];rfl
  · rw [Function.update_of_ne hz]
    by_cases hn : z<0
    · rw [inputTape_neg machine _ z hn,inputTape_neg machine _ z hn]
    · have he : z=(z.toNat : Int) := by omega
      rw [he]
      by_cases hi : z.toNat<u.length
      · rw [input_nat_option,input_nat_option,List.getElem?_append_left hi]
      · have hge : ((u++[b]).length : Int)≤(z.toNat : Int) := by simp;omega
        rw [inputTape_ge machine _ _ hge,inputTape_ge machine u _ (by omega)]

theorem block_erase_last (u : List Bool) (b : Bool) (p : Nat) :
    Function.update (blockTape (u++[b]) p) (p+u.length : Nat) 2=blockTape u p := by
  funext z
  by_cases hz : z=((p+u.length : Nat) : Int)
  · subst z
    rw [Function.update_self,block_after u p _ (by rfl)]
  · rw [Function.update_of_ne hz]
    by_cases hL : z=-1
    · subst z;rw [block_L,block_L]
    · simp only [blockTape,if_neg hL]
      have hne : z-(p : Int)≠(u.length : Int) := by omega
      have he := congrFun (input_erase_last u b) (z-(p : Int))
      rw [Function.update_of_ne hne] at he
      exact he

theorem scan_block (v : List Bool) (p : Nat) :
    run machine (ticks v.length) ⟨29,(p : Int),blockTape v p⟩=
      some ⟨29,(p+v.length : Nat),blockTape v p⟩ := by
  have hs := StandardBitMarkedCompaction.scan_right machine 29 (blockTape v p)
    (p : Int) v.length (by
      intro i hi
      rw [show (p : Int)+(i : Int)=((p+i : Nat) : Int) by omega,block_at v p i hi]
      cases v[i] <;> rfl)
  simpa only [show (p : Int)+(v.length : Int)=((p+v.length : Nat) : Int) by omega] using hs

theorem scan_turn (v : List Bool) (p : Nat) :
    step machine 0 ⟨29,(p+v.length : Nat),blockTape v p⟩=
      some ⟨30,((p+v.length : Nat) : Int)-1,blockTape v p⟩ := by
  exact keep_step 29 30 (blockTape v p) ((p+v.length : Nat) : Int) .left (by
    rw [block_after v p _ (by rfl)]
    rfl)

theorem pop_last (u : List Bool) (b : Bool) (p : Nat) :
    step machine 0 ⟨30,(p+u.length : Nat),blockTape (u++[b]) p⟩=
      some ⟨holdState b,((p+u.length : Nat) : Int)-1,blockTape u p⟩ := by
  have ht : blockTape (u++[b]) p (p+u.length : Nat)=enc b := by
    rw [block_at _ p u.length (by simp)];simp
  have hr : machine.rule 30 (enc b) 0=some ⟨2,holdState b,.left⟩ := by cases b <;> rfl
  simp only [step,ht,hr,Option.map_some,writtenTape,moveHead]
  rw [block_erase_last u b p]

theorem shift_one (u : List Bool) (b : Bool) (p : Nat) (hp : 0<p) :
    run machine (ticks (2*(u++[b]).length+2)) ⟨29,(p : Int),blockTape (u++[b]) p⟩=
      some ⟨34,(p : Int)-2,blockTape (u++[b]) (p-1)⟩ := by
  have hf : 2*(u++[b]).length+2=(u++[b]).length+1+1+(u.length+1) := by simp;omega
  have hh : ((p+(u++[b]).length : Nat) : Int)-1=((p+u.length : Nat) : Int) := by simp;omega
  rw [hf,ticks_add,ticks_add,ticks_add,run_append,run_append,run_append,scan_block,
    Option.bind_some,run_ticks_one,scan_turn,Option.bind_some,hh,run_ticks_one,pop_last,
    Option.bind_some]
  simpa only [List.append_nil] using roll_return u [] b p hp

theorem shift_setup (v : List Bool) (p : Nat) :
    step machine 0 ⟨34,(p : Int),blockTape v (p+1)⟩=
      some ⟨29,(p+1 : Nat),blockTape v (p+1)⟩ := by
  have hs := keep_step 34 29 (blockTape v (p+1)) (p : Int) .right (by
    rw [block_before v (p+1) _ (by omega) (by omega)]
    rfl)
  simpa only [moveHead,show (p : Int)+1=((p+1 : Nat) : Int) by omega] using hs

theorem shift_origin (v : List Bool) :
    step machine 0 ⟨34,-1,blockTape v 0⟩=some ⟨36,0,blockTape v 0⟩ := by
  exact keep_step 34 36 (blockTape v 0) (-1) .right (by rw [block_L];rfl)

def shiftFuel (v : List Bool) (p : Nat) : Nat := p*(2*v.length+3)+1

theorem shift_run (u : List Bool) (b : Bool) (p : Nat) :
    run machine (ticks (shiftFuel (u++[b]) p))
      ⟨34,(p : Int)-1,blockTape (u++[b]) p⟩=some ⟨36,0,blockTape (u++[b]) 0⟩ := by
  induction p with
  | zero => rw [shiftFuel,Nat.zero_mul,Nat.zero_add,run_ticks_one];exact shift_origin _
  | succ p ih =>
    have hf : shiftFuel (u++[b]) (p+1)=1+(2*(u++[b]).length+2)+shiftFuel (u++[b]) p := by
      unfold shiftFuel;ring
    have hh : ((p+1 : Nat) : Int)-1=(p : Int) := by omega
    rw [hf,ticks_add,ticks_add,run_append,run_append,hh,run_ticks_one,shift_setup,
      Option.bind_some,shift_one u b (p+1) (by omega),Option.bind_some]
    have hh' : ((p+1 : Nat) : Int)-2=(p : Int)-1 := by omega
    rw [hh',Nat.add_sub_cancel]
    exact ih

theorem shift_normalize (u : List Bool) (b : Bool) (p : Nat) :
    run machine (ticks ((p+1)*(2*(u++[b]).length+3)))
      ⟨34,(p : Int)-1,blockTape (u++[b]) p⟩=
      some (StandardBitVariableAddNormalize.finalConfig (u++[b])) := by
  have hf : (p+1)*(2*(u++[b]).length+3)=shiftFuel (u++[b]) p+(2*(u++[b]).length+2) := by
    unfold shiftFuel;ring
  rw [hf,ticks_add,run_append,shift_run,Option.bind_some]
  exact StandardBitVariableAddNormalize.normalize_run _

theorem inspect_nonempty (u : List Bool) (b : Bool) (p : Nat) :
    step machine 0 ⟨28,(p : Int),blockTape (u++[b]) p⟩=
      some ⟨34,(p : Int)-1,blockTape (u++[b]) p⟩ := by
  have ht := block_at (u++[b]) p 0 (by simp)
  simp only [Nat.add_zero] at ht
  exact keep_step 28 34 _ (p : Int) .left (by rw [ht];cases (u++[b])[0] <;> rfl)

theorem inspect_normalize (u : List Bool) (b : Bool) (p : Nat) :
    run machine (ticks (1+(p+1)*(2*(u++[b]).length+3)))
      ⟨28,(p : Int),blockTape (u++[b]) p⟩=
      some (StandardBitVariableAddNormalize.finalConfig (u++[b])) := by
  rw [ticks_add,run_append,run_ticks_one,inspect_nonempty,Option.bind_some,shift_normalize]

theorem empty_finish (p : Nat) :
    step machine 0 ⟨35,-1,blockTape [] p⟩=
      some (StandardBitVariableAddNormalize.finalConfig []) := by
  have he : Function.update (blockTape [] p) (-1) 2=inputTape machine [] := by
    rw [block_nil,StandardBitVariableAdd.boundary_erase_L,StandardBitVariableAdd.inputTape_nil]
  simp only [step,block_L,StandardBitVariableAdd.rule_empty_L,Option.map_some,writtenTape,moveHead]
  rw [he]
  rfl

theorem empty_seek (p : Nat) :
    run machine (ticks (p+1)) ⟨35,(p : Int)-1,blockTape [] p⟩=
      some (StandardBitVariableAddNormalize.finalConfig []) := by
  have hs := StandardBitMarkedCompaction.scan_left machine 35 (blockTape [] p)
    ((p : Int)-1) p (by
      intro i hi
      have hL : (p : Int)-1-(i : Int)≠-1 := by omega
      rw [block_before [] p _ hL (by omega)]
      rfl)
  rw [show (p : Int)-1-(p : Int)=(-1 : Int) by omega] at hs
  rw [ticks_add,run_append,hs,Option.bind_some,run_ticks_one,empty_finish]

theorem inspect_empty (p : Nat) :
    run machine (ticks (p+2)) ⟨28,(p : Int),blockTape [] p⟩=
      some (StandardBitVariableAddNormalize.finalConfig []) := by
  have hs := keep_step 28 35 (blockTape [] p) (p : Int) .left (by
    rw [block_after [] p _ (by simp)]
    rfl)
  have hf : p+2=1+(p+1) := by omega
  rw [hf,ticks_add,run_append,run_ticks_one,hs,Option.bind_some]
  exact empty_seek p

end PakFixedPolyomino.StandardBitVariableAddShift
