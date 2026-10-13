import PakFixedPolyomino.StandardBitDecrementWord

/-! Literal division by two shifts every raw little-endian word left one cell.
High zero digits are retained. All tape cells and ordinary transitions count. -/
namespace PakFixedPolyomino.StandardBitHalve
open StandardNondeterministicMachine StandardBitTime
open StandardBitDecrementWord (value)
open FiniteOneTapeSemantics (moveHead writtenTape)
set_option linter.unusedSimpArgs false

def halveBits (w : List Bool) : List Bool := w.tail
def enc (b : Bool) : Fin 4 := if b then 1 else 0
def carry (b : Bool) : Fin 10 := if b then 7 else 6

def machine : DeterministicMachine 10 4 where
  rule := fun q a _ =>
    if q = 2 then some ⟨a,3,.left⟩
    else if q = 3 then some ⟨3,4,.right⟩
    else if q = 4 then
      if a = 0 ∨ a = 1 then some ⟨2,5,.right⟩ else some ⟨a,9,.left⟩
    else if q = 5 then
      if a = 0 then some ⟨2,6,.left⟩
      else if a = 1 then some ⟨2,7,.left⟩ else some ⟨a,9,.left⟩
    else if q = 6 then some ⟨0,8,.right⟩
    else if q = 7 then some ⟨1,8,.right⟩
    else if q = 8 then some ⟨a,5,.right⟩
    else if q = 9 then
      if a = 3 then some ⟨2,0,.right⟩ else some ⟨a,9,.left⟩
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

def markedTape (w : List Bool) : Int → Fin 4 :=
  Function.update (inputTape machine (halveBits w)) (-1) 3

def phaseTape (w : List Bool) (k : Nat) (z : Int) : Fin 4 :=
  if z = -1 then 3
  else if 0 ≤ z ∧ z.toNat < k-1 then inputTape machine (halveBits w) z
  else if z = (k : Int)-1 then 2 else inputTape machine w z

def phaseConfig (w : List Bool) (k : Nat) : Configuration 10 4 :=
  ⟨5,k,phaseTape w k⟩
def returnConfig (w : List Bool) (z : Int) : Configuration 10 4 :=
  ⟨9,z,markedTape w⟩
def finalConfig (w : List Bool) : Configuration 10 4 :=
  ⟨0,0,inputTape machine (halveBits w)⟩

theorem halve_value (w : List Bool) : value (halveBits w) = value w / 2 := by
  cases w with
  | nil => rfl
  | cons b w => cases b <;> simp [halveBits,value] <;> omega

theorem halve_length (w : List Bool) : (halveBits w).length = w.length-1 := by
  simp [halveBits]

theorem tail_read (w : List Bool) (k : Nat) (hpos : 0 < k) (hk : k < w.length) :
    inputTape machine (halveBits w) ((k : Int)-1) = enc w[k] := by
  cases k with
  | zero => omega
  | succ k =>
    cases w with
    | nil => simp at hk
    | cons b w =>
      have he : ((k+1 : Nat) : Int)-1 = (k : Int) := by omega
      rw [he]
      simp [inputTape,halveBits,enc,machine,show k < w.length by simpa using hk]
      rfl

theorem start_run (w : List Bool) :
    run machine (ticks 2) (initial machine w) =
      some ⟨4,0,Function.update (inputTape machine w) (-1) 3⟩ := by
  simp [ticks,run,step,machine,initial,moveHead,writtenTape,Function.update_eq_self]

theorem setup_run (b : Bool) (w : List Bool) :
    run machine (ticks 3) (initial machine (b::w)) = some (phaseConfig (b::w) 1) := by
  have ht : Function.update (Function.update (inputTape machine (b::w)) (-1) 3) 0 2 =
      phaseTape (b::w) 1 := by
    funext z
    by_cases hz : z = -1 <;> by_cases h0 : z = 0 <;>
      simp [phaseTape,Function.update_apply,hz,h0]
  rw [show 3 = 2+1 by rfl,ticks_add,run_append,start_run,Option.bind_some,run_ticks_one]
  cases b <;> simp [step,machine,inputTape,moveHead,writtenTape,phaseConfig]
  all_goals exact ht

theorem phase_read (w : List Bool) (k : Nat) (hpos : 0 < k) (hk : k < w.length) :
    phaseTape w k k = enc w[k] := by
  have hn : (k : Int) ≠ -1 := by omega
  simp [phaseTape,hn,inputTape,enc,machine,hk,show ¬k < k-1 by omega,show (k : Int) ≠ (k : Int)-1 by omega]

theorem phase_update (w : List Bool) (k : Nat) (hpos : 0 < k) (hk : k < w.length) :
    Function.update (Function.update (phaseTape w k) k 2) ((k : Int)-1) (enc w[k]) =
      phaseTape w (k+1) := by
  funext z
  by_cases hlast : z = (k : Int)-1
  · subst z
    have hn : (k : Int)-1 ≠ -1 := by omega
    have he : ((k : Int)-1).toNat = k-1 := by omega
    simp [phaseTape,Function.update_apply,hn,he,tail_read w k hpos hk,
      show 0 ≤ (k : Int)-1 by omega,show k-1 < k by omega]
    intro hzero; omega
  · by_cases hz : z = (k : Int)
    · subst z
      have hn : (k : Int) ≠ -1 := by omega
      simp [phaseTape,Function.update_apply,hlast,hn]
    · rw [Function.update_of_ne hlast,Function.update_of_ne hz]
      unfold phaseTape
      split_ifs <;> first | rfl | (exfalso; omega)

theorem phase_cycle (w : List Bool) (k : Nat) (hpos : 0 < k) (hk : k < w.length) :
    run machine (ticks 3) (phaseConfig w k) = some (phaseConfig w (k+1)) := by
  have he : ((k : Int)-1)+1 = (k : Int) := by omega
  have hn : (k : Int) ≠ (k : Int)-1 := by omega
  have hfinish : Function.update
      (Function.update (Function.update (phaseTape w k) k 2) ((k : Int)-1) (enc w[k])) k 2 =
      Function.update (Function.update (phaseTape w k) k 2) ((k : Int)-1) (enc w[k]) := by
    rw [Function.update_comm (Ne.symm hn),Function.update_idem]
  cases hb : w[k] <;>
    simp [ticks,run,step,phaseConfig,phase_read w k hpos hk,machine,enc,hb,
      moveHead,writtenTape,he,hn,Function.update_apply]
  all_goals simpa [enc,hb] using hfinish.trans (phase_update w k hpos hk)

theorem phase_run (w : List Bool) (j : Nat) (hj : j+1 ≤ w.length) :
    run machine (ticks (3*j)) (phaseConfig w 1) = some (phaseConfig w (j+1)) := by
  induction j with
  | zero => simp [ticks]
  | succ j ih =>
    rw [show 3*(j+1) = 3*j+3 by omega,ticks_add,run_append,ih (by omega),Option.bind_some]
    exact phase_cycle w (j+1) (by omega) (by omega)

theorem phase_end (w : List Bool) (hw : 0 < w.length) :
    phaseTape w w.length = markedTape w := by
  funext z
  by_cases hz : z = -1
  · simp [phaseTape,markedTape,Function.update_apply,hz]
  · unfold markedTape
    rw [Function.update_of_ne hz]
    simp only [phaseTape,if_neg hz]
    by_cases hge : 0 ≤ z
    · by_cases hi : z.toNat < w.length-1
      · simp [hge,hi]
      · rw [if_neg (by simp [hi])]
        have htail : (halveBits w).length ≤ z.toNat := by rw [halve_length]; omega
        rw [inputTape_ge machine (halveBits w) z (by omega)]
        split_ifs with he
        · rfl
        · rw [inputTape_ge machine w z (by omega)]
    · rw [if_neg (by simp [hge])]
      have hn : z ≠ (w.length : Int)-1 := by omega
      rw [if_neg hn,inputTape_neg machine w z (by omega),inputTape_neg machine (halveBits w) z (by omega)]

theorem end_step (w : List Bool) (hw : 0 < w.length) :
    step machine 0 (phaseConfig w w.length) = some (returnConfig w ((w.length : Int)-1)) := by
  have hr : markedTape w (w.length : Int) = 2 := by
    rw [markedTape,Function.update_of_ne (by omega),inputTape_ge machine (halveBits w) _ (by rw [halve_length]; omega)]
    rfl
  rw [show phaseConfig w w.length = ⟨5,w.length,markedTape w⟩ by simp [phaseConfig,phase_end w hw]]
  simp [step,hr,machine,moveHead,writtenTape,returnConfig]

theorem return_step (w : List Bool) (k : Nat) :
    step machine 0 (returnConfig w k) = some (returnConfig w ((k : Int)-1)) := by
  have hn : markedTape w (k : Int) ≠ 3 := by
    simp [markedTape,Function.update_apply,inputTape,machine]
    split_ifs <;> decide
  simp [step,returnConfig,machine,hn,moveHead,writtenTape]

theorem return_run (w : List Bool) (k : Nat) :
    run machine (ticks k) (returnConfig w ((k : Int)-1)) = some (returnConfig w (-1)) := by
  induction k with
  | zero => simp [ticks]
  | succ k ih =>
    rw [show k+1 = 1+k by omega,ticks_add,run_append,run_ticks_one]
    have hs : ((1+k : Nat) : Int)-1 = (k : Int) := by omega
    rw [hs,return_step,Option.bind_some,ih]

theorem finish_step (w : List Bool) :
    step machine 0 (returnConfig w (-1)) = some (finalConfig w) := by
  have ht : Function.update (markedTape w) (-1) 2 = inputTape machine (halveBits w) := by
    funext z
    by_cases hz : z = -1
    · subst z
      simp [Function.update_apply,inputTape,markedTape,machine]
    · simp [Function.update_apply,markedTape,hz]

  simp [step,returnConfig,markedTape,machine,moveHead,writtenTape,finalConfig] at ht ⊢
  exact ht

theorem nonempty_run (b : Bool) (w : List Bool) :
    run machine (ticks (4*(b::w).length+2)) (initial machine (b::w)) = some (finalConfig (b::w)) := by
  rw [show 4*(b::w).length+2 = 3+3*w.length+1+(b::w).length+1 by simp; omega,
    ticks_add,run_append,ticks_add,run_append,ticks_add,run_append,ticks_add,run_append,
    setup_run,Option.bind_some,phase_run (b::w) w.length (by simp),Option.bind_some]
  rw [show w.length+1 = (b::w).length by simp,run_ticks_one,end_step _ (by simp),Option.bind_some,
    return_run,Option.bind_some,run_ticks_one,finish_step]

theorem empty_run : run machine (ticks 4) (initial machine []) = some (finalConfig []) := by
  rw [show ticks 4 = ticks (2+1+1) by rfl,ticks_add,run_append,ticks_add,run_append,start_run,
    Option.bind_some,run_ticks_one]
  have hs : step machine 0 ⟨4,0,Function.update (inputTape machine []) (-1) 3⟩ =
      some (returnConfig [] (-1)) := by
    simp [step,machine,inputTape,moveHead,writtenTape,returnConfig,markedTape,halveBits]
  rw [hs,Option.bind_some,run_ticks_one,finish_step]

theorem halve_computes : ComputesWithin machine halveBits (fun n => 4*n+4) := by
  intro w
  cases w with
  | nil => exact ⟨4,finalConfig [],le_rfl,empty_run,⟨rfl,rfl,rfl⟩⟩
  | cons b w => exact ⟨4*(b::w).length+2,finalConfig (b::w),by dsimp; omega,nonempty_run b w,⟨rfl,rfl,rfl⟩⟩

theorem halve_polyBitTime : PolyBitTime halveBits := by
  refine ⟨10,4,machine,4*Polynomial.X+4,?_⟩
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    using halve_computes

theorem halve_bit_spec : PolyBitTime halveBits ∧ ∀ w,
    value (halveBits w) = value w / 2 ∧ (halveBits w).length = w.length-1 ∧
    (∃ n out, n ≤ 4*w.length+4 ∧ run machine (ticks n) (initial machine w) = some out ∧
      Output machine (halveBits w) out) ∧ RunsAtMost machine w (4*w.length+4) := by
  refine ⟨halve_polyBitTime,?_⟩
  intro w
  exact ⟨halve_value w,halve_length w,halve_computes w,
    (ComputesWithin.actual_bounds machine halveBits _ halve_computes w).1⟩

end PakFixedPolyomino.StandardBitHalve
