import PakFixedPolyomino.StandardBitDecrementWord

/-! A literal ten-state machine tests the usual positional value for zero.
It consumes every raw bit and emits one clean bit in genuine ordinary time. -/
namespace PakFixedPolyomino.StandardBitZero
open StandardNondeterministicMachine StandardBitTime
open StandardBitDecrementWord (value)
open FiniteOneTapeSemantics (moveHead writtenTape)
set_option linter.unusedSimpArgs false

def advance (q b : Bool) : Bool := q || b

def after (q : Bool) : List Bool → Bool
  | [] => q
  | b::w => after (advance q b) w

def zeroBit (w : List Bool) : Bool := !(after false w)
def enc (b : Bool) : Fin 4 := if b then 1 else 0
def phaseState (q : Bool) : Fin 10 := if q then 5 else 4
def returnState (b : Bool) : Fin 10 := if b then 6 else 7
def emitState (b : Bool) : Fin 10 := if b then 8 else 9

theorem after_append (q : Bool) (x y : List Bool) :
    after q (x++y) = after (after q x) y := by
  induction x generalizing q with
  | nil => rfl
  | cons b x ih => simpa only [List.cons_append,after] using ih (advance q b)

theorem after_any (q : Bool) (w : List Bool) : after q w = (q || w.any id) := by
  induction w generalizing q with
  | nil => simp [after]
  | cons b w ih => simp [after,advance,ih,Bool.or_assoc]

theorem value_zero (w : List Bool) : value w = 0 ↔ w.any id = false := by
  induction w with
  | nil => simp [value]
  | cons b w ih =>
    cases b with
    | false => simpa [value] using ih
    | true => simp [value]

theorem zeroBit_iff (w : List Bool) : zeroBit w = true ↔ value w = 0 := by
  rw [zeroBit,after_any]
  have hv := value_zero w
  cases ha : w.any id <;> simp [ha] at hv ⊢ <;> exact hv

def machine : DeterministicMachine 10 4 where
  rule := fun q s _ =>
    if q = 2 then some ⟨s,3,.left⟩
    else if q = 3 then some ⟨3,4,.right⟩
    else if q = 4 then
      if s = 0 then some ⟨2,4,.right⟩
      else if s = 1 then some ⟨2,5,.right⟩
      else some ⟨2,6,.left⟩
    else if q = 5 then
      if s = 0 ∨ s = 1 then some ⟨2,5,.right⟩
      else some ⟨2,7,.left⟩
    else if q = 6 ∨ q = 7 then
      if s = 3 then some ⟨2,if q = 6 then 8 else 9,.right⟩
      else some ⟨s,q,.left⟩
    else if q = 8 then some ⟨1,0,.stay⟩
    else if q = 9 then some ⟨0,0,.stay⟩
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

def scanTape (w : List Bool) (k : Nat) (z : Int) : Fin 4 :=
  if z = -1 then 3
  else if 0 ≤ z ∧ z.toNat < k then 2 else inputTape machine w z
def scanConfig (w : List Bool) (k : Nat) (q : Bool) : Configuration 10 4 :=
  ⟨phaseState q,k,scanTape w k⟩
def endTape (z : Int) : Fin 4 := if z = -1 then 3 else 2
def returnConfig (b : Bool) (z : Int) : Configuration 10 4 :=
  ⟨returnState b,z,endTape⟩
def finalConfig (b : Bool) : Configuration 10 4 :=
  ⟨0,0,inputTape machine [b]⟩

theorem setup_run (w : List Bool) :
    run machine (ticks 2) (initial machine w) = some (scanConfig w 0 false) := by
  have ht : Function.update (inputTape machine w) (-1) 3 = scanTape w 0 := by
    funext z
    by_cases hz : z = -1 <;> simp [scanTape,Function.update_apply,hz]
  simp [ticks,run,step,machine,initial,moveHead,writtenTape,
    Function.update_eq_self,scanConfig,phaseState]
  exact ht

theorem scan_read (w : List Bool) (k : Nat) (hk : k < w.length) :
    scanTape w k (k : Int) = enc w[k] := by
  have hn : (k : Int) ≠ -1 := by omega
  simp [scanTape,hn,inputTape,enc,hk,machine]

theorem scan_update (w : List Bool) (k : Nat) :
    Function.update (scanTape w k) k 2 = scanTape w (k+1) := by
  funext z
  by_cases hz : z = (k : Int)
  · subst z
    have hn : (k : Int) ≠ -1 := by omega
    simp [scanTape,hn]
  · rw [Function.update_of_ne hz]
    unfold scanTape
    split_ifs <;> first | rfl | (exfalso; omega)

theorem phase_rule (q : Bool) (b : Bool) :
    machine.rule (phaseState q) (enc b) 0 =
      some ⟨2,phaseState (advance q b),.right⟩ := by
  cases q <;> cases b <;> simp [machine,phaseState,advance,enc]

theorem scan_step (w : List Bool) (k : Nat) (q : Bool) (hk : k < w.length) :
    step machine 0 (scanConfig w k q) = some (scanConfig w (k+1) (advance q w[k])) := by
  simp only [step,scanConfig,scan_read w k hk]
  rw [phase_rule]
  simp [writtenTape,scan_update,moveHead,Nat.cast_succ]

theorem scan_run (w : List Bool) (k : Nat) (hk : k ≤ w.length) (q : Bool) :
    run machine (ticks k) (scanConfig w 0 q) =
      some (scanConfig w k (after q (w.take k))) := by
  induction k with
  | zero => simp [ticks,after]
  | succ k ih =>
    have hlt : k < w.length := by omega
    rw [show k+1 = k+1 by rfl,ticks_add,run_append,ih (by omega),Option.bind_some,run_ticks_one]
    rw [List.take_succ_eq_append_getElem hlt,after_append]
    simpa only [after] using scan_step w k (after q (w.take k)) hlt

theorem scan_end (w : List Bool) : scanTape w w.length = endTape := by
  funext z
  by_cases hz : z = -1
  · simp [scanTape,endTape,hz]
  · simp only [scanTape,endTape,if_neg hz]
    by_cases hge : 0 ≤ z
    · by_cases hi : z.toNat < w.length
      · simp [hge,hi]
      · rw [if_neg (by simp [hi]),inputTape_ge machine w z (by omega)]
        rfl
    · rw [if_neg (by simp [hge]),inputTape_neg machine w z (by omega)]
      rfl

theorem end_step (w : List Bool) (q : Bool) :
    step machine 0 (scanConfig w w.length q) =
      some (returnConfig (!q) ((w.length : Int)-1)) := by
  have hr : endTape (w.length : Int) = 2 := by simp [endTape]
  rw [show scanConfig w w.length q = ⟨phaseState q,w.length,endTape⟩ by
    simp [scanConfig,scan_end]]
  cases q <;>
    simp [step,hr,phaseState,machine,returnConfig,returnState,moveHead,writtenTape]

theorem return_step (b : Bool) (k : Nat) :
    step machine 0 (returnConfig b k) = some (returnConfig b ((k : Int)-1)) := by
  have hr : endTape (k : Int) = 2 := by simp [endTape]
  cases b <;>
    simp [step,returnConfig,returnState,machine,hr,moveHead,writtenTape]

theorem return_run (b : Bool) (k : Nat) :
    run machine (ticks k) (returnConfig b ((k : Int)-1)) = some (returnConfig b (-1)) := by
  induction k with
  | zero => simp [ticks]
  | succ k ih =>
    rw [show k+1 = 1+k by omega,ticks_add,run_append,run_ticks_one]
    have hs : ((1+k : Nat) : Int)-1 = (k : Int) := by omega
    rw [hs,return_step,Option.bind_some,ih]

theorem finish_run (b : Bool) :
    run machine (ticks 2) (returnConfig b (-1)) = some (finalConfig b) := by
  have ht : Function.update endTape (-1) 2 = fun _ => (2 : Fin 4) := by
    funext z
    by_cases hz : z = -1 <;> simp [endTape,Function.update_apply,hz]
  have ho : Function.update (fun _ : Int => (2 : Fin 4)) 0 (enc b) = inputTape machine [b] := by
    funext z
    by_cases hz : z = 0
    · subst z; simp [inputTape,enc,machine]
    · rw [Function.update_of_ne hz]
      by_cases hge : 0 ≤ z
      · rw [inputTape_ge machine [b] z (by simp only [List.length_singleton]; omega)]
        rfl
      · rw [inputTape_neg machine [b] z (by omega)]
        rfl
  cases b <;>
    simp [ticks,run,step,returnConfig,returnState,emitState,endTape,machine,
      moveHead,writtenTape,ht,finalConfig]
  all_goals exact ho

theorem zero_run (w : List Bool) :
    run machine (ticks (2*w.length+5)) (initial machine w) = some (finalConfig (zeroBit w)) := by
  rw [show 2*w.length+5 = 2+w.length+1+w.length+2 by omega,ticks_add,run_append,
    ticks_add,run_append,ticks_add,run_append,ticks_add,run_append,
    setup_run,Option.bind_some,scan_run w w.length (le_rfl) false,Option.bind_some,
    run_ticks_one,end_step,Option.bind_some,return_run,Option.bind_some,finish_run]
  simp [zeroBit]

theorem zero_computes : ComputesWithin machine (fun w => [zeroBit w]) (fun k => 2*k+5) := by
  intro w
  exact ⟨2*w.length+5,finalConfig (zeroBit w),le_rfl,zero_run w,⟨rfl,rfl,rfl⟩⟩

theorem zero_polyBitTime : PolyBitTime (fun w => [zeroBit w]) := by
  refine ⟨10,4,machine,2*Polynomial.X+5,?_⟩
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_X] using zero_computes

theorem zero_bit_spec :
    PolyBitTime (fun w => [zeroBit w]) ∧
    ∀ w, run machine (ticks (2*w.length+5)) (initial machine w) = some (finalConfig (zeroBit w)) ∧
      Output machine [zeroBit w] (finalConfig (zeroBit w)) ∧
      RunsAtMost machine w (2*w.length+5) ∧ (zeroBit w = true ↔ value w = 0) := by
  refine ⟨zero_polyBitTime,?_⟩
  intro w
  exact ⟨zero_run w,⟨rfl,rfl,rfl⟩,
    halting_runsAtMost machine w _ _ (zero_run w) rfl,zeroBit_iff w⟩

end PakFixedPolyomino.StandardBitZero
