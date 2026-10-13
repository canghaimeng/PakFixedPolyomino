import PakFixedPolyomino.StandardBitMetric

/-! Actual format-validity bit for EVERY raw input, using ordinary tape steps.
The parser erases its input and emits a single validity bit at the origin. -/
namespace PakFixedPolyomino.StandardBitPairValidity
open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open FiniteOneTapeSemantics (moveHead writtenTape)

def advance (q : Fin 3) (b : Bool) : Fin 3 :=
  if q = 0 then if b then 1 else 2 else if q = 1 then 0 else 2
def after (q : Fin 3) : List Bool → Fin 3
  | [] => q
  | b::w => after (advance q b) w
def valid (w : List Bool) : Bool := (unpairBits w).isSome
def modeValid (q : Fin 3) : Bool := decide (q = 2)
def enc (b : Bool) : Fin 4 := if b then 1 else 0
def phaseState (q : Fin 3) : Fin 11 := ⟨q.val+4,by omega⟩
def returnState (b : Bool) : Fin 11 := if b then 7 else 8
def emitState (b : Bool) : Fin 11 := if b then 9 else 10

theorem after_append (q : Fin 3) (x y : List Bool) :
    after q (x++y) = after (after q x) y := by
  induction x generalizing q with
  | nil => rfl
  | cons b x ih => simpa only [List.cons_append,after] using ih (advance q b)

theorem after_suffix (w : List Bool) : after 2 w = 2 := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [after,advance] using ih

theorem valid_word (w : List Bool) : modeValid (after 0 w) = valid w := by
  have aux : ∀ n : Nat, ∀ w : List Bool, w.length = n →
      modeValid (after 0 w) = valid w := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hn
      cases w with
      | nil => rfl
      | cons b rest =>
        cases b with
        | false => simp [after,advance,after_suffix,modeValid,valid,unpairBits]
        | true =>
          cases rest with
          | nil => rfl
          | cons b rest =>
            have hr := ih rest.length (by simp only [List.length_cons] at hn; omega) rest rfl
            cases hp : unpairBits rest <;>
              simpa [after,advance,modeValid,valid,unpairBits,hp] using hr
  exact aux w.length w rfl

def machine : DeterministicMachine 11 4 where
  rule := fun q s _ =>
    if q = 2 then some ⟨s,3,.left⟩
    else if q = 3 then some ⟨3,4,.right⟩
    else if q = 4 then
      if s = 1 then some ⟨2,5,.right⟩
      else if s = 0 then some ⟨2,6,.right⟩
      else some ⟨2,8,.left⟩
    else if q = 5 then
      if s = 0 ∨ s = 1 then some ⟨2,4,.right⟩
      else some ⟨2,8,.left⟩
    else if q = 6 then
      if s = 0 ∨ s = 1 then some ⟨2,6,.right⟩
      else some ⟨2,7,.left⟩
    else if q = 7 ∨ q = 8 then
      if s = 3 then some ⟨2,if q = 7 then 9 else 10,.right⟩
      else some ⟨s,q,.left⟩
    else if q = 9 then some ⟨1,0,.stay⟩
    else if q = 10 then some ⟨0,0,.stay⟩
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

theorem config_ext {a b : Configuration 11 4}
    (hs : a.state = b.state) (hh : a.head = b.head) (ht : a.tape = b.tape) : a = b := by
  cases a; cases b; simp_all

def scanTape (w : List Bool) (k : Nat) (z : Int) : Fin 4 :=
  if z = -1 then 3
  else if 0 ≤ z ∧ z.toNat < k then 2 else inputTape machine w z
def scanConfig (w : List Bool) (k : Nat) (q : Fin 3) : Configuration 11 4 :=
  ⟨phaseState q,k,scanTape w k⟩
def endTape (z : Int) : Fin 4 := if z = -1 then 3 else 2
def returnConfig (b : Bool) (z : Int) : Configuration 11 4 :=
  ⟨returnState b,z,endTape⟩
def finalConfig (b : Bool) : Configuration 11 4 :=
  ⟨0,0,inputTape machine [b]⟩

theorem setup_run (w : List Bool) :
    run machine (ticks 2) (initial machine w) = some (scanConfig w 0 0) := by
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

theorem phase_rule (q : Fin 3) (b : Bool) :
    machine.rule (phaseState q) (enc b) 0 =
      some ⟨2,phaseState (advance q b),.right⟩ := by
  fin_cases q <;> cases b <;> simp [machine,phaseState,advance,enc]

theorem scan_step (w : List Bool) (k : Nat) (q : Fin 3) (hk : k < w.length) :
    step machine 0 (scanConfig w k q) = some (scanConfig w (k+1) (advance q w[k])) := by
  simp only [step,scanConfig,scan_read w k hk]
  rw [phase_rule]
  simp [writtenTape,scan_update,moveHead,Nat.cast_succ]

theorem scan_run (w : List Bool) (k : Nat) (hk : k ≤ w.length) (q : Fin 3) :
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

theorem end_step (w : List Bool) (q : Fin 3) :
    step machine 0 (scanConfig w w.length q) =
      some (returnConfig (modeValid q) ((w.length : Int)-1)) := by
  have hr : endTape (w.length : Int) = 2 := by simp [endTape]
  rw [show scanConfig w w.length q = ⟨phaseState q,w.length,endTape⟩ by
    simp [scanConfig,scan_end]]
  fin_cases q <;>
    simp [step,hr,phaseState,machine,returnConfig,returnState,modeValid,moveHead,writtenTape]

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

theorem validity_run (w : List Bool) :
    run machine (ticks (2*w.length+5)) (initial machine w) = some (finalConfig (valid w)) := by
  rw [show 2*w.length+5 = 2+w.length+1+w.length+2 by omega,ticks_add,run_append,
    ticks_add,run_append,ticks_add,run_append,ticks_add,run_append,
    setup_run,Option.bind_some,scan_run w w.length (le_rfl) 0,Option.bind_some,
    run_ticks_one,end_step,Option.bind_some,return_run,Option.bind_some,finish_run]
  simp [valid_word]

theorem validity_computes : ComputesWithin machine (fun w => [valid w]) (fun k => 2*k+5) := by
  intro w
  exact ⟨2*w.length+5,finalConfig (valid w),le_rfl,validity_run w,⟨rfl,rfl,rfl⟩⟩

theorem validity_polyBitTime : PolyBitTime (fun w => [valid w]) := by
  refine ⟨11,4,machine,2*Polynomial.X+5,?_⟩
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_X] using validity_computes

theorem valid_pair (x y : List Bool) : valid (pairBits x y) = true := by
  simp [valid,unpair_pairBits]

theorem valid_none (w : List Bool) (h : unpairBits w = none) : valid w = false := by
  simp [valid,h]

theorem valid_iff (w : List Bool) :
    valid w = true ↔ ∃ x y, unpairBits w = some (x,y) := by
  cases h : unpairBits w with
  | none => simp [valid,h]
  | some pair =>
    rcases pair with ⟨x,y⟩
    simp [valid,h]

theorem validity_exact (w : List Bool) :
    run machine (ticks (2*w.length+5)) (initial machine w) = some (finalConfig (valid w)) ∧
    Output machine [valid w] (finalConfig (valid w)) ∧
    RunsAtMost machine w (2*w.length+5) ∧
    (valid w = true ↔ ∃ x y, unpairBits w = some (x,y)) := by
  have hr := validity_run w
  exact ⟨hr,⟨rfl,rfl,rfl⟩,halting_runsAtMost machine w _ _ hr rfl,valid_iff w⟩

theorem validity_bit_spec :
    PolyBitTime (fun w => [valid w]) ∧
    ∀ w, run machine (ticks (2*w.length+5)) (initial machine w) = some (finalConfig (valid w)) ∧
      Output machine [valid w] (finalConfig (valid w)) ∧
      RunsAtMost machine w (2*w.length+5) ∧
      (valid w = true ↔ ∃ x y, unpairBits w = some (x,y)) :=
  ⟨validity_polyBitTime,validity_exact⟩

end PakFixedPolyomino.StandardBitPairValidity
