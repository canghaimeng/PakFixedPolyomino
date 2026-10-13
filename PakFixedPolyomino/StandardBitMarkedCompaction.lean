import PakFixedPolyomino.StandardBitPairCompactionTape

/-! Actual tape-transition compaction under explicit finite rule equalities.
The parser and ordinary initialized run are separate stages. -/
namespace PakFixedPolyomino.StandardBitMarkedCompaction
open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open StandardBitPairCompactionTape
open FiniteOneTapeSemantics (moveHead writtenTape)

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000
attribute [-simp] Nat.cast_add Nat.cast_mul Nat.cast_zero Nat.cast_sub

def carry (b : Bool) : Fin 17 := if b then 11 else 10

def CycleRules (M : DeterministicMachine 17 8) : Prop :=
  (∀ a, M.rule 9 a 0 =
    if a = 6 then some ⟨2,10,.left⟩
    else if a = 7 then some ⟨2,11,.left⟩
    else if a = 5 then some ⟨2,13,.left⟩
    else some ⟨a,9,.right⟩) ∧
  (∀ b a, M.rule (carry b) a 0 =
    if a = 4 then some ⟨enc b,12,.right⟩ else some ⟨a,carry b,.left⟩) ∧
  (∀ a, M.rule 12 a 0 = some ⟨4,9,.stay⟩)

def copyConfig (x y : List Bool) (k : Nat) : Configuration 17 8 :=
  ⟨9,k,tape x y k⟩

def takenTape (x y : List Bool) (k : Nat) : Int → Fin 8 :=
  Function.update (tape x y k) ((2*k+1 : Nat) : Int) 2

def placedTape (x y : List Bool) (k : Nat) (hk : k < x.length) : Int → Fin 8 :=
  Function.update (takenTape x y k) (k : Int) (enc x[k])

theorem preserve_step {ns nt : Nat} (M : DeterministicMachine ns nt)
    (q : Fin ns) (t : Int → Fin nt) (h : Int) (d : OneTapeTableau.Move)
    (hr : M.rule q (t h) 0 = some ⟨t h,q,d⟩) :
    step M 0 ⟨q,h,t⟩ = some ⟨q,moveHead d h,t⟩ := by
  simp [step,hr,writtenTape,Function.update_eq_self_iff]

theorem scan_right {ns nt : Nat} (M : DeterministicMachine ns nt)
    (q : Fin ns) (t : Int → Fin nt) (h : Int) (n : Nat)
    (hr : ∀ i < n, M.rule q (t (h+(i : Int))) 0 =
      some ⟨t (h+(i : Int)),q,.right⟩) :
    run M (ticks n) ⟨q,h,t⟩ = some ⟨q,h+(n : Int),t⟩ := by
  induction n with
  | zero => simp [ticks]
  | succ n ih =>
    rw [ticks_add,run_append,ih (fun i hi => hr i (by omega)),Option.bind_some,run_ticks_one]
    have hs := preserve_step M q t (h+(n : Int)) .right (hr n (by omega))
    simpa [moveHead,add_assoc] using hs

theorem scan_left {ns nt : Nat} (M : DeterministicMachine ns nt)
    (q : Fin ns) (t : Int → Fin nt) (h : Int) (n : Nat)
    (hr : ∀ i < n, M.rule q (t (h-(i : Int))) 0 =
      some ⟨t (h-(i : Int)),q,.left⟩) :
    run M (ticks n) ⟨q,h,t⟩ = some ⟨q,h-(n : Int),t⟩ := by
  induction n with
  | zero => simp [ticks]
  | succ n ih =>
    rw [ticks_add,run_append,ih (fun i hi => hr i (by omega)),Option.bind_some,run_ticks_one]
    have hs := preserve_step M q t (h-(n : Int)) .left (hr n (by omega))
    simpa [moveHead,sub_sub] using hs

theorem seek_run (M : DeterministicMachine 17 8) (hr : CycleRules M)
    (x y : List Bool) (k : Nat) (hk : k ≤ x.length) :
    run M (ticks (k+1)) (copyConfig x y k) =
      some ⟨9,((2*k+1 : Nat) : Int),tape x y k⟩ := by
  have hs := scan_right M 9 (tape x y k) (k : Int) (k+1)
  have hc : (k : Int)+((k+1 : Nat) : Int) = ((2*k+1 : Nat) : Int) := by omega
  rw [hc] at hs
  apply hs
  intro i hi
  have hh : (k : Int)+(i : Int) = ((k+i : Nat) : Int) := by omega
  rw [hh,hr.1]
  by_cases hz : i = 0
  · subst i
    simp only [Nat.add_zero,tape_dest]
    decide
  · have hgap := tape_gap x y k (k+i) hk (by omega) (by omega)
    rw [hgap]
    decide

theorem take_step (M : DeterministicMachine 17 8) (hr : CycleRules M)
    (x y : List Bool) (k : Nat) (hk : k < x.length) :
    step M 0 ⟨9,((2*k+1 : Nat) : Int),tape x y k⟩ =
      some ⟨carry x[k],((2*k : Nat) : Int),takenTape x y k⟩ := by
  have ht := tape_source x y k hk
  have hq : M.rule 9 (mark x[k]) 0 = some ⟨2,carry x[k],.left⟩ := by
    rw [hr.1]
    cases x[k] <;> simp [mark,carry]
  have hh : ((2*k+1 : Nat) : Int)-1 = ((2*k : Nat) : Int) := by omega
  simp only [step,ht,hq,Option.map_some,moveHead,writtenTape,hh,takenTape]

theorem taken_dest (x y : List Bool) (k : Nat) : takenTape x y k (k : Int) = 4 := by
  have hn : (k : Int) ≠ ((2*k+1 : Nat) : Int) := by omega
  rw [takenTape,Function.update_of_ne hn,tape_dest]

theorem taken_gap (x y : List Bool) (k i : Nat) (hk : k ≤ x.length)
    (hlo : k < i) (hhi : i < 2*k+1) : takenTape x y k (i : Int) = 2 := by
  have hn : (i : Int) ≠ ((2*k+1 : Nat) : Int) := by omega
  rw [takenTape,Function.update_of_ne hn,tape_gap x y k i hk hlo hhi]

theorem carry_run (M : DeterministicMachine 17 8) (hr : CycleRules M)
    (x y : List Bool) (k : Nat) (hk : k < x.length) :
    run M (ticks k) ⟨carry x[k],((2*k : Nat) : Int),takenTape x y k⟩ =
      some ⟨carry x[k],(k : Int),takenTape x y k⟩ := by
  have hs := scan_left M (carry x[k]) (takenTape x y k) ((2*k : Nat) : Int) k
  have hc : ((2*k : Nat) : Int)-(k : Int) = (k : Int) := by omega
  rw [hc] at hs
  apply hs
  intro i hi
  have hh : ((2*k : Nat) : Int)-(i : Int) = ((2*k-i : Nat) : Int) := by omega
  rw [hh,taken_gap x y k (2*k-i) (by omega) (by omega) (by omega),hr.2.1]
  simp only [show (2 : Fin 8) ≠ 4 by decide,if_false]

theorem write_step (M : DeterministicMachine 17 8) (hr : CycleRules M)
    (x y : List Bool) (k : Nat) (hk : k < x.length) :
    step M 0 ⟨carry x[k],(k : Int),takenTape x y k⟩ =
      some ⟨12,((k+1 : Nat) : Int),placedTape x y k hk⟩ := by
  have hq : M.rule (carry x[k]) 4 0 = some ⟨enc x[k],12,.right⟩ := by
    rw [hr.2.1]
    simp only [ite_true]
  have hh : (k : Int)+1 = ((k+1 : Nat) : Int) := by omega
  simp only [step,taken_dest,hq,Option.map_some,moveHead,writtenTape,hh,placedTape]

theorem place_step (M : DeterministicMachine 17 8) (hr : CycleRules M)
    (x y : List Bool) (k : Nat) (hk : k < x.length) :
    step M 0 ⟨12,((k+1 : Nat) : Int),placedTape x y k hk⟩ =
      some (copyConfig x y (k+1)) := by
  have hu := copy_update x y k hk
  simp only [step,hr.2.2,Option.map_some,moveHead,writtenTape,copyConfig,placedTape,takenTape]
  rw [hu]

theorem copy_one (M : DeterministicMachine 17 8) (hr : CycleRules M)
    (x y : List Bool) (k : Nat) (hk : k < x.length) :
    run M (ticks (2*k+4)) (copyConfig x y k) = some (copyConfig x y (k+1)) := by
  rw [show 2*k+4 = (k+1)+1+k+1+1 by omega,
    ticks_add,run_append,ticks_add,run_append,ticks_add,run_append,ticks_add,run_append,
    seek_run M hr x y k (by omega),Option.bind_some,run_ticks_one,take_step M hr x y k hk,
    Option.bind_some,carry_run M hr x y k hk,Option.bind_some,run_ticks_one,
    write_step M hr x y k hk,Option.bind_some,run_ticks_one,place_step M hr x y k hk]

theorem copy_prefix (M : DeterministicMachine 17 8) (hr : CycleRules M)
    (x y : List Bool) (k : Nat) (hk : k ≤ x.length) :
    run M (ticks (k*k+3*k)) (copyConfig x y 0) = some (copyConfig x y k) := by
  induction k with
  | zero => simp [ticks]
  | succ k ih =>
    have hsum : (k+1)*(k+1)+3*(k+1) = (k*k+3*k)+(2*k+4) := by ring
    rw [hsum,ticks_add,run_append,ih (by omega),Option.bind_some,copy_one M hr x y k (by omega)]

end PakFixedPolyomino.StandardBitMarkedCompaction
