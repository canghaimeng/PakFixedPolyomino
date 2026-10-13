import PakFixedPolyomino.StandardBitTimeComposition

/-! # Literal one-bit codePrefix insertion and fixed codePrefix bit-time

A carry bit in finite control shifts the input right in one forward pass.
The first blank receives the last carry; a backward pass returns to zero.
The full output tape is clean, including empty input, in exactly 2*n+2
ordinary one-cell transitions. Fixed finite prefixes follow from the checked
physical composition compiler, rather than a list-operation cost convention.
-/

namespace PakFixedPolyomino.StandardBitPrepend

open StandardNondeterministicMachine StandardBitTime StandardBitTimeComposition
open FiniteOneTapeSemantics (moveHead writtenTape)

abbrev bit (b : Bool) : Fin 3 := if b then 1 else 0
abbrev carryState (b : Bool) : Fin 5 := if b then 3 else 2

def machine (b : Bool) : DeterministicMachine 5 3 where
  rule q a _ :=
    if q = 2 ∨ q = 3 then
      if a = 2 then some ⟨if q = 3 then 1 else 0, 4, .left⟩
      else some ⟨if q = 3 then 1 else 0, if a = 1 then 3 else 2, .right⟩
    else if q = 4 then
      if a = 2 then some ⟨2, 0, .right⟩ else some ⟨a, 4, .left⟩
    else none
  start := carryState b
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

@[simp] theorem machine_zero (b : Bool) : (machine b).zero = 0 := rfl
@[simp] theorem machine_one (b : Bool) : (machine b).one = 1 := rfl
@[simp] theorem machine_blank (b : Bool) : (machine b).blank = 2 := rfl

theorem rule_scan_bit (b carry read : Bool) :
    (machine b).rule (carryState carry) (bit read) 0 =
      some ⟨bit carry, carryState read, .right⟩ := by
  cases carry <;> cases read <;> rfl

theorem rule_scan_blank (b carry : Bool) :
    (machine b).rule (carryState carry) 2 0 = some ⟨bit carry, 4, .left⟩ := by
  cases carry <;> rfl

theorem rule_return_bit (b read : Bool) :
    (machine b).rule 4 (bit read) 0 = some ⟨bit read, 4, .left⟩ := by
  cases read <;> rfl

theorem rule_return_blank (b : Bool) :
    (machine b).rule 4 2 0 = some ⟨2, 0, .right⟩ := rfl

def carry (b : Bool) (x : List Bool) (k : ℕ) : Bool :=
  if k = 0 then b else x[k - 1]?.getD false

def prefixTape (b : Bool) (x : List Bool) (k : ℕ) (z : Int) : Fin 3 :=
  if 0 ≤ z ∧ z < (k : Int) then inputTape (machine b) (b :: x) z
  else inputTape (machine b) x z

def scanConfig (b : Bool) (x : List Bool) (k : ℕ) : Configuration 5 3 :=
  ⟨carryState (carry b x k), k, prefixTape b x k⟩

def returnConfig (b : Bool) (x : List Bool) (z : Int) : Configuration 5 3 :=
  ⟨4, z, inputTape (machine b) (b :: x)⟩

def finalConfig (b : Bool) (x : List Bool) : Configuration 5 3 :=
  ⟨0, 0, inputTape (machine b) (b :: x)⟩

theorem scanConfig_zero (b : Bool) (x : List Bool) :
    scanConfig b x 0 = initial (machine b) x := by
  unfold scanConfig initial
  congr 1
  funext z
  have hf : ¬ (0 ≤ z ∧ z < (0 : Int)) := by omega
  simp [prefixTape, hf]

theorem prefixTape_at_head (b : Bool) (x : List Bool) (k : ℕ) :
    prefixTape b x k (k : Int) = inputTape (machine b) x (k : Int) := by
  simp [prefixTape]

theorem output_at (b : Bool) (x : List Bool) (k : ℕ) (hk : k ≤ x.length) :
    inputTape (machine b) (b :: x) (k : Int) = bit (carry b x k) := by
  rw [inputTape_ofNat (machine b) (b :: x) k (by simp; omega)]
  cases k with
  | zero => simp [carry]
  | succ k =>
      have hk' : k < x.length := by omega
      simp [carry, List.getElem?_eq_getElem hk']

theorem carry_succ (b : Bool) (x : List Bool) (k : ℕ) (hk : k < x.length) :
    carry b x (k + 1) = x[k] := by
  simp [carry, List.getElem?_eq_getElem hk]

theorem prefixTape_write (b : Bool) (x : List Bool) (k : ℕ) (hk : k ≤ x.length) :
    Function.update (prefixTape b x k) (k : Int) (bit (carry b x k)) =
      prefixTape b x (k + 1) := by
  funext z
  by_cases hz : z = (k : Int)
  · subst z
    have hin : 0 ≤ (k : Int) ∧ (k : Int) < ((k + 1 : ℕ) : Int) := by omega
    simp only [Function.update_self, prefixTape, if_pos hin]
    exact (output_at b x k hk).symm
  · have hcond : (0 ≤ z ∧ z < ((k + 1 : ℕ) : Int)) ↔
        (0 ≤ z ∧ z < (k : Int)) := by omega
    simp only [Function.update_of_ne hz, prefixTape, hcond]

theorem scan_step (b : Bool) (x : List Bool) (k : ℕ) (hk : k < x.length) :
    step (machine b) 0 (scanConfig b x k) = some (scanConfig b x (k + 1)) := by
  have hread : inputTape (machine b) x (k : Int) = bit x[k] :=
    inputTape_ofNat (machine b) x k hk
  simp only [step, scanConfig, prefixTape_at_head, hread, rule_scan_bit,
    Option.map_some, moveHead, writtenTape]
  rw [prefixTape_write b x k (Nat.le_of_lt hk), carry_succ b x k hk]
  congr 2

theorem scan_run (b : Bool) (x : List Bool) (k : ℕ) (hk : k ≤ x.length) :
    run (machine b) (ticks k) (initial (machine b) x) = some (scanConfig b x k) := by
  induction k with
  | zero => rw [scanConfig_zero]; rfl
  | succ k ih =>
      rw [ticks_add k 1, run_append, ih (by omega), Option.bind_some, run_ticks_one]
      exact scan_step b x k (by omega)

theorem prefixTape_complete (b : Bool) (x : List Bool) :
    prefixTape b x (x.length + 1) = inputTape (machine b) (b :: x) := by
  funext z
  unfold prefixTape
  split
  · rfl
  · rename_i hout
    have hz : z < 0 ∨ (x.length + 1 : Int) ≤ z := by omega
    rcases hz with hz | hz
    · rw [inputTape_neg (machine b) x z hz, inputTape_neg (machine b) (b :: x) z hz]
    · rw [inputTape_ge (machine b) x z (by omega),
        inputTape_ge (machine b) (b :: x) z (by simpa using hz)]

theorem scan_turn (b : Bool) (x : List Bool) :
    step (machine b) 0 (scanConfig b x x.length) =
      some (returnConfig b x ((x.length : Int) - 1)) := by
  have hblank : inputTape (machine b) x (x.length : Int) = 2 :=
    inputTape_ge (machine b) x _ (by rfl)
  simp only [step, scanConfig, prefixTape_at_head, hblank, rule_scan_blank,
    Option.map_some, moveHead, writtenTape, returnConfig]
  rw [prefixTape_write b x x.length (by rfl), prefixTape_complete]

theorem return_step (b : Bool) (x : List Bool) (k : ℕ) (hk : k < (b :: x).length) :
    step (machine b) 0 (returnConfig b x (k : Int)) =
      some (returnConfig b x ((k : Int) - 1)) := by
  have hread : inputTape (machine b) (b :: x) (k : Int) = bit (b :: x)[k] :=
    inputTape_ofNat (machine b) (b :: x) k hk
  simp only [step, returnConfig, hread, rule_return_bit,
    Option.map_some, moveHead, writtenTape]
  rw [← hread, Function.update_eq_self]

theorem return_run (b : Bool) (x : List Bool) (n : ℕ) (hn : n ≤ x.length) :
    run (machine b) (ticks n) (returnConfig b x ((n : Int) - 1)) =
      some (returnConfig b x (-1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change run (machine b) (0 :: ticks n)
        (returnConfig b x ((n + 1 : ℕ) - (1 : Int))) = _
      have hc : ((n + 1 : ℕ) : Int) - 1 = (n : Int) := by omega
      rw [hc, run_cons, return_step b x n (by simp; omega), Option.bind_some]
      exact ih (by omega)

theorem return_finish (b : Bool) (x : List Bool) :
    step (machine b) 0 (returnConfig b x (-1)) = some (finalConfig b x) := by
  have hblank : inputTape (machine b) (b :: x) (-1) = 2 :=
    inputTape_neg (machine b) (b :: x) (-1) (by omega)
  simp only [step, returnConfig, hblank, rule_return_blank,
    Option.map_some, moveHead, writtenTape, finalConfig]
  rw [← hblank, Function.update_eq_self]
  rfl

theorem prepend_run (b : Bool) (x : List Bool) :
    run (machine b) (ticks (2 * x.length + 2)) (initial (machine b) x) =
      some (finalConfig b x) := by
  have ht : 2 * x.length + 2 = x.length + 1 + x.length + 1 := by omega
  rw [ht, ticks_add, ticks_add, ticks_add, run_append, run_append, run_append,
    scan_run b x x.length (by rfl), Option.bind_some, run_ticks_one,
    scan_turn, Option.bind_some, return_run b x x.length (by rfl),
    Option.bind_some, run_ticks_one]
  exact return_finish b x

theorem prepend_computes (b : Bool) :
    ComputesWithin (machine b) (List.cons b) (fun n => 2 * n + 2) := by
  intro x
  exact ⟨2 * x.length + 2, finalConfig b x, by rfl, prepend_run b x, rfl, rfl, rfl⟩

theorem prepend_polyBitTime (b : Bool) : PolyBitTime (List.cons b) := by
  refine ⟨5, 3, machine b, Polynomial.C 2 * Polynomial.X + Polynomial.C 2, ?_⟩
  simpa using prepend_computes b

/-- The codePrefix is fixed finite data, hence finite recursive physical
composition creates one genuine finite machine for the whole function. -/
theorem fixed_prefix_polyBitTime (codePrefix : List Bool) :
    PolyBitTime (fun x => codePrefix ++ x) := by
  induction codePrefix with
  | nil => exact identity_polyBitTime
  | cons b codePrefix ih =>
      simpa only [Function.comp_def, List.cons_append] using
        polyBitTime_comp ih (prepend_polyBitTime b)

theorem prepend_exact :
    (∀ (b : Bool) x, run (machine b) (ticks (2 * x.length + 2))
      (initial (machine b) x) = some (finalConfig b x)) ∧
    (∀ (b : Bool) x, RunsAtMost (machine b) x (2 * x.length + 2)) ∧
    (∀ codePrefix : List Bool, PolyBitTime (fun x => codePrefix ++ x)) := by
  exact ⟨prepend_run, fun b x => halting_runsAtMost (machine b) x _ _
    (prepend_run b x) rfl, fixed_prefix_polyBitTime⟩

end PakFixedPolyomino.StandardBitPrepend
