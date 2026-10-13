import PakFixedPolyomino.StandardBitTimeComposition

/-! One literal four-state, three-symbol machine appends one bit in exactly
2*length+2 standard tape transitions. Fixed suffixes use physical composition.
The output is clean on the entire integer tape, including empty inputs. -/
namespace PakFixedPolyomino.StandardBitAppend
open StandardNondeterministicMachine StandardBitTime StandardBitTimeComposition
open FiniteOneTapeSemantics (moveHead writtenTape)

abbrev bit (b : Bool) : Fin 3 := if b then 1 else 0

def machine (b : Bool) : DeterministicMachine 4 3 where
  rule q a _ :=
    if q = 2 then
      if a = 2 then some ⟨bit b, 3, .left⟩ else some ⟨a, 2, .right⟩
    else if q = 3 then
      if a = 2 then some ⟨2, 0, .right⟩ else some ⟨a, 3, .left⟩
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

@[simp] theorem machine_zero (b : Bool) : (machine b).zero = 0 := rfl
@[simp] theorem machine_one (b : Bool) : (machine b).one = 1 := rfl
@[simp] theorem machine_blank (b : Bool) : (machine b).blank = 2 := rfl

theorem rule_scan_bit (b read : Bool) :
    (machine b).rule 2 (bit read) 0 = some ⟨bit read, 2, .right⟩ := by
  cases read <;> rfl

theorem rule_scan_blank (b : Bool) :
    (machine b).rule 2 2 0 = some ⟨bit b, 3, .left⟩ := rfl

theorem rule_return_bit (b read : Bool) :
    (machine b).rule 3 (bit read) 0 = some ⟨bit read, 3, .left⟩ := by
  cases read <;> rfl

theorem rule_return_blank (b : Bool) :
    (machine b).rule 3 2 0 = some ⟨2, 0, .right⟩ := rfl

def appendBit (b : Bool) (x : List Bool) : List Bool := x ++ [b]

@[simp] theorem appendBit_length (b : Bool) (x : List Bool) :
    (appendBit b x).length = x.length + 1 := by simp [appendBit]

def scanConfig (b : Bool) (x : List Bool) (k : Nat) : Configuration 4 3 :=
  ⟨2, k, inputTape (machine b) x⟩

def returnConfig (b : Bool) (x : List Bool) (z : Int) : Configuration 4 3 :=
  ⟨3, z, inputTape (machine b) (appendBit b x)⟩

def finalConfig (b : Bool) (x : List Bool) : Configuration 4 3 :=
  ⟨0, 0, inputTape (machine b) (appendBit b x)⟩

theorem scan_step (b : Bool) (x : List Bool) (k : Nat) (hk : k < x.length) :
    step (machine b) 0 (scanConfig b x k) = some (scanConfig b x (k+1)) := by
  have hread : inputTape (machine b) x (k : Int) = bit x[k] :=
    inputTape_ofNat (machine b) x k hk
  simp only [step, scanConfig, hread, rule_scan_bit, Option.map_some,
    moveHead, writtenTape]
  rw [← hread, Function.update_eq_self]
  congr 2

theorem scan_run (b : Bool) (x : List Bool) (k : Nat) (hk : k ≤ x.length) :
    run (machine b) (ticks k) (initial (machine b) x) = some (scanConfig b x k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [ticks_add k 1, run_append, ih (by omega), Option.bind_some, run_ticks_one]
      exact scan_step b x k (by omega)

theorem append_at_end (b : Bool) (x : List Bool) :
    inputTape (machine b) (appendBit b x) (x.length : Int) = bit b := by
  rw [inputTape_ofNat (machine b) (appendBit b x) x.length (by simp)]
  simp [appendBit]

theorem append_before_end (b : Bool) (x : List Bool) (k : Nat) (hk : k < x.length) :
    inputTape (machine b) (appendBit b x) (k : Int) = inputTape (machine b) x k := by
  rw [inputTape_ofNat (machine b) (appendBit b x) k (by simp; omega),
    inputTape_ofNat (machine b) x k hk]
  simp [appendBit, List.getElem_append_left hk]

theorem append_write (b : Bool) (x : List Bool) :
    Function.update (inputTape (machine b) x) (x.length : Int) (bit b) =
      inputTape (machine b) (appendBit b x) := by
  funext z
  by_cases he : z = (x.length : Int)
  · subst z; rw [Function.update_self, append_at_end]
  · rw [Function.update_of_ne he]
    by_cases hn : z < 0
    · rw [inputTape_neg _ _ _ hn, inputTape_neg _ _ _ hn]
    · have hznon : 0 ≤ z := by omega
      let k := z.toNat
      have hzk : z = (k : Int) := (Int.toNat_of_nonneg hznon).symm
      rw [hzk]
      by_cases hk : k < x.length
      · exact (append_before_end b x k hk).symm
      · have hg : (x.length : Int) ≤ (k : Int) := by omega
        have hgo : ((appendBit b x).length : Int) ≤ (k : Int) := by
          simp only [appendBit_length]; omega
        rw [inputTape_ge _ _ _ hg, inputTape_ge _ _ _ hgo]

theorem scan_turn (b : Bool) (x : List Bool) :
    step (machine b) 0 (scanConfig b x x.length) =
      some (returnConfig b x ((x.length : Int)-1)) := by
  have hblank : inputTape (machine b) x (x.length : Int) = 2 :=
    inputTape_ge (machine b) x _ le_rfl
  simp only [step, scanConfig, hblank, rule_scan_blank, Option.map_some,
    writtenTape, moveHead, returnConfig]
  rw [append_write]

theorem return_step (b : Bool) (x : List Bool) (k : Nat)
    (hk : k < (appendBit b x).length) :
    step (machine b) 0 (returnConfig b x k) = some (returnConfig b x ((k : Int)-1)) := by
  have hread : inputTape (machine b) (appendBit b x) (k : Int) =
      bit (appendBit b x)[k] := inputTape_ofNat (machine b) _ k hk
  simp only [step, returnConfig, hread, rule_return_bit, Option.map_some,
    moveHead, writtenTape]
  rw [← hread, Function.update_eq_self]

theorem return_run (b : Bool) (x : List Bool) (n : Nat) (hn : n ≤ x.length) :
    run (machine b) (ticks n) (returnConfig b x ((n : Int)-1)) =
      some (returnConfig b x (-1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change run (machine b) (0 :: ticks n)
        (returnConfig b x (((n+1 : Nat) : Int)-1)) = _
      have hc : ((n+1 : Nat) : Int)-1 = (n : Int) := by omega
      rw [hc, run_cons, return_step b x n (by simp; omega), Option.bind_some]
      exact ih (by omega)

theorem return_finish (b : Bool) (x : List Bool) :
    step (machine b) 0 (returnConfig b x (-1)) = some (finalConfig b x) := by
  have hblank : inputTape (machine b) (appendBit b x) (-1) = 2 :=
    inputTape_neg (machine b) _ _ (by omega)
  simp only [step, returnConfig, hblank, rule_return_blank, Option.map_some,
    moveHead, writtenTape, finalConfig]
  rw [← hblank, Function.update_eq_self]
  rfl

theorem append_run (b : Bool) (x : List Bool) :
    run (machine b) (ticks (2*x.length+2)) (initial (machine b) x) =
      some (finalConfig b x) := by
  have ht : 2*x.length+2 = x.length+1+x.length+1 := by omega
  rw [ht, ticks_add, ticks_add, ticks_add, run_append, run_append, run_append,
    scan_run b x x.length le_rfl, Option.bind_some, run_ticks_one,
    scan_turn, Option.bind_some, return_run b x x.length le_rfl,
    Option.bind_some, run_ticks_one]
  exact return_finish b x

theorem append_computes (b : Bool) :
    ComputesWithin (machine b) (appendBit b) (fun n=>2*n+2) := by
  intro x
  exact ⟨_,finalConfig b x,le_rfl,append_run b x,rfl,rfl,rfl⟩

theorem append_polyBitTime (b : Bool) : PolyBitTime (appendBit b) := by
  refine ⟨4,3,machine b,Polynomial.C 2 * Polynomial.X + Polynomial.C 2,?_⟩
  simpa using append_computes b

theorem fixed_suffix_polyBitTime (suffix : List Bool) :
    PolyBitTime (fun x=>x++suffix) := by
  induction suffix with
  | nil =>
      rw [show (fun x : List Bool => x ++ []) = id from by funext x; simp]
      exact identity_polyBitTime
  | cons b suffix ih =>
      simpa only [Function.comp_def, appendBit, List.append_assoc,
        List.singleton_append] using polyBitTime_comp (append_polyBitTime b) ih

theorem append_exact :
    (∀ (b : Bool) x, run (machine b) (ticks (2*x.length+2))
      (initial (machine b) x) = some (finalConfig b x)) ∧
    (∀ (b : Bool) x, RunsAtMost (machine b) x (2*x.length+2)) ∧
    (∀ suffix : List Bool, PolyBitTime (fun x=>x++suffix)) :=
  ⟨append_run,fun b x=>halting_runsAtMost (machine b) x _ _ (append_run b x) rfl,
    fixed_suffix_polyBitTime⟩

end PakFixedPolyomino.StandardBitAppend
