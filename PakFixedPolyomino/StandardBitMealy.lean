import PakFixedPolyomino.StandardBitTime

/-! A finite sequential bit transducer compiled into an ordinary three-symbol
tape machine. Each input cell is read and overwritten once, then the head
returns across the output. Every raw word takes exactly 2*length+2 transitions.
The transition function is finite control, not a tape arithmetic primitive. -/
namespace PakFixedPolyomino.StandardBitMealy
open StandardNondeterministicMachine StandardBitTime
open FiniteOneTapeSemantics (moveHead writtenTape)

variable {S : Nat}
abbrev bit (b : Bool) : Fin 3 := if b then 1 else 0

def scanState (q : Fin S) : Fin (S+3) := ⟨q.val+3,by omega⟩

def readState (q : Fin (S+3)) (h : 3 ≤ q.val) : Fin S :=
  ⟨q.val-3,by omega⟩

def machine (delta : Fin S → Bool → Fin S × Bool) (start : Fin S) :
    DeterministicMachine (S+3) 3 where
  rule q a _ :=
    if h : 3 ≤ q.val then
      if a = 2 then some ⟨2,2,.left⟩
      else let next := delta (readState q h) (a = 1)
           some ⟨bit next.2,scanState next.1,.right⟩
    else if q = 2 then
      if a = 2 then some ⟨2,0,.right⟩ else some ⟨a,2,.left⟩
    else none
  start := scanState start
  accept := 0
  reject := 1
  accept_ne_reject := by simp
  blank := 2
  zero := 0
  one := 1
  blank_ne_zero := by decide
  blank_ne_one := by decide
  zero_ne_one := by decide
  accept_terminal := by intros; simp [Fin.ext_iff,Nat.mod_eq_of_lt (by omega : 2 < S+3)]
  reject_terminal := by intros; simp [Fin.ext_iff,Nat.mod_eq_of_lt (by omega : 2 < S+3)]

def transform (delta : Fin S → Bool → Fin S × Bool) (q : Fin S) :
    List Bool → List Bool
  | [] => []
  | b :: x => (delta q b).2 :: transform delta (delta q b).1 x

def finishState (delta : Fin S → Bool → Fin S × Bool) (q : Fin S) :
    List Bool → Fin S
  | [] => q
  | b :: x => finishState delta (delta q b).1 x

@[simp] theorem transform_length (delta : Fin S → Bool → Fin S × Bool)
    (q : Fin S) (x : List Bool) : (transform delta q x).length = x.length := by
  induction x generalizing q with
  | nil => rfl
  | cons b x ih => simp [transform,ih]

variable (delta : Fin S → Bool → Fin S × Bool) (start : Fin S)

theorem rule_scan_bit (q : Fin S) (b : Bool) :
    (machine delta start).rule (scanState q) (bit b) 0 =
      some ⟨bit (delta q b).2,scanState (delta q b).1,.right⟩ := by
  rcases q with ⟨q,hq⟩
  cases b <;> simp [machine,scanState,readState,bit]

theorem rule_scan_blank (q : Fin S) :
    (machine delta start).rule (scanState q) 2 0 = some ⟨2,2,.left⟩ := by
  simp [machine,scanState]

theorem rule_return_bit (b : Bool) :
    (machine delta start).rule 2 (bit b) 0 = some ⟨bit b,2,.left⟩ := by
  cases b <;> simp [machine,bit,Nat.mod_eq_of_lt (by omega : 2 < S+3)]

theorem rule_return_blank :
    (machine delta start).rule 2 2 0 = some ⟨2,0,.right⟩ := by
  simp [machine,Nat.mod_eq_of_lt (by omega : 2 < S+3)]

theorem tape_set (x : List Bool) (k : Nat) (hk : k < x.length) (b : Bool) :
    Function.update (inputTape (machine delta start) x) (k : Int) (bit b) =
      inputTape (machine delta start) (x.set k b) := by
  funext z
  by_cases hn : z < 0
  · have hne : z ≠ (k : Int) := by omega
    rw [Function.update_of_ne hne,inputTape_neg _ _ _ hn,inputTape_neg _ _ _ hn]
  · have hz : 0 ≤ z := by omega
    let i := z.toNat
    have hzi : z = (i : Int) := (Int.toNat_of_nonneg hz).symm
    rw [hzi]
    by_cases hi : i < x.length
    · have hi' : i < (x.set k b).length := by simpa using hi
      rw [inputTape_ofNat _ (x.set k b) i hi']
      by_cases he : i = k
      · simp only [he,Function.update_self,List.getElem_set_self]; rfl
      · have hine : (i : Int) ≠ (k : Int) := by omega
        rw [Function.update_of_ne hine,inputTape_ofNat _ x i hi]
        simp [List.getElem_set_ne (Ne.symm he),machine,bit]
    · have hge : (x.length : Int) ≤ (i : Int) := by omega
      have hne : (i : Int) ≠ (k : Int) := by omega
      rw [Function.update_of_ne hne,inputTape_ge _ _ _ hge,
        inputTape_ge _ _ _ (by simpa using hge)]

def scanConfig (pref : List Bool) (q : Fin S) (rest : List Bool) :
    Configuration (S+3) 3 :=
  ⟨scanState q,pref.length,inputTape (machine delta start) (pref++rest)⟩

def returnConfig (y : List Bool) (z : Int) : Configuration (S+3) 3 :=
  ⟨2,z,inputTape (machine delta start) y⟩

def finalConfig (y : List Bool) : Configuration (S+3) 3 :=
  ⟨0,0,inputTape (machine delta start) y⟩

theorem scan_step (pref : List Bool) (q : Fin S) (b : Bool) (rest : List Bool) :
    step (machine delta start) 0 (scanConfig delta start pref q (b::rest)) =
      some (scanConfig delta start (pref++[(delta q b).2]) (delta q b).1 rest) := by
  have hread : inputTape (machine delta start) (pref++b::rest) (pref.length : Int) =
      bit b := by
    rw [inputTape_ofNat _ _ pref.length (by simp)]
    simp [machine,bit]
  have hwrite := tape_set delta start (pref++b::rest) pref.length (by simp) (delta q b).2
  have hset : (pref++b::rest).set pref.length (delta q b).2 =
      (pref++[(delta q b).2])++rest := by
    simp [List.set_append_right, List.append_assoc]
  rw [hset] at hwrite
  simp only [step,scanConfig,hread,rule_scan_bit,Option.map_some,moveHead,writtenTape]
  rw [hwrite]
  congr 2
  simp

theorem scan_run (pref : List Bool) (q : Fin S) (rest : List Bool) :
    run (machine delta start) (ticks rest.length) (scanConfig delta start pref q rest) =
      some (scanConfig delta start (pref++transform delta q rest)
        (finishState delta q rest) []) := by
  induction rest generalizing pref q with
  | nil => simp [ticks,transform,finishState]
  | cons b rest ih =>
      change run (machine delta start) (0::ticks rest.length) _ = _
      rw [run_cons,scan_step,Option.bind_some,ih]
      simp [transform,finishState,List.append_assoc]

theorem scan_turn (y : List Bool) (q : Fin S) :
    step (machine delta start) 0 (scanConfig delta start y q []) =
      some (returnConfig delta start y ((y.length : Int)-1)) := by
  have hblank : inputTape (machine delta start) y (y.length : Int) = 2 :=
    inputTape_ge _ _ _ le_rfl
  simp only [step,scanConfig,List.append_nil,hblank,rule_scan_blank,
    Option.map_some,moveHead,writtenTape,returnConfig]
  rw [← hblank,Function.update_eq_self]

theorem return_step (y : List Bool) (k : Nat) (hk : k < y.length) :
    step (machine delta start) 0 (returnConfig delta start y k) =
      some (returnConfig delta start y ((k : Int)-1)) := by
  have hread : inputTape (machine delta start) y (k : Int) = bit y[k] :=
    inputTape_ofNat _ _ _ hk
  simp only [step,returnConfig,hread,rule_return_bit,Option.map_some,moveHead,writtenTape]
  rw [← hread,Function.update_eq_self]

theorem return_run (y : List Bool) (n : Nat) (hn : n ≤ y.length) :
    run (machine delta start) (ticks n) (returnConfig delta start y ((n : Int)-1)) =
      some (returnConfig delta start y (-1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change run (machine delta start) (0::ticks n)
        (returnConfig delta start y (((n+1 : Nat) : Int)-1)) = _
      have hc : ((n+1 : Nat) : Int)-1 = (n : Int) := by omega
      rw [hc,run_cons,return_step delta start y n (by omega),Option.bind_some]
      exact ih (by omega)

theorem return_finish (y : List Bool) :
    step (machine delta start) 0 (returnConfig delta start y (-1)) =
      some (finalConfig delta start y) := by
  have hblank : inputTape (machine delta start) y (-1) = 2 :=
    inputTape_neg _ _ _ (by omega)
  simp only [step,returnConfig,hblank,rule_return_blank,Option.map_some,
    moveHead,writtenTape,finalConfig]
  rw [← hblank,Function.update_eq_self]
  rfl

theorem transducer_run (x : List Bool) :
    run (machine delta start) (ticks (2*x.length+2)) (initial (machine delta start) x) =
      some (finalConfig delta start (transform delta start x)) := by
  have ht : 2*x.length+2 = x.length+1+x.length+1 := by omega
  have hscan := scan_run delta start [] start x
  change run (machine delta start) (ticks x.length) (initial (machine delta start) x) =
    some (scanConfig delta start (transform delta start x) (finishState delta start x) []) at hscan
  rw [ht,ticks_add,ticks_add,ticks_add,run_append,run_append,run_append,hscan,
    Option.bind_some,run_ticks_one,scan_turn,Option.bind_some]
  simp only [transform_length]
  rw [return_run delta start _ x.length (by simp),Option.bind_some,run_ticks_one]
  exact return_finish delta start _

theorem transducer_computes :
    ComputesWithin (machine delta start) (transform delta start) (fun n=>2*n+2) := by
  intro x
  exact ⟨_,finalConfig delta start _,le_rfl,transducer_run delta start x,rfl,rfl,rfl⟩

theorem transducer_polyBitTime : PolyBitTime (transform delta start) := by
  refine ⟨S+3,3,machine delta start,Polynomial.C 2*Polynomial.X+Polynomial.C 2,?_⟩
  simpa using transducer_computes delta start

theorem transducer_exact :
    (∀ x,run (machine delta start) (ticks (2*x.length+2)) (initial (machine delta start) x) =
      some (finalConfig delta start (transform delta start x))) ∧
    (∀ x,RunsAtMost (machine delta start) x (2*x.length+2)) ∧
    PolyBitTime (transform delta start) :=
  ⟨transducer_run delta start,fun x=>halting_runsAtMost _ _ _ _
    (transducer_run delta start x) rfl,transducer_polyBitTime delta start⟩

end PakFixedPolyomino.StandardBitMealy
