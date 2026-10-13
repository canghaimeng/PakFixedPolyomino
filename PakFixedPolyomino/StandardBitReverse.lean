import PakFixedPolyomino.StandardBitTime

/-! Ordinary 14-state 8-symbol reversal of every raw `List Bool`. -/
namespace PakFixedPolyomino.StandardBitReverse
open StandardNondeterministicMachine StandardBitTime
open FiniteOneTapeSemantics (moveHead writtenTape)

def bit : Bool → Fin 8 | false => 0 | true => 1
def marked : Bool → Fin 8 | false => 3 | true => 4
def seekQ : Bool → Fin 14 | false => 7 | true => 8
def selQ : Bool → Fin 14 | false => 9 | true => 10
def retQ : Bool → Fin 14 | false => 11 | true => 12
def bitAt (x : List Bool) (i : Nat) : Bool := if h : i < x.length then x[i] else false
@[simp] theorem bitAt_lt (x : List Bool) (i : Nat) (h : i < x.length) : bitAt x i = x[i] := by
  simp [bitAt, h]

def delta (q : Fin 14) (a : Fin 8) : Option (FiniteOneTapeProgram.Action (Fin 14) (Fin 8)) :=
  if q = 2 then some ⟨a, 3, .left ⟩
  else if q = 3 then if a = 2 then some ⟨5, 4, .right ⟩ else none
  else if q = 4 then
    if a = 2 then some ⟨6, 5, .left ⟩
    else if a = 0 ∨ a = 1 then some ⟨a, 4, .right ⟩ else none
  else if q = 5 then
    if a = 5 then some ⟨5, 6, .right ⟩
    else if a = 0 ∨ a = 1 ∨ a = 3 ∨ a = 4 then
      some ⟨a, 5, .left ⟩ else none
  else if q = 6 then
    if a = 0 then some ⟨7, 7, .right ⟩
    else if a = 1 then some ⟨7, 8, .right ⟩
    else if a = 3 ∨ a = 4 then some ⟨a, 6, .right ⟩
    else if a = 6 then some ⟨2, 13, .left ⟩ else none
  else if q = 7 ∨ q = 8 then
    if a = 0 ∨ a = 1 ∨ a = 7 then some ⟨a, q, .right ⟩
    else if a = 3 ∨ a = 4 ∨ a = 6 then
      some ⟨a, if q = 7 then 9 else 10, .left ⟩ else none
  else if q = 9 ∨ q = 10 then
    let w : Fin 8 := if q = 9 then 3 else 4
    if a = 7 ∨ a = 0 then some ⟨w, 11, .left ⟩
    else if a = 1 then some ⟨w, 12, .left ⟩ else none
  else if q = 11 ∨ q = 12 then
    if a = 7 then some ⟨if q = 11 then 3 else 4, q, .left ⟩
    else if a = 5 then some ⟨5, 6, .right ⟩
    else if a = 0 ∨ a = 1 ∨ a = 3 ∨ a = 4 then
      some ⟨a, q, .left ⟩ else none
  else if q = 13 then
    if a = 3 then some ⟨0, 13, .left ⟩
    else if a = 4 then some ⟨1, 13, .left ⟩
    else if a = 0 ∨ a = 1 then some ⟨a, 13, .left ⟩
    else if a = 5 then some ⟨2, 0, .right ⟩ else none
  else none

def machine : DeterministicMachine 14 8 where
  rule q a _ := delta q a
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
  accept_terminal := by intros; simp [delta]
  reject_terminal := by intros; simp [delta]

@[simp] theorem m0 : machine.zero = 0 := rfl
@[simp] theorem m1 : machine.one = 1 := rfl
@[simp] theorem m2 : machine.blank = 2 := rfl
@[simp] theorem mA : machine.accept = 0 := rfl

def epochTape (x : List Bool) (k : Nat) (z : Int) : Fin 8 :=
  if z = -1 then 5
  else if z = (x.length : Int) then 6
  else if h : 0 ≤ z ∧ z.toNat < x.length then
    if z.toNat < k ∨ x.length - k ≤ z.toNat then
      marked (x[x.length - 1 - z.toNat]'(by omega))
    else bit (x[z.toNat]'(h.2))
  else 2

def epochConfig (x : List Bool) (k : Nat) : Configuration 14 8 := ⟨6, 0, epochTape x k⟩
def finalConfig (x : List Bool) : Configuration 14 8 := ⟨0, 0, inputTape machine x.reverse⟩
def setupFuel (n : Nat) : Nat := 2 * n + 4
def epochFuel (n k : Nat) : Nat := 2 * (n - k) + 2
def cleanupFuel (n : Nat) : Nat := 2 * n + 2
def reverseFuel (n : Nat) : Nat :=
  setupFuel n + (List.range ((n + 1) / 2)).foldl (fun s k => s + epochFuel n k) 0 +
    cleanupFuel n

def tapeConfig (q : Fin 14) (z : Int) (t : Int → Fin 8) : Configuration 14 8 := ⟨q, z, t⟩

theorem step_write (q q' : Fin 14) (z : Int) (t : Int → Fin 8) (a : Fin 8)
    (d : OneTapeTableau.Move)
    (hr : machine.rule q (t z) 0 = some ⟨a, q', d ⟩) :
    step machine 0 (tapeConfig q z t) =
      some (tapeConfig q' (moveHead d z) (Function.update t z a)) := by
  simp only [step, tapeConfig, hr, Option.map_some, writtenTape]

theorem step_preserve (q q' : Fin 14) (z : Int) (t : Int → Fin 8) (d : OneTapeTableau.Move)
    (hr : machine.rule q (t z) 0 = some ⟨t z, q', d ⟩) :
    step machine 0 (tapeConfig q z t) = some (tapeConfig q' (moveHead d z) t) := by
  rw [step_write q q' z t (t z) d hr, Function.update_eq_self]

theorem scan_right (q : Fin 14) (z : Int) (t : Int → Fin 8) (n : Nat)
    (hr : ∀ p : Nat, p < n → machine.rule q (t (z + p)) 0 =
      some ⟨t (z + p), q, .right ⟩) :
    run machine (ticks n) (tapeConfig q z t) = some (tapeConfig q (z + n) t) := by
  induction n generalizing z with
  | zero => simp [ticks, run, tapeConfig]
  | succ n ih =>
    change run machine (0 :: ticks n) (tapeConfig q z t) = _
    rw [run_cons, step_preserve q q z t .right (by simpa using hr 0 (by omega)),
      Option.bind_some]
    have ht := ih (z + 1) (by
      intro p hp
      simpa [Nat.cast_add, Nat.cast_one, Int.add_assoc, Int.add_comm,
        Int.add_left_comm] using hr (p + 1) (by omega))
    simpa [moveHead, Nat.cast_add, Nat.cast_one, Int.add_assoc, Int.add_comm,
      Int.add_left_comm] using ht

theorem scan_left (q : Fin 14) (z : Int) (t : Int → Fin 8) (n : Nat)
    (hr : ∀ p : Nat, p < n → machine.rule q (t (z - p)) 0 =
      some ⟨t (z - p), q, .left ⟩) :
    run machine (ticks n) (tapeConfig q z t) = some (tapeConfig q (z - n) t) := by
  induction n generalizing z with
  | zero => simp [ticks, run, tapeConfig]
  | succ n ih =>
    change run machine (0 :: ticks n) (tapeConfig q z t) = _
    rw [run_cons, step_preserve q q z t .left (by simpa using hr 0 (by omega)),
      Option.bind_some]
    have ht := ih (z - 1) (by
      intro p hp
      simpa [Nat.cast_add, Nat.cast_one, Int.sub_sub, Int.add_comm] using
        hr (p + 1) (by omega))
    simpa [moveHead, Nat.cast_add, Nat.cast_one, Int.sub_sub, Int.add_comm] using ht

theorem et_neg1 (x : List Bool) (k : Nat) : epochTape x k (-1) = 5 := by simp [epochTape]
theorem et_right (x : List Bool) (k : Nat) : epochTape x k x.length = 6 := by
  have h : (x.length : Int) ≠ -1 := by omega
  simp [epochTape, h]
theorem et_nat (x : List Bool) (k p : Nat) (hp : p < x.length) :
    epochTape x k p =
      if p < k ∨ x.length - k ≤ p then marked (x[x.length - 1 - p]'(by omega))
      else bit x[p] := by
  have h1 : (p : Int) ≠ -1 := by omega
  have hn : (p : Int) ≠ (x.length : Int) := by omega
  simp [epochTape, h1, hn, Int.toNat_natCast, hp]

theorem et0_input (x : List Bool) (z : Int) :
    epochTape x 0 z =
      (if z = -1 then 5 else if z = (x.length : Int) then 6 else inputTape machine x z) := by
  by_cases h1 : z = -1
  · simp [epochTape, h1]
  · by_cases hn : z = (x.length : Int)
    · simp [epochTape, hn]
    · simp [h1, hn]
      by_cases hpos : 0 ≤ z
      · by_cases hp : z.toNat < x.length
        · have hz' : z = (z.toNat : Int) := (Int.toNat_of_nonneg hpos).symm
          have hE : epochTape x 0 (z.toNat : Int) = bit (x[z.toNat]) := by
            rw [et_nat x 0 z.toNat hp]
            simp [Nat.not_lt.mpr (Nat.zero_le _), Nat.not_le.mpr hp]
          have hI : inputTape machine x (z.toNat : Int) = bit (x[z.toNat]) := by
            rw [inputTape_ofNat machine x z.toNat hp]; cases x[z.toNat] <;> rfl
          rw [hz', hE, hI]
        · have hge : (x.length : Int) ≤ z := by
            have : (x.length : Int) ≤ (z.toNat : Int) :=
              Nat.cast_le.mpr (Nat.not_lt.mp hp)
            rwa [Int.toNat_of_nonneg hpos] at this
          have hE : epochTape x 0 z = 2 := by
            unfold epochTape; simp [h1, hn, hpos, hp]
          exact hE.trans (inputTape_ge machine x z hge).symm
      · have hE : epochTape x 0 z = 2 := by unfold epochTape; simp [h1, hn, hpos]
        exact hE.trans (inputTape_neg machine x z (by omega)).symm

theorem foldl_epoch_le (n m : Nat) :
    (List.range m).foldl (fun s k => s + epochFuel n k) 0 ≤ m * (2 * n + 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have : epochFuel n m ≤ 2 * n + 2 := by unfold epochFuel; omega
      simpa [Nat.succ_mul] using Nat.add_le_add ih this

theorem reverseFuel_le (n : Nat) : reverseFuel n ≤ 8 * n * n + 20 * n + 20 := by
  have hsum := foldl_epoch_le n ((n + 1) / 2)
  have hdiv : 2 * ((n + 1) / 2) ≤ n + 1 := Nat.mul_div_le (n + 1) 2
  have hmul : ((n + 1) / 2) * (2 * n + 2) ≤ (n + 1) * (n + 1) := by
    have htwo : 2 * n + 2 = 2 * (n + 1) := by omega
    rw [htwo]
    calc ((n + 1) / 2) * (2 * (n + 1))
        = (2 * ((n + 1) / 2)) * (n + 1) := by ring
      _ ≤ (n + 1) * (n + 1) := Nat.mul_le_mul_right (n + 1) hdiv
  have hfuel : reverseFuel n =
      4 * n + 6 + (List.range ((n + 1) / 2)).foldl (fun s k => s + epochFuel n k) 0 := by
    simp [reverseFuel, setupFuel, cleanupFuel]; omega
  have h1 : reverseFuel n ≤ 4 * n + 6 + (n + 1) * (n + 1) := by
    rw [hfuel]; exact Nat.add_le_add_left (hsum.trans hmul) _
  nlinarith

def tapeL (x : List Bool) (z : Int) : Fin 8 := if z = -1 then 5 else inputTape machine x z

theorem setup_left (x : List Bool) :
    step machine 0 (initial machine x) = some (tapeConfig 3 (-1) (inputTape machine x)) := by
  have hr : machine.rule 2 (inputTape machine x 0) 0 =
      some ⟨inputTape machine x 0, 3, .left ⟩ := by
    simp [machine, delta]
  simpa [initial, machine, tapeConfig, moveHead, Function.update_eq_self] using
    step_preserve 2 3 0 (inputTape machine x) .left hr

theorem setup_sentinelL (x : List Bool) :
    step machine 0 (tapeConfig 3 (-1) (inputTape machine x)) =
      some (tapeConfig 4 0 (tapeL x)) := by
  have hr : machine.rule 3 2 0 = some ⟨5, 4, .right ⟩ := by
    simp [machine, delta]
  have hb : inputTape machine x (-1) = 2 := inputTape_neg machine x (-1) (by omega)
  have ht : Function.update (inputTape machine x) (-1) 5 = tapeL x := by
    funext z; by_cases hz : z = -1 <;> simp [tapeL, hz, Function.update]
  simpa [hb, ht, moveHead] using step_write 3 4 (-1) (inputTape machine x) 5 .right (by simpa [hb])

theorem setup_scan (x : List Bool) :
    run machine (ticks x.length) (tapeConfig 4 0 (tapeL x)) =
      some (tapeConfig 4 x.length (tapeL x)) := by
  have hz : ((0 : Int) + x.length) = (x.length : Int) := by omega
  rw [← hz]
  refine scan_right 4 0 (tapeL x) x.length ?_
  intro p hp
  have hne : ((p : Int)) ≠ -1 := by omega
  have hread : tapeL x p = bit x[p] := by
    simp [tapeL, hne, inputTape_ofNat machine x p hp]; cases x[p] <;> rfl
  have hr : machine.rule 4 (bit x[p]) 0 =
      some ⟨bit x[p], 4, .right ⟩ := by
    cases x[p] <;> simp [machine, delta, bit]
  simpa [hread, Nat.cast_zero, Int.zero_add] using hr

theorem setup_sentinelR (x : List Bool) :
    step machine 0 (tapeConfig 4 x.length (tapeL x)) =
      some (tapeConfig 5 ((x.length : Int) - 1) (epochTape x 0)) := by
  have hne : (x.length : Int) ≠ -1 := by omega
  have hb : tapeL x x.length = 2 := by
    simp [tapeL, hne, inputTape_ge machine x _ le_rfl]
  have hr : machine.rule 4 2 0 = some ⟨6, 5, .left ⟩ := by
    simp [machine, delta]
  have ht : Function.update (tapeL x) x.length 6 = epochTape x 0 := by
    funext z; rw [et0_input]
    by_cases h1 : z = -1
    · have : z ≠ (x.length : Int) := by omega
      simp [tapeL, Function.update, h1, this]
    · by_cases hn : z = (x.length : Int)
      · simp [Function.update, tapeL, hn]
      · simp [Function.update, tapeL, h1, hn]
  simpa [hb, ht, moveHead] using step_write 4 5 (x.length : Int) (tapeL x) 6 .left (by simpa [hb])

theorem setup_return (x : List Bool) :
    run machine (ticks x.length) (tapeConfig 5 ((x.length : Int) - 1) (epochTape x 0)) =
      some (tapeConfig 5 (-1) (epochTape x 0)) := by
  have hz : ((x.length : Int) - 1) - x.length = (-1 : Int) := by omega
  rw [← hz]
  refine scan_left 5 ((x.length : Int) - 1) (epochTape x 0) x.length ?_
  intro p hp
  have hid : ((x.length : Int) - 1 - (p : Int)) = ((x.length - 1 - p : Nat) : Int) := by omega
  have hp' : x.length - 1 - p < x.length := by omega
  have hplain : epochTape x 0 ((x.length - 1 - p : Nat) : Int) =
      bit (x[x.length - 1 - p]) := by
    rw [et_nat x 0 (x.length - 1 - p) hp']
    simp [Nat.not_lt.mpr (Nat.zero_le _), show ¬ x.length ≤ x.length - 1 - p by omega]
  have hr : machine.rule 5 (bit (x[x.length - 1 - p])) 0 =
      some ⟨bit (x[x.length - 1 - p]), 5, .left ⟩ := by
    cases x[x.length - 1 - p] <;> simp [machine, delta, bit]
  rw [hid, hplain]; exact hr

theorem setup_bounce (x : List Bool) :
    step machine 0 (tapeConfig 5 (-1) (epochTape x 0)) = some (epochConfig x 0) := by
  have hr : machine.rule 5 5 0 = some ⟨5, 6, .right ⟩ := by
    simp [machine, delta]
  have hb : epochTape x 0 (-1) = 5 := et_neg1 x 0
  have htape : Function.update (epochTape x 0) (-1) 5 = epochTape x 0 := by
    ext z; by_cases hz : z = -1 <;> simp [Function.update, hz, hb]
  have hstep := step_write 5 6 (-1) (epochTape x 0) 5 .right (by simpa [hb])
  rw [hstep]
  simp [epochConfig, tapeConfig, moveHead, htape]

theorem setup_run (x : List Bool) :
    run machine (ticks (setupFuel x.length)) (initial machine x) = some (epochConfig x 0) := by
  have ht : setupFuel x.length = 1 + 1 + x.length + 1 + x.length + 1 := by
    simp [setupFuel]; omega
  rw [ht, ticks_add, ticks_add, ticks_add, ticks_add, ticks_add, run_append, run_append,
    run_append, run_append, run_append, run_ticks_one, setup_left, Option.bind_some,
    run_ticks_one, setup_sentinelL, Option.bind_some, setup_scan, Option.bind_some,
    run_ticks_one, setup_sentinelR, Option.bind_some, setup_return, Option.bind_some,
    run_ticks_one]
  exact setup_bounce x

def holeTape (x : List Bool) (k : Nat) : Int → Fin 8 := Function.update (epochTape x k) k 7
def rightIdx (x : List Bool) (k : Nat) : Nat := x.length - k - 1
def afterSel (x : List Bool) (k : Nat) (hk : k < x.length) : Int → Fin 8 :=
  Function.update (holeTape x k) (rightIdx x k) (marked x[k])

theorem tape_succ (x : List Bool) (k : Nat) (hk : 2 * k < x.length) :
    Function.update (afterSel x k (by omega)) k
      (marked (x[rightIdx x k]'(by unfold rightIdx; omega))) = epochTape x (k + 1) := by
  funext z
  have hn : k < x.length := by omega
  have hr : rightIdx x k < x.length := by unfold rightIdx; omega
  have hkn : (k : Int) ≠ (x.length : Int) := by omega
  have hkm : (k : Int) ≠ -1 := by omega
  have hrn : ((rightIdx x k : Nat) : Int) ≠ (x.length : Int) := by unfold rightIdx; omega
  have hrm : ((rightIdx x k : Nat) : Int) ≠ -1 := by omega
  by_cases hz : z = (k : Int)
  · subst z
    have : x.length - 1 - k = rightIdx x k := by unfold rightIdx; omega
    simp [afterSel, holeTape, Function.update_self, epochTape, hkm, hkn,
      Int.toNat_natCast, hn, Nat.lt_succ_self, true_or, this]
  · by_cases hz' : z = (rightIdx x k : Int)
    · subst z
      have hne : (rightIdx x k : Int) ≠ (k : Int) := by
        intro h; have := Int.natCast_inj.mp h; unfold rightIdx at this; omega
      have : x.length - 1 - rightIdx x k = k := by unfold rightIdx; omega
      have hmark : x.length - (k + 1) ≤ rightIdx x k := by unfold rightIdx; omega
      simp [afterSel, holeTape, Function.update_of_ne hne, Function.update_self,
        epochTape, hrm, hrn, Int.toNat_natCast, hr, hmark, or_true, this]
    · have h1 : z ≠ (k : Int) := hz
      have h2 : z ≠ (rightIdx x k : Int) := hz'
      simp only [afterSel, holeTape, Function.update_of_ne h1, Function.update_of_ne h2]
      by_cases hneg : z = -1
      · simp [epochTape, hneg]
      · by_cases hlen : z = (x.length : Int)
        · simp [epochTape, hlen]
        · by_cases hzp : 0 ≤ z ∧ z.toNat < x.length
          · have hi := hzp.2
            have hzNat : z = (z.toNat : Int) := (Int.toNat_of_nonneg hzp.1).symm
            have hneK : z.toNat ≠ k := by
              intro h; apply h1; rw [hzNat, h]
            have hneR : z.toNat ≠ rightIdx x k := by
              intro h; apply h2; rw [hzNat, h]
            have hiff : (z.toNat < k ∨ x.length - k ≤ z.toNat) ↔
                (z.toNat < k + 1 ∨ x.length - (k + 1) ≤ z.toNat) := by
              unfold rightIdx at hneR; omega
            rw [hzNat, et_nat x k z.toNat hi, et_nat x (k + 1) z.toNat hi]
            exact if_congr hiff rfl rfl
          · unfold epochTape; simp [hneg, hlen, hzp]

theorem epoch_skip (x : List Bool) (k : Nat) (hk : 2 * k < x.length) :
    run machine (ticks k) (epochConfig x k) = some (tapeConfig 6 k (epochTape x k)) := by
  change run machine (ticks k) (tapeConfig 6 0 (epochTape x k)) = _
  have hz : ((0 : Int) + k) = (k : Int) := by omega
  rw [← hz]
  refine scan_right 6 0 (epochTape x k) k ?_
  intro p hp
  have hp' : p < x.length := by omega
  have hcell : epochTape x k p = marked (x[x.length - 1 - p]'(by omega)) := by
    rw [et_nat x k p hp']; simp [hp]
  have hr : machine.rule 6 (marked (x[x.length - 1 - p]'(by omega))) 0 =
      some ⟨marked (x[x.length - 1 - p]'(by omega)), 6, .right ⟩ := by
    cases x[x.length - 1 - p] <;> simp [machine, delta, marked]
  simpa [hcell, Nat.cast_zero, Int.zero_add] using hr

theorem epoch_pick (x : List Bool) (k : Nat) (hk : 2 * k < x.length) :
    step machine 0 (tapeConfig 6 k (epochTape x k)) =
      some (tapeConfig (seekQ (x[k]'(by omega))) (k + 1) (holeTape x k)) := by
  have hp : k < x.length := by omega
  have hplain : epochTape x k k = bit x[k] := by
    rw [et_nat x k k hp]; simp; omega
  have hr : machine.rule 6 (bit x[k]) 0 =
      some ⟨7, seekQ x[k], .right ⟩ := by
    cases x[k] <;> simp [machine, delta, bit, seekQ]
  have ht : Function.update (epochTape x k) k 7 = holeTape x k := rfl
  have hstep :=
    step_write 6 (seekQ (x[k]'(by omega))) k (epochTape x k) 7 .right
      (by simpa [hplain] using hr)
  rw [hstep]
  apply congrArg some
  simp [tapeConfig, moveHead, ht]

theorem epoch_seek_pass (x : List Bool) (k : Nat) (hk : 2 * k < x.length) :
    run machine (ticks (x.length - 2 * k - 1))
      (tapeConfig (seekQ (x[k]'(by omega))) (k + 1) (holeTape x k)) =
      some (tapeConfig (seekQ (x[k]'(by omega))) (x.length - k) (holeTape x k)) := by
  have hscan :
      ∀ p : Nat, p < x.length - 2 * k - 1 →
        machine.rule (seekQ (x[k]'(by omega))) (holeTape x k ((k : Int) + 1 + p)) 0 =
          some ⟨holeTape x k ((k : Int) + 1 + p), seekQ (x[k]'(by omega)), .right ⟩ := by
    intro p hp
    have hp' : k + 1 + p < x.length := by omega
    have hne : (k + 1 + p : Nat) ≠ k := by omega
    have hplain : holeTape x k ((k : Int) + 1 + p) = bit (x[k + 1 + p]) := by
      have hcast : ((k : Int) + 1 + p) = ((k + 1 + p : Nat) : Int) := by omega
      rw [hcast]
      simp only [holeTape, Function.update_of_ne (Nat.cast_injective.ne hne)]
      rw [et_nat x k _ hp']; simp; omega
    have hr : machine.rule (seekQ (x[k]'(by omega))) (bit (x[k + 1 + p])) 0 =
        some ⟨bit (x[k + 1 + p]), seekQ (x[k]'(by omega)), .right ⟩ := by
      cases x[k] <;> cases x[k + 1 + p] <;> simp [machine, delta, bit, seekQ]
    simpa [hplain] using hr
  have hrun :=
    scan_right (seekQ (x[k]'(by omega))) ((k : Int) + 1) (holeTape x k)
      (x.length - 2 * k - 1) hscan
  convert hrun using 3
  omega

theorem epoch_seek_turn (x : List Bool) (k : Nat) (hk : 2 * k < x.length) :
    step machine 0 (tapeConfig (seekQ (x[k]'(by omega))) ((x.length : Int) - k)
      (holeTape x k)) =
      some (tapeConfig (selQ (x[k]'(by omega))) (rightIdx x k) (holeTape x k)) := by
  have hne : ((x.length : Int) - k) ≠ (k : Int) := by omega
  have hcell : holeTape x k ((x.length : Int) - k) =
      if k = 0 then 6 else marked (x[k - 1]'(by omega)) := by
    simp only [holeTape, Function.update_of_ne hne]
    by_cases hk0 : k = 0
    · subst k
      have hz0 : (x.length : Int) - (0 : Nat) = x.length := by omega
      rw [hz0]; exact et_right x 0
    · have hcast : ((x.length : Int) - k) = ((x.length - k : Nat) : Int) := by omega
      have hp : x.length - k < x.length := by omega
      have hidx : x.length - 1 - (x.length - k) = k - 1 := by omega
      rw [hcast, et_nat x k _ hp]
      simp [hk0, show ¬ x.length - k < k by omega, le_rfl, hidx]
  have hhead : ((x.length : Int) - k) - 1 = (rightIdx x k : Int) := by
    unfold rightIdx; omega
  by_cases hk0 : k = 0
  · subst k
    have hz0 : (x.length : Int) - (0 : Nat) = x.length := by omega
    have hb : holeTape x 0 (x.length : Int) = 6 := by
      simpa [hz0] using hcell
    have hr : machine.rule (seekQ (x[0]'(by omega))) 6 0 =
        some ⟨6, selQ (x[0]'(by omega)), .left ⟩ := by
      cases x[0] <;> simp [machine, delta, seekQ, selQ]
    have hstep :=
      step_preserve (seekQ (x[0]'(by omega))) (selQ (x[0]'(by omega)))
        (x.length : Int) (holeTape x 0) .left (by simpa [hb] using hr)
    convert hstep using 3
    simp [tapeConfig, moveHead, rightIdx]; omega
  · have hm : holeTape x k ((x.length : Int) - k) = marked (x[k - 1]'(by omega)) := by
      simpa [hk0] using hcell
    have hr : machine.rule (seekQ (x[k]'(by omega))) (marked (x[k - 1]'(by omega))) 0 =
        some ⟨marked (x[k - 1]'(by omega)), selQ (x[k]'(by omega)), .left ⟩ := by
      cases x[k] <;> cases x[k - 1] <;> simp [machine, delta, seekQ, selQ, marked]
    have hstep :=
      step_preserve (seekQ (x[k]'(by omega))) (selQ (x[k]'(by omega)))
        ((x.length : Int) - k) (holeTape x k) .left (by simpa [hm] using hr)
    rw [hstep]; apply congrArg some
    simp [tapeConfig, moveHead, hhead]

theorem epoch_select (x : List Bool) (k : Nat) (hk : 2 * k < x.length) :
    step machine 0 (tapeConfig (selQ (x[k]'(by omega))) (rightIdx x k) (holeTape x k)) =
      some (tapeConfig
        (if rightIdx x k = k then 11
          else retQ (x[rightIdx x k]'(by unfold rightIdx; omega)))
        ((rightIdx x k : Int) - 1) (afterSel x k (by omega))) := by
  have hn : k < x.length := by omega
  have hr : rightIdx x k < x.length := by unfold rightIdx; omega
  by_cases hm : rightIdx x k = k
  · have hread : holeTape x k (rightIdx x k) = 7 := by simp [holeTape, hm]
    have hrule : machine.rule (selQ (x[k]'(by omega))) 7 0 =
        some ⟨marked (x[k]'(by omega)), 11, .left ⟩ := by
      cases x[k] <;> simp [machine, delta, selQ, marked]
    have hstep :=
      step_write (selQ (x[k]'(by omega))) 11 (rightIdx x k) (holeTape x k)
        (marked (x[k]'(by omega))) .left (by simpa [hread] using hrule)
    rw [hstep]; apply congrArg some
    simp [tapeConfig, moveHead, afterSel, hm]
  · have hne : (rightIdx x k : Int) ≠ (k : Int) := by
      intro h; exact hm (Int.natCast_inj.mp h)
    have hplain : holeTape x k (rightIdx x k) = bit (x[rightIdx x k]) := by
      simp only [holeTape, Function.update_of_ne hne]
      rw [et_nat x k _ hr]; unfold rightIdx at hm ⊢; simp; omega
    have hrule : machine.rule (selQ (x[k]'(by omega))) (bit (x[rightIdx x k])) 0 =
        some ⟨marked (x[k]'(by omega)), retQ (x[rightIdx x k]), .left ⟩ := by
      cases x[k] <;> cases x[rightIdx x k] <;> simp [machine, delta, selQ, retQ, bit, marked]
    have hstep :=
      step_write (selQ (x[k]'(by omega))) (retQ (x[rightIdx x k])) (rightIdx x k)
        (holeTape x k) (marked (x[k]'(by omega))) .left
        (by simpa [hplain] using hrule)
    rw [hstep]; apply congrArg some
    simp [tapeConfig, moveHead, afterSel, hm]

def retState (x : List Bool) (k : Nat) (hk : 2 * k < x.length) : Fin 14 :=
  if h : rightIdx x k = k then 11
  else retQ (x[rightIdx x k]'(by unfold rightIdx; omega))

theorem retQ_bit (b b' : Bool) :
    machine.rule (retQ b) (bit b') 0 = some ⟨bit b', retQ b, .left ⟩ := by
  cases b <;> cases b' <;> simp [machine, delta, retQ, bit]
theorem retQ_marked (b b' : Bool) :
    machine.rule (retQ b) (marked b') 0 = some ⟨marked b', retQ b, .left ⟩ := by
  cases b <;> cases b' <;> simp [machine, delta, retQ, marked]
theorem retQ_hole (b : Bool) :
    machine.rule (retQ b) 7 0 = some ⟨marked b, retQ b, .left ⟩ := by
  cases b <;> simp [machine, delta, retQ, marked]
theorem retQ_sent (b : Bool) :
    machine.rule (retQ b) 5 0 = some ⟨5, 6, .right ⟩ := by
  cases b <;> simp [machine, delta, retQ]
theorem rule11_marked (b : Bool) :
    machine.rule 11 (marked b) 0 = some ⟨marked b, 11, .left ⟩ := by
  cases b <;> simp [machine, delta, marked]
theorem rule11_sent : machine.rule 11 5 0 = some ⟨5, 6, .right ⟩ := by
  simp [machine, delta]
theorem rule6_marked (b : Bool) :
    machine.rule 6 (marked b) 0 = some ⟨marked b, 6, .right ⟩ := by
  cases b <;> simp [machine, delta, marked]
theorem rule6_sentR : machine.rule 6 6 0 = some ⟨2, 13, .left ⟩ := by
  simp [machine, delta]
theorem rule13_marked (b : Bool) :
    machine.rule 13 (marked b) 0 = some ⟨bit b, 13, .left ⟩ := by
  cases b <;> simp [machine, delta, marked, bit]
theorem rule13_sent : machine.rule 13 5 0 = some ⟨2, 0, .right ⟩ := by
  simp [machine, delta]

theorem bounce_pick (q : Fin 14) (t : Int → Fin 8)
    (ht : t (-1) = 5)
    (hr : machine.rule q 5 0 = some ⟨5, 6, .right ⟩) :
    step machine 0 (tapeConfig q (-1) t) = some (tapeConfig 6 0 t) := by
  have htape : Function.update t (-1) 5 = t := by
    ext z; by_cases hz : z = -1 <;> simp [Function.update, hz, ht]
  have hstep := step_write q 6 (-1) t 5 .right (by simpa [ht] using hr)
  rw [hstep]; simp [tapeConfig, moveHead, htape]

theorem afterSel_middle (x : List Bool) (k : Nat) (hk : 2 * k < x.length)
    (hm : rightIdx x k = k) :
    afterSel x k (by omega) = epochTape x (k + 1) := by
  have hn : k < x.length := by omega
  have hts := tape_succ x k hk
  have hcell : afterSel x k hn k = marked (x[k]'(by omega)) := by
    simp [afterSel, holeTape, hm]
  have hbit : marked (x[rightIdx x k]'(by unfold rightIdx; omega)) =
      marked (x[k]'(by omega)) := by simp [hm]
  rw [hbit] at hts
  rw [← hcell] at hts
  simpa [Function.update_eq_self] using hts

end PakFixedPolyomino.StandardBitReverse
