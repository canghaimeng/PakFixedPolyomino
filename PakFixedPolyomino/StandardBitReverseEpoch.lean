import PakFixedPolyomino.StandardBitReverse

/-! Ordinary return and one swap epoch of the frozen 14×8 reversal machine. -/
namespace PakFixedPolyomino.StandardBitReverseEpoch
open StandardNondeterministicMachine StandardBitTime StandardBitReverse
open FiniteOneTapeSemantics (moveHead)

theorem epochConfig_tape (x : List Bool) (k : Nat) :
    epochConfig x k = tapeConfig 6 0 (epochTape x k) := rfl

theorem retState_middle (x : List Bool) (k : Nat) (hk : 2 * k < x.length)
    (hm : rightIdx x k = k) : retState x k hk = 11 := by
  simp [retState, hm]

theorem retState_pair (x : List Bool) (k : Nat) (hk : 2 * k < x.length)
    (hm : rightIdx x k ≠ k) :
    retState x k hk = retQ (x[rightIdx x k]'(by unfold rightIdx; omega)) := by
  simp [retState, hm]

theorem middle_fuel (x : List Bool) (k : Nat) (hk : 2 * k < x.length)
    (hm : rightIdx x k = k) : x.length - k = k + 1 := by
  simp only [rightIdx] at hm; omega

theorem pair_le (x : List Bool) (k : Nat) (hk : 2 * k < x.length)
    (hm : rightIdx x k ≠ k) : k + 1 ≤ rightIdx x k := by
  unfold rightIdx at hm ⊢; omega

theorem pair_fuel (x : List Bool) (k : Nat) (hk : 2 * k < x.length)
    (hm : rightIdx x k ≠ k) :
    x.length - k = (rightIdx x k - (k + 1)) + (1 + (k + 1)) := by
  have hgt := pair_le x k hk hm
  unfold rightIdx at hgt ⊢; omega

theorem pair_gap (x : List Bool) (k : Nat) (hk : 2 * k < x.length)
    (hm : rightIdx x k ≠ k) :
    rightIdx x k - (k + 1) = rightIdx x k - k - 1 := by
  have hgt := pair_le x k hk hm
  omega

theorem marked_succ (x : List Bool) (k i : Nat) (_hk : 2 * k < x.length)
    (hi : i < x.length) (hmark : i < k + 1) :
    epochTape x (k + 1) i = marked (x[x.length - 1 - i]'(by omega)) := by
  rw [et_nat x (k + 1) i hi]; simp [hmark]


theorem afterSel_plain (x : List Bool) (k i : Nat) (hn : k < x.length)
    (hlo : k < i) (hhi : i < rightIdx x k) (hi : i < x.length) :
    afterSel x k hn i = bit (x[i]) := by
  have hneK : (i : Int) ≠ (k : Int) := by omega
  have hneR : (i : Int) ≠ (rightIdx x k : Int) := by omega
  simp only [afterSel, holeTape, Function.update_of_ne hneR,
    Function.update_of_ne hneK]
  rw [et_nat x k i hi]
  unfold rightIdx at hhi
  simp; omega

theorem afterSel_hole (x : List Bool) (k : Nat) (hn : k < x.length)
    (hne : (k : Int) ≠ (rightIdx x k : Int)) : afterSel x k hn k = 7 := by
  simp [afterSel, holeTape, Function.update_of_ne hne]

theorem return_middle (x : List Bool) (k : Nat) (hk : 2 * k < x.length)
    (hm : rightIdx x k = k) :
    run machine (ticks (k + 1))
      (tapeConfig 11 ((k : Int) - 1) (epochTape x (k + 1))) =
      some (epochConfig x (k + 1)) := by
  have hb := bounce_pick 11 (epochTape x (k + 1)) (et_neg1 x (k + 1)) rule11_sent
  by_cases h0 : k = 0
  · subst k
    rw [run_ticks_one]
    convert hb using 2
    · simp [tapeConfig]
    · simp [epochConfig, tapeConfig]
  · have hpos : 1 ≤ k := by omega
    have hrules :
        ∀ p : Nat, p < k →
          machine.rule 11 (epochTape x (k + 1) ((k : Int) - 1 - p)) 0 =
            some ⟨epochTape x (k + 1) ((k : Int) - 1 - p), 11, .left ⟩ := by
      intro p hp
      have hid : ((k : Int) - 1 - p) = ((k - 1 - p : Nat) : Int) := by omega
      have hp' : k - 1 - p < x.length := by omega
      have hcell := marked_succ x k (k - 1 - p) hk hp' (by omega)
      simpa [hid, hcell] using
        rule11_marked (x[x.length - 1 - (k - 1 - p)]'(by omega))
    have hscan := scan_left 11 ((k : Int) - 1) (epochTape x (k + 1)) k hrules
    have hscan' :
        run machine (ticks k)
          (tapeConfig 11 ((k : Int) - 1) (epochTape x (k + 1))) =
          some (tapeConfig 11 (-1) (epochTape x (k + 1))) := by
      convert hscan using 3; omega
    rw [ticks_add, run_append, hscan', Option.bind_some, run_ticks_one, hb,
      epochConfig_tape]

theorem return_pair (x : List Bool) (k : Nat) (hk : 2 * k < x.length)
    (hm : rightIdx x k ≠ k) :
    run machine (ticks (x.length - k))
      (tapeConfig (retQ (x[rightIdx x k]'(by unfold rightIdx; omega)))
        ((rightIdx x k : Int) - 1) (afterSel x k (by omega))) =
      some (epochConfig x (k + 1)) := by
  have hn : k < x.length := by omega
  have hri : rightIdx x k < x.length := by unfold rightIdx; omega
  have hgt := pair_le x k hk hm
  have hdecomp := pair_fuel x k hk hm
  have hgap := pair_gap x k hk hm
  have hticks : ticks (x.length - k) =
      ticks (rightIdx x k - k - 1) ++ ticks (1 + (k + 1)) := by
    rw [← ticks_add, show x.length - k = (rightIdx x k - k - 1) + (1 + (k + 1)) by
      omega]
  rw [hticks, run_append]
  have hrules1 :
      ∀ p : Nat, p < rightIdx x k - k - 1 →
        machine.rule (retQ (x[rightIdx x k]'hri))
          (afterSel x k hn ((rightIdx x k : Int) - 1 - p)) 0 =
          some ⟨afterSel x k hn ((rightIdx x k : Int) - 1 - p),
            retQ (x[rightIdx x k]'hri), .left ⟩ := by
    intro p hp
    have hid : ((rightIdx x k : Int) - 1 - p) =
        ((rightIdx x k - 1 - p : Nat) : Int) := by omega
    have hp' : rightIdx x k - 1 - p < x.length := by unfold rightIdx; omega
    have hlo : k < rightIdx x k - 1 - p := by omega
    have hhi : rightIdx x k - 1 - p < rightIdx x k := by omega
    have hcell := afterSel_plain x k (rightIdx x k - 1 - p) hn hlo hhi hp'
    simpa [hid, hcell] using
      retQ_bit (x[rightIdx x k]'hri) (x[rightIdx x k - 1 - p])
  have hscan1 :=
    scan_left (retQ (x[rightIdx x k]'hri)) ((rightIdx x k : Int) - 1)
      (afterSel x k hn) (rightIdx x k - k - 1) hrules1
  have hscan1' :
      run machine (ticks (rightIdx x k - k - 1))
        (tapeConfig (retQ (x[rightIdx x k]'hri)) ((rightIdx x k : Int) - 1)
          (afterSel x k hn)) =
        some (tapeConfig (retQ (x[rightIdx x k]'hri)) k (afterSel x k hn)) := by
    convert hscan1 using 3; omega
  rw [hscan1', Option.bind_some, ticks_add, run_append, run_ticks_one]
  have hne : (k : Int) ≠ (rightIdx x k : Int) := by
    intro h; exact hm (Int.natCast_inj.mp h.symm)
  have hfill :=
    step_write (retQ (x[rightIdx x k]'hri)) (retQ (x[rightIdx x k]'hri)) k
      (afterSel x k hn) (marked (x[rightIdx x k]'hri)) .left
      (by simpa [afterSel_hole x k hn hne] using retQ_hole (x[rightIdx x k]'hri))
  rw [hfill, Option.bind_some]
  have htape := tape_succ x k hk
  have hcfg :
      tapeConfig (retQ (x[rightIdx x k]'hri)) (moveHead .left k)
        (Function.update (afterSel x k hn) k (marked (x[rightIdx x k]'hri))) =
        tapeConfig (retQ (x[rightIdx x k]'hri)) ((k : Int) - 1)
          (epochTape x (k + 1)) := by
    simp [tapeConfig, moveHead, htape]
  rw [hcfg]
  have hrules2 :
      ∀ p : Nat, p < k →
        machine.rule (retQ (x[rightIdx x k]'hri))
          (epochTape x (k + 1) ((k : Int) - 1 - p)) 0 =
          some ⟨epochTape x (k + 1) ((k : Int) - 1 - p),
            retQ (x[rightIdx x k]'hri), .left ⟩ := by
    intro p hp
    have hid : ((k : Int) - 1 - p) = ((k - 1 - p : Nat) : Int) := by omega
    have hp' : k - 1 - p < x.length := by omega
    have hcell := marked_succ x k (k - 1 - p) hk hp' (by omega)
    simpa [hid, hcell] using
      retQ_marked (x[rightIdx x k]'hri)
        (x[x.length - 1 - (k - 1 - p)]'(by omega))
  have hscan2 :=
    scan_left (retQ (x[rightIdx x k]'hri)) ((k : Int) - 1)
      (epochTape x (k + 1)) k hrules2
  have hscan2' :
      run machine (ticks k)
        (tapeConfig (retQ (x[rightIdx x k]'hri)) ((k : Int) - 1)
          (epochTape x (k + 1))) =
        some (tapeConfig (retQ (x[rightIdx x k]'hri)) (-1)
          (epochTape x (k + 1))) := by
    convert hscan2 using 3; omega
  rw [ticks_add, run_append, hscan2', Option.bind_some, run_ticks_one]
  have hb := bounce_pick (retQ (x[rightIdx x k]'hri)) (epochTape x (k + 1))
    (et_neg1 x (k + 1)) (retQ_sent (x[rightIdx x k]'hri))
  rw [hb, epochConfig_tape]

theorem return_run (x : List Bool) (k : Nat) (hk : 2 * k < x.length) :
    run machine (ticks (x.length - k))
      (tapeConfig (retState x k hk) ((rightIdx x k : Int) - 1)
        (afterSel x k (by omega))) = some (epochConfig x (k + 1)) := by
  by_cases hm : rightIdx x k = k
  · have hst := retState_middle x k hk hm
    have hhead : (rightIdx x k : Int) - 1 = (k : Int) - 1 := by simp [hm]
    have htape := afterSel_middle x k hk hm
    have hfuel := middle_fuel x k hk hm
    rw [hst, hhead, htape, hfuel]
    exact return_middle x k hk hm
  · have hst := retState_pair x k hk hm
    rw [hst]
    exact return_pair x k hk hm

theorem epoch_fuel_split (n k : Nat) (hk : 2 * k < n) :
    epochFuel n k =
      k + (1 + ((n - 2 * k - 1) + (1 + (1 + (n - k))))) := by
  unfold epochFuel; omega

theorem epoch_run (x : List Bool) (k : Nat) (hk : 2 * k < x.length) :
    run machine (ticks (epochFuel x.length k)) (epochConfig x k) =
      some (epochConfig x (k + 1)) := by
  rw [epoch_fuel_split x.length k hk, ticks_add, run_append, epoch_skip x k hk,
    Option.bind_some, ticks_add, run_append, run_ticks_one, epoch_pick x k hk,
    Option.bind_some, ticks_add, run_append, epoch_seek_pass x k hk,
    Option.bind_some, ticks_add, run_append, run_ticks_one, epoch_seek_turn x k hk,
    Option.bind_some, ticks_add, run_append, run_ticks_one, epoch_select x k hk,
    Option.bind_some]
  have hst :
      (if rightIdx x k = k then (11 : Fin 14)
        else retQ (x[rightIdx x k]'(by unfold rightIdx; omega))) =
        retState x k hk := by
    simp [retState]
  simp [hst]
  exact return_run x k hk

theorem epoch_exact :
    ∀ (x : List Bool) (k : Nat), 2 * k < x.length →
      run machine (ticks (epochFuel x.length k)) (epochConfig x k) =
        some (epochConfig x (k + 1)) :=
  fun x k hk => epoch_run x k hk

end PakFixedPolyomino.StandardBitReverseEpoch
