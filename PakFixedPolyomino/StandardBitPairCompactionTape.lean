import PakFixedPolyomino.StandardBitPairProjection

/-! Whole-tape invariants for retaining and compacting the first paired word.
These are explicit tape equalities, not initialized-machine or time claims. -/
namespace PakFixedPolyomino.StandardBitPairCompactionTape
open StandardNondeterministicMachine StandardBitTime StandardBitMetric

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

def enc (b : Bool) : Fin 8 := if b then 1 else 0
def mark (b : Bool) : Fin 8 := if b then 7 else 6

def natTape (x y : List Bool) (k i : Nat) : Fin 8 :=
  if h : i < k ∧ i < x.length then enc x[i]
  else if i = k then 4
  else if i = (pairBits x y).length then 5
  else if h : i % 2 = 1 ∧ k ≤ i / 2 ∧ i / 2 < x.length then mark x[i / 2]
  else 2

def tape (x y : List Bool) (k : Nat) (z : Int) : Fin 8 :=
  if z = -1 then 3 else if 0 ≤ z then natTape x y k z.toNat else 2

theorem pair_length (x y : List Bool) :
    (pairBits x y).length = 2*x.length+1+y.length := by
  simp [pairBits_length]

theorem pair_length_gt (x y : List Bool) : x.length < (pairBits x y).length := by
  rw [pair_length]
  omega

theorem tape_nat (x y : List Bool) (k i : Nat) :
    tape x y k (i : Int) = natTape x y k i := by
  simp [tape]

theorem tape_L (x y : List Bool) (k : Nat) : tape x y k (-1) = 3 := by
  simp [tape]

theorem tape_dest (x y : List Bool) (k : Nat) : tape x y k (k : Int) = 4 := by
  rw [tape_nat]
  simp [natTape]

theorem tape_source (x y : List Bool) (k : Nat) (hk : k < x.length) :
    tape x y k (2*k+1 : Nat) = mark x[k] := by
  have hn := pair_length x y
  rw [tape_nat]
  have hp : ¬ (2*k+1 < k ∧ 2*k+1 < x.length) := by omega
  have hd : 2*k+1 ≠ k := by omega
  have he : 2*k+1 ≠ (pairBits x y).length := by omega
  have hmod : (2*k+1)%2 = 1 := by omega
  have hdiv : (2*k+1)/2 = k := by omega
  simp only [natTape,dif_neg hp,if_neg hd,if_neg he,hmod,hdiv]
  rw [dif_pos (show True ∧ k ≤ k ∧ k < x.length by exact ⟨trivial,le_rfl,hk⟩)]

theorem tape_gap (x y : List Bool) (k i : Nat)
    (hk : k ≤ x.length) (hlo : k < i) (hhi : i < 2*k+1) :
    tape x y k (i : Int) = 2 := by
  rw [tape_nat]
  have hn := pair_length x y
  have hp : ¬ (i < k ∧ i < x.length) := by omega
  have hd : i ≠ k := by omega
  have he : i ≠ (pairBits x y).length := by omega
  have hm : ¬ (i % 2 = 1 ∧ k ≤ i/2 ∧ i/2 < x.length) := by omega
  simp only [natTape,dif_neg hp,if_neg hd,if_neg he,dif_neg hm]

theorem tape_end (x y : List Bool) (k : Nat) (hk : k ≤ x.length) :
    tape x y k ((pairBits x y).length : Int) = 5 := by
  rw [tape_nat]
  have hn := pair_length_gt x y
  have hp : ¬ ((pairBits x y).length < k ∧ (pairBits x y).length < x.length) := by omega
  have hd : (pairBits x y).length ≠ k := by omega
  simp only [natTape,dif_neg hp,if_neg hd,ite_true]

theorem natTape_other (x y : List Bool) (k i : Nat)
    (hi : i ≠ k) (hd : i ≠ k+1) (hs : i ≠ 2*k+1) :
    natTape x y k i = natTape x y (k+1) i := by
  have hp : (i < k ∧ i < x.length) ↔ (i < k+1 ∧ i < x.length) := by omega
  have hm : (i % 2 = 1 ∧ k ≤ i/2 ∧ i/2 < x.length) ↔
      (i % 2 = 1 ∧ k+1 ≤ i/2 ∧ i/2 < x.length) := by omega
  simp only [natTape,← hp,← hm,if_neg hi,if_neg hd]

theorem natTape_consumed (x y : List Bool) (k : Nat)
    (hk : k < x.length) (hpos : 0 < k) : natTape x y (k+1) (2*k+1) = 2 := by
  have hn := pair_length x y
  have hp : ¬ (2*k+1 < k+1 ∧ 2*k+1 < x.length) := by omega
  have hd : 2*k+1 ≠ k+1 := by omega
  have he : 2*k+1 ≠ (pairBits x y).length := by omega
  have hm : ¬ ((2*k+1)%2 = 1 ∧ k+1 ≤ (2*k+1)/2 ∧ (2*k+1)/2 < x.length) := by omega
  simp only [natTape,dif_neg hp,if_neg hd,if_neg he,dif_neg hm]

theorem copy_update (x y : List Bool) (k : Nat) (hk : k < x.length) :
    Function.update
      (Function.update (Function.update (tape x y k) ((2*k+1 : Nat) : Int) 2)
        (k : Int) (enc x[k])) ((k+1 : Nat) : Int) 4 = tape x y (k+1) := by
  funext z
  by_cases hz : z = ((k+1 : Nat) : Int)
  · subst z
    rw [Function.update_self]
    exact (tape_dest x y (k+1)).symm
  · by_cases hi : z = (k : Int)
    · subst z
      have hp : k < k+1 ∧ k < x.length := ⟨by omega,hk⟩
      simp only [Function.update_apply,if_neg hz,ite_true,tape_nat,natTape,dif_pos hp]
    · by_cases hs : z = ((2*k+1 : Nat) : Int)
      · subst z
        have hpos : 0 < k := by omega
        simp only [Function.update_apply,if_neg hz,if_neg hi,ite_true,tape_nat]
        exact (natTape_consumed x y k hk hpos).symm
      · simp only [Function.update_apply,if_neg hz,if_neg hi,if_neg hs]
        by_cases hn : 0 ≤ z
        · have hki : z.toNat ≠ k := by omega
          have hdi : z.toNat ≠ k+1 := by omega
          have hsi : z.toNat ≠ 2*k+1 := by omega
          simp only [tape]
          split_ifs <;> try rfl
          exact natTape_other x y k z.toNat hki hdi hsi
        · simp [tape,hn]

theorem complete_nat (x y : List Bool) (i : Nat) :
    natTape x y x.length i =
      if h : i < x.length then enc x[i]
      else if i = x.length then 4
      else if i = (pairBits x y).length then 5 else 2 := by
  have hm : ¬ (i%2 = 1 ∧ x.length ≤ i/2 ∧ i/2 < x.length) := by omega
  simp only [natTape,and_self,dif_neg hm]

theorem complete_erase (x y : List Bool) :
    Function.update
      (Function.update (tape x y x.length) ((pairBits x y).length : Int) 2)
      (x.length : Int) 2 =
    Function.update (inputTape StandardBitPairProjection.machine x) (-1) 3 := by
  funext z
  have hn := pair_length_gt x y
  by_cases hl : z = -1
  · subst z
    have hd : (-1 : Int) ≠ (x.length : Int) := by omega
    have he : (-1 : Int) ≠ ((pairBits x y).length : Int) := by omega
    simp only [Function.update_apply,if_neg hd,if_neg he,tape_L,ite_true]
  · by_cases hz : 0 ≤ z
    · lift z to Nat using hz with i
      have hL : (i : Int) ≠ -1 := by omega
      simp only [Function.update_apply,if_neg hL,tape_nat,complete_nat]
      by_cases hi : i < x.length
      · have hd : (i : Int) ≠ (x.length : Int) := by omega
        have he : (i : Int) ≠ ((pairBits x y).length : Int) := by omega
        rw [if_neg hd,if_neg he,dif_pos hi,inputTape_ofNat _ x i hi]
        rfl
      · have hg : (x.length : Int) ≤ (i : Int) := by omega
        rw [inputTape_ge _ x _ hg,StandardBitPairProjection.machine_blank,dif_neg hi]
        by_cases hd : i = x.length
        · subst i
          simp only [ite_true]
        · have hd' : (i : Int) ≠ (x.length : Int) := by omega
          rw [if_neg hd',if_neg hd]
          by_cases he : i = (pairBits x y).length
          · subst i
            simp only [ite_true]
          · have he' : (i : Int) ≠ ((pairBits x y).length : Int) := by omega
            rw [if_neg he',if_neg he]
    · have hd : z ≠ (x.length : Int) := by omega
      have he : z ≠ ((pairBits x y).length : Int) := by omega
      simp only [Function.update_apply,if_neg hl,if_neg hd,if_neg he,tape,
        if_neg hl,if_neg hz,inputTape_neg _ x z (by omega),StandardBitPairProjection.machine_blank]

end PakFixedPolyomino.StandardBitPairCompactionTape
