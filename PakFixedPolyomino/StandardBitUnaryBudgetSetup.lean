import PakFixedPolyomino.StandardBitUnaryBudgetCompare

/-! Exact ordinary setup/budget alignment and the physical q9 return to L.
This module does not assert complete comparator correctness or runtime. -/
namespace PakFixedPolyomino.StandardBitUnaryBudgetSetup
open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open StandardBitUnaryBudgetCompare
open StandardBitPairProjection (natInt natInt_inj natInt_ne_neg1 nat_ne_neg1
  pairBits_payload pairBits_y update_same)
open StandardBitMarkedCompaction (scan_left)
open FiniteOneTapeSemantics (writtenTape moveHead)

set_option maxHeartbeats 800000

theorem ended_nat_budget (x y : List Bool) (i : Nat) :
    endedTape x y (natInt i)=budgetTape x y 0 x (natInt i) := by
  rw [budget_at]
  by_cases hE : i=Eidx x y
  · subst i
    have hlt : ¬ Eidx x y < D x := by simp [D,Eidx];omega
    have hne : Eidx x y ≠ D x := by simp [D,Eidx];omega
    have hprefix : ¬ Eidx x y < D x+1+0 := by simp [D,Eidx];omega
    simp [endedTape,budgetNat,hlt,hne,hprefix]
  · have hEi : natInt i ≠ natInt (Eidx x y) := by
      intro h;exact hE (natInt_inj.mp h)
    unfold endedTape
    rw [Function.update_of_ne hEi]
    by_cases hS : i=D x
    · subst i
      have hp : ¬ D x < D x := Nat.lt_irrefl _
      simp [skipTape,budgetNat,hp]
    · have hSi : natInt i ≠ natInt (D x) := by
        intro h;exact hS (natInt_inj.mp h)
      unfold skipTape
      rw [Function.update_of_ne hSi]
      by_cases hi : i < D x
      · unfold workTape workNat
        rw [if_neg (natInt_ne_neg1 i),dif_pos (Nat.cast_nonneg i)]
        simp only [natInt,Int.toNat_natCast,if_pos hi]
        unfold budgetNat
        rw [if_pos hi]
        by_cases he : i%2=0
        · simp [he]
        · have ho : i%2=1 := by omega
          have hidx : i < (pairBits x y).length := by
            have hlen := pairBits_length x y;unfold D at hi;omega
          have hu : i/2 < x.length := by unfold D at hi;omega
          have hodd : 2*(i/2)+1=i := by omega
          have hp := pairBits_payload x y (i/2) hu
          have hp' : (pairBits x y)[i]'hidx=x[i/2]'hu := by simpa only [hodd] using hp
          simp only [he,if_false,dif_pos hidx,dif_pos hu]
          rw [hp']
      · rw [work_ge (pairBits x y) (D x) i (by omega)]
        unfold budgetNat
        rw [if_neg hi,if_neg hS]
        have hn : ¬ i < D x+1+0 := by omega
        rw [if_neg hn]
        by_cases hy : i < Eidx x y
        · have hj : i-(D x+1) < y.length := by unfold Eidx D at*;omega
          have hnidx : i < (pairBits x y).length := by
            have hlen := pairBits_length x y;unfold Eidx at hy;omega
          have hiidx : D x+1+(i-(D x+1))=i := by omega
          have hp := pairBits_y x y (i-(D x+1)) hj
          have hh : 2*x.length+1+(i-(D x+1))=i := by unfold D at*;omega
          have hp' : (pairBits x y)[i]'hnidx=y[i-(D x+1)]'hj := by simpa only [hh] using hp
          rw [if_pos hy,dif_pos hj,read_bit _ _ hnidx,hp']
        · have hge : ((pairBits x y).length : Int) ≤ natInt i := by
            have hlen := pairBits_length x y;unfold Eidx at*;unfold natInt;omega
          rw [if_neg hy,if_neg hE,inputTape_ge machine (pairBits x y) _ hge,machine_blank]

theorem ended_to_budget (x y : List Bool) : endedTape x y=budgetTape x y 0 x := by
  funext z
  by_cases hL : z=(-1 : Int)
  · subst z;rw [ended_L,budget_L]
  · by_cases hp : 0 ≤ z
    · have hz : z=natInt z.toNat := (Int.toNat_of_nonneg hp).symm
      rw [hz];exact ended_nat_budget x y z.toNat
    · have hD : z ≠ natInt (D x) := by unfold natInt;omega
      have hE : z ≠ natInt (Eidx x y) := by unfold natInt;omega
      simp [endedTape,skipTape,Function.update_of_ne hD,Function.update_of_ne hE,
        workTape,budgetTape,hL,hp]

theorem setup_budget_run (x y : List Bool) :
    run machine (ticks (2*x.length+2*y.length+5)) (initial machine (pairBits x y))=
      some ⟨8,natInt (D x+1),budgetTape x y 0 x⟩ := by
  simpa only [ended_to_budget] using setup_run x y

theorem budget_nat_ne_L (x y u : List Bool) (k i : Nat) :
    budgetTape x y k u (natInt i) ≠ (3 : Fin 8) := by
  rw [budget_at]
  unfold budgetNat
  split_ifs <;> try decide
  all_goals unfold enc;split_ifs <;> decide

theorem seek_L (x y u : List Bool) (k : Nat) :
    run machine (ticks (D x+k+2)) ⟨9,natInt (D x+k),budgetTape x y (k+1) u⟩=
      some ⟨10,0,budgetTape x y (k+1) u⟩ := by
  have hw : run machine (ticks (D x+k+1))
      ⟨9,natInt (D x+k),budgetTape x y (k+1) u⟩=
      some ⟨9,-1,budgetTape x y (k+1) u⟩ := by
    have hh : natInt (D x+k)-((D x+k+1 : Nat) : Int)=(-1 : Int) := by unfold natInt;omega
    rw [← hh]
    apply scan_left (M:=machine) (q:=9) (t:=budgetTape x y (k+1) u)
      (h:=natInt (D x+k)) (n:=D x+k+1)
    intro i hi
    have hz : natInt (D x+k)-(i : Int)=natInt (D x+k-i) := by unfold natInt;omega
    rw [hz]
    exact rule_seekL_not _ (budget_nat_ne_L x y u (k+1) _)
  have hf : D x+k+2=(D x+k+1)+1 := by omega
  rw [hf,ticks_add,run_append,hw,Option.bind_some,run_ticks_one]
  simp [step,budget_L,rule_seekL,writtenTape,moveHead,update_same]

end PakFixedPolyomino.StandardBitUnaryBudgetSetup
