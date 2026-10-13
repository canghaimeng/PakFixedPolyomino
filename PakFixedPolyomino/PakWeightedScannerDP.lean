import PakFixedPolyomino.PakScannerBaselineDP
import PakFixedPolyomino.PakScannerTailIdentityWeights
import PakFixedPolyomino.PakWeightedFullFrameStandardFirstBranch

/-! Weighted ALL-headed scanner DP: one finite State × HeadBudget transfer
with literal LegalScan, source-head increment, and actual tailIdentityCopies
edge weights. Linear-in-n arithmetic specification, not polynomial BIT-time. -/

namespace PakFixedPolyomino.PakWeightedScannerDP

noncomputable section

open PakScannerBaselineDP PakScannerBaselineAutomaton
open PakWeightedFullFrameStandardFirstBranch
open Finset

def edgeWeight (source target : ConcretePakScanner.State) : Nat :=
  PakScannerTailIdentityWeights.tailIdentityCopies (some (source, target))

def initialVector : BudgetState → Nat :=
  fun sb =>
    if sb.1 = PakCouplingGenerated.scannerBottom ∧ sb.2 = HeadBudget.zero then 1
    else 0

def transfer (bit : Bool) (v : BudgetState → Nat) : BudgetState → Nat :=
  fun sb =>
    ∑ source : ConcretePakScanner.State, ∑ old : HeadBudget,
      if ConcretePakScanner.LegalScan source sb.1 bit ∧
          addHead (stateHead source) old = sb.2 then
        v (source, old) * edgeWeight source sb.1
      else 0

def weightedFold (n : Nat) : Nat → (BudgetState → Nat)
  | 0 => initialVector
  | k + 1 => transfer (n.testBit k) (weightedFold n k)

def weightedAccept (n : Nat) : Nat :=
  weightedFold n n (ConcretePakScanner.topNorth, HeadBudget.one)

theorem weightedFold_zero (n : Nat) : weightedFold n 0 = initialVector := rfl

theorem weightedFold_succ (n k : Nat) :
    weightedFold n (k + 1) = transfer (n.testBit k) (weightedFold n k) :=
  rfl

def pathWeight {n : Nat} : ∀ {k : Nat} {target : ConcretePakScanner.State}
    {budget : HeadBudget}, DPPath n k target budget → Nat
  | 0, _, _, _ => 1
  | _ + 1, target, _, p => pathWeight p.2.2.1 * edgeWeight p.1 target

@[simp] theorem pathWeight_zero {n : Nat} {target : ConcretePakScanner.State}
    {budget : HeadBudget} (p : DPPath n 0 target budget) :
    pathWeight p = 1 := rfl

@[simp] theorem pathWeight_succ {n k : Nat} {target : ConcretePakScanner.State}
    {budget : HeadBudget} (p : DPPath n (k + 1) target budget) :
    pathWeight p = pathWeight p.2.2.1 * edgeWeight p.1 target := rfl

def fibreSum (n k : Nat) (target : ConcretePakScanner.State)
    (budget : HeadBudget) : Nat :=
  ∑ p : DPPath n k target budget, pathWeight p

theorem fibreSum_zero (n : Nat) (target : ConcretePakScanner.State)
    (budget : HeadBudget) :
    fibreSum n 0 target budget = initialVector (target, budget) := by
  simp only [fibreSum, pathWeight_zero]
  rw [← Fintype.card_eq_sum_ones]
  simpa [initialVector, baselineDP] using dpPath_zero_card n target budget

theorem pathWeight_eq_prod {n k : Nat} {target : ConcretePakScanner.State}
    {budget : HeadBudget} (p : DPPath n k target budget) :
    pathWeight p = ∏ j : Fin k,
      edgeWeight (p.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
        (p.states ⟨j.1 + 1, by omega⟩) := by
  induction k generalizing target budget with
  | zero => simp [pathWeight]
  | succ k ih =>
      rw [Fin.prod_univ_castSucc]
      simp only [pathWeight]
      rw [ih p.2.2.1]
      congr 1
      · apply prod_congr rfl
        intro j _
        congr 1
        · let q : Fin (k + 1) := ⟨j.1, Nat.lt_succ_of_lt j.2⟩
          rw [show (⟨j.castSucc.1, Nat.lt_succ_of_lt j.castSucc.2⟩ : Fin (k + 2)) =
            Fin.castSucc q by ext; rfl]
          simp only [DPPath.states, Fin.lastCases_castSucc]
          congr
        · let q₁ : Fin (k + 1) := ⟨j.1 + 1, by omega⟩
          rw [show (⟨j.castSucc.1 + 1, by omega⟩ : Fin (k + 2)) =
            Fin.castSucc q₁ by ext; rfl]
          simp only [DPPath.states, Fin.lastCases_castSucc]
          congr
      · have hs : p.states ⟨(Fin.last k).1, Nat.lt_succ_of_lt (Fin.last k).2⟩ = p.1 := by
          convert p.states_penultimate
          simp [Fin.last]
        have ht : p.states ⟨(Fin.last k).1 + 1, by omega⟩ = target := by
          have hidx : (⟨(Fin.last k).1 + 1, by omega⟩ : Fin (k + 2)) =
              Fin.last (k + 1) := Fin.ext (by simp [Fin.last])
          rw [hidx, p.states_final]
        rw [hs, ht]

theorem pathWeight_eq_scannerIdentity {n : Nat} (hn : 0 < n)
    (p : DPPath n n ConcretePakScanner.topNorth .one) :
    pathWeight p =
      scannerIdentityWeight (p.toHeadedScannerPath hn).val := by
  rw [pathWeight_eq_prod]
  unfold scannerIdentityWeight ScannerPath.column
  apply Fintype.prod_congr
  intro j
  simp [edgeWeight, DPPath.toHeadedScannerPath, DPPath.toScannerPath]

def dpPathSuccEquiv (n k : Nat) (target : ConcretePakScanner.State)
    (budget : HeadBudget) :
    DPPath n (k + 1) target budget ≃
      Σ source : ConcretePakScanner.State,
        Σ old : HeadBudget,
          {_p : DPPath n k source old //
            ConcretePakScanner.LegalScan source target (n.testBit k) ∧
              addHead (stateHead source) old = budget} where
  toFun p := ⟨p.1, p.2⟩
  invFun q := ⟨q.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fibreSum_succ (n k : Nat) (target : ConcretePakScanner.State)
    (budget : HeadBudget) :
    fibreSum n (k + 1) target budget =
      transfer (n.testBit k) (fun sb => fibreSum n k sb.1 sb.2)
        (target, budget) := by
  classical
  unfold fibreSum transfer
  let e := dpPathSuccEquiv n k target budget
  rw [← e.symm.sum_comp pathWeight]
  simp only [Fintype.sum_sigma]
  apply sum_congr rfl
  intro source _
  apply sum_congr rfl
  intro old _
  by_cases hcond :
      ConcretePakScanner.LegalScan source target (n.testBit k) ∧
        addHead (stateHead source) old = budget
  · simp only [hcond]
    have hpw :
        ∀ x : {p : DPPath n k source old //
            ConcretePakScanner.LegalScan source target (n.testBit k) ∧
              addHead (stateHead source) old = budget},
          pathWeight (e.symm ⟨source, ⟨old, x⟩⟩) =
            pathWeight x.1 * edgeWeight source target := fun _ => rfl
    simp_rw [hpw]
    rw [← sum_mul]
    congr 1
    let u := Equiv.subtypeUnivEquiv
      (fun _ : DPPath n k source old => hcond)
    calc
      ∑ x : {p : DPPath n k source old //
            ConcretePakScanner.LegalScan source target (n.testBit k) ∧
              addHead (stateHead source) old = budget},
          pathWeight x.1 =
          ∑ x, pathWeight (u x) := by
        apply sum_congr rfl
        intro x _
        simp [u, Equiv.subtypeUnivEquiv]
      _ = ∑ p : DPPath n k source old, pathWeight p :=
        u.sum_comp (fun p => pathWeight p)
  · simp only [hcond]
    have : IsEmpty
        {p : DPPath n k source old //
          ConcretePakScanner.LegalScan source target (n.testBit k) ∧
            addHead (stateHead source) old = budget} :=
      ⟨fun x => hcond x.2⟩
    simp [univ_eq_empty]

theorem fibreSum_eq_fold (n k : Nat) (hk : k ≤ n)
    (target : ConcretePakScanner.State) (budget : HeadBudget) :
    fibreSum n k target budget = weightedFold n k (target, budget) := by
  induction k generalizing target budget with
  | zero => exact fibreSum_zero n target budget
  | succ k ih =>
      rw [fibreSum_succ, weightedFold_succ]
      congr 1
      funext sb
      exact ih (by omega) sb.1 sb.2

theorem weightedAccept_zero : weightedAccept 0 = 0 := by
  simp [weightedAccept, weightedFold, initialVector]

theorem headedScannerPath_zero_empty : IsEmpty (HeadedScannerPath 0) :=
  ⟨fun P => Nat.lt_irrefl 0 P.1.pos⟩

theorem weightedBaselineCount_zero :
    weightedBaselineCount 0 = 0 := by
  rw [weighted_baseline_eq_all_headed_scanner_sum]
  have := headedScannerPath_zero_empty
  simp [univ_eq_empty]

theorem weightedAccept_eq_headed_sum (n : Nat) (hn : 0 < n) :
    weightedAccept n =
      ∑ P : HeadedScannerPath n, scannerIdentityWeight P.val := by
  unfold weightedAccept
  rw [← fibreSum_eq_fold n n le_rfl ConcretePakScanner.topNorth .one]
  unfold fibreSum
  let e := dpPathEquivHeadedScannerPath n hn
  calc
    ∑ p : DPPath n n ConcretePakScanner.topNorth .one, pathWeight p =
        ∑ p, scannerIdentityWeight (e p).val := by
      apply Fintype.sum_congr
      intro p
      exact pathWeight_eq_scannerIdentity hn p
    _ = ∑ P : HeadedScannerPath n, scannerIdentityWeight P.val :=
      e.sum_comp (fun P => scannerIdentityWeight P.val)

theorem weightedAccept_eq_weightedBaselineCount (n : Nat) :
    weightedAccept n = weightedBaselineCount n := by
  cases n with
  | zero => rw [weightedAccept_zero, weightedBaselineCount_zero]
  | succ n =>
      rw [weighted_baseline_eq_all_headed_scanner_sum]
      exact weightedAccept_eq_headed_sum (n + 1) (Nat.succ_pos n)

theorem edgeWeight_le_two (source target : ConcretePakScanner.State) :
    edgeWeight source target ≤ 2 := by
  simp [edgeWeight, PakScannerTailIdentityWeights.tailIdentityCopies]
  split_ifs <;> omega

theorem card_headBudget : Fintype.card HeadBudget = 3 := by
  have h : (univ : Finset HeadBudget) =
      insert HeadBudget.zero
        (insert HeadBudget.one ({HeadBudget.many} : Finset HeadBudget)) := by
    ext x
    cases x <;> simp
  have h0 : HeadBudget.zero ∉
      insert HeadBudget.one ({HeadBudget.many} : Finset HeadBudget) := by
    simp
  have h1 : HeadBudget.one ∉ ({HeadBudget.many} : Finset HeadBudget) := by
    simp
  rw [Fintype.card, h, Finset.card_insert_of_notMem h0,
    Finset.card_insert_of_notMem h1, Finset.card_singleton]

def growthBase : Nat := 6 * Fintype.card ConcretePakScanner.State

theorem transfer_le (bit : Bool) (v : BudgetState → Nat) (B : Nat)
    (hv : ∀ sb, v sb ≤ B) (sb : BudgetState) :
    transfer bit v sb ≤ growthBase * B := by
  unfold transfer growthBase
  have hterm : ∀ source old,
      (if ConcretePakScanner.LegalScan source sb.1 bit ∧
          addHead (stateHead source) old = sb.2 then
        v (source, old) * edgeWeight source sb.1
      else 0) ≤ 2 * B := by
    intro source old
    split_ifs
    · have := Nat.mul_le_mul (hv (source, old)) (edgeWeight_le_two source sb.1)
      simpa [Nat.mul_comm] using this
    · exact Nat.zero_le _
  have hsum :
      (∑ source : ConcretePakScanner.State, ∑ old : HeadBudget,
        if ConcretePakScanner.LegalScan source sb.1 bit ∧
            addHead (stateHead source) old = sb.2 then
          v (source, old) * edgeWeight source sb.1
        else 0) ≤
      ∑ source : ConcretePakScanner.State, ∑ old : HeadBudget, 2 * B := by
    apply Finset.sum_le_sum
    intro source _
    apply Finset.sum_le_sum
    intro old _
    exact hterm source old
  refine hsum.trans (le_of_eq ?_)
  simp only [sum_const, card_univ, card_headBudget]
  ring

theorem weightedFold_le (n k : Nat) (sb : BudgetState) :
    weightedFold n k sb ≤ growthBase ^ k := by
  induction k generalizing sb with
  | zero =>
      simp only [weightedFold]
      have : growthBase ^ 0 = 1 := Nat.pow_zero _
      rw [this]
      dsimp [initialVector]
      split_ifs
      · exact Nat.le_refl 1
      · exact Nat.zero_le 1
  | succ k ih =>
      rw [weightedFold_succ]
      have h := transfer_le (n.testBit k) (weightedFold n k) (growthBase ^ k)
        (fun t => ih t) sb
      rw [Nat.mul_comm] at h
      simpa [Nat.pow_succ] using h

theorem weightedBaselineCount_le (n : Nat) :
    weightedBaselineCount n ≤ growthBase ^ n := by
  rw [← weightedAccept_eq_weightedBaselineCount]
  exact weightedFold_le n n (ConcretePakScanner.topNorth, HeadBudget.one)

def weighted_scanner_dp_spec : Prop :=
  (∀ n, weightedFold n 0 = initialVector) ∧
    (∀ n k, weightedFold n (k + 1) =
      transfer (n.testBit k) (weightedFold n k)) ∧
    (∀ n k target budget, k ≤ n →
      fibreSum n k target budget = weightedFold n k (target, budget)) ∧
    (∀ n, weightedAccept n = weightedBaselineCount n) ∧
    (∀ source target, edgeWeight source target ≤ 2) ∧
    (∀ n k sb, weightedFold n k sb ≤ growthBase ^ k) ∧
    (∀ n, weightedBaselineCount n ≤ growthBase ^ n)

theorem weighted_scanner_dp_spec_holds : weighted_scanner_dp_spec :=
  ⟨weightedFold_zero, weightedFold_succ,
    fun n k target budget hk => fibreSum_eq_fold n k hk target budget,
    weightedAccept_eq_weightedBaselineCount, edgeWeight_le_two,
    weightedFold_le, weightedBaselineCount_le⟩

end
end PakFixedPolyomino.PakWeightedScannerDP
