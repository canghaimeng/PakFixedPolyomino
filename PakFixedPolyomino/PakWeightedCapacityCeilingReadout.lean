import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-! Finite geometric capacity weights and the exact ceiling readout
`(F + A - 1) / A = C` under prefix saturation, a zero below `L`, and a
strict missing-tail deficit. Arithmetic only: not BIT-time, not a
physical scanner certificate. -/

namespace PakFixedPolyomino.PakWeightedCapacityCeilingReadout

open Finset

def weightedCapacitySum (S : ℕ) (g : ℕ → ℕ) : ℕ :=
  ∑ K ∈ range S, 2 ^ (S - 1 - K) * g K

def fullCapacityWeight (S L : ℕ) : ℕ :=
  2 ^ (S - L) - 1

lemma two_pow_sum_range (n : ℕ) :
    ∑ k ∈ range n, (2 : ℕ) ^ k = 2 ^ n - 1 := by
  simpa using Nat.geomSum_eq (by decide : 2 ≤ 2) n

lemma two_pow_le_of_le {m n : ℕ} (h : m ≤ n) : (2 : ℕ) ^ m ≤ 2 ^ n :=
  Nat.pow_le_pow_right (by decide : 0 < 2) h

lemma filter_ge_eq_Ico (S L : ℕ) :
    (range S).filter (fun K => L ≤ K) = Ico L S := by
  ext K
  simp [mem_range, mem_Ico]
  omega

lemma two_pow_sub_one_sub {a b : ℕ} (hba : b ≤ a) :
    (2 ^ a - 1) - (2 ^ b - 1) = 2 ^ a - 2 ^ b := by
  have h1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hpow : 2 ^ b ≤ 2 ^ a := two_pow_le_of_le hba
  omega

lemma suffix_two_pow_sum {S L : ℕ} (_hLS : L ≤ S) :
    ∑ K ∈ Ico L S, (2 : ℕ) ^ (S - 1 - K) = 2 ^ (S - L) - 1 := by
  rw [sum_Ico_eq_sum_range]
  trans ∑ i ∈ range (S - L), (2 : ℕ) ^ ((S - L) - 1 - i)
  · refine sum_congr rfl ?_
    intro i hi
    simp only [mem_range] at hi
    congr 1
    omega
  · rw [sum_range_reflect (fun j => (2 : ℕ) ^ j) (S - L)]
    exact two_pow_sum_range (S - L)

theorem suffix_weight_eq {S L : ℕ} (hLS : L ≤ S) :
    ∑ K ∈ (range S).filter (fun K => L ≤ K), 2 ^ (S - 1 - K) =
      fullCapacityWeight S L := by
  rw [filter_ge_eq_Ico, fullCapacityWeight]
  exact suffix_two_pow_sum hLS

theorem interval_weight_eq {S L H : ℕ} (hLH : L ≤ H) (hHS : H ≤ S) :
    ∑ K ∈ Ico L H, (2 : ℕ) ^ (S - 1 - K) =
      2 ^ (S - L) - 2 ^ (S - H) := by
  have hLS : L ≤ S := le_trans hLH hHS
  have hunion : Ico L S = Ico L H ∪ Ico H S :=
    (Ico_union_Ico_eq_Ico hLH hHS).symm
  have hdisj : Disjoint (Ico L H) (Ico H S) := Ico_disjoint_Ico_consecutive L H S
  have hsum :
      ∑ K ∈ Ico L H, (2 : ℕ) ^ (S - 1 - K) +
          ∑ K ∈ Ico H S, (2 : ℕ) ^ (S - 1 - K) =
        ∑ K ∈ Ico L S, (2 : ℕ) ^ (S - 1 - K) := by
    rw [hunion, sum_union hdisj]
  have hsub :
      ∑ K ∈ Ico L H, (2 : ℕ) ^ (S - 1 - K) =
        ∑ K ∈ Ico L S, (2 : ℕ) ^ (S - 1 - K) -
          ∑ K ∈ Ico H S, (2 : ℕ) ^ (S - 1 - K) :=
    Nat.eq_sub_of_add_eq hsum
  rw [hsub, suffix_two_pow_sum hLS, suffix_two_pow_sum hHS,
    two_pow_sub_one_sub (Nat.sub_le_sub_left hLH S)]

lemma weightedCapacitySum_eq_from {S L : ℕ} (g : ℕ → ℕ)
    (hzero : ∀ K, K < L → g K = 0) :
    weightedCapacitySum S g =
      ∑ K ∈ Ico L S, 2 ^ (S - 1 - K) * g K := by
  unfold weightedCapacitySum
  rw [← sum_filter_add_sum_filter_not (range S) (fun K => L ≤ K)]
  have hlow :
      ∑ K ∈ (range S).filter (fun K => ¬ L ≤ K),
          2 ^ (S - 1 - K) * g K = 0 := by
    apply sum_eq_zero
    intro K hK
    simp only [mem_filter, mem_range, not_le] at hK
    rw [hzero K hK.2, mul_zero]
  rw [filter_ge_eq_Ico, hlow, add_zero]

theorem weightedCapacitySum_le {S L C : ℕ} (g : ℕ → ℕ)
    (hbound : ∀ K, K < S → g K ≤ C)
    (hzero : ∀ K, K < L → g K = 0) :
    weightedCapacitySum S g ≤ C * fullCapacityWeight S L := by
  by_cases hLS : L ≤ S
  · rw [weightedCapacitySum_eq_from g hzero, fullCapacityWeight,
      ← suffix_two_pow_sum hLS, mul_sum]
    refine sum_le_sum ?_
    intro K hK
    simp only [mem_Ico] at hK
    rw [mul_comm C]
    exact Nat.mul_le_mul_left _ (hbound K hK.2)
  · have hF : weightedCapacitySum S g = 0 := by
      unfold weightedCapacitySum
      apply sum_eq_zero
      intro K hK
      simp only [mem_range] at hK
      have : K < L := lt_of_lt_of_le hK (le_of_not_ge hLS)
      rw [hzero K this, mul_zero]
    simp [hF]

theorem weightedCapacitySum_ge {S L H C : ℕ} (g : ℕ → ℕ)
    (hLH : L ≤ H) (hHS : H ≤ S)
    (hzero : ∀ K, K < L → g K = 0)
    (hsat : ∀ K, L ≤ K → K < H → g K = C) :
    C * (2 ^ (S - L) - 2 ^ (S - H)) ≤ weightedCapacitySum S g := by
  have hdisj : Disjoint (Ico L H) (Ico H S) := Ico_disjoint_Ico_consecutive L H S
  have hunion : Ico L S = Ico L H ∪ Ico H S :=
    (Ico_union_Ico_eq_Ico hLH hHS).symm
  rw [weightedCapacitySum_eq_from g hzero, hunion, sum_union hdisj]
  have hsatSum :
      ∑ K ∈ Ico L H, 2 ^ (S - 1 - K) * g K =
        C * ∑ K ∈ Ico L H, 2 ^ (S - 1 - K) := by
    rw [mul_sum]
    refine sum_congr rfl ?_
    intro K hK
    simp only [mem_Ico] at hK
    rw [hsat K hK.1 hK.2, mul_comm]
  rw [hsatSum, interval_weight_eq hLH hHS]
  exact Nat.le_add_right _ _

lemma missing_tail_lt {S L H B C : ℕ}
    (hLH : L < H) (hHS : H ≤ S) (hpad : L + B + 2 ≤ H)
    (hC : C ≤ 2 ^ B) :
    C * (2 ^ (S - H) - 1) < fullCapacityWeight S L := by
  have hSHB : S - H + B ≤ S - L - 2 := by omega
  have hpow : 2 ^ (S - H + B) ≤ 2 ^ (S - L - 2) := two_pow_le_of_le hSHB
  have hB : 2 ^ B ≤ 2 ^ (S - L - 2) := two_pow_le_of_le (by omega)
  have hdistrib :
      2 ^ B * (2 ^ (S - H) - 1) = 2 ^ (S - H + B) - 2 ^ B := by
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_comm]
  have hmul :
      C * (2 ^ (S - H) - 1) ≤ 2 ^ (S - H + B) - 2 ^ B := by
    calc
      C * (2 ^ (S - H) - 1)
          ≤ 2 ^ B * (2 ^ (S - H) - 1) := Nat.mul_le_mul_right _ hC
      _ = 2 ^ (S - H + B) - 2 ^ B := hdistrib
  have hstep : 2 ^ (S - H + B) - 2 ^ B ≤ 2 ^ (S - L - 2) - 2 ^ B :=
    Nat.sub_le_sub_right hpow _
  have hclose : 2 ^ (S - L - 2) - 2 ^ B < fullCapacityWeight S L := by
    unfold fullCapacityWeight
    have hSL : S - L = S - L - 2 + 2 := by omega
    have h4 : 2 ^ (S - L) = 2 ^ (S - L - 2) * 4 := by
      rw [hSL, pow_add]
      norm_num
    rw [h4]
    set a := 2 ^ (S - L - 2)
    have ha : 1 ≤ a := Nat.one_le_two_pow
    have hstep1 : a - 2 ^ B + 2 ≤ a + 2 :=
      Nat.add_le_add_right (Nat.sub_le a (2 ^ B)) 2
    have hstep2 : a + 2 ≤ a * 4 := by
      have hmul : (1 : ℕ) * 2 ≤ a * 3 :=
        Nat.mul_le_mul ha (by decide : (2 : ℕ) ≤ 3)
      have h3 : 2 ≤ 3 * a := by
        have : 2 ≤ a * 3 := by simpa using hmul
        rw [Nat.mul_comm] at this
        exact this
      have hadd : a + 2 ≤ a + 3 * a := Nat.add_le_add_left h3 a
      have hre : a + 3 * a = a * 4 := by
        rw [Nat.add_comm, Nat.mul_comm 3 a, ← Nat.mul_succ]
      rw [hre] at hadd
      exact hadd
    have hsum : a - 2 ^ B + 2 ≤ a * 4 := le_trans hstep1 hstep2
    have h4pos : 1 ≤ a * 4 := by
      have hmul : a * 1 ≤ a * 4 :=
        Nat.mul_le_mul_left a (by decide : (1 : ℕ) ≤ 4)
      have : a ≤ a * 4 := by simpa using hmul
      exact le_trans ha this
    have : a - 2 ^ B + 1 ≤ a * 4 - 1 :=
      (Nat.le_sub_iff_add_le h4pos).2 hsum
    exact Nat.lt_of_succ_le this
  exact lt_of_le_of_lt (le_trans hmul hstep) hclose

lemma fullCapacityWeight_pos {S L H : ℕ} (hLH : L < H) (hHS : H ≤ S) :
    0 < fullCapacityWeight S L := by
  unfold fullCapacityWeight
  have h1 : 1 ≤ S - L := by omega
  have h2 : 2 ≤ 2 ^ (S - L) := two_pow_le_of_le h1
  omega

theorem weighted_capacity_ceiling_readout
    (S L H B C : ℕ) (g : ℕ → ℕ)
    (hLH : L < H) (hHS : H ≤ S) (hpad : L + B + 2 ≤ H)
    (hC : C ≤ 2 ^ B)
    (hbound : ∀ K, K < S → g K ≤ C)
    (hzero : ∀ K, K < L → g K = 0)
    (hsat : ∀ K, L ≤ K → K < H → g K = C) :
    (weightedCapacitySum S g + fullCapacityWeight S L - 1) /
      fullCapacityWeight S L = C := by
  set F := weightedCapacitySum S g
  set A := fullCapacityWeight S L
  have hA : 0 < A := fullCapacityWeight_pos hLH hHS
  have hA1 : 1 ≤ A := Nat.succ_le_iff.mpr hA
  have hle : F ≤ C * A := weightedCapacitySum_le g hbound hzero
  have hge : C * (2 ^ (S - L) - 2 ^ (S - H)) ≤ F :=
    weightedCapacitySum_ge g hLH.le hHS hzero hsat
  have hinterval :
      2 ^ (S - L) - 2 ^ (S - H) = A - (2 ^ (S - H) - 1) := by
    change 2 ^ (S - L) - 2 ^ (S - H) =
      (2 ^ (S - L) - 1) - (2 ^ (S - H) - 1)
    exact (two_pow_sub_one_sub (Nat.sub_le_sub_left hLH.le S)).symm
  have hDlt : C * (2 ^ (S - H) - 1) < A :=
    missing_tail_lt hLH hHS hpad hC
  have hDle : C * (2 ^ (S - H) - 1) ≤ A - 1 := Nat.le_pred_of_lt hDlt
  have hge' : C * A - C * (2 ^ (S - H) - 1) ≤ F := by
    have : C * (A - (2 ^ (S - H) - 1)) ≤ F := by
      rwa [← hinterval]
    rwa [Nat.mul_sub] at this
  have hlow : C * A ≤ F + A - 1 := by
    have hmid : C * A - (A - 1) ≤ F :=
      le_trans (Nat.sub_le_sub_left hDle (C * A)) hge'
    have : C * A ≤ F + (A - 1) := (Nat.sub_le_iff_le_add).1 hmid
    rw [Nat.add_sub_assoc hA1]
    exact this
  have hhigh : F + A - 1 ≤ C * A + A - 1 := by
    rw [Nat.add_sub_assoc hA1, Nat.add_sub_assoc hA1]
    exact Nat.add_le_add_right hle (A - 1)
  exact (Nat.div_eq_iff hA).2 ⟨hlow, hhigh⟩

/-- Joint: suffix/interval weights, upper/lower bounds, exact ceiling. -/
def weighted_capacity_ceiling_spec : Prop :=
  (∀ S L, L ≤ S →
    ∑ K ∈ (range S).filter (fun K => L ≤ K), 2 ^ (S - 1 - K) =
      fullCapacityWeight S L) ∧
  (∀ S L H, L ≤ H → H ≤ S →
    ∑ K ∈ Ico L H, (2 : ℕ) ^ (S - 1 - K) =
      2 ^ (S - L) - 2 ^ (S - H)) ∧
  (∀ S L C g, (∀ K, K < S → g K ≤ C) → (∀ K, K < L → g K = 0) →
    weightedCapacitySum S g ≤ C * fullCapacityWeight S L) ∧
  (∀ S L H C g, L ≤ H → H ≤ S →
    (∀ K, K < L → g K = 0) →
    (∀ K, L ≤ K → K < H → g K = C) →
    C * (2 ^ (S - L) - 2 ^ (S - H)) ≤ weightedCapacitySum S g) ∧
  (∀ S L H B C g,
    L < H → H ≤ S → L + B + 2 ≤ H → C ≤ 2 ^ B →
    (∀ K, K < S → g K ≤ C) →
    (∀ K, K < L → g K = 0) →
    (∀ K, L ≤ K → K < H → g K = C) →
    (weightedCapacitySum S g + fullCapacityWeight S L - 1) /
      fullCapacityWeight S L = C)

theorem weighted_capacity_ceiling_spec_holds :
    weighted_capacity_ceiling_spec :=
  ⟨fun _ _ => suffix_weight_eq,
    fun _ _ _ => interval_weight_eq,
    fun _ _ _ => weightedCapacitySum_le,
    fun _ _ _ _ => weightedCapacitySum_ge,
    weighted_capacity_ceiling_readout⟩

end PakFixedPolyomino.PakWeightedCapacityCeilingReadout
