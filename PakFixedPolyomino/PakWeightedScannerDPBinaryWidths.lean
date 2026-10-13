import PakFixedPolyomino.PakWeightedScannerDP
import PakFixedPolyomino.PakFixedWeightedOracleLengthGuard
import PakFixedPolyomino.StandardBitPairProjection
import Mathlib.Data.Num.Lemmas

/-! Binary digit capacity of every original weighted DP coordinate. These
are internally proved numerical storage bounds, not a tape-time certificate.
The total answer guard bounds every counter by a linear polynomial in the
actual paired input length, including arbitrary raw answer words. -/
namespace PakFixedPolyomino.PakWeightedScannerDPBinaryWidths
open Computability PakWeightedScannerDP PakScannerBaselineDP
open PakFixedWeightedOracleLengthGuard
open StandardNondeterministicMachine (Machine)

theorem encode_pos_length (n : PosNum) : (encodePosNum n).length = n.natSize := by
  induction n with
  | one => rfl
  | bit0 n ih => simp [encodePosNum,PosNum.natSize,ih]
  | bit1 n ih => simp [encodePosNum,PosNum.natSize,ih]

theorem encode_num_length (n : Num) : (encodeNum n).length = n.natSize := by
  cases n with
  | zero => rfl
  | pos n => exact encode_pos_length n

theorem encode_nat_length (n : Nat) : (encodeNat n).length = n.size := by
  change (encodeNum (n : Num)).length = n.size
  rw [encode_num_length,Num.natSize_to_nat]
  simp only [Num.to_of_nat]

theorem encode_length_of_lt_pow {v k : Nat} (h : v < 2^k) :
    (encodeNat v).length ≤ k := by
  rw [encode_nat_length]
  exact Nat.size_le.mpr h

theorem growth_pow_lt_binary (k : Nat) : growthBase^k < 2^(growthBase*k+1) := by
  have hbase : growthBase ≤ 2^growthBase := Nat.le_of_lt Nat.lt_two_pow_self
  have hpow : growthBase^k ≤ (2^growthBase)^k := Nat.pow_le_pow_left hbase k
  have hnext : 2^(growthBase*k) < 2^(growthBase*k+1) := by
    rw [pow_succ]
    have hp : 0 < 2^(growthBase*k) := pow_pos (by decide) _
    omega
  rw [← pow_mul] at hpow
  exact hpow.trans_lt hnext

theorem fold_bits_length (n k : Nat) (sb : BudgetState) :
    (encodeNat (weightedFold n k sb)).length ≤ growthBase*k+1 :=
  encode_length_of_lt_pow ((weightedFold_le n k sb).trans_lt (growth_pow_lt_binary k))

theorem baseline_bits_length (n : Nat) :
    (encodeNat (PakWeightedFullFrameStandardFirstBranch.weightedBaselineCount n)).length ≤
      growthBase*n+1 :=
  encode_length_of_lt_pow ((weightedBaselineCount_le n).trans_lt (growth_pow_lt_binary n))

theorem guarded_pair_counter_width {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat)
    (raw x bits : List Bool) (hpair : StandardBitMetric.unpairBits raw = some (x,bits))
    (hguard : macroSide M p x < bits.length) (k : Nat) (hk : k ≤ macroSide M p x)
    (sb : BudgetState) :
    (encodeNat (weightedFold (macroSide M p x) k sb)).length ≤ growthBase*raw.length+1 := by
  have hraw : raw = StandardBitMetric.pairBits x bits :=
    StandardBitPairProjection.unpairBits_eq_some.mp hpair
  have hlen : bits.length ≤ raw.length := by
    rw [hraw,StandardBitMetric.pairBits_length]
    omega
  have hkraw : k ≤ raw.length := by omega
  exact (fold_bits_length _ _ _).trans (by
    have h := Nat.mul_le_mul_left growthBase hkraw
    omega)

theorem weighted_dp_binary_width_spec :
    (∀ n k sb,(encodeNat (weightedFold n k sb)).length ≤ growthBase*k+1) ∧
    (∀ n,(encodeNat (PakWeightedFullFrameStandardFirstBranch.weightedBaselineCount n)).length ≤
      growthBase*n+1) ∧
    (∀ ns nt (M : Machine ns nt 2) p raw x bits,
      StandardBitMetric.unpairBits raw = some (x,bits) → macroSide M p x < bits.length →
      ∀ k,k ≤ macroSide M p x → ∀ sb,
        (encodeNat (weightedFold (macroSide M p x) k sb)).length ≤ growthBase*raw.length+1) :=
  ⟨fold_bits_length,baseline_bits_length,fun _ _ M p raw x bits hp hg k hk sb =>
    guarded_pair_counter_width M p raw x bits hp hg k hk sb⟩

end PakFixedPolyomino.PakWeightedScannerDPBinaryWidths
