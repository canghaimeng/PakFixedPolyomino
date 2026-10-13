import PakFixedPolyomino.PakWeightedScannerDPBinaryWidths

/-! Storage bounds for the original total readout on every raw paired word.
These are numerical binary lengths; ordinary tape execution remains separate. -/
namespace PakFixedPolyomino.PakGuardedReadoutStorageBounds
noncomputable section
open Computability StandardBitTime StandardBitMetric
open PakFixedWeightedStandardBinaryCount (value value_lt_pow_length)
open StandardNondeterministicMachine (Machine)
open PakFixedWeightedOracleLengthGuard
open PakFixedWeightedPhysicalSourceReadout (sourceAnswer)
open PakAllFrameWeightedOrdinarySourceReadout (sourceReadoutWeight source_readout_weight_pos)
open PakFixedWeightedRegisterInventory (params)
open PakWeightedCoupledCoefficient (weightedExtractionQ)
open PakWeightedFullFrameStandardFirstBranch (weightedBaselineCount)
open PakWeightedScannerDPBinaryWidths (encode_length_of_lt_pow)

theorem fixed_power_bits_length (c k : Nat) :
    (encodeNat (c^k)).length ≤ c*k+1 := by
  have hc : c ≤ 2^c := Nat.le_of_lt Nat.lt_two_pow_self
  have hp : c^k ≤ (2^c)^k := Nat.pow_le_pow_left hc k
  rw [← pow_mul] at hp
  have hnext : 2^(c*k) < 2^(c*k+1) := by
    rw [pow_succ]
    have hpos : 0 < 2^(c*k) := pow_pos (by decide) _
    omega
  exact encode_length_of_lt_pow (hp.trans_lt hnext)

theorem ceiling_le_self (v a : Nat) (ha : 0 < a) : (v+a-1)/a ≤ v := by
  apply (Nat.div_le_iff_le_mul ha).mpr
  have h : v ≤ v*a := by
    have hm := Nat.mul_le_mul_left v (show 1 ≤ a by omega)
    simpa using hm
  omega

def residual {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (answer : Nat) : Nat :=
  (answer / params.amp^amplifierExponent (macroSide M p x) - 1) /
      weightedExtractionQ^PakAmpCoefficient.BoundaryMask.full.qDegree
        (macroSide M p x) (macroSide M p x) - weightedBaselineCount (macroSide M p x)

theorem residual_le {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (answer : Nat) : residual M p x answer ≤ answer := by
  unfold residual
  exact (Nat.sub_le _ _).trans ((Nat.div_le_self _ _).trans
    ((Nat.sub_le _ _).trans (Nat.div_le_self _ _)))

theorem source_answer_le {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (answer : Nat) : sourceAnswer M p x answer ≤ answer := by
  change (residual M p x answer + sourceReadoutWeight M p x - 1) /
    sourceReadoutWeight M p x ≤ answer
  exact (ceiling_le_self _ _ (source_readout_weight_pos M p x)).trans (residual_le M p x answer)

theorem guarded_answer_le {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat)
    (x bits : List Bool) : guardedAnswer M p x bits ≤ value bits := by
  unfold guardedAnswer
  split_ifs
  · exact source_answer_le M p x (value bits)
  · exact Nat.zero_le _

theorem guarded_answer_bits_length {ns nt : Nat} (M : Machine ns nt 2)
    (p : Polynomial Nat) (x bits : List Bool) :
    (encodeNat (guardedAnswer M p x bits)).length ≤ bits.length :=
  encode_length_of_lt_pow ((guarded_answer_le M p x bits).trans_lt (value_lt_pow_length bits))

theorem paired_lengths {raw x bits : List Bool}
    (h : unpairBits raw = some (x,bits)) : x.length ≤ raw.length ∧ bits.length ≤ raw.length := by
  rw [StandardBitPairProjection.unpairBits_eq_some.mp h,pairBits_length]
  omega

theorem total_postprocessor_length {ns nt : Nat} (M : Machine ns nt 2)
    (p : Polynomial Nat) (raw : List Bool) : (guardedPostprocessor M p raw).length ≤ raw.length := by
  unfold guardedPostprocessor
  cases hp : unpairBits raw with
  | none => simp
  | some pair =>
    rcases pair with ⟨x,bits⟩
    exact (guarded_answer_bits_length M p x bits).trans (paired_lengths hp).2

theorem scanner_capacity_le_side (x : List Bool) :
    PakSlotOneScannerMultiplicity.scannerCapacityCount x ≤ ConcretePakSide.sideValue x := by
  unfold PakSlotOneScannerMultiplicity.scannerCapacityCount
  rw [PakSideScanner.sideScannerBits_length]
  omega

theorem readout_weight_le_pow_side {ns nt : Nat} (M : Machine ns nt 2)
    (p : Polynomial Nat) (x : List Bool) : sourceReadoutWeight M p x ≤ 2^macroSide M p x := by
  unfold sourceReadoutWeight PakWeightedCapacityCeilingReadout.fullCapacityWeight
  exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by decide)
    ((Nat.sub_le _ _).trans (scanner_capacity_le_side _)))

theorem readout_weight_bits_length {ns nt : Nat} (M : Machine ns nt 2)
    (p : Polynomial Nat) (x : List Bool) :
    (encodeNat (sourceReadoutWeight M p x)).length ≤ macroSide M p x+1 := by
  apply encode_length_of_lt_pow
  have hnext : 2^macroSide M p x < 2^(macroSide M p x+1) := by
    rw [pow_succ]
    have hp : 0 < 2^macroSide M p x := pow_pos (by decide) _
    omega
  exact (readout_weight_le_pow_side M p x).trans_lt hnext

theorem amplifier_exponent_le (n : Nat) : amplifierExponent n ≤ 2*n*n := by
  unfold amplifierExponent
  exact Nat.mul_le_mul_left (2*n) (Nat.sub_le n 1)

theorem amplifier_denominator_bits_length (n : Nat) :
    (encodeNat (params.amp^amplifierExponent n)).length ≤ params.amp*(2*n*n)+1 :=
  (fixed_power_bits_length _ _).trans (by
    have h := Nat.mul_le_mul_left params.amp (amplifier_exponent_le n)
    omega)

theorem coefficient_denominator_bits_length (n : Nat) (hn : 2 ≤ n) :
    (encodeNat (weightedExtractionQ^PakAmpCoefficient.BoundaryMask.full.qDegree n n)).length ≤
      weightedExtractionQ*(4*n)+1 := by
  apply (fixed_power_bits_length _ _).trans
  have hd : PakAmpCoefficient.BoundaryMask.full.qDegree n n ≤ 4*n := by
    rw [PakAmpCoefficient.BoundaryMask.full_qDegree hn hn]
    omega
  have h := Nat.mul_le_mul_left weightedExtractionQ hd
  omega

theorem guarded_numerator_bits_length {ns nt : Nat} (M : Machine ns nt 2)
    (p : Polynomial Nat) (x bits : List Bool) (hg : macroSide M p x < bits.length) :
    (encodeNat (residual M p x (value bits)+sourceReadoutWeight M p x-1)).length ≤ bits.length+1 := by
  apply encode_length_of_lt_pow
  have hr := (residual_le M p x (value bits)).trans_lt (value_lt_pow_length bits)
  have ha := (readout_weight_le_pow_side M p x).trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hg))
  rw [pow_succ]
  omega

theorem raw_guarded_storage {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat)
    (raw x bits : List Bool) (hp : unpairBits raw = some (x,bits))
    (hg : macroSide M p x < bits.length) :
    (encodeNat (params.amp^amplifierExponent (macroSide M p x))).length ≤
        params.amp*(2*raw.length*raw.length)+1 ∧
    (encodeNat (weightedExtractionQ^PakAmpCoefficient.BoundaryMask.full.qDegree
        (macroSide M p x) (macroSide M p x))).length ≤ weightedExtractionQ*(4*raw.length)+1 ∧
    (encodeNat (sourceReadoutWeight M p x)).length ≤ raw.length+1 ∧
    (encodeNat (residual M p x (value bits)+sourceReadoutWeight M p x-1)).length ≤ raw.length+1 ∧
    (∀ k,k ≤ macroSide M p x → ∀ sb,
      (encodeNat (PakWeightedScannerDP.weightedFold (macroSide M p x) k sb)).length ≤
        PakWeightedScannerDP.growthBase*raw.length+1) := by
  have hbits := (paired_lengths hp).2
  have hn : macroSide M p x ≤ raw.length := by omega
  refine ⟨(amplifier_denominator_bits_length _).trans ?_,
    (coefficient_denominator_bits_length _ (macro_side_ge_two M p x)).trans ?_,
    (readout_weight_bits_length M p x).trans (by omega),
    (guarded_numerator_bits_length M p x bits hg).trans (by omega),?_⟩
  · have hq : 2*macroSide M p x*macroSide M p x ≤ 2*raw.length*raw.length :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) hn
    have h := Nat.mul_le_mul_left params.amp hq
    omega
  · have h := Nat.mul_le_mul_left weightedExtractionQ (Nat.mul_le_mul_left 4 hn)
    omega
  · intro k hk sb
    exact PakWeightedScannerDPBinaryWidths.guarded_pair_counter_width M p raw x bits hp hg k hk sb

theorem guarded_readout_storage_spec :
    (∀ ns nt (M : Machine ns nt 2) p raw,(guardedPostprocessor M p raw).length ≤ raw.length) ∧
    (∀ ns nt (M : Machine ns nt 2) p raw x bits,
      unpairBits raw = some (x,bits) → macroSide M p x < bits.length →
      (encodeNat (params.amp^amplifierExponent (macroSide M p x))).length ≤
        params.amp*(2*raw.length*raw.length)+1 ∧
      (encodeNat (weightedExtractionQ^PakAmpCoefficient.BoundaryMask.full.qDegree
        (macroSide M p x) (macroSide M p x))).length ≤ weightedExtractionQ*(4*raw.length)+1 ∧
      (encodeNat (sourceReadoutWeight M p x)).length ≤ raw.length+1 ∧
      (encodeNat (residual M p x (value bits)+sourceReadoutWeight M p x-1)).length ≤ raw.length+1 ∧
      (∀ k,k ≤ macroSide M p x → ∀ sb,
        (encodeNat (PakWeightedScannerDP.weightedFold (macroSide M p x) k sb)).length ≤
          PakWeightedScannerDP.growthBase*raw.length+1)) :=
  ⟨fun _ _ M p raw => total_postprocessor_length M p raw,
    fun _ _ M p raw x bits hp hg => raw_guarded_storage M p raw x bits hp hg⟩

end
end PakFixedPolyomino.PakGuardedReadoutStorageBounds
