import PakFixedPolyomino.PakFixedWeightedStandardBinaryCount
import PakFixedPolyomino.StandardBitMetric

set_option maxRecDepth 100000

/-! The actual fixed physical amplifier forces long true oracle answers.
This proves the guard for a total postprocessor specification. It is not an
arithmetic-operation or tape-time certificate. -/
namespace PakFixedPolyomino.PakFixedWeightedOracleLengthGuard
noncomputable section
open Computability PakFixedWeightedStandardBinaryCount
open PakFixedWeightedRegisterInventory (params wangTile liveWangTile)
open PakFixedWeightedPhysicalSourceReadout (sourceSide sourceAnswer)
open StandardNondeterministicMachine (Machine RunsAtMost acceptingCount SharpEXP)

theorem amplifier_ge_two (P : RegisterParams) : 2 ≤ P.amp := by
  have hr : 0 < P.perimeterBase := by have := P.perimeterBase_ge_two; omega
  have hp : 0 < P.perimeterBase^3 := pow_pos hr 3
  change 2 ≤ 1024 * P.perimeterBase^3
  omega

theorem amp_ge_two : 2 ≤ params.amp := amplifier_ge_two params

theorem exponent_ge_side (n : Nat) (hn : 2 ≤ n) : n ≤ amplifierExponent n := by
  have hh : 1 ≤ n-1 := by omega
  have h := Nat.mul_le_mul_left n hh
  unfold amplifierExponent
  nlinarith

theorem amplifier_le_indexed_count (n : Nat) (hn : 2 ≤ n) :
    params.amp ^ amplifierExponent n ≤
      PakFixedWeightedRegisterInventory.squareCount (params.pitch*n) := by
  have hc : 1 ≤ openWangCount wangTile n n := by
    change 1 ≤ openWangCount (withDummyWangTile liveWangTile) n n
    rw [withDummyOpenCount_eq_add_one liveWangTile n n (by omega) (by omega)]
    omega
  have hf := PakFixedWeightedRegisterInventory.physical_floor_readout n hn
  have hdiv : 1 ≤ PakFixedWeightedRegisterInventory.squareCount (params.pitch*n) /
      params.amp^amplifierExponent n := by rw [hf]; exact hc
  calc
    params.amp^amplifierExponent n = 1*(params.amp^amplifierExponent n) := by simp
    _ ≤ (PakFixedWeightedRegisterInventory.squareCount (params.pitch*n) /
        params.amp^amplifierExponent n) * (params.amp^amplifierExponent n) :=
      Nat.mul_le_mul_right _ hdiv
    _ ≤ PakFixedWeightedRegisterInventory.squareCount (params.pitch*n) :=
      Nat.div_mul_le_self _ _

theorem pow_side_le_shape_count (n : Nat) (hn : 2 ≤ n) :
    2^n ≤ PakFixedWeightedShapeFamily.squareCount (params.pitch*n) := by
  rw [PakFixedWeightedShapeFamily.square_count_eq_indexed]
  calc
    2^n ≤ 2^amplifierExponent n := Nat.pow_le_pow_right (by decide) (exponent_ge_side n hn)
    _ ≤ params.amp^amplifierExponent n := Nat.pow_le_pow_left amp_ge_two (amplifierExponent n)
    _ ≤ _ := amplifier_le_indexed_count n hn

theorem count_bits_longer_than_side (n : Nat) (hn : 2 ≤ n) :
    n < (encodeNat (PakFixedWeightedShapeFamily.squareCount (params.pitch*n))).length := by
  have hl := pow_side_le_shape_count n hn
  have hu := value_lt_pow_length (encodeNat (PakFixedWeightedShapeFamily.squareCount (params.pitch*n)))
  rw [value_encode_nat] at hu
  by_contra h
  have he : (encodeNat (PakFixedWeightedShapeFamily.squareCount (params.pitch*n))).length ≤ n := by omega
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) he
  omega

variable {ns nt : Nat}

def macroSide (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) : Nat :=
  ConcretePakSide.sideValue (ULogTernaryGeneratedMarginScanner.input M p x)

def oracleAnswer (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) : Nat :=
  binarySquareCount (encodeNat (sourceSide M p x))

theorem macro_side_ge_two (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    2 ≤ macroSide M p x :=
  (by decide : 2 ≤ 5).trans (PakSideScanner.sideValue_ge_five _)

theorem true_answer_guard (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    macroSide M p x < (encodeNat (oracleAnswer M p x)).length := by
  rw [oracleAnswer,binary_square_count_encode]
  exact count_bits_longer_than_side _ (macro_side_ge_two M p x)

/-- Total numeric specification: short raw answers return zero before the
large arithmetic branch. The guard still requires its own tape compiler. -/
def guardedAnswer (M : Machine ns nt 2) (p : Polynomial Nat) (x bits : List Bool) : Nat :=
  if macroSide M p x < bits.length then sourceAnswer M p x (value bits) else 0

theorem short_answer_zero (M : Machine ns nt 2) (p : Polynomial Nat) (x bits : List Bool)
    (h : bits.length ≤ macroSide M p x) : guardedAnswer M p x bits = 0 := by
  simp [guardedAnswer,show ¬macroSide M p x < bits.length from by omega]

theorem true_guarded_answer (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    guardedAnswer M p x (encodeNat (oracleAnswer M p x)) =
      sourceAnswer M p x (oracleAnswer M p x) := by
  rw [guardedAnswer,if_pos (true_answer_guard M p x),value_encode_nat]

def guardedPostprocessor (M : Machine ns nt 2) (p : Polynomial Nat)
    (raw : List Bool) : List Bool :=
  match StandardBitMetric.unpairBits raw with
  | none => []
  | some (x,bits) => encodeNat (guardedAnswer M p x bits)

theorem guarded_source_readout (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2^p.eval x.length)) :
    guardedPostprocessor M p (StandardBitMetric.pairInputAnswer x (oracleAnswer M p x)) =
      encodeNat (acceptingCount M x (2^p.eval x.length)) := by
  simp only [guardedPostprocessor,StandardBitMetric.pairInputAnswer,
    StandardBitMetric.unpair_pairBits,true_guarded_answer]
  rw [oracleAnswer,binary_source_readout M p x ht]

theorem standard_sharp_exp_guarded_readout (f : List Bool → Nat) (hf : SharpEXP f) :
    ∃ ns nt, ∃ M : Machine ns nt 2, ∃ p : Polynomial Nat,
      ∀ x, guardedPostprocessor M p (StandardBitMetric.pairInputAnswer x (oracleAnswer M p x)) =
        encodeNat (f x) := by
  obtain ⟨ns,nt,M,p,h⟩ := standard_sharp_exp_binary_source_readout f hf
  refine ⟨ns,nt,M,p,?_⟩
  intro x
  simp only [guardedPostprocessor,StandardBitMetric.pairInputAnswer,
    StandardBitMetric.unpair_pairBits,true_guarded_answer]
  exact congrArg encodeNat (h x)

def oracle_length_guard_spec : Prop :=
  (∀ n, 2 ≤ n → 2^n ≤ PakFixedWeightedShapeFamily.squareCount (params.pitch*n)) ∧
  (∀ ns nt (M : Machine ns nt 2) p x,
    macroSide M p x < (encodeNat (oracleAnswer M p x)).length) ∧
  (∀ f : List Bool → Nat, SharpEXP f →
    ∃ ns nt, ∃ M : Machine ns nt 2, ∃ p : Polynomial Nat,
      ∀ x, guardedPostprocessor M p (StandardBitMetric.pairInputAnswer x (oracleAnswer M p x)) =
        encodeNat (f x))

theorem oracle_length_guard_spec_holds : oracle_length_guard_spec :=
  ⟨pow_side_le_shape_count,fun _ _ M p x => true_answer_guard M p x,
    standard_sharp_exp_guarded_readout⟩

end
end PakFixedPolyomino.PakFixedWeightedOracleLengthGuard
