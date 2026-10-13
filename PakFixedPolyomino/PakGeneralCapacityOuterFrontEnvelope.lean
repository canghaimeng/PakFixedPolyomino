import PakFixedPolyomino.PakGeneralCapacityOuterFrontFuel

/-! The literal slot-one start and complete parser/copier front at every
actual minimum-capable scanner capacity. All bounds concern occupied physical
arrows, not bit-time execution of a reduction. -/
namespace PakFixedPolyomino.PakGeneralCapacityOuterFrontEnvelope
open MStarConcreteAlphabet
open PakGeneralCapacityInitialWindow PakGeneralCapacityParserCopierFront
open PakGeneralCapacityOuterFrontStandard PakSlotOneScannerMultiplicity
open PakParserOuterBridge PakOuterFrontQuantitative
open PakCopierReserveLowerBound PakGeneralCapacityOuterFrontFuel

theorem parser_linear_le_pow (m : Nat) : 150 * m + 376 ≤ 2 ^ (m + 9) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    calc
      150 * (m + 1) + 376 ≤ 2 * (150 * m + 376) := by omega
      _ ≤ 2 * 2 ^ (m + 9) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ ((m + 1) + 9) := by
        rw [show (m + 1) + 9 = (m + 9) + 1 by omega, pow_succ]
        ring

theorem parser_polynomial_lt_pow (m : Nat) :
    75 * m * m + 301 * m + 226 < 2 ^ (m + 9) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have linear := parser_linear_le_pow m
    calc
      75 * (m + 1) * (m + 1) + 301 * (m + 1) + 226 =
          (75 * m * m + 301 * m + 226) + (150 * m + 376) := by ring
      _ < 2 ^ (m + 9) + 2 ^ (m + 9) := Nat.add_lt_add_of_lt_of_le ih linear
      _ = 2 ^ ((m + 1) + 9) := by
        rw [show (m + 1) + 9 = (m + 9) + 1 by omega, pow_succ]
        ring

theorem parser_fuel_lt_pow (x : ConcretePakSide.Word) :
    PakOuterParserNumericSuffix.parserExplicitFuel x < 2 ^ (24 * x.length + 45) := by
  rw [PakOuterParserNumericSuffix.parserExplicitFuel_closed]
  exact (parser_polynomial_lt_pow x.length).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))

def startFrontFuel (x : ConcretePakSide.Word) (available : Nat) : Nat :=
  1 + generalOuterFrontFuel x available

theorem start_front_fuel_le_pow47 (x : ConcretePakSide.Word) (available : Nat)
    (minimum : minimumSuccessfulWorkCount x.length ≤ available) :
    startFrontFuel x available ≤ 2 ^ (24 * x.length + 47) + 2 * available := by
  have parser := parser_fuel_lt_pow x
  have front := generalOuterFrontFuel_le_envelope x available minimum
  have positive : 1 ≤ 2 ^ (24 * x.length + 45) := Nat.one_le_two_pow
  have four : 4 * 2 ^ (24 * x.length + 45) = 2 ^ (24 * x.length + 47) := by
    rw [show (4 : Nat) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  unfold startFrontFuel
  omega

theorem capacity_start_at_most_one (x : ConcretePakSide.Word) (cap : ScannerCapacity x) :
    OuterReachesAtMost 1 (capacityEncodedStartConfig x cap)
      (capacityEncodedParserConfig x cap) := by
  refine ⟨[PakEncodedStart.startOneArrow], by simp, ?_⟩
  change (FiniteOneTapeSemantics.step MStarULogAssembly.program MStarOuterProgram.movable
      (capacityEncodedStartConfig x cap) PakEncodedStart.startOneArrow).bind
        (FiniteOneTapeSemantics.run MStarULogAssembly.program MStarOuterProgram.movable []) = _
  rw [capacityEncodedStart_slotOne_step]
  rfl

theorem actual_start_front_bounded (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (minimum : minimumSuccessfulWorkCount x.length ≤ cap.val) :
    ∃ d, CapacitySideCopierRealize x cap minimum
        (.groupReady (rawGeneralCapacityGroupZipper x
          (actualFinalCapacity x.length cap.val) (capacityCopierJunk x) (capacityHashTail x cap))) d ∧
      OuterReachesAtMost (startFrontFuel x cap.val) (capacityEncodedStartConfig x cap) d := by
  rcases actual_outer_front_bounded x cap minimum with ⟨d, realized, front⟩
  exact ⟨d, realized, outerReachesAtMost_trans (capacity_start_at_most_one x cap) front⟩

theorem actual_start_front_envelope (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (minimum : minimumSuccessfulWorkCount x.length ≤ cap.val) :
    ∃ d, CapacitySideCopierRealize x cap minimum
        (.groupReady (rawGeneralCapacityGroupZipper x
          (actualFinalCapacity x.length cap.val) (capacityCopierJunk x) (capacityHashTail x cap))) d ∧
      OuterReachesAtMost (2 ^ (24 * x.length + 47) + 2 * cap.val)
        (capacityEncodedStartConfig x cap) d := by
  rcases actual_start_front_bounded x cap minimum with ⟨d, realized, arrows, bound, run⟩
  exact ⟨d, realized, arrows, bound.trans (start_front_fuel_le_pow47 x cap.val minimum), run⟩

theorem sixteen_front_constant_le_side (x : ConcretePakSide.Word) :
    16 * 2 ^ (24 * x.length + 47) ≤ ConcretePakSide.sideValue x := by
  have power : 16 * 2 ^ (24 * x.length + 47) = 2 ^ (24 * x.length + 51) := by
    rw [show (16 : Nat) = 2 ^ 4 by norm_num, ← pow_add]
    congr 1
    omega
  rw [power]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) (by
    unfold ConcretePakSide.paddingLength
    omega)).trans (Nat.ge_two_pow_of_testBit (PakSideScanner.sideValue_padding_testBit x))

theorem start_front_fits_low_capacity (x : ConcretePakSide.Word) (available : Nat)
    (minimum : minimumSuccessfulWorkCount x.length ≤ available)
    (low : 16 * available ≤ ConcretePakSide.sideValue x) :
    4 * startFrontFuel x available < ConcretePakSide.sideValue x := by
  have front := start_front_fuel_le_pow47 x available minimum
  have constant := sixteen_front_constant_le_side x
  have positive := PakSideScanner.sideValue_pos x
  omega

end PakFixedPolyomino.PakGeneralCapacityOuterFrontEnvelope
