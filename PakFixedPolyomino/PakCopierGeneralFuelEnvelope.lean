import PakFixedPolyomino.PakCopierGeneralCompleteFuel

/-! Capacity-dependent physical microstep envelope for the actual copier.
The input-only canonical cost bounds the minimum cost; unused capacity
adds exactly two literal scans. These are not BIT-time certificates. -/
namespace PakFixedPolyomino.PakCopierGeneralFuelEnvelope
open MStarCopierExecution PakCopierReserveLowerBound PakOuterFrontNumericBound
open PakCopierRawCounterFuel PakCopierGeneralCompleteFuel
open PakCopierGeneralGroupPayloadFuel PakCopierGeneralFinalFuel

def canonicalAvailable (x : List Bool) : Nat :=
  2 * iteratedGroupWidth x.length 256 + x.length

theorem general_copier_fuel_at_canonical (x : List Bool) :
    generalCopierFuel x (canonicalAvailable x) = copierExplicitFuel x := by
  have identity := groupMinimumConsumed_add_width x.length 256
  have remaining : canonicalAvailable x - 255 - groupMinimumConsumed x.length 256 - 1 =
      iteratedGroupWidth x.length 256 + x.length := by
    unfold canonicalAvailable
    omega
  unfold generalCopierFuel copierExplicitFuel
  dsimp only
  rw [remaining]
  simp only [rawCounterPayloadFuel, generalPayloadFuel, Nat.zero_add,
    List.append_nil, Nat.add_sub_cancel, generalFinalFuel_closed, copierFinalFuel_closed,
    List.length_reverse]
  ring

theorem general_copier_minimum_fuel_le_canonical (x : List Bool) :
    generalCopierFuel x (minimumSuccessfulWorkCount x.length) ≤ copierExplicitFuel x := by
  have affine := generalCopierFuel_affine_available x
    (minimumSuccessfulWorkCount x.length) (iteratedGroupWidth x.length 256) (Nat.le_refl _)
  have size : minimumSuccessfulWorkCount x.length + iteratedGroupWidth x.length 256 =
      canonicalAvailable x := by
    unfold minimumSuccessfulWorkCount canonicalAvailable
    omega
  rw [size, general_copier_fuel_at_canonical] at affine
  omega

theorem general_copier_fuel_from_minimum (x : List Bool) (available : Nat)
    (minimum : minimumSuccessfulWorkCount x.length ≤ available) :
    generalCopierFuel x available =
      generalCopierFuel x (minimumSuccessfulWorkCount x.length) +
        2 * (available - minimumSuccessfulWorkCount x.length) := by
  have affine := generalCopierFuel_affine_available x
    (minimumSuccessfulWorkCount x.length)
    (available - minimumSuccessfulWorkCount x.length) (Nat.le_refl _)
  simpa only [Nat.add_sub_of_le minimum] using affine

theorem general_copier_fuel_le_canonical_plus_capacity (x : List Bool) (available : Nat)
    (minimum : minimumSuccessfulWorkCount x.length ≤ available) :
    generalCopierFuel x available ≤ copierExplicitFuel x + 2 * available := by
  rw [general_copier_fuel_from_minimum x available minimum]
  have small := general_copier_minimum_fuel_le_canonical x
  omega

theorem general_copier_fuel_le_pow24_plus_capacity (x : List Bool) (available : Nat)
    (minimum : minimumSuccessfulWorkCount x.length ≤ available) :
    generalCopierFuel x available ≤ 2 ^ (24 * x.length + 45) + 2 * available := by
  exact (general_copier_fuel_le_canonical_plus_capacity x available minimum).trans
    (Nat.add_le_add_right (copierExplicitFuel_le_pow24 x) (2 * available))

end PakFixedPolyomino.PakCopierGeneralFuelEnvelope
