import PakFixedPolyomino.PakCopierRawGroupFoldFuel
import PakFixedPolyomino.PakCopierRawCounterFuel

/-! Literal complete copier fuel at actual minimum-capable workspace.
Only the final pair of buffer scans depends on unused actual capacity. -/
namespace PakFixedPolyomino.PakCopierGeneralCompleteFuel
open MStarCopierExecution MStarCopierMicrocode
open PakCopierReserveLowerBound PakOuterFrontNumericBound
open PakCopierRawEightRoundFuel PakCopierRawGroupFoldFuel
open PakCopierRawCounterFuel PakCopierGeneralGroupPayloadFuel

def generalCopierFuel (x : List Bool) (available : Nat) : Nat :=
  let n := iteratedGroupWidth x.length 256
  let afterGroups := available - 255 - groupMinimumConsumed x.length 256
  4 + (copierEightRoundFuel 1 +
    (copierGroupFoldFuel x.reverse 0 x.length 256 +
      (rawCounterPayloadFuel x n +
        generalPayloadFuel x [] 0 n (afterGroups - 1))))

theorem run_raw_copier_complete (x : List Bool) (available : Nat)
    (junk external : List MStarCopierMicrocode.ConcreteTape)
    (minimum : minimumSuccessfulWorkCount x.length ≤ available) :
    run (generalCopierFuel x available) (rawCopierSeed x available junk external) =
      .groupReady (rawGeneralCapacityGroupZipper x
        (actualFinalCapacity x.length available) junk external) := by
  let n := iteratedGroupWidth x.length 256
  let gmin := groupMinimumConsumed x.length 256
  let afterGroups := available - 255 - gmin
  let sourceTail := List.replicate x.length MStarParserMicrocode.lenDone ++
    MStarParserMicrocode.sepPad :: junk
  have identity := groupMinimumConsumed_add_width x.length 256
  have positive : 0 < n := iteratedGroupWidth_pos x.length 256 (by omega)
  have baseRoom : 255 ≤ available := by
    unfold minimumSuccessfulWorkCount at minimum
    omega
  have groupRoom : gmin ≤ available - 255 := by
    dsimp [gmin]
    unfold minimumSuccessfulWorkCount at minimum
    omega
  have payloadRoom : x.length + 1 ≤ afterGroups := by
    dsimp [afterGroups, gmin]
    unfold minimumSuccessfulWorkCount at minimum
    omega
  have after : (afterGroups - 1) + 1 = afterGroups := by omega
  have base : run (copierEightRoundFuel 1)
      (rawRoundStage (0 : Fin 8) 0 1 available external
        (groupSource x.reverse 0 x.length junk)) =
      rawGroupedState x.reverse 0 x.length 256 (available - 255) junk external := by
    simpa [rawGroupedState] using run_raw_eight_doublings 1 available (by omega)
      (by simpa using baseRoom) external (groupSource x.reverse 0 x.length junk)
  have groups : run (copierGroupFoldFuel x.reverse 0 x.length 256)
      (rawGroupedState x.reverse 0 x.length 256 (available - 255) junk external) =
      rawGroupedState x.reverse x.length 0 n afterGroups junk external := by
    simpa [n, afterGroups, gmin] using run_raw_group_fold x.reverse 0 x.length 256
      (available - 255) junk external (by omega) groupRoom
  have counter : run (rawCounterPayloadFuel x n)
      (rawGroupedState x.reverse x.length 0 n afterGroups junk external) =
      rawPayloadLoop [] 0 n x (afterGroups - 1) sourceTail external := by
    simpa only [after, sourceTail] using run_raw_counter_payload x n (afterGroups - 1)
      positive junk external
  have capacity : afterGroups - 1 - x.length + 1 =
      actualFinalCapacity x.length available := by
    dsimp [afterGroups, gmin, actualFinalCapacity, consumedBeforeFinalBuffer,
      minimumSuccessfulWorkCount]
    unfold minimumSuccessfulWorkCount at minimum
    omega
  have payload := run_raw_payload_to_group_ready x [] 0 n (afterGroups - 1)
    sourceTail external (by omega)
  have payload' : run (generalPayloadFuel x [] 0 n (afterGroups - 1))
      (rawPayloadLoop [] 0 n x (afterGroups - 1) sourceTail external) =
      .groupReady (rawGeneralCapacityGroupZipper x
        (actualFinalCapacity x.length available) junk external) := by
    simpa [rawGeneralCapacityGroupZipper, n, sourceTail, capacity,
      List.append_assoc] using payload
  unfold generalCopierFuel
  change run (4 + (copierEightRoundFuel 1 +
      (copierGroupFoldFuel x.reverse 0 x.length 256 +
        (rawCounterPayloadFuel x n + generalPayloadFuel x [] 0 n (afterGroups - 1)))))
    (rawCopierSeed x available junk external) = _
  rw [run_add, run_raw_seed, run_add, base, run_add, groups,
    run_add, counter, payload']

theorem generalCopierFuel_affine_available (x : List Bool) (available slack : Nat)
    (minimum : minimumSuccessfulWorkCount x.length ≤ available) :
    generalCopierFuel x (available + slack) = generalCopierFuel x available + 2 * slack := by
  have identity := groupMinimumConsumed_add_width x.length 256
  have after : available + slack - 255 - groupMinimumConsumed x.length 256 - 1 =
      (available - 255 - groupMinimumConsumed x.length 256 - 1) + slack := by
    unfold minimumSuccessfulWorkCount at minimum
    omega
  have room : x.length ≤ available - 255 - groupMinimumConsumed x.length 256 - 1 := by
    unfold minimumSuccessfulWorkCount at minimum
    omega
  unfold generalCopierFuel
  dsimp only
  rw [after, generalPayloadFuel_affine_available x [] 0
    (iteratedGroupWidth x.length 256)
    (available - 255 - groupMinimumConsumed x.length 256 - 1) slack room]
  omega

end PakFixedPolyomino.PakCopierGeneralCompleteFuel
