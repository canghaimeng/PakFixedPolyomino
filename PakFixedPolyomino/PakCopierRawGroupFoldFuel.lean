import PakFixedPolyomino.PakCopierRawEightRoundFuel
import PakFixedPolyomino.PakCopierGeneralGroupPayloadFuel

/-! Exact chronological group-fold cost at actual capacity. Each group
consumes 255 times its incoming unary width. The actual remainder is
carried to the next group, without reserving a canonical terminal block. -/
namespace PakFixedPolyomino.PakCopierRawGroupFoldFuel
open MStarCopierExecution MStarCopierMicrocode
open PakCopierReserveLowerBound PakOuterFrontNumericBound
open PakCopierRawEightRoundFuel PakCopierGeneralGroupPayloadFuel

theorem run_raw_group_fold (bits : List Bool) (done groups n available : Nat)
    (junk external : List MStarCopierMicrocode.ConcreteTape)
    (positive : 0 < n) (room : groupMinimumConsumed groups n ≤ available) :
    run (copierGroupFoldFuel bits done groups n)
      (rawGroupedState bits done groups n available junk external) =
      rawGroupedState bits (done + groups) 0 (iteratedGroupWidth groups n)
        (available - groupMinimumConsumed groups n) junk external := by
  induction groups generalizing done n available with
  | zero => simp [copierGroupFoldFuel, groupMinimumConsumed, iteratedGroupWidth]
  | succ groups ih =>
      have firstRoom : 255 * n ≤ available := by
        simp only [groupMinimumConsumed] at room
        omega
      have restRoom : groupMinimumConsumed groups (256 * n) ≤ available - 255 * n := by
        simp only [groupMinimumConsumed] at room
        omega
      have remaining : available - 255 * n - groupMinimumConsumed groups (256 * n) =
          available - groupMinimumConsumed (groups + 1) n := by
        simp only [groupMinimumConsumed]
        omega
      rw [copierGroupFoldFuel, run_add,
        run_raw_restart_next_group bits done groups n available junk external positive,
        run_add, run_raw_eight_doublings n available positive firstRoom external
          (groupSource bits (done + 1) groups junk)]
      have rest := ih (done + 1) (256 * n) (available - 255 * n) (by omega) restRoom
      simpa only [rawGroupedState, iteratedGroupWidth, remaining, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using rest

end PakFixedPolyomino.PakCopierRawGroupFoldFuel
