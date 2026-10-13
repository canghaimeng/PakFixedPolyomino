import PakFixedPolyomino.PakCopierRawRoundFuel

/-! Eight literal doubling rounds consume 255*n actual work cells. The
exact old phase cost remains valid without reserving a second terminal
block of 256*n cells. The markR and remaining buffer stay at their actual
positions. -/
namespace PakFixedPolyomino.PakCopierRawEightRoundFuel
open MStarCopierExecution MStarCopierMicrocode
open PakCopierReserveLowerBound PakOuterFrontNumericBound PakCopierRawRoundFuel

theorem run_raw_eight_doublings (n available : Nat) (positive : 0 < n)
    (room : 255 * n ≤ available)
    (external source : List MStarCopierMicrocode.ConcreteTape) :
    run (copierEightRoundFuel n)
      (rawRoundStage (0 : Fin 8) 0 n available external source) =
      rawGroupBlock source (256 * n) (available - 255 * n) external := by
  let a1 := available - n
  let a2 := a1 - 2 * n
  let a3 := a2 - 4 * n
  let a4 := a3 - 8 * n
  let a5 := a4 - 16 * n
  let a6 := a5 - 32 * n
  let a7 := a6 - 64 * n
  have h1 : run (copierDoubleRoundFuel n)
      (rawRoundStage (0 : Fin 8) 0 n available external source) =
      rawRoundStage (1 : Fin 8) 0 (2 * n) a1 external source := by
    simpa [a1, nextRound, show 2 * n = 2 * n by ring] using
      run_raw_double_next (0 : Fin 8) n available (by omega)
        (by decide) external source (by omega)
  have h2 : run (copierDoubleRoundFuel (2 * n))
      (rawRoundStage (1 : Fin 8) 0 (2 * n) a1 external source) =
      rawRoundStage (2 : Fin 8) 0 (4 * n) a2 external source := by
    simpa [a2, nextRound, show 2 * (2 * n) = 4 * n by ring] using
      run_raw_double_next (1 : Fin 8) (2 * n) a1 (by omega)
        (by decide) external source (by dsimp [a1]; omega)
  have h3 : run (copierDoubleRoundFuel (4 * n))
      (rawRoundStage (2 : Fin 8) 0 (4 * n) a2 external source) =
      rawRoundStage (3 : Fin 8) 0 (8 * n) a3 external source := by
    simpa [a3, nextRound, show 2 * (4 * n) = 8 * n by ring] using
      run_raw_double_next (2 : Fin 8) (4 * n) a2 (by omega)
        (by decide) external source (by dsimp [a2, a1]; omega)
  have h4 : run (copierDoubleRoundFuel (8 * n))
      (rawRoundStage (3 : Fin 8) 0 (8 * n) a3 external source) =
      rawRoundStage (4 : Fin 8) 0 (16 * n) a4 external source := by
    simpa [a4, nextRound, show 2 * (8 * n) = 16 * n by ring] using
      run_raw_double_next (3 : Fin 8) (8 * n) a3 (by omega)
        (by decide) external source (by dsimp [a3, a2, a1]; omega)
  have h5 : run (copierDoubleRoundFuel (16 * n))
      (rawRoundStage (4 : Fin 8) 0 (16 * n) a4 external source) =
      rawRoundStage (5 : Fin 8) 0 (32 * n) a5 external source := by
    simpa [a5, nextRound, show 2 * (16 * n) = 32 * n by ring] using
      run_raw_double_next (4 : Fin 8) (16 * n) a4 (by omega)
        (by decide) external source (by dsimp [a4, a3, a2, a1]; omega)
  have h6 : run (copierDoubleRoundFuel (32 * n))
      (rawRoundStage (5 : Fin 8) 0 (32 * n) a5 external source) =
      rawRoundStage (6 : Fin 8) 0 (64 * n) a6 external source := by
    simpa [a6, nextRound, show 2 * (32 * n) = 64 * n by ring] using
      run_raw_double_next (5 : Fin 8) (32 * n) a5 (by omega)
        (by decide) external source (by dsimp [a5, a4, a3, a2, a1]; omega)
  have h7 : run (copierDoubleRoundFuel (64 * n))
      (rawRoundStage (6 : Fin 8) 0 (64 * n) a6 external source) =
      rawRoundStage (7 : Fin 8) 0 (128 * n) a7 external source := by
    simpa [a7, nextRound, show 2 * (64 * n) = 128 * n by ring] using
      run_raw_double_next (6 : Fin 8) (64 * n) a6 (by omega)
        (by decide) external source (by dsimp [a6, a5, a4, a3, a2, a1]; omega)
  have last : run (copierDoubleRoundFuel (128 * n))
      (rawRoundStage (7 : Fin 8) 0 (128 * n) a7 external source) =
      rawGroupBlock source (256 * n) (available - 255 * n) external := by
    have remaining : a7 - 128 * n = available - 255 * n := by
      dsimp [a7, a6, a5, a4, a3, a2, a1]
      omega
    simpa [remaining, show 2 * (128 * n) = 256 * n by ring] using
      run_raw_double_final (7 : Fin 8) (128 * n) a7 (by omega)
        (by decide) external source (by
          dsimp [a7, a6, a5, a4, a3, a2, a1]
          omega)
  unfold copierEightRoundFuel
  rw [run_add, h1, run_add, h2, run_add, h3, run_add, h4,
    run_add, h5, run_add, h6, run_add, h7, last]

end PakFixedPolyomino.PakCopierRawEightRoundFuel
