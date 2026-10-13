import PakFixedPolyomino.PakCopierReserveLowerBound
import PakFixedPolyomino.PakOuterFrontNumericBound

/-! Exact doubling-round costs for actual available workspace. Only the
cells genuinely consumed by the current unary pass are reserved; no
canonical retained second buffer or fixed terminal coordinate is imposed. -/
namespace PakFixedPolyomino.PakCopierRawRoundFuel
open MStarCopierExecution MStarCopierMicrocode
open PakCopierReserveLowerBound PakOuterFrontNumericBound

theorem raw_round_eq (r : Fin 8) (processed remaining available : Nat)
    (external source : List MStarCopierMicrocode.ConcreteTape) (room : remaining ≤ available) :
    rawRoundStage r processed remaining available external source =
      roundStage r processed remaining
        (List.replicate (available - remaining) (.core MStarConcreteAlphabet.work) ++
          rightEnd :: external) source := by
  have count : remaining + (available - remaining) = available := Nat.add_sub_of_le room
  have buffer :
      List.replicate available (.core MStarConcreteAlphabet.work) ++ rightEnd :: external =
        List.replicate remaining (.core MStarConcreteAlphabet.work) ++
          (List.replicate (available - remaining) (.core MStarConcreteAlphabet.work) ++
            rightEnd :: external) := by
    rw [← List.append_assoc, ← List.replicate_add, count]
  cases processed <;> cases remaining <;>
    simp only [rawRoundStage, roundStage, Nat.sub_zero, List.replicate_zero, List.nil_append,
      List.append_assoc, List.cons_append]
  all_goals rw [buffer]

theorem run_raw_process_all (r : Fin 8) (processed remaining available : Nat)
    (external source : List MStarCopierMicrocode.ConcreteTape) (room : remaining ≤ available) :
    run (copierProcessAllFuel processed remaining)
      (rawRoundStage r processed remaining available external source) =
      rawRoundStage r (processed + remaining) 0 (available - remaining) external source := by
  rw [raw_round_eq r processed remaining available external source room, run_process_all]
  simpa only [Nat.sub_zero] using
    (raw_round_eq r (processed + remaining) 0 (available - remaining) external source
      (Nat.zero_le _)).symm

def roundReturnFuel (n : Nat) : Nat := copierNormalizeEntryFuel n + (2 * n + 1)

theorem run_raw_round_return (r : Fin 8) (n available : Nat) (positive : 0 < n)
    (external source : List MStarCopierMicrocode.ConcreteTape) :
    run (roundReturnFuel n) (rawRoundStage r n 0 available external source) =
      roundCompleted r n
        (List.replicate available (.core MStarConcreteAlphabet.work) ++ rightEnd :: external)
        source := by
  rw [raw_round_eq r n 0 available external source (Nat.zero_le _)]
  simp only [Nat.sub_zero]
  rw [roundReturnFuel, run_add, run_normalizeStarted r n positive,
    run_add, run_normalizedAtMark, run_roundCompleted]

theorem run_raw_round_next (r : Fin 8) (n available : Nat) (positive : 0 < n)
    (next : r.val < 7) (external source : List MStarCopierMicrocode.ConcreteTape) :
    run (roundReturnFuel n) (rawRoundStage r n 0 available external source) =
      rawRoundStage (nextRound r next) 0 (2 * n) available external source := by
  rw [run_raw_round_return r n available positive external source]
  have two : 2 * n = (2 * n - 1) + 1 := by omega
  unfold roundCompleted
  rw [dif_pos next, two]
  simp [rawRoundStage, List.append_assoc]

theorem run_raw_round_final (r : Fin 8) (n available : Nat) (positive : 0 < n)
    (last : ¬ r.val < 7) (external source : List MStarCopierMicrocode.ConcreteTape) :
    run (roundReturnFuel n) (rawRoundStage r n 0 available external source) =
      rawGroupBlock source (2 * n) available external := by
  rw [run_raw_round_return r n available positive external source]
  simp [roundCompleted, last, rawGroupBlock, List.append_assoc]

theorem run_raw_double_next (r : Fin 8) (n available : Nat) (positive : 0 < n)
    (next : r.val < 7) (external source : List MStarCopierMicrocode.ConcreteTape) (room : n ≤ available) :
    run (copierDoubleRoundFuel n) (rawRoundStage r 0 n available external source) =
      rawRoundStage (nextRound r next) 0 (2 * n) (available - n) external source := by
  have fuel : copierDoubleRoundFuel n = copierProcessAllFuel 0 n + roundReturnFuel n := by
    simp [copierDoubleRoundFuel, roundReturnFuel, Nat.add_assoc]
  rw [fuel, run_add, run_raw_process_all r 0 n available external source room]
  simp only [Nat.zero_add]
  exact run_raw_round_next r n (available - n) positive next external source

theorem run_raw_double_final (r : Fin 8) (n available : Nat) (positive : 0 < n)
    (last : ¬ r.val < 7) (external source : List MStarCopierMicrocode.ConcreteTape) (room : n ≤ available) :
    run (copierDoubleRoundFuel n) (rawRoundStage r 0 n available external source) =
      rawGroupBlock source (2 * n) (available - n) external := by
  have fuel : copierDoubleRoundFuel n = copierProcessAllFuel 0 n + roundReturnFuel n := by
    simp [copierDoubleRoundFuel, roundReturnFuel, Nat.add_assoc]
  rw [fuel, run_add, run_raw_process_all r 0 n available external source room]
  simp only [Nat.zero_add]
  exact run_raw_round_final r n (available - n) positive last external source

end PakFixedPolyomino.PakCopierRawRoundFuel
