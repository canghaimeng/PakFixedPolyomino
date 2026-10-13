import PakFixedPolyomino.ULogConcreteTargetGrowthUnderflow

/-! Link the literal empty-boundary obstruction to its internally constructed
reachable transformed tape. This is one selected rewrite stage, not a global
scanner capacity threshold. -/
namespace PakFixedPolyomino.ULogConcreteTargetGrowthReachableUnderflow
open ULogAlphabet ULogProgram ULogBootstrapExecution ULogConcreteChoiceBarrier
open ULogConcreteTargetGrowthUnderflow

theorem reaches_penultimate (remaining done available : Nat)
    (hgt : available < remaining) (corridor : List Tape)
    (hsafe : TargetRewriteCorridorSafe corridor) (left : List Tape) :
    ∃ fuel, fuel ≤ fuelBound remaining done available corridor ∧
      ValidZeroRun fuel (start remaining done available corridor left)
        (reachedPenultimate remaining done available corridor left) ∧
      (∀ m, m < fuel →
        ¬ IsConcreteCycleStop (run m (start remaining done available corridor left))) ∧
      run fuel (start remaining done available corridor left) =
        reachedPenultimate remaining done available corridor left := by
  have hrem : 0 < remaining - available := by omega
  obtain ⟨a, ⟨ha, hgrows⟩⟩ :=
    stopFree_grows remaining done available hgt corridor hsafe left
  have hscan := stopFree_finalScan hrem (done + available) corridor hsafe
    (List.replicate available (ulogCore ULogAlphabet.codeZero) ++ left)
  have hall := hgrows.append hscan
  have hlen := scanPath_length hrem (done + available) corridor
  refine ⟨_, ?_, hall.valid, hall.stop_free, hall.valid.eq_run⟩
  rw [hlen]
  have hsum : remaining - available + (done + available) + corridor.length =
      remaining + done + corridor.length := by omega
  rw [hsum]
  set L := remaining + done + corridor.length
  have hsmall : a + L + 2 ≤ (2 * L + 7) * (available + 1) := by
    have : (2 * L + 7) * available + L + 2 ≤
        (2 * L + 7) * (available + 1) := by
      simp [Nat.mul_add]; omega
    omega
  have hlarge : (2 * L + 7) * (available + 1) ≤
      fuelBound remaining done available corridor := by
    unfold fuelBound
    exact Nat.mul_le_mul_right _ (by omega)
  exact hsmall.trans hlarge

theorem reachable_underflow_spec (remaining done available : Nat)
    (hgt : available < remaining) (corridor : List Tape)
    (hsafe : TargetRewriteCorridorSafe corridor) (left : List Tape) :
    (∃ fuel, fuel ≤ fuelBound remaining done available corridor ∧
      ValidZeroRun fuel (start remaining done available corridor left)
        (reachedPenultimate remaining done available corridor left) ∧
      (∀ m, m < fuel →
        ¬ IsConcreteCycleStop (run m (start remaining done available corridor left))) ∧
      run fuel (start remaining done available corridor left) =
        reachedPenultimate remaining done available corridor left) ∧
    (∃ fuel, fuel ≤ fuelBound remaining done available corridor ∧
      ValidZeroRun fuel (start remaining done available corridor left) .stuck ∧
      (∀ m, m < fuel →
        ¬ IsConcreteCycleStop (run m (start remaining done available corridor left))) ∧
      run fuel (start remaining done available corridor left) = .stuck) ∧
    oneStep (reachedPenultimate remaining done available corridor left) = .stuck ∧
    (∀ (labels : List (Fin 2)) (tape : MStarParserExecution.Zipper Tape),
      ConcreteMicroPath
        (start remaining done available corridor left) labels (.accepted tape) → False) :=
  ⟨reaches_penultimate remaining done available hgt corridor hsafe left,
    run_to_stuck remaining done available hgt corridor hsafe left,
    reachedPenultimate_oneStep remaining done available corridor left,
    no_accepting_path remaining done available hgt corridor hsafe left⟩

end PakFixedPolyomino.ULogConcreteTargetGrowthReachableUnderflow
