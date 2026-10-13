import PakFixedPolyomino.PakFixedShapeFeedbackRuntime
import PakFixedPolyomino.StandardMachineDeterministicNondeterministicSequence
import PakFixedPolyomino.StandardMachineExponentialCountingClosure

/-! The actual physical initializer and feedback machine give a fixed standard
ND witness on every original binary side. All clocks and counts are internal. -/
namespace PakFixedPolyomino.PakFixedShapeStandardMembership
noncomputable section
open StandardNondeterministicMachine
open PakFixedShapeCommonAlphabetInitialization (initializer feedback implementation)
open PakFixedShapeFlaggedPreparation (state)
open PakFixedShapeNondeterministicTimeEnvelope (loopBudget totalBudget)
open PakFixedWeightedStandardBinaryCount (binarySquareCount)

theorem same_codes :
    StandardMachineDeterministicNondeterministicSequence.SameCodes initializer feedback := by
  obtain ⟨hb,hz,ho⟩ := PakFixedShapeCommonAlphabetInitialization.codes
  exact ⟨hb.symm,hz.symm,ho.symm⟩

def machine := StandardMachineDeterministicNondeterministicSequence.machine
  initializer feedback PakFixedShapeFeedbackEncoding.positive same_codes
def budget := totalBudget implementation.exponent

theorem all_prefix_bound (side : List Bool) :
    RunsAtMost machine side (budget side.length) := by
  exact StandardMachineDeterministicNondeterministicSequence.sequence_runsAtMost
    initializer feedback PakFixedShapeFeedbackEncoding.positive same_codes side
    (2^implementation.exponent.eval side.length) (loopBudget side.length)
    (PakFixedShapeCommonAlphabetInitialization.initializer_prefix_bound side)
    (StandardMachineDeterministicNondeterministicSequence.targetBound_of_runs
      initializer feedback same_codes (fun raw => state raw ∅)
      (fun n => 2^implementation.exponent.eval n)
      PakFixedShapeCommonAlphabetInitialization.initializer_computes side (loopBudget side.length)
      (PakFixedShapeFeedbackRuntime.common_prefix_bound side))

def leafEquiv (side : List Bool) :
    AcceptingLeaf feedback (state side ∅) ≃ AcceptingLeaf machine side :=
  StandardMachineDeterministicNondeterministicSequence.leafEquiv
    initializer feedback PakFixedShapeFeedbackEncoding.positive same_codes
    (fun raw => state raw ∅) (fun n => 2^implementation.exponent.eval n)
    PakFixedShapeCommonAlphabetInitialization.initializer_computes side

theorem binarySquareCount_eq_leafCard (side : List Bool) :
    binarySquareCount side=Nat.card (AcceptingLeaf machine side) :=
  (PakFixedShapeCommonAlphabetInitialization.squareCount_eq_feedbackLeafCard side).trans
    (Nat.card_congr (leafEquiv side))

theorem binarySquareCount_eq_finite_count (side : List Bool) :
    binarySquareCount side=acceptingCount machine side (budget side.length) :=
  (binarySquareCount_eq_leafCard side).trans
    ((Nat.card_congr (acceptingLeavesEquiv machine side (budget side.length)
      (all_prefix_bound side)).symm).trans Nat.card_eq_fintype_card)

theorem target_membership : SharpEXP binarySquareCount :=
  StandardMachineExponentialCountingClosure.sharpEXP_of_operational_counts
    machine binarySquareCount budget all_prefix_bound binarySquareCount_eq_finite_count
    PakFixedShapeFeedbackRuntime.total_budget_exponential

end
end PakFixedPolyomino.PakFixedShapeStandardMembership
