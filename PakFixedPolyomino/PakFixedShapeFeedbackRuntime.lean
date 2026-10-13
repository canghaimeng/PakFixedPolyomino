import PakFixedPolyomino.PakFixedShapeFeedbackCausalBounds
import PakFixedPolyomino.PakFixedShapeCommonAlphabetInitialization
import PakFixedPolyomino.StandardMachineNondeterministicFeedbackReachable

/-! Actual full feedback transition bounds on every original side input.
All five causal component premises and the nonempty initial entry are supplied
internally. Counts cover every raw accepting leaf, with no clock premise. -/
namespace PakFixedPolyomino.PakFixedShapeFeedbackRuntime
noncomputable section
open StandardNondeterministicMachine
open PakFixedShapeNondeterministicPhases
open PakFixedShapeFeedbackCausalBounds
open PakFixedShapeConfigurationRank (Entry rank entry_rank_bound)
open PakFixedShapeFlaggedPreparation (state)
open PakFixedShapeNondeterministicTimeEnvelope (cycleBudget loopBudget totalBudget)

theorem causal_premises (side : List Bool) :
    StandardMachineNondeterministicFeedbackReachable.CausalPremises
      prepareMachine roundMachine stripMachine (Entry side) rank (A side) (B side) (C side) where
  hP := preparation_bound side
  hH1 := first_strip_bound side
  hM := round_bound side
  hH2 := second_strip_bound side
  hret := return_entry_decreases side

theorem cycle_bound_eq (side : List Bool) :
    StandardMachineNondeterministicFeedback.cycleBound (A side) (B side) (C side)=cycleBudget side.length := by
  rw [PakFixedShapeNondeterministicTimeEnvelope.cycleBudget_eq]
  rfl

theorem all_prefix_bound (side : List Bool) :
    RunsAtMost PakFixedShapeFeedbackEncoding.machine (state side ∅) (loopBudget side.length) := by
  intro slots out hr
  have hi := initial_entry side
  have hk := entry_rank_bound side (initial prepareMachine (state side ∅)) hi
  have hrun := hr
  change run (StandardMachineNondeterministicFeedback.machine prepareMachine roundMachine stripMachine
    PakFixedShapeFeedbackEncoding.positive PakFixedShapeFeedbackEncoding.same_codes) slots
    (initial (StandardMachineNondeterministicFeedback.machine prepareMachine roundMachine stripMachine
      PakFixedShapeFeedbackEncoding.positive PakFixedShapeFeedbackEncoding.same_codes) (state side ∅))=some out at hrun
  rw [StandardMachineNondeterministicFeedback.initial_liftP prepareMachine roundMachine stripMachine
    PakFixedShapeFeedbackEncoding.positive PakFixedShapeFeedbackEncoding.same_codes (state side ∅)] at hrun
  have h := StandardMachineNondeterministicFeedbackReachable.prefix_from_P
    prepareMachine roundMachine stripMachine PakFixedShapeFeedbackEncoding.positive
    PakFixedShapeFeedbackEncoding.same_codes (Entry side) rank (A side) (B side) (C side)
    ((PakFixedWeightedStandardBinaryCount.value side)^2) (causal_premises side)
    (initial prepareMachine (state side ∅)) slots out hi hk hrun
  rw [cycle_bound_eq] at h
  exact h.trans (PakFixedShapeNondeterministicTimeEnvelope.rank_cycles_envelope side _ (le_refl _))

theorem common_prefix_bound (side : List Bool) :
    RunsAtMost PakFixedShapeCommonAlphabetInitialization.feedback (state side ∅) (loopBudget side.length) :=
  PakFixedShapeCommonAlphabetInitialization.feedback_prefix_bound _ _ (all_prefix_bound side)

theorem squareCount_eq_finite_count (side : List Bool) :
    PakFixedWeightedShapeFamily.squareCount (PakFixedWeightedStandardBinaryCount.value side)=
      acceptingCount PakFixedShapeFeedbackEncoding.machine (state side ∅) (loopBudget side.length) :=
  PakFixedShapeFeedbackLeafEquivalence.squareCount_eq_acceptingCount side _ (all_prefix_bound side)

theorem squareCount_eq_common_finite_count (side : List Bool) :
    PakFixedWeightedShapeFamily.squareCount (PakFixedWeightedStandardBinaryCount.value side)=
      acceptingCount PakFixedShapeCommonAlphabetInitialization.feedback (state side ∅) (loopBudget side.length) := by
  rw [PakFixedShapeCommonAlphabetInitialization.squareCount_eq_feedbackLeafCard]
  exact (Nat.card_congr (acceptingLeavesEquiv _ _ _ (common_prefix_bound side)).symm).trans
    Nat.card_eq_fintype_card

theorem total_budget_exponential : ∃ e : Polynomial Nat,∀ m,
    totalBudget PakFixedShapeCommonAlphabetInitialization.implementation.exponent m≤2^e.eval m :=
  PakFixedShapeNondeterministicTimeEnvelope.totalBudget_exponential _

end
end PakFixedPolyomino.PakFixedShapeFeedbackRuntime
