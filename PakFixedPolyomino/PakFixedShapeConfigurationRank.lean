import PakFixedPolyomino.StandardMachineCleanWordReadback
import PakFixedPolyomino.PakFixedShapeNondeterministicPhases
import PakFixedPolyomino.PakFixedShapeOccupancyRank

/-! The feedback rank is a proof function of an actual preparation-entry
configuration. Clean-tape injectivity removes any dependence on choosing a
placement history. It is never inspected by the finite machine's rule. -/
namespace PakFixedPolyomino.PakFixedShapeConfigurationRank
noncomputable section
open StandardNondeterministicMachine
open PakFixedShapeNondeterministicPhases (preparation roundAlphabet extraAlphabet prepareMachine)
open PakFixedShapeFlaggedPreparation (state)
open PakFixedShapeChoiceWords (Done)
open PakFixedWeightedStandardBinaryCount (value)

def rank (c : Configuration preparation.states (roundAlphabet+extraAlphabet+3)) : Nat :=
  PakFixedShapeOccupancyRank.rank (StandardMachineCleanWordReadback.word prepareMachine c.tape)
def Entry (side : List Bool) (c : Configuration preparation.states (roundAlphabet+extraAlphabet+3)) : Prop :=
  ∃ done : Done,c=initial prepareMachine (state side done)

theorem rank_initial (raw : List Bool) : rank (initial prepareMachine raw)=PakFixedShapeOccupancyRank.rank raw := by
  exact congrArg PakFixedShapeOccupancyRank.rank (StandardMachineCleanWordReadback.word_inputTape prepareMachine raw)

theorem entry_rank_bound (side : List Bool) (c : Configuration preparation.states (roundAlphabet+extraAlphabet+3))
    (hc : Entry side c) : rank c≤(value side)^2 := by
  obtain ⟨done,rfl⟩ := hc
  exact (rank_initial (state side done)).trans_le
    (PakFixedShapeOccupancyRank.rank_state_bound side done)

theorem step_decreases (side : List Bool) (done : Done) (i : Fin PakFixedShapeFiniteLabelRound.L) (out : List Bool)
    (hr : PakFixedShapeFlaggedChoiceWords.step i (state side done)=some out) :
    rank (initial prepareMachine out)<rank (initial prepareMachine (state side done)) := by
  rw [rank_initial,rank_initial]
  exact PakFixedShapeOccupancyRank.step_decreases side done i out hr
end
end PakFixedPolyomino.PakFixedShapeConfigurationRank
