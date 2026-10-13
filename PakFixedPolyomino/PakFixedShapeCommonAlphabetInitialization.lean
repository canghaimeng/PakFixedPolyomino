import PakFixedPolyomino.PakFixedShapeOccupancyInitialization
import PakFixedPolyomino.PakFixedShapeFeedbackLeafEquivalence
import PakFixedPolyomino.StandardMachineAlphabetLeafTransport

/-! One fixed common-alphabet initializer and physical feedback machine.
The initializer's entire output tape is the original empty-occupancy state;
alphabet relabeling preserves every raw feedback slot and accepting leaf. -/
namespace PakFixedPolyomino.PakFixedShapeCommonAlphabetInitialization
noncomputable section
open StandardNondeterministicMachine StandardBitTime
open PakFixedShapeFlaggedPreparation (state)

structure Implementation where
  states : Nat
  alphabet : Nat
  machine : DeterministicMachine states alphabet
  exponent : Polynomial Nat

theorem exists_implementation : ∃ d : Implementation,
    ComputesWithin d.machine PakFixedShapeOccupancyInitialization.initialized
      (fun n => 2^d.exponent.eval n) := by
  obtain ⟨ns,nt,M,e,h⟩ := PakFixedShapeOccupancyInitialization.initialization_compiled
  exact ⟨⟨ns,nt,M,e⟩,h⟩

def implementation : Implementation := Classical.choose exists_implementation
theorem implementation_computes :
    ComputesWithin implementation.machine PakFixedShapeOccupancyInitialization.initialized
      (fun n => 2^implementation.exponent.eval n) := Classical.choose_spec exists_implementation

def feedbackAlphabet := PakFixedShapeNondeterministicPhases.roundAlphabet+
  PakFixedShapeNondeterministicPhases.extraAlphabet+3
def commonAlphabet := feedbackAlphabet+implementation.alphabet+3
def initializer := StandardMachineNondeterministicCommonAlphabet.right
  (ntA:=feedbackAlphabet) implementation.machine
def feedback := StandardMachineNondeterministicCommonAlphabet.left
  (ntB:=implementation.alphabet) PakFixedShapeFeedbackEncoding.machine PakFixedShapeFeedbackEncoding.positive
def feedbackMap := StandardMachineNondeterministicCommonAlphabet.leftMap
  (ntB:=implementation.alphabet) PakFixedShapeFeedbackEncoding.machine PakFixedShapeFeedbackEncoding.positive

theorem codes : feedback.blank=initializer.blank ∧ feedback.zero=initializer.zero ∧
    feedback.one=initializer.one :=
  StandardMachineNondeterministicCommonAlphabet.same_codes
    PakFixedShapeFeedbackEncoding.machine implementation.machine PakFixedShapeFeedbackEncoding.positive

theorem initialized_eq_state (side : List Bool) :
    PakFixedShapeOccupancyInitialization.initialized side=state side ∅ := by
  simp only [PakFixedShapeOccupancyInitialization.initialized,state,
    PakFixedShapeOccupancyInitialization.empty_mask,StandardBitSquareOccupancyAllocation.cells,pow_two]

theorem initializer_computes : ComputesWithin initializer (fun side => state side ∅)
    (fun n => 2^implementation.exponent.eval n) := by
  have h := StandardMachineNondeterministicCommonAlphabet.right_computes
    (ntA:=feedbackAlphabet) implementation.machine _ _ implementation_computes
  have he : PakFixedShapeOccupancyInitialization.initialized=(fun side => state side ∅) :=
    funext initialized_eq_state
  rw [he] at h
  exact h

theorem initializer_prefix_bound (side : List Bool) :
    RunsAtMost initializer side (2^implementation.exponent.eval side.length) :=
  (ComputesWithin.actual_bounds initializer _ _ initializer_computes side).1

theorem actual_accepted_restart (side : List Bool) (slots : List (Fin 1))
    (out : Configuration implementation.states commonAlphabet)
    (hr : run initializer slots (initial initializer side)=some out) (ha : out.state=initializer.accept) :
    PakFixedShapeFeedbackComponents.restart feedback out=initial feedback (state side ∅) := by
  have he := (StandardMachineDeterministicDuration.accepted_run_unique initializer _ _
    initializer_computes side slots out hr ha).2
  obtain ⟨hb,hz,ho⟩ := codes
  apply PakFixedShapeFeedbackComponents.restart_clean feedback initializer hb hz ho
  · exact congrArg (fun c : Configuration implementation.states commonAlphabet => c.head) he
  · exact congrArg (fun c : Configuration implementation.states commonAlphabet => c.tape) he

def feedbackLeafEquiv (raw : List Bool) :
    AcceptingLeaf feedback raw ≃ AcceptingLeaf PakFixedShapeFeedbackEncoding.machine raw :=
  StandardMachineAlphabetLeafTransport.leafEquiv PakFixedShapeFeedbackEncoding.machine feedbackMap raw

theorem squareCount_eq_feedbackLeafCard (side : List Bool) :
    PakFixedWeightedShapeFamily.squareCount (PakFixedWeightedStandardBinaryCount.value side)=
      Nat.card (AcceptingLeaf feedback (state side ∅)) :=
  (PakFixedShapeFeedbackLeafEquivalence.squareCount_eq_leafCard side).trans
    (Nat.card_congr (feedbackLeafEquiv (state side ∅))).symm

theorem feedback_prefix_bound (raw : List Bool) (bound : Nat)
    (h : RunsAtMost PakFixedShapeFeedbackEncoding.machine raw bound) : RunsAtMost feedback raw bound :=
  StandardMachineAlphabetLeafTransport.runsAtMost PakFixedShapeFeedbackEncoding.machine feedbackMap raw bound h

end
end PakFixedPolyomino.PakFixedShapeCommonAlphabetInitialization
