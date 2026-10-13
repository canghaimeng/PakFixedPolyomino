import PakFixedPolyomino.PakFixedShapeStandardMembership
import PakFixedPolyomino.PakFixedShapeExactMetricHardness

/-! One explicit fixed finite connected translation-only family, counting
exact tilings of the unmodified square under the original binary convention. -/
namespace PakFixedPolyomino.PakFixedShapeHeadline
noncomputable section
open PakFixedShapeExactCountingModel

def targetFamily : Finset Polyomino := PakFixedWeightedRegisterInventory.tileFamily
def targetCount : List Bool → Nat := binaryTranslationSquareCount targetFamily

theorem membership : StandardNondeterministicMachine.SharpEXP targetCount := by
  change StandardNondeterministicMachine.SharpEXP
    (binaryTranslationSquareCount PakFixedWeightedRegisterInventory.tileFamily)
  rw [fixed_binary_count_function]
  exact PakFixedShapeStandardMembership.target_membership

theorem metric_hardness : StandardBitMetric.HardForSharpEXP targetCount :=
  PakFixedShapeExactMetricHardness.exact_metric_hardness

theorem complete : StandardBitMetric.CompleteForSharpEXP targetCount :=
  ⟨membership,metric_hardness⟩

theorem fixed_family_complete_spec :
    targetFamily.Nonempty ∧
    (∀ P ∈ targetFamily,P.Nonempty ∧ FourConnected P) ∧
    StandardBitMetric.CompleteForSharpEXP targetCount :=
  ⟨PakFixedWeightedShapeFamily.tile_family_nonempty,
    PakFixedWeightedRegisterInventory.tile_family_members,complete⟩

theorem pak_headline : ∃ T : Finset Polyomino,
    T.Nonempty ∧ (∀ P ∈ T,P.Nonempty ∧ FourConnected P) ∧
    StandardBitMetric.CompleteForSharpEXP (binaryTranslationSquareCount T) :=
  ⟨targetFamily,fixed_family_complete_spec⟩

end
end PakFixedPolyomino.PakFixedShapeHeadline
