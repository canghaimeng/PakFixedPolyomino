import PakFixedPolyomino.PakFixedWeightedMetricHardnessClosed
import PakFixedPolyomino.PakFixedShapeExactCountingModel

/-! Closed standard BIT-metric hardness in the literal translation-square
counting model. Membership remains the physical initializer-join obligation. -/
namespace PakFixedPolyomino.PakFixedShapeExactMetricHardness
open PakFixedShapeExactCountingModel

theorem exact_metric_hardness :
    StandardBitMetric.HardForSharpEXP
      (binaryTranslationSquareCount PakFixedWeightedRegisterInventory.tileFamily) := by
  rw [fixed_binary_count_function]
  exact PakFixedWeightedMetricHardnessClosed.metric_hardness

theorem fixed_original_metric_hardness_spec :
    PakFixedWeightedRegisterInventory.tileFamily.Nonempty ∧
    (∀ P ∈ PakFixedWeightedRegisterInventory.tileFamily,P.Nonempty ∧ FourConnected P) ∧
    StandardBitMetric.HardForSharpEXP
      (binaryTranslationSquareCount PakFixedWeightedRegisterInventory.tileFamily) :=
  ⟨PakFixedWeightedShapeFamily.tile_family_nonempty,
    PakFixedWeightedRegisterInventory.tile_family_members,exact_metric_hardness⟩

end PakFixedPolyomino.PakFixedShapeExactMetricHardness
