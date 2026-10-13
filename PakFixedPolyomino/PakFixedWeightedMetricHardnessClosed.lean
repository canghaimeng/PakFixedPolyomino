import PakFixedPolyomino.StandardBitVariableDivideLoop
import PakFixedPolyomino.PakFixedWeightedMetricHardnessAssembly

/-! Closed polynomial BIT-time metric hardness of the ORIGINAL fixed finite
connected translation-only shape family on the unmodified square and EVERY
usual-value binary side word. The actual ordinary division compiler supplies
the assembly's final premise internally. Source machine normalization, path
counts, full-frame/capacity/time identities and both actual bit transducers
are internally proved. Target ND membership remains a separate obligation. -/
namespace PakFixedPolyomino.PakFixedWeightedMetricHardnessClosed
open StandardBitTime
open StandardNondeterministicMachine (Machine)
open PakFixedWeightedStandardBinaryCount (binarySquareCount)
open PakFixedWeightedOracleLengthGuard (guardedPostprocessor)

theorem division_polyBitTime : PolyBitTime PakGuardedReadoutBitAssembly.divideBits :=
  StandardBitVariableDivideLoop.divide_polyBitTime

theorem postprocessor_polyBitTime {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (guardedPostprocessor M p) :=
  PakGuardedReadoutBitAssembly.postprocessor_polyBitTime M p division_polyBitTime

theorem source_reduces (f : List Bool → Nat)
    (hf : StandardNondeterministicMachine.SharpEXP f) :
    StandardBitMetric.Reduces f binarySquareCount :=
  PakFixedWeightedMetricHardnessAssembly.source_reduces f hf division_polyBitTime

theorem metric_hardness : StandardBitMetric.HardForSharpEXP binarySquareCount :=
  PakFixedWeightedMetricHardnessAssembly.metric_hardness division_polyBitTime

theorem fixed_shape_metric_hardness_spec :
    PakFixedWeightedRegisterInventory.tileFamily.Nonempty ∧
    (∀ P ∈ PakFixedWeightedRegisterInventory.tileFamily,P.Nonempty ∧ FourConnected P) ∧
    StandardBitMetric.HardForSharpEXP binarySquareCount ∧
    (∀ ns nt (M : Machine ns nt 2) p,
      PolyBitTime (PakFixedPitchBinaryInstance.instanceBits M p) ∧
      PolyBitTime (guardedPostprocessor M p) ∧
      ∀ raw,(guardedPostprocessor M p raw).length≤raw.length) :=
  ⟨PakFixedWeightedShapeFamily.tile_family_nonempty,
    PakFixedWeightedRegisterInventory.tile_family_members,metric_hardness,
    fun _ _ M p => ⟨PakLiteralSideBitTimeClosed.instanceBits_polyBitTime M p,
      postprocessor_polyBitTime M p,PakGuardedReadoutStorageBounds.total_postprocessor_length M p⟩⟩

end PakFixedPolyomino.PakFixedWeightedMetricHardnessClosed
