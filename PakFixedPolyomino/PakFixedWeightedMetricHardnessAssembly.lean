import PakFixedPolyomino.PakGuardedReadoutBitAssembly
import PakFixedPolyomino.PakLiteralSideBitTimeClosed

/-! Standard #EXP metric hardness for the ORIGINAL fixed connected shape-set
square count, conditional solely on the explicit ordinary variable-division
bit compiler. The source class is the full standard finite-branching machine
class; effective binary normalization, ALL-frame physical counting, capacity
and time invariance, input transducer and exact every-raw postprocessor are
supplied internally. The division premise remains for the disjoint backend
to discharge. This intermediate theorem asserts no target ND membership. -/
namespace PakFixedPolyomino.PakFixedWeightedMetricHardnessAssembly
noncomputable section
open Computability StandardBitTime StandardBitMetric
open StandardNondeterministicMachine (SharpEXP)
open PakFixedWeightedStandardBinaryCount (binarySquareCount)
open PakFixedWeightedOracleLengthGuard (guardedPostprocessor oracleAnswer)
open PakFixedPitchBinaryInstance (instanceBits instanceBits_eq_encode)

theorem source_reduces (f : List Bool → Nat) (hf : StandardNondeterministicMachine.SharpEXP f)
    (hd : PolyBitTime PakGuardedReadoutBitAssembly.divideBits) :
    StandardBitMetric.Reduces f binarySquareCount := by
  obtain ⟨ns,nt,M,p,hcorrect⟩ :=
    PakFixedWeightedOracleLengthGuard.standard_sharp_exp_guarded_readout f hf
  refine ⟨{
    instanceMap := instanceBits M p
    postprocessor := guardedPostprocessor M p
    instance_polytime := PakLiteralSideBitTimeClosed.instanceBits_polyBitTime M p
    postprocessor_polytime := PakGuardedReadoutBitAssembly.postprocessor_polyBitTime M p hd
    correct := ?_ }⟩
  intro x
  rw [instanceBits_eq_encode]
  exact hcorrect x

theorem metric_hardness (hd : PolyBitTime PakGuardedReadoutBitAssembly.divideBits) :
    StandardBitMetric.HardForSharpEXP binarySquareCount := fun f hf => source_reduces f hf hd

theorem metric_hardness_spec (hd : PolyBitTime PakGuardedReadoutBitAssembly.divideBits) :
    StandardBitMetric.HardForSharpEXP binarySquareCount ∧
    (∀ f,StandardNondeterministicMachine.SharpEXP f → StandardBitMetric.Reduces f binarySquareCount) :=
  ⟨metric_hardness hd,fun f hf => source_reduces f hf hd⟩

end
end PakFixedPolyomino.PakFixedWeightedMetricHardnessAssembly
