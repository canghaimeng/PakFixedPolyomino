import PakFixedPolyomino.PakGeneralCapacityOuterFrontEnvelope
import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerPhysicalCapacityCounts

/-! A concrete physical square-time region for the actual standard-machine
input. Start/parser/copier arrows and the complete qStart suffix fit together
at every actual minimum-capable capacity below one sixteenth of the side.
This does not assert an ALLouter inverse or full-frame counting census. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginScannerSquareFrontFuel
noncomputable section
open ULogTernaryGeneratedMarginScanner (input states)
open ULogTernaryGeneratedMarginScannerPhysicalFuel
open ULogTernaryGeneratedMarginScannerPhysicalCapacityCounts
open PakGeneralCapacityOuterFrontEnvelope PakSlotOneScannerMultiplicity
open PakGeneralCapacityInitialWindow PakGeneralCapacityParserCopierFront
open PakGeneralCapacityOuterFrontStandard PakOuterFrontQuantitative
open PakCopierReserveLowerBound PakULogGeneralCapacityBootstrap
open ULogConcreteMicroTimeCounts ULogCompiler
open StandardNondeterministicMachine (Machine RunsAtMost acceptingCount)
variable {ns nt : Nat}

theorem sixteen_suffix_fuel_lt_radius_nine (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) :
    16 * totalPhysicalFuelBound M p x < (PakOuterULogBridge.copiedCoreRadius (input M p x)) ^ 9 := by
  let R := PakOuterULogBridge.copiedCoreRadius (input M p x)
  have large : 256 ≤ R := PakOuterULogBridge.copiedCoreRadius_ge_256 _
  have boot := bootstrap_fuel_lt_copied_pow_eight M p x
  have body := physical_fuel_lt_copied_pow_eight M p x
  have sum : totalPhysicalFuelBound M p x < 2 * R ^ 8 := by
    unfold totalPhysicalFuelBound
    change bootstrapFuel M p x < R ^ 8 at boot
    change physicalFuelBound M p x < R ^ 8 at body
    omega
  calc
    16 * totalPhysicalFuelBound M p x < 32 * R ^ 8 := by omega
    _ ≤ R * R ^ 8 := Nat.mul_le_mul_right _ (by omega : 32 ≤ R)
    _ = R ^ 9 := by rw [show 9 = 8 + 1 by decide, pow_succ]; ring

theorem radius_nine_le_side (y : ConcretePakSide.Word) :
    (PakOuterULogBridge.copiedCoreRadius y) ^ 9 ≤ ConcretePakSide.sideValue y := by
  have same : (PakOuterULogBridge.copiedCoreRadius y) ^ 9 =
      2 ^ ConcretePakSide.paddingLength y.length := by
    unfold PakOuterULogBridge.copiedCoreRadius MStarParserCopySpec.timeExponent
    rw [← pow_mul]
    congr 1
    unfold ConcretePakSide.paddingLength
    ring
  rw [same]
  exact Nat.ge_two_pow_of_testBit (PakSideScanner.sideValue_padding_testBit y)

theorem sixteen_suffix_fuel_le_side (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) :
    16 * totalPhysicalFuelBound M p x ≤ ConcretePakSide.sideValue (input M p x) :=
  (sixteen_suffix_fuel_lt_radius_nine M p x).le.trans (radius_nine_le_side _)

def residualSquareCutoff (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (available : Nat) : Nat :=
  ConcretePakSide.sideValue (input M p x) - startFrontFuel (input M p x) available - 4

theorem low_capacity_square_slack (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (available : Nat)
    (minimum : minimumSuccessfulWorkCount (input M p x).length ≤ available)
    (low : 16 * available ≤ ConcretePakSide.sideValue (input M p x)) :
    startFrontFuel (input M p x) available + totalPhysicalFuelBound M p x + 4 ≤
      ConcretePakSide.sideValue (input M p x) := by
  have front := start_front_fuel_le_pow47 (input M p x) available minimum
  have constant := sixteen_front_constant_le_side (input M p x)
  have suffix := sixteen_suffix_fuel_le_side M p x
  have positive : 1 ≤ 2 ^ (24 * (input M p x).length + 47) := Nat.one_le_two_pow
  omega

theorem low_capacity_suffix_fuel_le_cutoff (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (available : Nat)
    (minimum : minimumSuccessfulWorkCount (input M p x).length ≤ available)
    (low : 16 * available ≤ ConcretePakSide.sideValue (input M p x)) :
    totalPhysicalFuelBound M p x ≤ residualSquareCutoff M p x available := by
  have slack := low_capacity_square_slack M p x available minimum low
  unfold residualSquareCutoff
  omega

theorem low_capacity_qStart_count (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length))
    (cap : ScannerCapacity (input M p x))
    (minimum : minimumSuccessfulWorkCount (input M p x).length ≤ cap.val)
    (low : 16 * cap.val ≤ ConcretePakSide.sideValue (input M p x)) :
    acceptingMicroPaths (residualSquareCutoff M p x cap.val)
      (.running ULogControl.qStart (generalCapacityCoreZipper (input M p x)
        (actualFinalCapacity (input M p x).length cap.val))) =
      if ULogTernaryGeneratedMarginSourceClock.reserve nt p x + 1 + (states M p - 1) + 4 ≤
          actualFinalCapacity (input M p x).length cap.val
      then acceptingCount M x (2 ^ p.eval x.length) else 0 :=
  all_physical_capacity_time_count M p x ht _ _
    (low_capacity_suffix_fuel_le_cutoff M p x cap.val minimum low)

theorem actual_start_front_with_source_slack (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (cap : ScannerCapacity (input M p x))
    (minimum : minimumSuccessfulWorkCount (input M p x).length ≤ cap.val)
    (low : 16 * cap.val ≤ ConcretePakSide.sideValue (input M p x)) :
    ∃ d, CapacitySideCopierRealize (input M p x) cap minimum
        (.groupReady (rawGeneralCapacityGroupZipper (input M p x)
          (actualFinalCapacity (input M p x).length cap.val)
          (capacityCopierJunk (input M p x)) (capacityHashTail (input M p x) cap))) d ∧
      OuterReachesAtMost (startFrontFuel (input M p x) cap.val)
        (capacityEncodedStartConfig (input M p x) cap) d ∧
      totalPhysicalFuelBound M p x ≤ residualSquareCutoff M p x cap.val := by
  rcases actual_start_front_bounded (input M p x) cap minimum with ⟨d, realized, executed⟩
  exact ⟨d, realized, executed, low_capacity_suffix_fuel_le_cutoff M p x cap.val minimum low⟩

end
end PakFixedPolyomino.ULogTernaryGeneratedMarginScannerSquareFrontFuel
