import PakFixedPolyomino.PakGeneralCapacityOuterFrontStandard
import PakFixedPolyomino.PakOuterFrontQuantitative
import PakFixedPolyomino.PakCopierGeneralFuelEnvelope

/-! Actual occupied outer arrows at every minimum-capable scanner workspace.
The bound is derived from the executed parser and whole copier microcode.
It is physical tape time, not a bit-time reduction certificate. -/
namespace PakFixedPolyomino.PakGeneralCapacityOuterFrontFuel
open MStarConcreteAlphabet
open PakGeneralCapacityInitialWindow PakGeneralCapacityParserCopierFront
open PakGeneralCapacityOuterFrontStandard PakSlotOneScannerMultiplicity
open PakParserOuterBridge PakOuterFrontQuantitative
open PakCopierReserveLowerBound PakCopierGeneralCompleteFuel PakCopierGeneralFuelEnvelope

def generalOuterFrontFuel (x : ConcretePakSide.Word) (available : Nat) : Nat :=
  PakOuterParserNumericSuffix.parserExplicitFuel x + 1 + generalCopierFuel x available

theorem capacity_parser_one_step (x : ConcretePakSide.Word) (cap : ScannerCapacity x) :
    ParserOuterOneStepSimulation zero one work (CapacitySideParserRealize x cap) := by
  intro r s c realized step
  rcases capacitySideParser_outerStepSimulation_atMostOne x cap r s c realized step with
    ⟨d, next, arrows, bound, executed⟩
  exact ⟨d, next, arrows, bound, executed⟩

theorem capacity_copier_one_step (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (minimum : minimumSuccessfulWorkCount x.length ≤ cap.val) :
    CopierOuterOneStepSimulation (CapacitySideCopierRealize x cap minimum) := by
  intro r s c realized step
  rcases capacitySideCopier_outerStepSimulation_atMostOne x cap minimum r s c realized step with
    ⟨d, next, arrows, bound, executed⟩
  exact ⟨d, next, arrows, bound, executed⟩

theorem actual_outer_front_bounded (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (minimum : minimumSuccessfulWorkCount x.length ≤ cap.val) :
    ∃ d, CapacitySideCopierRealize x cap minimum
        (.groupReady (rawGeneralCapacityGroupZipper x
          (actualFinalCapacity x.length cap.val) (capacityCopierJunk x) (capacityHashTail x cap))) d ∧
      OuterReachesAtMost (generalOuterFrontFuel x cap.val) (capacityEncodedParserConfig x cap) d := by
  rcases parserRun_outerAtMost zero one work (CapacitySideParserRealize x cap)
      (capacity_parser_one_step x cap) (PakOuterParserNumericSuffix.parserExplicitFuel x)
      (run_capacityParserInitial_explicitFuel x cap)
      (capacitySideParserRealize_initial x cap) with
    ⟨parserEnd, ready, parserRun⟩
  rcases capacityCopyReady_enters_capacityCopier_atMostOne x cap minimum parserEnd ready with
    ⟨seedEnd, seedReady, entryArrows, entryBound, entryRun⟩
  have entry : OuterReachesAtMost 1 parserEnd seedEnd := ⟨entryArrows, entryBound, entryRun⟩
  have copierRun := run_raw_copier_complete x cap.val (capacityCopierJunk x)
    (capacityHashTail x cap) minimum
  rw [rawCopierSeed_eq_capacityRawCopierSeedZipper] at copierRun
  rcases copierRun_outerAtMost (CapacitySideCopierRealize x cap minimum)
      (capacity_copier_one_step x cap minimum) (generalCopierFuel x cap.val)
      copierRun seedReady with ⟨finish, finished, copierOuter⟩
  exact ⟨finish, finished, outerReachesAtMost_trans
    (outerReachesAtMost_trans parserRun entry) copierOuter⟩

theorem generalOuterFrontFuel_le_envelope (x : ConcretePakSide.Word) (available : Nat)
    (minimum : minimumSuccessfulWorkCount x.length ≤ available) :
    generalOuterFrontFuel x available ≤
      PakOuterParserNumericSuffix.parserExplicitFuel x + 1 +
        (2 ^ (24 * x.length + 45) + 2 * available) := by
  exact Nat.add_le_add_left (general_copier_fuel_le_pow24_plus_capacity x available minimum) _

theorem actual_outer_front_envelope (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (minimum : minimumSuccessfulWorkCount x.length ≤ cap.val) :
    ∃ d, CapacitySideCopierRealize x cap minimum
        (.groupReady (rawGeneralCapacityGroupZipper x
          (actualFinalCapacity x.length cap.val) (capacityCopierJunk x) (capacityHashTail x cap))) d ∧
      OuterReachesAtMost (PakOuterParserNumericSuffix.parserExplicitFuel x + 1 +
        (2 ^ (24 * x.length + 45) + 2 * cap.val)) (capacityEncodedParserConfig x cap) d := by
  rcases actual_outer_front_bounded x cap minimum with ⟨d, realized, arrows, bound, executed⟩
  exact ⟨d, realized, arrows, bound.trans (generalOuterFrontFuel_le_envelope x cap.val minimum), executed⟩

end PakFixedPolyomino.PakGeneralCapacityOuterFrontFuel
