import PakFixedPolyomino.PakAllFrameCapacityMinimumReadback
import PakFixedPolyomino.PakOuterULogReflection

/-! Every actual capacity fibre reaches its exact guarded framed interpreter
start. The entire integer tape and physical anchor are retained. Source/raw
word bijection and spatially bounded forward framing are separate. -/
namespace PakFixedPolyomino.PakCapacityFrontFramedEndpoint
open PakSlotOneScannerMultiplicity PakAllFrameCapacityWeightedPartition
open PakGeneralCapacityInitialWindow PakCapacityOuterFrontDeterministicPrefix
open PakParserOuterBridge PakOuterULogBridge PakOuterULogReflection
open MStarFixedWidthFirstHitEquiv

abbrev groupZipper (x : ConcretePakSide.Word) (cap : ScannerCapacity x) :=
  PakCopierReserveLowerBound.rawGeneralCapacityGroupZipper x
    (PakCopierReserveLowerBound.actualFinalCapacity x.length cap.val)
    (PakGeneralCapacityParserCopierFront.capacityCopierJunk x)
    (PakGeneralCapacityParserCopierFront.capacityHashTail x cap)

abbrev leftExtra (x : ConcretePakSide.Word) (cap : ScannerCapacity x) :=
  (groupZipper x cap).leftRev

abbrev rightExtra (x : ConcretePakSide.Word) (cap : ScannerCapacity x) :=
  MStarOuterProgram.Tape.markR ::
    PakGeneralCapacityParserCopierFront.capacityHashTail x cap

abbrev coreZipper (x : ConcretePakSide.Word) (cap : ScannerCapacity x) :=
  PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper x
    (PakCopierReserveLowerBound.actualFinalCapacity x.length cap.val)

theorem group_framing_guards (x : ConcretePakSide.Word) (cap : ScannerCapacity x) :
    FramingGuards (leftExtra x cap) (rightExtra x cap) := by
  constructor
  · intro y
    simp [NonCoreHead, leftExtra, groupZipper,
      PakCopierReserveLowerBound.rawGeneralCapacityGroupZipper]
  · exact (framingGuards_markers []
      (PakGeneralCapacityParserCopierFront.capacityHashTail x cap)).right

theorem group_framed_eq (x : ConcretePakSide.Word) (cap : ScannerCapacity x) :
    groupZipper x cap = frameCoreZipper (leftExtra x cap) (rightExtra x cap)
      (coreZipper x cap) :=
  PakULogGeneralCapacityBootstrap.rawGeneralCapacityGroupZipper_eq_framed x
    (PakCopierReserveLowerBound.actualFinalCapacity x.length cap.val)
    (PakGeneralCapacityParserCopierFront.capacityCopierJunk x)
    (PakGeneralCapacityParserCopierFront.capacityHashTail x cap)

theorem group_realize_framed (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.val)
    (d : PakMStarCouplingCorrectness.MStarConfig)
    (hd : PakGeneralCapacityOuterFrontStandard.CapacitySideCopierRealize x cap hmin
      (groupResult x cap) d) :
    ∃ origin : Int, d = anchoredFramedULogConfig ULogControl.qStart origin
      (leftExtra x cap) (rightExtra x cap) (coreZipper x cap) := by
  obtain ⟨origin, hcfg⟩ := hd.2
  refine ⟨origin, hcfg.trans ?_⟩
  change anchoredGroupReadyConfig origin (groupZipper x cap) = _
  simp only [anchoredGroupReadyConfig, anchoredFramedULogConfig,
    ← group_framed_eq x cap]
  rfl

theorem fibre_front_framed (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (F : CapacityFibre x cap) :
    ∃ origin : Int, ∃ labels : List MStarULogAssembly.Arrow,
      Prefix labels (capacityEncodedParserConfig x cap)
        (anchoredFramedULogConfig ULogControl.qStart origin
          (leftExtra x cap) (rightExtra x cap) (coreZipper x cap)) ∧
      labels.length ≤ PakGeneralCapacityOuterFrontFuel.generalOuterFrontFuel x cap.val ∧
      (∀ B, Nat.card (AcceptedWordsAtLength (capacityEncodedParserConfig x cap) B) =
        if labels.length ≤ B then
          Nat.card (FirstHitWordsAtMost
            (anchoredFramedULogConfig ULogControl.qStart origin
              (leftExtra x cap) (rightExtra x cap) (coreZipper x cap))
            (B - labels.length)) else 0) := by
  obtain ⟨d, labels, hd, hb, hp, hs, he, hc, hall, hshort⟩ :=
    PakAllFrameCapacityMinimumReadback.fibre_front_cancellation x cap F
  obtain ⟨origin, hdframe⟩ := group_realize_framed x cap
    (PakAllFrameCapacityMinimumReadback.fibre_minimum x cap F) d hd
  exact ⟨origin, labels, hdframe ▸ hp, hb, hdframe ▸ hall⟩

def capacity_front_framed_spec : Prop :=
  (∀ (x : ConcretePakSide.Word) (cap : ScannerCapacity x),
    FramingGuards (leftExtra x cap) (rightExtra x cap)) ∧
  (∀ (x : ConcretePakSide.Word) (cap : ScannerCapacity x),
    groupZipper x cap = frameCoreZipper (leftExtra x cap) (rightExtra x cap) (coreZipper x cap)) ∧
  (∀ (x : ConcretePakSide.Word) (cap : ScannerCapacity x) (F : CapacityFibre x cap),
    ∃ origin : Int, ∃ labels : List MStarULogAssembly.Arrow,
      Prefix labels (capacityEncodedParserConfig x cap)
        (anchoredFramedULogConfig ULogControl.qStart origin
          (leftExtra x cap) (rightExtra x cap) (coreZipper x cap)) ∧
      labels.length ≤ PakGeneralCapacityOuterFrontFuel.generalOuterFrontFuel x cap.val ∧
      (∀ B, Nat.card (AcceptedWordsAtLength (capacityEncodedParserConfig x cap) B) =
        if labels.length ≤ B then
          Nat.card (FirstHitWordsAtMost
            (anchoredFramedULogConfig ULogControl.qStart origin
              (leftExtra x cap) (rightExtra x cap) (coreZipper x cap))
            (B - labels.length)) else 0))

theorem capacity_front_framed_spec_holds : capacity_front_framed_spec :=
  ⟨group_framing_guards, group_framed_eq, fibre_front_framed⟩

end PakFixedPolyomino.PakCapacityFrontFramedEndpoint
