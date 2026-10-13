import PakFixedPolyomino.PakAllCapacityFrameFramedCount
import PakFixedPolyomino.PakAllFramedFirstHitMicroBijection
import PakFixedPolyomino.PakAllFrameOrdinarySourceCapacityNecessary
import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerSquareFrontFuel

/-! EVERY original capacity fibre count is bounded by the ordinary source
acceptingCount. Sharp scanner-source shortages are ZERO. Under the original
copier-minimum and 16*cap.val ≤ side numeric hypotheses, the fibre count
equals the saturated physical qStart count. Prefix fit and remaining
deadline are derived internally from generalOuterFrontFuel and square slack. -/
namespace PakFixedPolyomino.PakAllFrameOrdinarySourceCounts
open PakAllFrameCapacityWeightedPartition PakSlotOneScannerMultiplicity
open PakCapacityFrontFramedEndpoint PakOuterULogBridge
open PakAllCapacityFrameFramedCount PakAllFramedFirstHitMicroBijection
open PakAllFrameOrdinarySourceCapacityNecessary
open PakAllFrameCapacityMinimumReadback
open ULogTernaryGeneratedMarginScanner (input)
open ULogTernaryGeneratedMarginScannerWeightedRawReadout (firstSaturatedCapacity)
open ULogTernaryGeneratedMarginScannerPhysicalFuel
open ULogTernaryGeneratedMarginScannerAllCutoffBounds
open ULogTernaryGeneratedMarginScannerPhysicalCapacityCounts
open ULogTernaryGeneratedMarginScannerSquareFrontFuel
open ULogConcreteMicroTimeCounts
open PakCopierReserveLowerBound
open PakGeneralCapacityOuterFrontFuel PakGeneralCapacityOuterFrontEnvelope
open StandardNondeterministicMachine (Machine RunsAtMost acceptingCount)
open MStarFixedWidthFirstHitEquiv
variable {ns nt : Nat}

private theorem prefix_fits_and_remaining
    (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (available prefixLen : Nat)
    (minimum : minimumSuccessfulWorkCount (input M p x).length ≤ available)
    (low : 16 * available ≤ ConcretePakSide.sideValue (input M p x))
    (hpref : prefixLen ≤ generalOuterFrontFuel (input M p x) available) :
    prefixLen ≤ ConcretePakSide.sideValue (input M p x) - 1 ∧
      totalPhysicalFuelBound M p x ≤
        ConcretePakSide.sideValue (input M p x) - 1 - prefixLen := by
  have slack := low_capacity_square_slack M p x available minimum low
  unfold startFrontFuel at slack
  omega

theorem fibre_count_eq_raw_cutoff
    (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (_hmin : minimumSuccessfulWorkCount x.length ≤ cap.val)
    (origin : Int) (labels : List MStarULogAssembly.Arrow)
    (hfit : labels.length ≤ ConcretePakSide.sideValue x - 1)
    (hcount : capacityFibreCount x cap =
      if labels.length ≤ ConcretePakSide.sideValue x - 1 then
        Nat.card (FirstHitWordsAtMost
          (anchoredFramedULogConfig ULogControl.qStart origin
            (leftExtra x cap) (rightExtra x cap) (coreZipper x cap))
          (ConcretePakSide.sideValue x - 1 - labels.length)) else 0) :
    capacityFibreCount x cap =
      acceptingMicroPaths (ConcretePakSide.sideValue x - 1 - labels.length)
        (.running ULogControl.qStart (coreZipper x cap)) := by
  rw [hcount, if_pos hfit]
  simpa [acceptingMicroPaths] using
    framed_first_hit_micro_card ULogControl.qStart origin
      (leftExtra x cap) (rightExtra x cap) (group_framing_guards x cap)
      (coreZipper x cap) (ConcretePakSide.sideValue x - 1 - labels.length)

theorem fibre_count_le_accepting
    (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length))
    (cap : ScannerCapacity (input M p x)) :
    capacityFibreCount (input M p x) cap ≤
      acceptingCount M x (2 ^ p.eval x.length) := by
  by_cases hshort : cap.val < minimumSuccessfulWorkCount (input M p x).length
  · have hz := insufficient_capacity_count_zero (input M p x) cap hshort
    omega
  · have hmin : minimumSuccessfulWorkCount (input M p x).length ≤ cap.val :=
      Nat.le_of_not_gt hshort
    obtain ⟨origin, labels, _hp, _hb, hcount⟩ :=
      minimum_fibre_front_count (input M p x) cap hmin
    by_cases hfit : labels.length ≤ ConcretePakSide.sideValue (input M p x) - 1
    · have hraw := fibre_count_eq_raw_cutoff (input M p x) cap hmin origin labels
        hfit hcount
      have hupper := all_cutoff_source_upper M p x ht
        (actualFinalCapacity (input M p x).length cap.val)
        (ConcretePakSide.sideValue (input M p x) - 1 - labels.length)
      exact hraw.trans_le (by simpa [coreZipper] using hupper)
    · rw [hcount, if_neg hfit]
      exact Nat.zero_le _

theorem scanner_source_shortage_zero
    (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length))
    (cap : ScannerCapacity (input M p x))
    (shortage : cap.val < firstSourceScannerCapacity M p x) :
    capacityFibreCount (input M p x) cap = 0 :=
  scanner_source_shortage_fibre_count_zero M p x ht cap shortage

theorem low_capacity_fibre_exact
    (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length))
    (cap : ScannerCapacity (input M p x))
    (minimum : minimumSuccessfulWorkCount (input M p x).length ≤ cap.val)
    (low : 16 * cap.val ≤ ConcretePakSide.sideValue (input M p x)) :
    capacityFibreCount (input M p x) cap =
      if firstSaturatedCapacity M p x ≤
          actualFinalCapacity (input M p x).length cap.val
      then acceptingCount M x (2 ^ p.eval x.length) else 0 := by
  obtain ⟨origin, labels, _hp, hb, hcount⟩ :=
    minimum_fibre_front_count (input M p x) cap minimum
  obtain ⟨hfit, htime⟩ :=
    prefix_fits_and_remaining M p x cap.val labels.length minimum low hb
  have hraw := fibre_count_eq_raw_cutoff (input M p x) cap minimum origin labels
    hfit hcount
  have hphys := all_physical_capacity_time_count M p x ht
    (actualFinalCapacity (input M p x).length cap.val)
    (ConcretePakSide.sideValue (input M p x) - 1 - labels.length) htime
  rw [hraw, firstSaturatedCapacity]
  exact hphys

def all_frame_ordinary_source_counts_spec : Prop :=
  ∀ (ns nt : Nat) (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)),
    (∀ cap : ScannerCapacity (input M p x),
      capacityFibreCount (input M p x) cap ≤
        acceptingCount M x (2 ^ p.eval x.length)) ∧
    (∀ cap : ScannerCapacity (input M p x),
      cap.val < firstSourceScannerCapacity M p x →
        capacityFibreCount (input M p x) cap = 0) ∧
    (∀ cap : ScannerCapacity (input M p x),
      minimumSuccessfulWorkCount (input M p x).length ≤ cap.val →
      16 * cap.val ≤ ConcretePakSide.sideValue (input M p x) →
        capacityFibreCount (input M p x) cap =
          if firstSaturatedCapacity M p x ≤
              actualFinalCapacity (input M p x).length cap.val
          then acceptingCount M x (2 ^ p.eval x.length) else 0)

theorem all_frame_ordinary_source_counts_spec_holds :
    all_frame_ordinary_source_counts_spec :=
  fun _ _ M p x ht =>
    ⟨fibre_count_le_accepting M p x ht,
      scanner_source_shortage_zero M p x ht,
      low_capacity_fibre_exact M p x ht⟩

end PakFixedPolyomino.PakAllFrameOrdinarySourceCounts
