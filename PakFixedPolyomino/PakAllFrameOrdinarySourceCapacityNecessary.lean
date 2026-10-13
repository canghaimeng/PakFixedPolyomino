import PakFixedPolyomino.PakAllFrameFramedCountUpper
import PakFixedPolyomino.PakOuterFramedSimulationStandard
import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerWeightedRawReadout

/-! Every actual source-encoded capacity fibre obeys the genuine source
workspace threshold. An existential raw projection suffices for this
necessity and zero result; cardinal upper bounds require the separate
all-word inverse. No physical forward-frame construction is asserted. -/
namespace PakFixedPolyomino.PakAllFrameOrdinarySourceCapacityNecessary
open PakAllFrameCapacityWeightedPartition PakSlotOneScannerMultiplicity
open PakCapacityFrontFramedEndpoint PakOuterULogBridge
open MStarFixedWidthFirstHitEquiv ULogBootstrapExecution
open ULogTernaryGeneratedMarginScanner (input states)
open ULogTernaryGeneratedMarginScannerWeightedRawReadout (firstSaturatedCapacity)
open StandardNondeterministicMachine (Machine RunsAtMost acceptingCount)
variable {ns nt : Nat}

theorem fibre_raw_accepts (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (F : CapacityFibre x cap) :
    ∃ slots tape, ConcreteMicroPath (.running ULogControl.qStart (coreZipper x cap))
      slots (.accepted tape) ∧ slots.length ≤ ConcretePakSide.sideValue x - 1 := by
  classical
  obtain ⟨origin, labels, hp, hw, hb, hu⟩ :=
    PakAllFrameFramedCountUpper.fibre_front_framed_upper x cap F
  let c := anchoredFramedULogConfig ULogControl.qStart origin
    (leftExtra x cap) (rightExtra x cap) (coreZipper x cap)
  let T := ConcretePakSide.sideValue x - 1 - labels.length
  have hpos : 0 < Nat.card (FirstHitWordsAtMost c T) :=
    lt_of_lt_of_le (PakAllFrameFramedCountUpper.fibre_count_pos x cap F) hu
  have hn : Nonempty (FirstHitWordsAtMost c T) :=
    (Nat.card_ne_zero.mp (Nat.ne_of_gt hpos)).1
  let w := Classical.choice hn
  obtain ⟨d, hd⟩ := w.2.2
  let H := PakOuterULogTraceBridge.OuterArrowHistory.of_run_eq w.1 c d hd.1
  obtain ⟨slots, tape, hr, hl⟩ :=
    PakOuterFramedSimulationStandard.outerHistory_from_framedSim_to_concreteMicroPath
      H ULogControl.qStart origin (leftExtra x cap) (rightExtra x cap)
      (group_framing_guards x cap) (coreZipper x cap) rfl hd.2.1
  refine ⟨slots, tape, hr, ?_⟩
  have bound := w.2.1
  dsimp [T] at bound
  omega

theorem fibre_source_capacity_necessary (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length))
    (cap : ScannerCapacity (input M p x)) (F : CapacityFibre (input M p x) cap) :
    firstSaturatedCapacity M p x ≤
      PakCopierReserveLowerBound.actualFinalCapacity (input M p x).length cap.val := by
  obtain ⟨slots, tape, hr, hl⟩ := fibre_raw_accepts (input M p x) cap F
  exact ULogTernaryGeneratedMarginScannerPhysicalCapacityCounts.physical_accepting_sharp_capacity_necessary
    M p x ht _ slots tape hr

theorem source_shortage_fibre_empty (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length))
    (cap : ScannerCapacity (input M p x))
    (shortage : PakCopierReserveLowerBound.actualFinalCapacity (input M p x).length cap.val <
      firstSaturatedCapacity M p x) : IsEmpty (CapacityFibre (input M p x) cap) :=
  ⟨fun F => Nat.not_le_of_gt shortage (fibre_source_capacity_necessary M p x ht cap F)⟩

theorem source_shortage_fibre_count_zero (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length))
    (cap : ScannerCapacity (input M p x))
    (shortage : PakCopierReserveLowerBound.actualFinalCapacity (input M p x).length cap.val <
      firstSaturatedCapacity M p x) : capacityFibreCount (input M p x) cap = 0 := by
  exact Nat.card_eq_zero.mpr (Or.inl (source_shortage_fibre_empty M p x ht cap shortage))

noncomputable def firstSourceScannerCapacity (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) : Nat :=
  PakCopierReserveLowerBound.consumedBeforeFinalBuffer (input M p x).length +
    firstSaturatedCapacity M p x

theorem fibre_scanner_capacity_necessary (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length))
    (cap : ScannerCapacity (input M p x)) (F : CapacityFibre (input M p x) cap) :
    firstSourceScannerCapacity M p x ≤ cap.val := by
  have h := fibre_source_capacity_necessary M p x ht cap F
  have positive : 0 < firstSaturatedCapacity M p x := by
    unfold firstSaturatedCapacity
    omega
  unfold firstSourceScannerCapacity PakCopierReserveLowerBound.actualFinalCapacity at *
  omega

theorem scanner_source_shortage_fibre_count_zero (M : Machine ns nt 2)
    (p : Polynomial Nat) (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length))
    (cap : ScannerCapacity (input M p x)) (shortage : cap.val < firstSourceScannerCapacity M p x) :
    capacityFibreCount (input M p x) cap = 0 := by
  apply Nat.card_eq_zero.mpr
  exact Or.inl ⟨fun F => Nat.not_le_of_gt shortage
    (fibre_scanner_capacity_necessary M p x ht cap F)⟩

theorem fibre_source_count_pos (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length))
    (cap : ScannerCapacity (input M p x)) (F : CapacityFibre (input M p x) cap) :
    0 < acceptingCount M x (2 ^ p.eval x.length) := by
  obtain ⟨slots, tape, hr, hl⟩ := fibre_raw_accepts (input M p x) cap F
  let T := ConcretePakSide.sideValue (input M p x) - 1
  let start := ULogBootstrapExecution.Result.running ULogControl.qStart
    (coreZipper (input M p x) cap)
  letI := ULogConcreteMicroCutoffMonotonicity.finite_raw_cutoff T start
  letI : Nonempty (ULogConcreteMicroTimeCounts.RawAcceptingMicroWordsAtMost T start) :=
    ⟨⟨slots, hl, tape, hr⟩⟩
  have rawpos : 0 < ULogConcreteMicroTimeCounts.acceptingMicroPaths T start := Nat.card_pos
  exact lt_of_lt_of_le rawpos
    (ULogTernaryGeneratedMarginScannerAllCutoffBounds.all_cutoff_source_upper M p x ht _ T)

theorem source_count_zero_fibre_empty (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length))
    (zero : acceptingCount M x (2 ^ p.eval x.length) = 0)
    (cap : ScannerCapacity (input M p x)) : IsEmpty (CapacityFibre (input M p x) cap) :=
  ⟨fun F => by have positive := fibre_source_count_pos M p x ht cap F; omega⟩

theorem source_count_zero_fibre_count_zero (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length))
    (zero : acceptingCount M x (2 ^ p.eval x.length) = 0)
    (cap : ScannerCapacity (input M p x)) : capacityFibreCount (input M p x) cap = 0 :=
  Nat.card_eq_zero.mpr (Or.inl (source_count_zero_fibre_empty M p x ht zero cap))

def ordinary_source_capacity_necessary_spec : Prop :=
  (∀ (x : ConcretePakSide.Word) (cap : ScannerCapacity x) (F : CapacityFibre x cap),
    ∃ slots tape, ConcreteMicroPath (.running ULogControl.qStart (coreZipper x cap))
      slots (.accepted tape) ∧ slots.length ≤ ConcretePakSide.sideValue x - 1) ∧
  (∀ (ns nt : Nat) (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (ht : RunsAtMost M x (2 ^ p.eval x.length)) (cap : ScannerCapacity (input M p x)),
    (∀ F : CapacityFibre (input M p x) cap,
      firstSourceScannerCapacity M p x ≤ cap.val ∧
        0 < acceptingCount M x (2 ^ p.eval x.length)) ∧
    (cap.val < firstSourceScannerCapacity M p x → capacityFibreCount (input M p x) cap = 0) ∧
    (acceptingCount M x (2 ^ p.eval x.length) = 0 → capacityFibreCount (input M p x) cap = 0))

theorem ordinary_source_capacity_necessary_spec_holds : ordinary_source_capacity_necessary_spec :=
  ⟨fibre_raw_accepts, fun _ _ M p x ht cap =>
    ⟨fun F => ⟨fibre_scanner_capacity_necessary M p x ht cap F,
      fibre_source_count_pos M p x ht cap F⟩,
    scanner_source_shortage_fibre_count_zero M p x ht cap,
    fun zero => source_count_zero_fibre_count_zero M p x ht zero cap⟩⟩

end PakFixedPolyomino.PakAllFrameOrdinarySourceCapacityNecessary
