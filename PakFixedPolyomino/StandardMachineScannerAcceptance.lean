import PakFixedPolyomino.StandardMachineScannerCounts
import PakFixedPolyomino.StandardMachineBinaryChoices
import PakFixedPolyomino.ULogSourceObliviousMultiCycleAcceptance

/-! # Exact ordinary-source alignment of raw scanner endpoint counts

Ordinary finite branching is normalized internally to literal binary slots.
Actual physical source paths fit a materialized time-radius window. The
counted raw domain consists of every successful whole-cycle word ending at
the actual accepting atLeft endpoint, across every source length up to its
time bound. This is a source-count bridge, not a fixed-universal-machine,
physical halting, capacity-invariance or full square-frame theorem.
-/

namespace PakFixedPolyomino.StandardMachineScannerAcceptance

open StandardNondeterministicMachine StandardMachineBinaryChoices
open StandardMachineZipperBridge (toBounded)
open StandardMachineWindowBridge StandardMachineScannerCounts
open ULogSourceObliviousAcceptedCycles ULogSourceObliviousCycleTraces
open ULogSourceObliviousUpdateExecution ULogSourceObliviousInitialWindowExecution
open ULogSourceObliviousWindowFootprint

theorem ordinary_counts_and_scanner_resources {ns nt : ℕ}
    (M : Machine ns nt 2) (x : List Bool) (bound : ℕ) (exterior : Int → Phys) :
    Finite (AllRawAcceptingCycles M x bound exterior) ∧
    acceptingCount M x bound = Nat.card (AllRawAcceptingCycles M x bound exterior) ∧
    (RunsAtMost M x bound →
      Nonempty (AcceptingLeaf M x ≃ AllRawAcceptingCycles M x bound exterior)) ∧
    (∀ raw : AllRawAcceptingCycles M x bound exterior,
      raw.2.1.1.length = raw.1.val *
        (4 * ((x.length + 2 * bound + 3) * (nt + 1)) + 6) ∧
      raw.2.1.1.length ≤ bound *
        (4 * ((x.length + 2 * bound + 3) * (nt + 1)) + 6) ∧
      PrefixInInterval (toBounded M) (Nat.zero_lt_of_lt M.blank.isLt) M.blank
        0 (((x.length + 2 * bound + 3) * (nt + 1) + 1 : ℕ) : Int) raw.2.1.1
        (initialWindowConfig M.start (inputWindow M x bound) exterior)) := by
  refine ⟨inferInstance, all_raw_accepting_count M x bound exterior,
    fun htime => ⟨allLeavesRawEquiv M x bound htime exterior⟩, ?_⟩
  intro raw
  obtain ⟨hlen, hbound⟩ := all_raw_physical_length M x bound exterior raw
  refine ⟨hlen, hbound, ?_⟩
  have hfoot :=
    (ULogSourceObliviousMultiCycleAcceptance.all_raw_multicycle_counts_and_resources
      (toBounded M) (Nat.zero_lt_of_lt M.blank.isLt) M.blank exterior raw.1.val
      M.start M.accept (inputWindow M x bound)).2.2.2.2.2.2.2.2 raw.2.1
  simpa only [inputWindow_width, Nat.cast_add, Nat.cast_one] using hfoot

theorem sharpEXP_all_raw_source_counts (f : List Bool → ℕ) (hf : SharpEXP f) :
    ∃ ns nt, ∃ M : Machine ns nt 2, ∃ exponent : Polynomial ℕ,
      ∀ x : List Bool, RunsAtMost M x (2 ^ exponent.eval x.length) ∧
        ∀ exterior : Int → Phys,
          f x = Nat.card
            (AllRawAcceptingCycles M x (2 ^ exponent.eval x.length) exterior) ∧
          Nonempty (AcceptingLeaf M x ≃
            AllRawAcceptingCycles M x (2 ^ exponent.eval x.length) exterior) := by
  obtain ⟨ns, nt, M, exponent, hM⟩ := (sharpEXP_iff_binary f).mp hf
  refine ⟨ns, nt, M, exponent, ?_⟩
  intro x
  obtain ⟨htime, hcount⟩ := hM x
  exact ⟨htime, fun exterior =>
    ⟨hcount.trans (all_raw_accepting_count M x _ exterior),
      ⟨allLeavesRawEquiv M x _ htime exterior⟩⟩⟩

theorem ordinary_source_raw_count_bridge :
    (∀ {ns nt : ℕ} (M : Machine ns nt 2) (x : List Bool) (bound : ℕ) (exterior : Int → Phys),
      Finite (AllRawAcceptingCycles M x bound exterior) ∧
      acceptingCount M x bound = Nat.card (AllRawAcceptingCycles M x bound exterior) ∧
      (RunsAtMost M x bound →
        Nonempty (AcceptingLeaf M x ≃ AllRawAcceptingCycles M x bound exterior)) ∧
      (∀ raw : AllRawAcceptingCycles M x bound exterior,
        raw.2.1.1.length = raw.1.val *
          (4 * ((x.length + 2 * bound + 3) * (nt + 1)) + 6) ∧
        raw.2.1.1.length ≤ bound *
          (4 * ((x.length + 2 * bound + 3) * (nt + 1)) + 6) ∧
        PrefixInInterval (toBounded M) (Nat.zero_lt_of_lt M.blank.isLt) M.blank
          0 (((x.length + 2 * bound + 3) * (nt + 1) + 1 : ℕ) : Int) raw.2.1.1
          (initialWindowConfig M.start (inputWindow M x bound) exterior))) ∧
    (∀ f : List Bool → ℕ, SharpEXP f →
      ∃ ns nt, ∃ M : Machine ns nt 2, ∃ exponent : Polynomial ℕ,
        ∀ x : List Bool, RunsAtMost M x (2 ^ exponent.eval x.length) ∧
          ∀ exterior : Int → Phys,
            f x = Nat.card (AllRawAcceptingCycles M x (2 ^ exponent.eval x.length) exterior) ∧
            Nonempty (AcceptingLeaf M x ≃
              AllRawAcceptingCycles M x (2 ^ exponent.eval x.length) exterior)) := by
  exact ⟨ordinary_counts_and_scanner_resources, sharpEXP_all_raw_source_counts⟩

end PakFixedPolyomino.StandardMachineScannerAcceptance
