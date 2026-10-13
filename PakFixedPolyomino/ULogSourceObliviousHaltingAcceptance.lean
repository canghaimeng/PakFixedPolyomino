import PakFixedPolyomino.ULogSourceObliviousHaltingCounts

/-! # Exact operational scope of the completed-cycle halting bridge

The original source model is preserved internally. The target rule table
really halts, and all raw accepting histories of each whole-cycle horizon
are counted. Arbitrary stopping lengths, fixed universality, loading and
common square-frame resources remain explicit separate obligations.
-/

namespace PakFixedPolyomino.ULogSourceObliviousHaltingAcceptance

open StandardNondeterministicMachine StandardMachineBinaryChoices
open StandardMachineZipperBridge StandardMachineWindowBridge StandardMachineScannerCounts
open StandardMachineScannerAcceptance
open FiniteOneTapeProgram FiniteOneTapeSemantics FiniteOneTapeHaltingRestriction
open ULogCompiler ULogSourceObliviousWindow ULogSourceObliviousScanProgram
open ULogSourceObliviousInitialWindowExecution ULogSourceObliviousUpdateExecution
open ULogSourceObliviousHaltingProgram ULogSourceObliviousHaltingCounts
open ULogSourceObliviousWindowFootprint

variable {ns nt : ℕ}

/-- Actual restricted-program executions at EVERY chronological prefix. -/
def HaltPrefixInInterval (M : Machine ns nt 2) (lo hi : Int)
    (word : List (Arrow (haltProgram M))) (c : ScanCfg ns nt) : Prop :=
  ∀ k ≤ word.length, ∃ middle,
    run (haltProgram M) (fun _ => true) (word.take k) c = some middle ∧
      lo ≤ middle.head ∧ middle.head ≤ hi

theorem all_halt_resources (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (exterior : Int → Phys)
    (raw : AllAcceptingHaltCycles M x bound exterior) :
    raw.2.1.length = raw.1.val *
      (4 * ((x.length + 2 * bound + 3) * (nt + 1)) + 6) ∧
    raw.2.1.length ≤ bound *
      (4 * ((x.length + 2 * bound + 3) * (nt + 1)) + 6) ∧
    HaltPrefixInInterval M 0
      (((x.length + 2 * bound + 3) * (nt + 1) + 1 : ℕ) : Int) raw.2.1
      (initialWindowConfig M.start (inputWindow M x bound) exterior) := by
  have hlen : raw.2.1.length = raw.1.val *
      (4 * ((x.length + 2 * bound + 3) * (nt + 1)) + 6) := by
    simpa only [inputWindow_width] using raw.2.2.1
  refine ⟨hlen, hlen.le.trans (Nat.mul_le_mul_right _
    (Nat.le_of_lt_succ raw.1.isLt)), ?_⟩
  let old := allHaltRawEquiv M x bound exterior raw
  have hfoot := (ordinary_counts_and_scanner_resources M x bound exterior).2.2.2 old
  have hp := hfoot.2.2
  change PrefixInInterval (toBounded M) (Nat.zero_lt_of_lt M.blank.isLt) M.blank
    0 _ (raw.2.1.map (includeArrow (original M) (halted M)))
      (initialWindowConfig M.start (inputWindow M x bound) exterior) at hp
  intro k hk
  have hmLen := List.length_map (as := raw.2.1) (includeArrow (original M) (halted M))
  obtain ⟨middle, hrun, hlo, hhi⟩ := hp k (hk.trans (Nat.le_of_eq hmLen.symm))
  refine ⟨middle, ?_, hlo, hhi⟩
  have heq := run_includeArrows (original M) (halted M) (fun _ => true)
    (raw.2.1.take k) (initialWindowConfig M.start (inputWindow M x bound) exterior)
  have hm := List.map_take (f := includeArrow (original M) (halted M))
    (l := raw.2.1) (i := k)
  have hpRun := congrArg (fun word : List (Arrow (original M)) =>
    run (original M) (fun _ => true) word
      (initialWindowConfig M.start (inputWindow M x bound) exterior)) hm
  exact heq.symm.trans (hpRun.trans hrun)

theorem sharpEXP_all_halt_counts (f : List Bool → ℕ) (hf : SharpEXP f) :
    ∃ ns nt, ∃ M : Machine ns nt 2, ∃ exponent : Polynomial ℕ,
      ∀ x : List Bool, RunsAtMost M x (2 ^ exponent.eval x.length) ∧
        ∀ exterior : Int → Phys,
          f x = Nat.card
            (AllAcceptingHaltCycles M x (2 ^ exponent.eval x.length) exterior) ∧
          Nonempty (AcceptingLeaf M x ≃
            AllAcceptingHaltCycles M x (2 ^ exponent.eval x.length) exterior) := by
  obtain ⟨ns, nt, M, exponent, hM⟩ := (sharpEXP_iff_binary f).mp hf
  refine ⟨ns, nt, M, exponent, ?_⟩
  intro x
  obtain ⟨htime, hcount⟩ := hM x
  exact ⟨htime, fun exterior =>
    ⟨hcount.trans (ordinary_halt_count M x _ exterior),
      ⟨allLeavesHaltEquiv M x _ htime exterior⟩⟩⟩

/-- This endpoint states its whole-cycle scope explicitly. Physical terminal
rules, literal multiplicities, all source leaves, exact time and prefix head
bounds are derived. No fixed-machine or arbitrary-length assertion appears. -/
theorem ordinary_source_completed_halting_bridge :
    (∀ {ns nt : ℕ} (M : Machine ns nt 2),
      (∀ x slot, (haltProgram M).rule (.atLeft M.accept) x slot = none) ∧
      (∀ x slot, (haltProgram M).rule (.atLeft M.reject) x slot = none) ∧
      (∀ x slot, (haltProgram M).rule .reject x slot = none) ∧
      ∀ (x : List Bool) (bound : ℕ) (exterior : Int → Phys),
        Finite (AllAcceptingHaltCycles M x bound exterior) ∧
        acceptingCount M x bound = Nat.card (AllAcceptingHaltCycles M x bound exterior) ∧
        (RunsAtMost M x bound →
          Nonempty (AcceptingLeaf M x ≃ AllAcceptingHaltCycles M x bound exterior)) ∧
        Function.Injective (fun raw : AllAcceptingHaltCycles M x bound exterior => raw.2.1) ∧
        (∀ raw : AllAcceptingHaltCycles M x bound exterior,
          raw.2.1.length = raw.1.val *
            (4 * ((x.length + 2 * bound + 3) * (nt + 1)) + 6) ∧
          raw.2.1.length ≤ bound *
            (4 * ((x.length + 2 * bound + 3) * (nt + 1)) + 6) ∧
          HaltPrefixInInterval M 0
            (((x.length + 2 * bound + 3) * (nt + 1) + 1 : ℕ) : Int) raw.2.1
            (initialWindowConfig M.start (inputWindow M x bound) exterior)) ∧
        (∀ raw : AllAcceptingHaltCycles M x bound exterior,
          ∃ out, run (haltProgram M) (fun _ => true) raw.2.1
            (initialWindowConfig M.start (inputWindow M x bound) exterior) = some out ∧
            out.state = State.atLeft M.accept ∧
            ∀ continuation : List (Arrow (haltProgram M)), continuation ≠ [] →
              run (haltProgram M) (fun _ => true) continuation out = none)) ∧
    (∀ f : List Bool → ℕ, SharpEXP f →
      ∃ ns nt, ∃ M : Machine ns nt 2, ∃ exponent : Polynomial ℕ,
        ∀ x : List Bool, RunsAtMost M x (2 ^ exponent.eval x.length) ∧
          ∀ exterior : Int → Phys,
            f x = Nat.card (AllAcceptingHaltCycles M x (2 ^ exponent.eval x.length) exterior) ∧
            Nonempty (AcceptingLeaf M x ≃
              AllAcceptingHaltCycles M x (2 ^ exponent.eval x.length) exterior)) := by
  refine ⟨?_, sharpEXP_all_halt_counts⟩
  intro ns nt M
  refine ⟨haltProgram_accept_terminal M, haltProgram_source_reject_terminal M,
    haltProgram_reject_terminal M, ?_⟩
  intro x bound exterior
  exact ⟨inferInstance, ordinary_halt_count M x bound exterior,
    fun htime => ⟨allLeavesHaltEquiv M x bound htime exterior⟩,
    allHalt_word_injective M x bound exterior, all_halt_resources M x bound exterior,
    fun raw => accepting_endpoint_no_extension M exterior raw.1.val M.start
      (inputWindow M x bound) raw.2⟩

end PakFixedPolyomino.ULogSourceObliviousHaltingAcceptance
