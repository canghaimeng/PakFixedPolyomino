import PakFixedPolyomino.ULogSourceObliviousStoppingGrammar
import PakFixedPolyomino.ULogSourceObliviousHaltingAcceptance

/-! # Every raw physical accepting leaf of the actual halt table

The counted domain contains only a literal word and its successful accepting
execution. Cycle divisibility, the logical trace, the ordinary source run and
the source-time cutoff are all derived internally. Input is the materialized
window; an actual loader and a fixed universal interpreter remain separate.
-/

namespace PakFixedPolyomino.ULogSourceObliviousHaltingLeaves

open FiniteOneTapeProgram FiniteOneTapeHaltingRestriction
open StandardNondeterministicMachine StandardMachineBinaryChoices
open StandardMachineZipperBridge StandardMachineWindowBridge StandardMachineScannerCounts
open ULogCompiler ULogSourceObliviousWindow ULogSourceObliviousScanProgram
open ULogSourceObliviousInitialWindowExecution ULogSourceObliviousUpdateExecution
open ULogSourceObliviousAcceptedCycles ULogSourceObliviousHaltingProgram
open ULogSourceObliviousHaltingCounts ULogSourceObliviousHaltingAcceptance
open ULogSourceObliviousStoppingGrammar

variable {ns nt : ℕ}

/-- ALL finite literal accepting words. There is no horizon, safety,
canonical-image, intermediate-boundary or live-arrow field. -/
def AcceptingHaltLeaves (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (exterior : Int → Phys) :=
  {word : List (Arrow (haltProgram M)) //
    ∃ out, FiniteOneTapeSemantics.run (haltProgram M) (fun _ => true) word
      (initialWindowConfig M.start (inputWindow M x bound) exterior) = some out ∧
      out.state = State.atLeft M.accept}

def forgetCycles (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (exterior : Int → Phys)
    (raw : AllAcceptingHaltCycles M x bound exterior) :
    AcceptingHaltLeaves M x bound exterior := ⟨raw.2.1, raw.2.2.2⟩

theorem forgetCycles_injective (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (exterior : Int → Phys) :
    Function.Injective (forgetCycles M x bound exterior) := by
  intro a b heq
  exact allHalt_word_injective M x bound exterior (congrArg Subtype.val heq)

/-- The inverse runs on the same actual materialized initial tape even when
the displayed cycle count exceeds bound; source RunsAtMost then excludes it. -/
theorem completed_accepting_length_le (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (htime : RunsAtMost M x bound) (exterior : Int → Phys) (n : ℕ)
    (raw : AcceptingHaltCycles M exterior n M.start (inputWindow M x bound)) :
    n ≤ bound := by
  let originalRaw := includeAccepted M exterior n M.start (inputWindow M x bound) raw
  let word := (acceptedEquiv (toBounded M) (Nat.zero_lt_of_lt M.blank.isLt) M.blank
    exterior n M.start M.accept (inputWindow M x bound)).symm originalRaw
  obtain ⟨out, hrun, hacc⟩ := word.2
  obtain ⟨actual, hactual, hactualrun, hout⟩ := run_window_inverse M word.1.1
    (inputOrigin bound) (inputSize x bound) (initial M x)
    (initial_headIn M x bound) out hrun
  have hlength := htime word.1.1 actual hactualrun
  exact word.1.2.1 ▸ hlength

theorem forgetCycles_surjective (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (htime : RunsAtMost M x bound) (exterior : Int → Phys) :
    Function.Surjective (forgetCycles M x bound exterior) := by
  intro raw
  obtain ⟨out, hrun, hacc⟩ := raw.2
  have hinclude := (run_includeArrows (original M) (halted M) (fun _ => true) raw.1
    (initialWindowConfig M.start (inputWindow M x bound) exterior)).trans hrun
  obtain ⟨n, hlen⟩ := atLeft_stopping_length (toBounded M)
    (Nat.zero_lt_of_lt M.blank.isLt) M.blank exterior M.start (inputWindow M x bound)
    (raw.1.map (includeArrow (original M) (halted M))) out hinclude ⟨M.accept, hacc⟩
  have hrawLen : raw.1.length = n * (4 * windowWidth (inputWindow M x bound) + 6) := by
    exact (List.length_map (as := raw.1) (includeArrow (original M) (halted M))).symm.trans hlen
  let completed : AcceptingHaltCycles M exterior n M.start (inputWindow M x bound) :=
    ⟨raw.1, hrawLen, raw.2⟩
  have hn := completed_accepting_length_le M x bound htime exterior n completed
  exact ⟨⟨⟨n, Nat.lt_succ_of_le hn⟩, completed⟩, Subtype.ext rfl⟩

noncomputable def cyclesLeavesEquiv (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (htime : RunsAtMost M x bound) (exterior : Int → Phys) :
    AllAcceptingHaltCycles M x bound exterior ≃ AcceptingHaltLeaves M x bound exterior :=
  Equiv.ofBijective (forgetCycles M x bound exterior)
    ⟨forgetCycles_injective M x bound exterior,
      forgetCycles_surjective M x bound htime exterior⟩

theorem acceptingHaltLeaves_finite (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (htime : RunsAtMost M x bound) (exterior : Int → Phys) :
    Finite (AcceptingHaltLeaves M x bound exterior) :=
  Finite.of_equiv _ (cyclesLeavesEquiv M x bound htime exterior)

noncomputable def ordinaryLeavesEquiv (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (htime : RunsAtMost M x bound) (exterior : Int → Phys) :
    AcceptingLeaf M x ≃ AcceptingHaltLeaves M x bound exterior :=
  (allLeavesHaltEquiv M x bound htime exterior).trans
    (cyclesLeavesEquiv M x bound htime exterior)

theorem all_physical_leaf_count (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (htime : RunsAtMost M x bound) (exterior : Int → Phys) :
    acceptingCount M x bound = Nat.card (AcceptingHaltLeaves M x bound exterior) :=
  (ordinary_halt_count M x bound exterior).trans
    (Nat.card_congr (cyclesLeavesEquiv M x bound htime exterior))

theorem all_physical_leaf_resources (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (htime : RunsAtMost M x bound) (exterior : Int → Phys)
    (raw : AcceptingHaltLeaves M x bound exterior) :
    (∃ n ≤ bound, raw.1.length = n *
      (4 * ((x.length + 2 * bound + 3) * (nt + 1)) + 6)) ∧
    raw.1.length ≤ bound * (4 * ((x.length + 2 * bound + 3) * (nt + 1)) + 6) ∧
    HaltPrefixInInterval M 0
      (((x.length + 2 * bound + 3) * (nt + 1) + 1 : ℕ) : Int) raw.1
      (initialWindowConfig M.start (inputWindow M x bound) exterior) := by
  obtain ⟨completed, hraw⟩ := forgetCycles_surjective M x bound htime exterior raw
  have hword : completed.2.1 = raw.1 := congrArg Subtype.val hraw
  obtain ⟨hlen, htime, hfoot⟩ := all_halt_resources M x bound exterior completed
  refine ⟨⟨completed.1.val, Nat.le_of_lt_succ completed.1.isLt, ?_⟩, ?_, ?_⟩
  · exact hword ▸ hlen
  · exact hword ▸ htime
  · exact hword ▸ hfoot

theorem sharpEXP_all_physical_leaf_counts (f : List Bool → ℕ) (hf : SharpEXP f) :
    ∃ ns nt, ∃ M : Machine ns nt 2, ∃ exponent : Polynomial ℕ,
      ∀ x : List Bool, RunsAtMost M x (2 ^ exponent.eval x.length) ∧
        ∀ exterior : Int → Phys,
          f x = Nat.card
            (AcceptingHaltLeaves M x (2 ^ exponent.eval x.length) exterior) ∧
          Nonempty (AcceptingLeaf M x ≃
            AcceptingHaltLeaves M x (2 ^ exponent.eval x.length) exterior) := by
  obtain ⟨ns, nt, M, exponent, hM⟩ := (sharpEXP_iff_binary f).mp hf
  refine ⟨ns, nt, M, exponent, ?_⟩
  intro x
  obtain ⟨htime, hcount⟩ := hM x
  exact ⟨htime, fun exterior =>
    ⟨hcount.trans (all_physical_leaf_count M x _ htime exterior),
      ⟨ordinaryLeavesEquiv M x _ htime exterior⟩⟩⟩

end PakFixedPolyomino.ULogSourceObliviousHaltingLeaves
