import PakFixedPolyomino.ULogSourceObliviousHaltingProgram

/-! # All completed-cycle accepting counts for the actual halt table

The counted words are literal successful runs of the restricted executable
program. Their endpoint has no outgoing physical rule. No live-arrow,
canonical-image or intermediate-phase condition is added to the domain.
Whole-cycle length remains explicit until the arbitrary-length phase grammar
is proved. This is not yet the fixed-machine or full-frame counting theorem.
-/

namespace PakFixedPolyomino.ULogSourceObliviousHaltingCounts

open FiniteOneTapeProgram FiniteOneTapeSemantics FiniteOneTapeHaltingRestriction
open StandardNondeterministicMachine StandardMachineZipperBridge
open StandardMachineWindowBridge StandardMachineScannerCounts
open ULogCompiler ULogSourceObliviousWindow ULogSourceObliviousScanProgram
open ULogSourceObliviousInitialWindowExecution ULogSourceObliviousUpdateExecution
open ULogSourceObliviousCycleTraces ULogSourceObliviousAcceptedCycles
open ULogSourceObliviousHaltingProgram

variable {ns nt : ℕ}

abbrev original (M : Machine ns nt 2) :=
  program (toBounded M) (Nat.zero_lt_of_lt M.blank.isLt) M.blank

/-- EVERY successful accepting word of the displayed length in the actual
restricted program, including the empty word for an accepting start. -/
def AcceptingHaltCycles (M : Machine ns nt 2) (exterior : Int → Phys)
    (n : ℕ) (q : Fin ns) (w : LogicalWindow nt) :=
  {word : List (Arrow (haltProgram M)) //
    word.length = n * (4 * windowWidth w + 6) ∧
      ∃ out, run (haltProgram M) (fun _ => true) word
        (initialWindowConfig q w exterior) = some out ∧ out.state = State.atLeft M.accept}

def includeAccepted (M : Machine ns nt 2) (exterior : Int → Phys)
    (n : ℕ) (q : Fin ns) (w : LogicalWindow nt)
    (raw : AcceptingHaltCycles M exterior n q w) :
    AcceptedRawCycles (toBounded M) (Nat.zero_lt_of_lt M.blank.isLt) M.blank
      exterior n q M.accept w := by
  refine ⟨⟨raw.1.map (includeArrow (original M) (halted M)), ?_, ?_⟩, ?_⟩
  · exact (List.length_map (as := raw.1) (includeArrow (original M) (halted M))).trans raw.2.1
  · obtain ⟨out, hrun, hacc⟩ := raw.2.2
    refine ⟨out, ?_, M.accept, hacc⟩
    exact (run_includeArrows (original M) (halted M) (fun _ => true) raw.1
      (initialWindowConfig q w exterior)).trans hrun
  · obtain ⟨out, hrun, hacc⟩ := raw.2.2
    refine ⟨out, ?_, hacc⟩
    exact (run_includeArrows (original M) (halted M) (fun _ => true) raw.1
      (initialWindowConfig q w exterior)).trans hrun

theorem includeAccepted_injective (M : Machine ns nt 2) (exterior : Int → Phys)
    (n : ℕ) (q : Fin ns) (w : LogicalWindow nt) :
    Function.Injective (includeAccepted M exterior n q w) := by
  intro a b heq
  apply Subtype.ext
  exact (List.map_injective_iff.mpr (includeArrow_injective (original M) (halted M)))
    (congrArg (fun z => z.1.1) heq)

/-- Liveness is derived by the inverse for ALL original raw cycle runs. -/
def liftAccepted (M : Machine ns nt 2) (exterior : Int → Phys)
    (n : ℕ) (q : Fin ns) (w : LogicalWindow nt)
    (raw : AcceptedRawCycles (toBounded M) (Nat.zero_lt_of_lt M.blank.isLt) M.blank
      exterior n q M.accept w) : AcceptingHaltCycles M exterior n q w := by
  have hlive := all_raw_cycles_live M (Nat.zero_lt_of_lt M.blank.isLt) M.blank
    exterior n q w raw.1
  let word := liftWord (original M) (halted M) raw.1.1 hlive
  refine ⟨word, ?_, ?_⟩
  · have hlen := congrArg List.length (include_liftWord (original M) (halted M)
      raw.1.1 hlive)
    change (liftWord (original M) (halted M) raw.1.1 hlive).length = _
    simpa only [List.length_map] using hlen.trans raw.1.2.1
  · obtain ⟨out, hrun, hacc⟩ := raw.2
    refine ⟨out, ?_, hacc⟩
    exact (run_liftWord (original M) (halted M) (fun _ => true) raw.1.1 hlive
      (initialWindowConfig q w exterior)).trans hrun

noncomputable def haltRawEquiv (M : Machine ns nt 2) (exterior : Int → Phys)
    (n : ℕ) (q : Fin ns) (w : LogicalWindow nt) :
    AcceptingHaltCycles M exterior n q w ≃
      AcceptedRawCycles (toBounded M) (Nat.zero_lt_of_lt M.blank.isLt) M.blank
        exterior n q M.accept w :=
  Equiv.ofBijective (includeAccepted M exterior n q w) (by
    refine ⟨includeAccepted_injective M exterior n q w, ?_⟩
    intro raw
    refine ⟨liftAccepted M exterior n q w raw, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact include_liftWord (original M) (halted M) raw.1.1
      (all_raw_cycles_live M (Nat.zero_lt_of_lt M.blank.isLt) M.blank exterior n q w raw.1))

instance acceptingHaltCycles_finite (M : Machine ns nt 2) (exterior : Int → Phys)
    (n : ℕ) (q : Fin ns) (w : LogicalWindow nt) :
    Finite (AcceptingHaltCycles M exterior n q w) :=
  Finite.of_injective _ (includeAccepted_injective M exterior n q w)

abbrev AllAcceptingHaltCycles (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (exterior : Int → Phys) :=
  (n : Fin (bound + 1)) ×
    AcceptingHaltCycles M exterior n.val M.start (inputWindow M x bound)

noncomputable def allHaltRawEquiv (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (exterior : Int → Phys) :
    AllAcceptingHaltCycles M x bound exterior ≃ AllRawAcceptingCycles M x bound exterior :=
  Equiv.sigmaCongrRight fun n => haltRawEquiv M exterior n.val M.start (inputWindow M x bound)

noncomputable def ordinaryHaltEquiv (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (exterior : Int → Phys) :
    AcceptingCode M x bound ≃ AllAcceptingHaltCycles M x bound exterior :=
  (codeRawEquiv M x bound exterior).trans (allHaltRawEquiv M x bound exterior).symm

theorem ordinary_halt_count (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (exterior : Int → Phys) :
    acceptingCount M x bound = Nat.card (AllAcceptingHaltCycles M x bound exterior) := by
  rw [all_raw_accepting_count M x bound exterior]
  exact Nat.card_congr (allHaltRawEquiv M x bound exterior).symm

noncomputable def allLeavesHaltEquiv (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (htime : RunsAtMost M x bound) (exterior : Int → Phys) :
    AcceptingLeaf M x ≃ AllAcceptingHaltCycles M x bound exterior :=
  (allLeavesRawEquiv M x bound htime exterior).trans (allHaltRawEquiv M x bound exterior).symm

theorem accepting_endpoint_no_extension (M : Machine ns nt 2) (exterior : Int → Phys)
    (n : ℕ) (q : Fin ns) (w : LogicalWindow nt)
    (raw : AcceptingHaltCycles M exterior n q w) :
    ∃ out, run (haltProgram M) (fun _ => true) raw.1
      (initialWindowConfig q w exterior) = some out ∧ out.state = State.atLeft M.accept ∧
      ∀ continuation : List (Arrow (haltProgram M)), continuation ≠ [] →
        run (haltProgram M) (fun _ => true) continuation out = none := by
  obtain ⟨out, hrun, hacc⟩ := raw.2.2
  refine ⟨out, hrun, hacc, ?_⟩
  intro continuation hne
  exact terminal_run_nonempty_none (original M) (halted M) (fun _ => true) out
    (by rw [hacc]; exact halted_accept M) continuation hne

theorem allHalt_word_injective (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (exterior : Int → Phys) :
    Function.Injective (fun raw : AllAcceptingHaltCycles M x bound exterior => raw.2.1) := by
  rintro ⟨n, a⟩ ⟨m, b⟩ heq
  have hlen := congrArg List.length heq
  have hm : n = m := Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega)
    (a.2.1.symm.trans (hlen.trans b.2.1)))
  subst m
  have hab : a = b := Subtype.ext heq
  subst b
  rfl

end PakFixedPolyomino.ULogSourceObliviousHaltingCounts
