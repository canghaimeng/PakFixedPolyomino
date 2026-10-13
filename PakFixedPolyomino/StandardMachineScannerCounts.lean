import PakFixedPolyomino.StandardMachineWindowBridge
import PakFixedPolyomino.ULogSourceObliviousAcceptedCycles

/-! # Ordinary accepting words and all raw whole-cycle scanner counts

The materialized input window has input.length + 2*bound + 3 actual letters.
Every ordinary path of length at most bound fits by one-cell head geometry;
every successful window word conversely executes the ordinary machine.
Thus literal ordinary accepting words, rather than a normalized subclass,
are counted by ALL raw completed scanner words of their corresponding length.
Halting/clock/loading and full square-frame counting remain separate.
-/

namespace PakFixedPolyomino.StandardMachineScannerCounts

open StandardNondeterministicMachine
open StandardMachineZipperBridge (toBounded)
open StandardMachineWindowBridge
open ULogSourceObliviousLogicalRuns ULogSourceObliviousAcceptedCycles
open ULogSourceObliviousCycleTraces ULogSourceObliviousUpdateExecution

variable {ns nt : ℕ}

def OrdinaryAcceptedWords (M : Machine ns nt 2) (x : List Bool) (n : ℕ) :=
  {word : List (Fin 2) // word.length = n ∧ Accepted M x word}

instance ordinaryWords_finite (M : Machine ns nt 2) (x : List Bool) (n : ℕ) :
    Finite (OrdinaryAcceptedWords M x n) := by
  apply Finite.of_injective (fun word : OrdinaryAcceptedWords M x n =>
    WordCode.ofList (bound := n) word.1 (Nat.le_of_eq word.2.1))
  intro a b heq
  apply Subtype.ext
  have hword := congrArg WordCode.toList heq
  simpa using hword

def toLogicalAccepted (M : Machine ns nt 2) (x : List Bool)
    (bound n : ℕ) (hn : n ≤ bound) (word : OrdinaryAcceptedWords M x n) :
    AcceptedLogicalWords (toBounded M) n M.start M.accept (inputWindow M x bound) := by
  have ha : ∃ encoded, ULogSourceObliviousLogicalRuns.run (toBounded M) word.1
      (M.start, inputWindow M x bound) = some encoded ∧ encoded.1 = M.accept := by
    obtain ⟨out, hrun, hacc⟩ := (accepted_iff M x word.1).mp word.2.2
    obtain ⟨hout, hwrun⟩ := initialized_run_window M x bound word.1 out
      (Nat.le_trans (Nat.le_of_eq word.2.1) hn) hrun
    exact ⟨(out.state, window (inputOrigin bound) (inputSize x bound) out hout), hwrun, hacc⟩
  refine ⟨⟨word.1, word.2.1, ?_⟩, ha⟩
  obtain ⟨encoded, hrun, _⟩ := ha
  exact ⟨encoded, hrun⟩

noncomputable def ordinaryLogicalEquiv (M : Machine ns nt 2) (x : List Bool)
    (bound n : ℕ) (hn : n ≤ bound) :
    OrdinaryAcceptedWords M x n ≃
      AcceptedLogicalWords (toBounded M) n M.start M.accept (inputWindow M x bound) :=
  Equiv.ofBijective (toLogicalAccepted M x bound n hn) (by
    constructor
    · intro a b heq
      apply Subtype.ext
      exact congrArg (fun z => z.1.1) heq
    · intro word
      obtain ⟨out, hrun, hacc⟩ := word.2
      obtain ⟨actual, hactual, hactualrun, hout⟩ := run_window_inverse M word.1.1
        (inputOrigin bound) (inputSize x bound) (initial M x)
        (initial_headIn M x bound) out hrun
      have haccept : Accepted M x word.1.1 := (accepted_iff M x _).mpr
        ⟨actual, hactualrun, by rw [hout] at hacc; exact hacc⟩
      let original : OrdinaryAcceptedWords M x n := ⟨word.1.1, word.1.2.1, haccept⟩
      exact ⟨original, Subtype.ext (Subtype.ext rfl)⟩)

noncomputable def ordinaryScannerEquiv (M : Machine ns nt 2) (x : List Bool)
    (bound n : ℕ) (hn : n ≤ bound) (exterior : Int → Phys) :
    OrdinaryAcceptedWords M x n ≃
      AcceptedRawCycles (toBounded M) (Nat.zero_lt_of_lt M.blank.isLt) M.blank
        exterior n M.start M.accept (inputWindow M x bound) :=
  (ordinaryLogicalEquiv M x bound n hn).trans
    (acceptedEquiv (toBounded M) (Nat.zero_lt_of_lt M.blank.isLt) M.blank
      exterior n M.start M.accept (inputWindow M x bound))

theorem ordinary_raw_count_eq (M : Machine ns nt 2) (x : List Bool)
    (bound n : ℕ) (hn : n ≤ bound) (exterior : Int → Phys) :
    Nat.card (AcceptedRawCycles (toBounded M) (Nat.zero_lt_of_lt M.blank.isLt) M.blank
      exterior n M.start M.accept (inputWindow M x bound)) =
        Nat.card (OrdinaryAcceptedWords M x n) :=
  Nat.card_congr (ordinaryScannerEquiv M x bound n hn exterior).symm

def ordinaryCodeEquiv (M : Machine ns nt 2) (x : List Bool) (bound : ℕ) :
    AcceptingCode M x bound ≃
      ((n : Fin (bound + 1)) × OrdinaryAcceptedWords M x n.val) where
  toFun code := ⟨code.1.1, ⟨code.1.toList, WordCode.toList_length code.1, code.2⟩⟩
  invFun word := ⟨WordCode.ofList word.2.1 (by
    have hn := word.1.isLt
    have hlen := word.2.2.1
    omega), by simpa using word.2.2.2⟩
  left_inv code := by
    apply Subtype.ext
    apply WordCode.toList_injective
    simp
  right_inv word := by
    rcases word with ⟨⟨n, hn⟩, raw, hlen, hacc⟩
    change raw.length = n at hlen
    subst n
    simp [WordCode.ofList, WordCode.toList]

abbrev AllRawAcceptingCycles (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (exterior : Int → Phys) :=
  (n : Fin (bound + 1)) ×
    AcceptedRawCycles (toBounded M) (Nat.zero_lt_of_lt M.blank.isLt) M.blank
      exterior n.val M.start M.accept (inputWindow M x bound)

noncomputable def codeRawEquiv (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (exterior : Int → Phys) :
    AcceptingCode M x bound ≃ AllRawAcceptingCycles M x bound exterior :=
  (ordinaryCodeEquiv M x bound).trans
    (Equiv.sigmaCongrRight fun n => ordinaryScannerEquiv M x bound n.val
      (Nat.le_of_lt_succ n.isLt) exterior)

theorem all_raw_accepting_count (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (exterior : Int → Phys) :
    acceptingCount M x bound = Nat.card (AllRawAcceptingCycles M x bound exterior) := by
  rw [acceptingCount, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (codeRawEquiv M x bound exterior)

/-- If bound is actual source time, the finite raw count covers EVERY ordinary
accepting leaf, including the empty leaf when the ordinary start accepts.
This is not yet a physical halting-leaf or full-frame count. -/
noncomputable def allLeavesRawEquiv (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (htime : RunsAtMost M x bound) (exterior : Int → Phys) :
    AcceptingLeaf M x ≃ AllRawAcceptingCycles M x bound exterior :=
  (acceptingLeavesEquiv M x bound htime).symm.trans (codeRawEquiv M x bound exterior)

theorem inputWindow_width (M : Machine ns nt 2) (x : List Bool) (bound : ℕ) :
    windowWidth (inputWindow M x bound) = (x.length + 2 * bound + 3) * (nt + 1) := by
  rw [windowWidth_eq, inputWindow_length]

theorem allRaw_word_injective (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (exterior : Int → Phys) :
    Function.Injective (fun raw : AllRawAcceptingCycles M x bound exterior => raw.2.1.1) := by
  rintro ⟨n, a⟩ ⟨m, b⟩ heq
  have ha := a.1.2.1
  have hb := b.1.2.1
  have hlen := congrArg List.length heq
  have hm : n = m := Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega)
    (ha.symm.trans (hlen.trans hb)))
  subst m
  have hab : a = b := Subtype.ext (Subtype.ext heq)
  subst b
  rfl

theorem all_raw_physical_length (M : Machine ns nt 2) (x : List Bool)
    (bound : ℕ) (exterior : Int → Phys)
    (raw : AllRawAcceptingCycles M x bound exterior) :
    raw.2.1.1.length = raw.1.val * (4 * ((x.length + 2 * bound + 3) * (nt + 1)) + 6) ∧
      raw.2.1.1.length ≤ bound * (4 * ((x.length + 2 * bound + 3) * (nt + 1)) + 6) := by
  have hlen := raw.2.1.2.1
  have heq : raw.2.1.1.length =
      raw.1.val * (4 * ((x.length + 2 * bound + 3) * (nt + 1)) + 6) := by
    simpa only [inputWindow_width] using hlen
  exact ⟨heq, heq.le.trans (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ raw.1.isLt))⟩

end PakFixedPolyomino.StandardMachineScannerCounts
