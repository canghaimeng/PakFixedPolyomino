import PakFixedPolyomino.PakSideScanner
import Mathlib.Tactic

/-!
# Explicit local costs for the parser--copier front end

This file deliberately records *run equalities*, rather than choosing the
least successful fuel.  Thus every bound below is an executable natural
number attached to a literal microcode phase.  The copier ledger is complete
through its eight-round, group, payload, and final phases; the remaining local
work is the parser suffix and the final comparison with the encoded side.
No least-witness construction is used here.
-/

namespace PakFixedPolyomino.PakOuterFrontNumericBound

open MStarConcreteAlphabet
open MStarCopierExecution

/-! ## A parser prefix with its literal fuel -/

/-- Fuel for the fixed-padding and padding-scan prefix of the parser.
The bracketing follows the chronological composition of the four runs. -/
def parserPrefixFuel (x : ConcretePakSide.Word) : ℕ :=
  72 + (1 + (72 * x.length + 1))

theorem parserPrefixFuel_eq (x : ConcretePakSide.Word) :
    parserPrefixFuel x = 72 + (1 + (72 * x.length + 1)) := by
  rfl

theorem parserPrefixFuel_closed (x : ConcretePakSide.Word) :
    parserPrefixFuel x = 74 + 72 * x.length := by
  simp [parserPrefixFuel]
  omega

theorem parserPrefixFuel_lt_sideValue (x : ConcretePakSide.Word) :
    parserPrefixFuel x < ConcretePakSide.sideValue x := by
  have hspace := PakSideScanner.parserCells_le_sideScannerBits_length x
  rw [PakSideScanner.parserCells_length,
    PakSideScanner.sideScannerBits_length] at hspace
  rw [parserPrefixFuel_closed]
  omega

/-- The fixed initial padding has a 72-step literal trace. -/
theorem run_fixedPaddingPassed (x : ConcretePakSide.Word) :
    MStarParserExecution.run zero one work 72
      (MStarParserExecution.initial zero one work
        (ConcretePakSide.encodedWord x)) =
      fixedPaddingPassed x := by
  let right : List (MStarOuterProgram.Tape CoreTape) :=
    List.replicate x.length (.core zero) ++
      .core one :: x.reverse.map (MStarParserExecution.bitCell zero one) ++
        [.core one, .core work]
  have hpad : ConcretePakSide.paddingLength x.length = 72 + 72 * x.length := by
    simp [ConcretePakSide.paddingLength]
    omega
  have h72 : List.replicate 72
      (MStarOuterProgram.Tape.core zero) =
      .core zero :: List.replicate 71 (.core zero) := by
    norm_num [List.replicate_succ]
  have hcells : MStarParserExecution.inputCells zero one work
      (ConcretePakSide.encodedWord x) =
      .core zero ::
        (List.replicate 71 (.core zero) ++
          List.replicate (72 * x.length) (.core zero) ++ .core one :: right) := by
    rw [MStarParserExecution.inputCells_encodedWord, hpad,
      List.replicate_add, h72]
    simp [right, List.append_assoc]
  have hinit : MStarParserExecution.initial zero one work
      (ConcretePakSide.encodedWord x) =
      .running (MStarParserMicrocode.fixed 0)
        ⟨[], .core zero,
          List.replicate 71 (.core zero) ++
            List.replicate (72 * x.length) (.core zero) ++ .core one :: right⟩ := by
    unfold MStarParserExecution.initial
    rw [hcells]
  have htarget : fixedPaddingPassed x =
      .running (MStarParserMicrocode.fixed ⟨72, by decide⟩)
        (beforeScanZeros (72 * x.length) fixedPaddingTail (.core one) right) := by
    simp [fixedPaddingPassed, right, List.append_assoc]
  rw [hinit, htarget]
  exact run_fixed_72_beforeScanZeros (72 * x.length) (.core one) right

theorem run_paddingScanStarted (x : ConcretePakSide.Word) :
    MStarParserExecution.run zero one work 1 (fixedPaddingPassed x) =
      paddingScanStarted x := by
  change MStarParserExecution.oneStep zero one work (fixedPaddingPassed x) =
    paddingScanStarted x
  unfold fixedPaddingPassed paddingScanStarted
  exact oneStep_fixed_72 _

theorem run_paddingScanAtSeparator (x : ConcretePakSide.Word) :
    MStarParserExecution.run zero one work (72 * x.length)
      (paddingScanStarted x) = paddingScanAtSeparator x := by
  simpa [paddingScanStarted, paddingScanAtSeparator] using
    (run_scanPad_zeros (72 * x.length) fixedPaddingTail (.core one)
      (List.replicate x.length
          (MStarOuterProgram.Tape.core zero : MStarOuterProgram.Tape CoreTape) ++
        (.core one ::
          (x.reverse.map (MStarParserExecution.bitCell zero one) ++
            [.core one, .core work]))))

theorem run_lenStarted (x : ConcretePakSide.Word) :
    MStarParserExecution.run zero one work 1 (paddingScanAtSeparator x) =
      lenStarted x.length
        (x.reverse.map (MStarParserExecution.bitCell zero one) ++
          [.core one, .core work]) := by
  cases x with
  | nil =>
      simp [MStarParserExecution.run, paddingScanAtSeparator, afterScanZeros,
        lenStarted, MStarParserExecution.beforeRightRepeat, fixedPaddingTail,
        oneStep_scanPad_separator]
  | cons b bs =>
      simp [MStarParserExecution.run, paddingScanAtSeparator, afterScanZeros,
        lenStarted, MStarParserExecution.beforeRightRepeat, fixedPaddingTail,
        oneStep_scanPad_separator, List.replicate_succ, List.append_assoc]

theorem parserPrefix_runs (x : ConcretePakSide.Word) :
    MStarParserExecution.run zero one work (parserPrefixFuel x)
      (MStarParserExecution.initial zero one work
        (ConcretePakSide.encodedWord x)) =
      lenStarted x.length
        (x.reverse.map (MStarParserExecution.bitCell zero one) ++
          [.core one, .core work]) := by
  rw [parserPrefixFuel_eq, MStarParserExecution.run_add,
    run_fixedPaddingPassed, MStarParserExecution.run_add,
    run_paddingScanStarted, MStarParserExecution.run_add,
    run_paddingScanAtSeparator, run_lenStarted]

/-! ## Exact recurrence for one unary copier pass -/

/-- The literal cost of moving one old unary cell through a doubling round. -/
def copierProcessOneFuel (processed remaining : ℕ) : ℕ :=
  processed + (1 + ((seekCells processed remaining).length +
    (2 + ((returnCells processed remaining).length + 1))))

theorem copierProcessOneFuel_closed (processed remaining : ℕ) :
    copierProcessOneFuel processed remaining = 4 * processed + 2 * remaining + 6 := by
  simp [copierProcessOneFuel, seekCells, returnCells]
  omega

theorem run_process_one (r : Fin 8) (processed remaining : ℕ)
    (tail source : List MStarCopierMicrocode.ConcreteTape) :
    MStarCopierExecution.run (copierProcessOneFuel processed remaining)
      (roundStage r processed (remaining + 1) tail source) =
      roundStage r (processed + 1) remaining tail source := by
  have h0 : MStarCopierExecution.run processed
      (roundStage r processed (remaining + 1) tail source) =
      atOld r processed remaining tail source := by
    have hrun := MStarCopierExecution.run_findOld_B r processed (.markL :: source)
      MStarCopierMicrocode.cellA
      (List.replicate remaining MStarCopierMicrocode.cellA ++
        List.replicate processed MStarCopierMicrocode.cellB ++
        .markR :: List.replicate (remaining + 1)
          (.core MStarConcreteAlphabet.work) ++ tail)
    cases processed with
    | zero =>
        simpa [MStarCopierExecution.roundStage, MStarCopierExecution.atOld,
          MStarCopierExecution.beforeRightRepeat] using hrun
    | succ processed =>
        simpa [MStarCopierExecution.roundStage, MStarCopierExecution.atOld,
          MStarCopierExecution.beforeRightRepeat,
          List.replicate_succ, List.append_assoc] using hrun
  have h1 : MStarCopierExecution.run 1
      (atOld r processed remaining tail source) =
      seekStarted r processed remaining tail source := by
    cases processed <;> cases remaining <;>
      simp [MStarCopierExecution.run, MStarCopierExecution.atOld,
        MStarCopierExecution.seekStarted, MStarCopierExecution.seekCells,
        MStarCopierExecution.afterRightRepeat,
        MStarCopierExecution.beforeRightList,
        MStarCopierExecution.findOld_A_step,
        List.replicate_succ, List.append_assoc]
  have h2 : MStarCopierExecution.run (seekCells processed remaining).length
      (seekStarted r processed remaining tail source) =
      atBoundary r processed remaining tail source := by
    apply MStarCopierExecution.run_right_list_of (.seekBoundary r)
      (seekCells processed remaining)
    intro x hx left y right
    have hcell : x = MStarCopierMicrocode.cellA ∨
        x = MStarCopierMicrocode.cellB := by
      simp [seekCells] at hx
      rcases hx with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    exact MStarCopierExecution.seekBoundary_cell_step r x hcell left y right
  have h3 : MStarCopierExecution.run 2
      (atBoundary r processed remaining tail source) =
      returnStarted r processed remaining tail source := by
    cases processed <;> cases remaining <;>
      simp [MStarCopierExecution.run, MStarCopierExecution.atBoundary,
        MStarCopierExecution.returnStarted, MStarCopierExecution.returnCells,
        MStarCopierExecution.seekCells, MStarCopierExecution.afterRightList,
        MStarCopierExecution.beforeLeftList,
        MStarCopierExecution.seekBoundary_end_step,
        MStarCopierExecution.placeBoundary_step, List.replicate_succ,
        List.append_assoc] <;>
      rw [← List.append_assoc, ← List.replicate_add]
  have h4 : MStarCopierExecution.run (returnCells processed remaining).length
      (returnStarted r processed remaining tail source) =
      returnedToMark r processed remaining tail source := by
    apply MStarCopierExecution.run_left_list_of (.returnLeft r)
      (returnCells processed remaining)
    intro x hx left y right
    have hcell : x = MStarCopierMicrocode.cellA ∨
        x = MStarCopierMicrocode.cellB := by
      simp [returnCells, seekCells] at hx
      aesop
    exact MStarCopierExecution.returnLeft_cell_step r x hcell left y right
  have h5 : MStarCopierExecution.run 1
      (returnedToMark r processed remaining tail source) =
      roundStage r (processed + 1) remaining tail source := by
    cases processed <;>
      simp [MStarCopierExecution.run, MStarCopierExecution.returnedToMark,
        MStarCopierExecution.roundStage, MStarCopierExecution.returnCells,
        MStarCopierExecution.seekCells, MStarCopierExecution.afterLeftList,
        MStarCopierExecution.returnLeft_mark_step, List.reverse_append,
        List.replicate_succ, MStarConcreteAlphabet.replicate_cons_rotate,
        List.append_assoc]
  simp only [copierProcessOneFuel]
  rw [MStarCopierExecution.run_add, h0, MStarCopierExecution.run_add, h1,
    MStarCopierExecution.run_add, h2, MStarCopierExecution.run_add, h3,
    MStarCopierExecution.run_add, h4, h5]

/-- Accumulated exact fuel for the remaining unary cells of one round. -/
def copierProcessAllFuel : ℕ → ℕ → ℕ
  | _, 0 => 0
  | processed, remaining + 1 =>
      copierProcessOneFuel processed remaining +
        copierProcessAllFuel (processed + 1) remaining

theorem copierProcessAllFuel_closed (processed remaining : ℕ) :
    copierProcessAllFuel processed remaining =
      4 * processed * remaining + 3 * remaining * remaining + 3 * remaining := by
  induction remaining generalizing processed with
  | zero => simp [copierProcessAllFuel]
  | succ remaining ih =>
      rw [copierProcessAllFuel, copierProcessOneFuel_closed, ih]
      ring

theorem run_process_all (r : Fin 8) (processed remaining : ℕ)
    (tail source : List MStarCopierMicrocode.ConcreteTape) :
    MStarCopierExecution.run (copierProcessAllFuel processed remaining)
      (roundStage r processed remaining tail source) =
      roundStage r (processed + remaining) 0 tail source := by
  induction remaining generalizing processed with
  | zero => simp [copierProcessAllFuel]
  | succ remaining ih =>
      rw [copierProcessAllFuel, MStarCopierExecution.run_add,
        run_process_one]
      simpa only [Nat.add_assoc, Nat.succ_eq_add_one, Nat.add_comm,
        Nat.add_left_comm] using ih (processed + 1)

/-! ## The rest of one literal doubling round -/

/-- Fuel after the unary pass for finding the boundary and entering the
normalization sweep. -/
def copierNormalizeEntryFuel (n : ℕ) : ℕ := 2 * n + 1

theorem run_normalizeStarted (r : Fin 8) (n : ℕ) (hn : 0 < n)
    (tail source : List MStarCopierMicrocode.ConcreteTape) :
    MStarCopierExecution.run (copierNormalizeEntryFuel n)
      (roundStage r n 0 tail source) =
      normalizeStarted r n tail source := by
  let atEnd : MStarCopierExecution.Result :=
    .running (.findOld r)
      (MStarCopierExecution.afterRightRepeat (2 * n)
        MStarCopierMicrocode.cellB (.markL :: source) .markR tail)
  have hfind : MStarCopierExecution.run (2 * n)
      (roundStage r n 0 tail source) = atEnd := by
    have hrun := MStarCopierExecution.run_findOld_B r (2 * n)
      (.markL :: source) .markR tail
    cases n with
    | zero => omega
    | succ n =>
        have hstage : roundStage r (n + 1) 0 tail source =
            .running (.findOld r)
              (MStarCopierExecution.beforeRightRepeat (2 * (n + 1))
                MStarCopierMicrocode.cellB (.markL :: source) .markR tail) := by
          unfold MStarCopierExecution.roundStage
            MStarCopierExecution.beforeRightRepeat
          rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
          apply congrArg (MStarCopierExecution.Result.running (.findOld r))
          apply MStarParserExecution.Zipper.ext <;> simp only
          simp only [List.replicate_zero, List.nil_append, List.append_nil]
          rw [← List.replicate_add]
          rw [show n + (n + 1) = 2 * n + 1 by omega]
          simp [List.append_assoc]
        rw [hstage]
        exact hrun
  have hboundary : MStarCopierExecution.run 1 atEnd =
      normalizeStarted r n tail source := by
    cases n with
    | zero => omega
    | succ n =>
        unfold atEnd MStarCopierExecution.normalizeStarted
        rw [show 2 * (n + 1) = (2 * (n + 1) - 1) + 1 by omega]
        simp [MStarCopierExecution.afterRightRepeat,
          MStarCopierExecution.beforeLeftRepeat,
          MStarCopierExecution.findOld_boundary_step,
          List.replicate_add, List.replicate_succ, List.append_assoc]
  unfold copierNormalizeEntryFuel
  rw [MStarCopierExecution.run_add, hfind, hboundary]

theorem run_normalizedAtMark (r : Fin 8) (n : ℕ)
    (tail source : List MStarCopierMicrocode.ConcreteTape) :
    MStarCopierExecution.run (2 * n) (normalizeStarted r n tail source) =
      normalizedAtMark r n tail source := by
  simpa [MStarCopierExecution.normalizeStarted,
    MStarCopierExecution.normalizedAtMark] using
    (MStarCopierExecution.run_normalize_B r (2 * n) source .markL
      (.markR :: tail))

theorem run_roundCompleted (r : Fin 8) (n : ℕ)
    (tail source : List MStarCopierMicrocode.ConcreteTape) :
    MStarCopierExecution.run 1 (normalizedAtMark r n tail source) =
      roundCompleted r n tail source := by
  change MStarCopierExecution.oneStep (normalizedAtMark r n tail source) =
    roundCompleted r n tail source
  unfold MStarCopierExecution.normalizedAtMark
    MStarCopierExecution.roundCompleted MStarCopierExecution.oneStep
    MStarCopierMicrocode.copierStep
  by_cases hr : r.1 < 7
  · rw [dif_pos hr]
    by_cases hn : n = 0
    · subst n
      simp [hr, MStarCopierMicrocode.cellB, MStarCopierMicrocode.copyGo,
        MStarParserExecution.applyAction, List.replicate_succ]
    · rw [show 2 * n = (2 * n - 1) + 1 by omega]
      simp [hr, MStarCopierMicrocode.cellB, MStarCopierMicrocode.copyGo,
        MStarParserExecution.applyAction, List.replicate_succ]
  · rw [dif_neg hr]
    simp [hr, MStarCopierMicrocode.cellB, MStarCopierMicrocode.copyGo,
      MStarParserExecution.applyAction, List.replicate_succ]

/-- Complete cost of one unary-doubling round, up to its round-complete
control state. -/
def copierDoubleRoundFuel (n : ℕ) : ℕ :=
  copierProcessAllFuel 0 n + (copierNormalizeEntryFuel n + (2 * n + 1))

theorem copierDoubleRoundFuel_closed (n : ℕ) :
    copierDoubleRoundFuel n = 3 * n * n + 7 * n + 2 := by
  rw [copierDoubleRoundFuel, copierProcessAllFuel_closed]
  simp [copierNormalizeEntryFuel]
  ring

theorem run_doubleRound_completed (r : Fin 8) (n : ℕ) (hn : 0 < n)
    (tail source : List MStarCopierMicrocode.ConcreteTape) :
    MStarCopierExecution.run (copierDoubleRoundFuel n)
      (roundStage r 0 n
        (List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail)
        source) =
      roundCompleted r n
        (List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail)
        source := by
  unfold copierDoubleRoundFuel
  rw [MStarCopierExecution.run_add, run_process_all]
  simp only [Nat.zero_add]
  rw [MStarCopierExecution.run_add, run_normalizeStarted r n hn,
    MStarCopierExecution.run_add, run_normalizedAtMark, run_roundCompleted]

theorem run_doubleRound_next (r : Fin 8) (n : ℕ) (hn : 0 < n)
    (hr : r.1 < 7) (tail source : List MStarCopierMicrocode.ConcreteTape) :
    MStarCopierExecution.run (copierDoubleRoundFuel n)
      (roundStage r 0 n
        (List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail)
        source) =
      roundStage (MStarCopierMicrocode.nextRound r hr) 0 (2 * n) tail source := by
  rw [run_doubleRound_completed r n hn]
  exact MStarCopierExecution.roundCompleted_eq_next r n hn hr tail source

theorem run_doubleRound_final (r : Fin 8) (n : ℕ) (hn : 0 < n)
    (hr : ¬ r.1 < 7) (tail source : List MStarCopierMicrocode.ConcreteTape) :
    MStarCopierExecution.run (copierDoubleRoundFuel n)
      (roundStage r 0 n
        (List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail)
        source) =
      .running .groupDone (doubledGroupZipper n tail source) := by
  rw [run_doubleRound_completed r n hn]
  simp [MStarCopierExecution.roundCompleted,
    MStarCopierExecution.doubledGroupZipper, hr, List.append_assoc]

/-- Chronologically bracketed cost of the eight literal unary-doubling
rounds which multiply a block width by `256`. -/
def copierEightRoundFuel (n : ℕ) : ℕ :=
  copierDoubleRoundFuel n +
    (copierDoubleRoundFuel (2 * n) +
      (copierDoubleRoundFuel (4 * n) +
        (copierDoubleRoundFuel (8 * n) +
          (copierDoubleRoundFuel (16 * n) +
            (copierDoubleRoundFuel (32 * n) +
              (copierDoubleRoundFuel (64 * n) +
                copierDoubleRoundFuel (128 * n)))))))

theorem copierEightRoundFuel_closed (n : ℕ) :
    copierEightRoundFuel n = 65535 * n * n + 1785 * n + 16 := by
  simp only [copierEightRoundFuel, copierDoubleRoundFuel_closed]
  ring

theorem run_eight_doublings (n : ℕ) (hn : 0 < n)
    (tail source : List MStarCopierMicrocode.ConcreteTape) :
    MStarCopierExecution.run (copierEightRoundFuel n)
      (roundStage 0 0 n (eightRoundReserve n tail) source) =
      .running .groupDone
        ⟨source, .markL,
          List.replicate (256 * n) MStarCopierMicrocode.cellA ++ .markR ::
            List.replicate (256 * n) (.core MStarConcreteAlphabet.work) ++ tail⟩ := by
  let t₁ : List MStarCopierMicrocode.ConcreteTape :=
    List.replicate (4 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (8 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (16 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (32 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (64 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (128 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (256 * n) (.core MStarConcreteAlphabet.work) ++ tail
  let t₂ : List MStarCopierMicrocode.ConcreteTape :=
    List.replicate (8 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (16 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (32 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (64 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (128 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (256 * n) (.core MStarConcreteAlphabet.work) ++ tail
  let t₃ : List MStarCopierMicrocode.ConcreteTape :=
    List.replicate (16 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (32 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (64 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (128 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (256 * n) (.core MStarConcreteAlphabet.work) ++ tail
  let t₄ : List MStarCopierMicrocode.ConcreteTape :=
    List.replicate (32 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (64 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (128 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (256 * n) (.core MStarConcreteAlphabet.work) ++ tail
  let t₅ : List MStarCopierMicrocode.ConcreteTape :=
    List.replicate (64 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (128 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (256 * n) (.core MStarConcreteAlphabet.work) ++ tail
  let t₆ : List MStarCopierMicrocode.ConcreteTape :=
    List.replicate (128 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (256 * n) (.core MStarConcreteAlphabet.work) ++ tail
  let t₇ : List MStarCopierMicrocode.ConcreteTape :=
    List.replicate (256 * n) (.core MStarConcreteAlphabet.work) ++ tail
  have ht₁ : t₁ = List.replicate (4 * n) (.core MStarConcreteAlphabet.work) ++
      t₂ := by
    dsimp [t₁, t₂]
    simp only [List.append_assoc]
  have ht₂ : t₂ = List.replicate (8 * n) (.core MStarConcreteAlphabet.work) ++
      t₃ := by
    dsimp [t₂, t₃]
    simp only [List.append_assoc]
  have ht₃ : t₃ = List.replicate (16 * n) (.core MStarConcreteAlphabet.work) ++
      t₄ := by
    dsimp [t₃, t₄]
    simp only [List.append_assoc]
  have ht₄ : t₄ = List.replicate (32 * n) (.core MStarConcreteAlphabet.work) ++
      t₅ := by
    dsimp [t₄, t₅]
    simp only [List.append_assoc]
  have ht₅ : t₅ = List.replicate (64 * n) (.core MStarConcreteAlphabet.work) ++
      t₆ := by
    dsimp [t₅, t₆]
    simp only [List.append_assoc]
  have ht₆ : t₆ = List.replicate (128 * n) (.core MStarConcreteAlphabet.work) ++
      t₇ := by
    dsimp [t₆, t₇]
    simp only [List.append_assoc]
  have h₀ : MStarCopierExecution.run (copierDoubleRoundFuel n)
      (roundStage 0 0 n (List.replicate (2 * n)
        (.core MStarConcreteAlphabet.work) ++ t₁) source) =
      roundStage 1 0 (2 * n) t₁ source := by
    simpa [MStarCopierMicrocode.nextRound] using
      run_doubleRound_next (0 : Fin 8) n hn (by decide) t₁ source
  have h₁ : MStarCopierExecution.run (copierDoubleRoundFuel (2 * n))
      (roundStage 1 0 (2 * n) (List.replicate (4 * n)
        (.core MStarConcreteAlphabet.work) ++ t₂) source) =
      roundStage 2 0 (4 * n) t₂ source := by
    have h := run_doubleRound_next (1 : Fin 8) (2 * n) (by omega)
      (by decide) t₂ source
    rw [show 2 * (2 * n) = 4 * n by ring] at h
    simpa [MStarCopierMicrocode.nextRound] using h
  have h₂ : MStarCopierExecution.run (copierDoubleRoundFuel (4 * n))
      (roundStage 2 0 (4 * n) (List.replicate (8 * n)
        (.core MStarConcreteAlphabet.work) ++ t₃) source) =
      roundStage 3 0 (8 * n) t₃ source := by
    have h := run_doubleRound_next (2 : Fin 8) (4 * n) (by omega)
      (by decide) t₃ source
    rw [show 2 * (4 * n) = 8 * n by ring] at h
    simpa [MStarCopierMicrocode.nextRound] using h
  have h₃ : MStarCopierExecution.run (copierDoubleRoundFuel (8 * n))
      (roundStage 3 0 (8 * n) (List.replicate (16 * n)
        (.core MStarConcreteAlphabet.work) ++ t₄) source) =
      roundStage 4 0 (16 * n) t₄ source := by
    have h := run_doubleRound_next (3 : Fin 8) (8 * n) (by omega)
      (by decide) t₄ source
    rw [show 2 * (8 * n) = 16 * n by ring] at h
    simpa [MStarCopierMicrocode.nextRound] using h
  have h₄ : MStarCopierExecution.run (copierDoubleRoundFuel (16 * n))
      (roundStage 4 0 (16 * n) (List.replicate (32 * n)
        (.core MStarConcreteAlphabet.work) ++ t₅) source) =
      roundStage 5 0 (32 * n) t₅ source := by
    have h := run_doubleRound_next (4 : Fin 8) (16 * n) (by omega)
      (by decide) t₅ source
    rw [show 2 * (16 * n) = 32 * n by ring] at h
    simpa [MStarCopierMicrocode.nextRound] using h
  have h₅ : MStarCopierExecution.run (copierDoubleRoundFuel (32 * n))
      (roundStage 5 0 (32 * n) (List.replicate (64 * n)
        (.core MStarConcreteAlphabet.work) ++ t₆) source) =
      roundStage 6 0 (64 * n) t₆ source := by
    have h := run_doubleRound_next (5 : Fin 8) (32 * n) (by omega)
      (by decide) t₆ source
    rw [show 2 * (32 * n) = 64 * n by ring] at h
    simpa [MStarCopierMicrocode.nextRound] using h
  have h₆ : MStarCopierExecution.run (copierDoubleRoundFuel (64 * n))
      (roundStage 6 0 (64 * n) (List.replicate (128 * n)
        (.core MStarConcreteAlphabet.work) ++ t₇) source) =
      roundStage 7 0 (128 * n) t₇ source := by
    have h := run_doubleRound_next (6 : Fin 8) (64 * n) (by omega)
      (by decide) t₇ source
    rw [show 2 * (64 * n) = 128 * n by ring] at h
    simpa [MStarCopierMicrocode.nextRound] using h
  have h₇ : MStarCopierExecution.run (copierDoubleRoundFuel (128 * n))
      (roundStage 7 0 (128 * n) t₇ source) =
      .running .groupDone
        ⟨source, .markL,
          List.replicate (256 * n) MStarCopierMicrocode.cellA ++ .markR ::
            List.replicate (256 * n) (.core MStarConcreteAlphabet.work) ++ tail⟩ := by
    have h := run_doubleRound_final (7 : Fin 8) (128 * n) (by omega)
      (by decide) tail source
    have hdouble : 2 * (128 * n) = 256 * n := by ring
    simp only [MStarCopierExecution.doubledGroupZipper, hdouble] at h
    simpa only [t₇] using h
  have hstart : roundStage 0 0 n (eightRoundReserve n tail) source =
      roundStage 0 0 n (List.replicate (2 * n)
        (.core MStarConcreteAlphabet.work) ++ t₁) source := by
    simp only [MStarCopierExecution.eightRoundReserve, t₁, List.append_assoc]
  rw [hstart, copierEightRoundFuel]
  rw [MStarCopierExecution.run_add, h₀, ht₁,
    MStarCopierExecution.run_add, h₁, ht₂,
    MStarCopierExecution.run_add, h₂, ht₃,
    MStarCopierExecution.run_add, h₃, ht₄,
    MStarCopierExecution.run_add, h₄, ht₅,
    MStarCopierExecution.run_add, h₅, ht₆,
    MStarCopierExecution.run_add, h₆, h₇]

/-! ## Restarting one payload-length group -/

theorem groupPrefix_length (bits : List Bool) (done : ℕ) :
    (groupPrefix bits done).length = bits.length + done + 2 := by
  simp [MStarCopierExecution.groupPrefix]
  omega

def copierGroupRestartFuel (bits : List Bool) (done : ℕ) : ℕ :=
  1 + ((groupPrefix bits done).length +
    (1 + ((groupPrefix bits done).length + 1)))

theorem copierGroupRestartFuel_closed (bits : List Bool) (done : ℕ) :
    copierGroupRestartFuel bits done = 2 * (bits.length + done + 2) + 3 := by
  rw [copierGroupRestartFuel, groupPrefix_length]
  ring

theorem run_restart_next_group (bits : List Bool) (done remaining : ℕ)
    (junk : List MStarCopierMicrocode.ConcreteTape) (n : ℕ) (hn : 0 < n)
    (reserve : List MStarCopierMicrocode.ConcreteTape) :
    MStarCopierExecution.run (copierGroupRestartFuel bits done)
      (.running .groupDone
        ⟨groupSource bits done (remaining + 1) junk, .markL,
          List.replicate n MStarCopierMicrocode.cellA ++ .markR ::
            List.replicate n (.core MStarConcreteAlphabet.work) ++ reserve⟩) =
      roundStage 0 0 n reserve
        (groupSource bits (done + 1) remaining junk) := by
  let blockRight : List MStarCopierMicrocode.ConcreteTape :=
    List.replicate n MStarCopierMicrocode.cellA ++ .markR ::
      List.replicate n (.core MStarConcreteAlphabet.work) ++ reserve
  have h0 : MStarCopierExecution.run 1
      (.running .groupDone
        ⟨groupSource bits done (remaining + 1) junk, .markL, blockRight⟩) =
      groupSeekStarted bits done remaining junk blockRight := by
    change MStarCopierExecution.oneStep
      (.running .groupDone
        ⟨groupSource bits done (remaining + 1) junk, .markL, blockRight⟩) = _
    simp [MStarCopierExecution.groupSource, MStarCopierExecution.groupPrefix,
      MStarCopierExecution.groupSeekStarted,
      MStarCopierExecution.beforeLeftList,
      MStarCopierExecution.groupDone_step, List.replicate_succ,
      List.append_assoc]
  have h1 : MStarCopierExecution.run (groupPrefix bits done).length
      (groupSeekStarted bits done remaining junk blockRight) =
      groupAtPaired bits done remaining junk blockRight := by
    apply MStarCopierExecution.run_left_list_of .groupSeekLen
      (groupPrefix bits done)
    intro x hx left y right
    have hpass : x = MStarParserMicrocode.endpointMark ∨
        x = MStarParserMicrocode.payloadZero ∨
        x = MStarParserMicrocode.payloadOne ∨ x = MStarParserMicrocode.sepLen ∨
        x = MStarParserMicrocode.lenDone := by
      simp [MStarCopierExecution.groupPrefix] at hx
      rcases hx with rfl | hx | rfl | ⟨-, rfl⟩
      · exact Or.inl rfl
      · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
          simp [MStarConcreteAlphabet.payloadMarker]
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    exact MStarCopierExecution.groupSeek_pass_step x hpass left y right
  have h2 : MStarCopierExecution.run 1
      (groupAtPaired bits done remaining junk blockRight) =
      groupReturnStarted bits done remaining junk blockRight := by
    change MStarCopierExecution.oneStep
      (groupAtPaired bits done remaining junk blockRight) = _
    have hne : (groupPrefix bits done).reverse ≠ [] := by
      simp [MStarCopierExecution.groupPrefix]
    cases hrev : (groupPrefix bits done).reverse with
    | nil => exact (hne hrev).elim
    | cons x xs =>
        simp [MStarCopierExecution.groupAtPaired,
          MStarCopierExecution.groupReturnStarted,
          MStarCopierExecution.afterLeftList,
          MStarCopierExecution.beforeRightList, hrev,
          MStarCopierExecution.groupSeek_paired_step]
  have h3 : MStarCopierExecution.run (groupPrefix bits done).length
      (groupReturnStarted bits done remaining junk blockRight) =
      groupReturnedToMark bits done remaining junk blockRight := by
    rw [show (groupPrefix bits done).length =
      (groupPrefix bits done).reverse.length by simp]
    apply MStarCopierExecution.run_right_list_of .groupReturn
      (groupPrefix bits done).reverse
    intro x hx left y right
    have hx' : x ∈ groupPrefix bits done := by
      simpa using (List.mem_reverse.mp hx)
    have hpass : x = MStarParserMicrocode.lenDone ∨
        x = MStarParserMicrocode.sepLen ∨
        x = MStarParserMicrocode.payloadZero ∨
        x = MStarParserMicrocode.payloadOne ∨
        x = MStarParserMicrocode.endpointMark := by
      simp [MStarCopierExecution.groupPrefix] at hx'
      rcases hx' with rfl | hx | rfl | ⟨-, rfl⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
          simp [MStarConcreteAlphabet.payloadMarker]
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    exact MStarCopierExecution.groupReturn_pass_step x hpass left y right
  have h4 : MStarCopierExecution.run 1
      (groupReturnedToMark bits done remaining junk blockRight) =
      roundStage 0 0 n reserve
        (groupSource bits (done + 1) remaining junk) := by
    cases n with
    | zero => omega
    | succ n =>
        have hrotate := MStarCopierExecution.replicate_cons_rotate
          MStarParserMicrocode.lenDone done
          (List.replicate remaining MStarParserMicrocode.pairedLen ++
            MStarParserMicrocode.sepPad :: junk)
        have hreturned : groupReturnedToMark bits done remaining junk blockRight =
            .running .groupReturn
              ⟨groupSource bits (done + 1) remaining junk, .markL, blockRight⟩ := by
          unfold MStarCopierExecution.groupReturnedToMark
          apply congrArg (MStarCopierExecution.Result.running .groupReturn)
          apply MStarParserExecution.Zipper.ext
          · simpa [MStarCopierExecution.afterRightList,
              MStarCopierExecution.groupSource, MStarCopierExecution.groupPrefix,
              List.reverse_reverse, List.map_reverse, List.reverse_append,
              List.replicate_succ, List.append_assoc, hrotate]
          · rfl
          · rfl
        rw [hreturned]
        change MStarCopierExecution.oneStep
          (.running .groupReturn
            ⟨groupSource bits (done + 1) remaining junk, .markL, blockRight⟩) = _
        dsimp [blockRight]
        simpa [MStarCopierExecution.roundStage, List.replicate_succ,
          List.cons_append, List.append_assoc] using
          (MStarCopierExecution.groupReturn_mark_step
            (MStarCopierExecution.groupSource bits (done + 1) remaining junk)
            MStarCopierMicrocode.cellA
            (List.replicate n MStarCopierMicrocode.cellA ++
              (.markR :: .core MStarConcreteAlphabet.work ::
                (List.replicate n (.core MStarConcreteAlphabet.work) ++ reserve))))
  unfold copierGroupRestartFuel
  rw [show List.replicate n MStarCopierMicrocode.cellA ++ .markR ::
      List.replicate n (.core MStarConcreteAlphabet.work) ++ reserve =
        blockRight by rfl]
  rw [MStarCopierExecution.run_add, h0, MStarCopierExecution.run_add, h1,
    MStarCopierExecution.run_add, h2, MStarCopierExecution.run_add, h3, h4]

/-- Executable fuel recurrence for all still-unprocessed paired length
markers.  The width argument is multiplied by 256 after each group. -/
def copierGroupFoldFuel (bits : List Bool) : ℕ → ℕ → ℕ → ℕ
  | done, 0, _ => 0
  | done, groups + 1, n =>
      copierGroupRestartFuel bits done +
        (copierEightRoundFuel n +
          copierGroupFoldFuel bits (done + 1) groups (256 * n))

theorem run_group_fold (bits : List Bool) (done groups : ℕ)
    (junk : List MStarCopierMicrocode.ConcreteTape) (n : ℕ) (hn : 0 < n)
    (tail : List MStarCopierMicrocode.ConcreteTape) :
    MStarCopierExecution.run (copierGroupFoldFuel bits done groups n)
      (.running .groupDone
        ⟨groupSource bits done groups junk, .markL,
          List.replicate n MStarCopierMicrocode.cellA ++ .markR ::
            List.replicate n (.core MStarConcreteAlphabet.work) ++
              groupExtraReserve groups n tail⟩) =
      (.running .groupDone
        ⟨groupSource bits (done + groups) 0 junk, .markL,
          List.replicate (iteratedGroupWidth groups n) MStarCopierMicrocode.cellA ++
            .markR :: List.replicate (iteratedGroupWidth groups n)
              (.core MStarConcreteAlphabet.work) ++ tail⟩) := by
  induction groups generalizing done n with
  | zero => simp [copierGroupFoldFuel, MStarCopierExecution.groupExtraReserve,
      MStarCopierExecution.iteratedGroupWidth]
  | succ groups ih =>
      rw [copierGroupFoldFuel, MStarCopierExecution.groupExtraReserve]
      rw [MStarCopierExecution.run_add,
        run_restart_next_group bits done groups junk n hn
          (MStarCopierExecution.eightRoundReserve n
            (MStarCopierExecution.groupExtraReserve groups (256 * n) tail)),
        MStarCopierExecution.run_add,
        run_eight_doublings n hn
          (MStarCopierExecution.groupExtraReserve groups (256 * n) tail)
          (groupSource bits (done + 1) groups junk)]
      simpa [MStarCopierExecution.groupExtraReserve,
        MStarCopierExecution.iteratedGroupWidth, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using
        ih (done + 1) (256 * n) (by positivity)

/-! ## A closed coarse envelope for the group fold -/

/-- One number simultaneously bounds the source-prefix scan and every unary
width reached while the remaining `groups` are processed. -/
def copierGroupFoldEnvelope (bits : List Bool) (done groups n : ℕ) : ℕ :=
  bits.length + done + groups + 2 + 256 ^ groups * n

def copierGroupFoldStageBound (envelope : ℕ) : ℕ :=
  2 * envelope + 3 + (65535 * envelope * envelope + 1785 * envelope + 16)

theorem copierGroupFoldEnvelope_succ (bits : List Bool) (done groups n : ℕ) :
    copierGroupFoldEnvelope bits (done + 1) groups (256 * n) =
      copierGroupFoldEnvelope bits done (groups + 1) n := by
  simp [copierGroupFoldEnvelope, Nat.pow_succ]
  ring

theorem copierEightRoundFuel_le_envelope {n envelope : ℕ} (hn : n ≤ envelope) :
    copierEightRoundFuel n ≤
      65535 * envelope * envelope + 1785 * envelope + 16 := by
  rw [copierEightRoundFuel_closed]
  gcongr

theorem copierGroupRestartFuel_le_envelope (bits : List Bool) (done groups n : ℕ) :
    copierGroupRestartFuel bits done ≤
      2 * copierGroupFoldEnvelope bits done (groups + 1) n + 3 := by
  rw [copierGroupRestartFuel_closed]
  unfold copierGroupFoldEnvelope
  omega

theorem copierGroupFoldFuel_le_coarse (bits : List Bool) (done groups n : ℕ) :
    copierGroupFoldFuel bits done groups n ≤
      groups * copierGroupFoldStageBound
        (copierGroupFoldEnvelope bits done groups n) := by
  induction groups generalizing done n with
  | zero => simp [copierGroupFoldFuel]
  | succ groups ih =>
      let envelope := copierGroupFoldEnvelope bits done (groups + 1) n
      have hen : n ≤ envelope := by
        have hpow : 1 ≤ 256 ^ (groups + 1) :=
          Nat.one_le_pow (groups + 1) 256 (by decide)
        have hmul : n ≤ 256 ^ (groups + 1) * n := by
          simpa using Nat.mul_le_mul_right n hpow
        dsimp [envelope, copierGroupFoldEnvelope]
        exact hmul.trans (by omega)
      have hrestart : copierGroupRestartFuel bits done ≤ 2 * envelope + 3 := by
        simpa [envelope] using copierGroupRestartFuel_le_envelope bits done groups n
      have height : copierEightRoundFuel n ≤
          65535 * envelope * envelope + 1785 * envelope + 16 :=
        copierEightRoundFuel_le_envelope hen
      have hrec := ih (done + 1) (256 * n)
      have henv : copierGroupFoldEnvelope bits (done + 1) groups (256 * n) =
          envelope := by
        simpa [envelope] using copierGroupFoldEnvelope_succ bits done groups n
      rw [henv] at hrec
      unfold copierGroupFoldFuel
      change copierGroupRestartFuel bits done +
          (copierEightRoundFuel n +
            copierGroupFoldFuel bits (done + 1) groups (256 * n)) ≤ _
      have hstage : copierGroupRestartFuel bits done + copierEightRoundFuel n ≤
          copierGroupFoldStageBound envelope := by
        unfold copierGroupFoldStageBound
        exact Nat.add_le_add hrestart height
      calc
        copierGroupRestartFuel bits done +
            (copierEightRoundFuel n +
              copierGroupFoldFuel bits (done + 1) groups (256 * n)) ≤
            copierGroupFoldStageBound envelope +
              groups * copierGroupFoldStageBound envelope := by
          omega
        _ = (groups + 1) * copierGroupFoldStageBound envelope := by ring

/-! ## Literal fuel for one payload-copy iteration -/

def copierPayloadIterationFuel (copiedRev : List Bool) (processed n : ℕ) : ℕ :=
  (payloadPath copiedRev processed n).length +
    (1 + ((payloadPath copiedRev processed n).length + (1 + 1)))

theorem run_payload_iteration (b : Bool) (copiedRev : List Bool)
    (processed n : ℕ) (source : List MStarCopierMicrocode.ConcreteTape)
    (next : MStarCopierMicrocode.ConcreteTape)
    (right : List MStarCopierMicrocode.ConcreteTape) :
    MStarCopierExecution.run
      (copierPayloadIterationFuel copiedRev processed n)
      (payloadBefore copiedRev processed n (next :: source)
        (MStarConcreteAlphabet.payloadMarker b)
        (.core MStarConcreteAlphabet.work :: right)) =
      payloadBefore (b :: copiedRev) (processed + 1) n source next right := by
  have h0 : MStarCopierExecution.run (payloadPath copiedRev processed n).length
      (payloadBefore copiedRev processed n (next :: source)
        (MStarConcreteAlphabet.payloadMarker b)
        (.core MStarConcreteAlphabet.work :: right)) =
      payloadAtSource copiedRev processed n (next :: source)
        (MStarConcreteAlphabet.payloadMarker b)
        (.core MStarConcreteAlphabet.work :: right) := by
    apply MStarCopierExecution.run_left_list_of .payloadSeek
      (payloadPath copiedRev processed n)
    intro x hx left y trail
    exact MStarCopierExecution.payloadSeek_pass_step x
      (MStarCopierExecution.payloadPath_seek_pass copiedRev processed n x hx)
      left y trail
  have h1 : MStarCopierExecution.run 1
      (payloadAtSource copiedRev processed n (next :: source)
        (MStarConcreteAlphabet.payloadMarker b)
        (.core MStarConcreteAlphabet.work :: right)) =
      payloadCarryStarted b copiedRev processed n
        (next :: source) (.core MStarConcreteAlphabet.work :: right) := by
    change MStarCopierExecution.oneStep
      (payloadAtSource copiedRev processed n (next :: source)
        (MStarConcreteAlphabet.payloadMarker b)
        (.core MStarConcreteAlphabet.work :: right)) = _
    have hne : (payloadPath copiedRev processed n).reverse ≠ [] := by
      simp [MStarCopierExecution.payloadPath]
    cases hrev : (payloadPath copiedRev processed n).reverse with
    | nil => exact (hne hrev).elim
    | cons x xs =>
        simp [MStarCopierExecution.payloadAtSource,
          MStarCopierExecution.payloadCarryStarted,
          MStarCopierExecution.afterLeftList,
          MStarCopierExecution.beforeRightList, hrev,
          MStarCopierExecution.payloadSeek_marker_step]
  have h2 : MStarCopierExecution.run (payloadPath copiedRev processed n).length
      (payloadCarryStarted b copiedRev processed n
        (next :: source) (.core MStarConcreteAlphabet.work :: right)) =
      payloadAtBoundary b copiedRev processed n
        (next :: source) (.core MStarConcreteAlphabet.work :: right) := by
    rw [show (payloadPath copiedRev processed n).length =
      (payloadPath copiedRev processed n).reverse.length by simp]
    apply MStarCopierExecution.run_right_list_of (.payloadCarry b)
      (payloadPath copiedRev processed n).reverse
    intro x hx left y trail
    have hx' : x ∈ payloadPath copiedRev processed n := by
      simpa using (List.mem_reverse.mp hx)
    exact MStarCopierExecution.payloadCarry_pass_step b x
      (MStarCopierExecution.payloadPath_carry_pass copiedRev processed n x hx')
      left y trail
  have h3 : MStarCopierExecution.run 1
      (payloadAtBoundary b copiedRev processed n
        (next :: source) (.core MStarConcreteAlphabet.work :: right)) =
      .running .payloadPlace
        ⟨MStarCopierExecution.coreBit b :: payloadPath copiedRev processed n ++
            MStarParserMicrocode.lenDone :: next :: source,
          .core MStarConcreteAlphabet.work, right⟩ := by
    change MStarCopierExecution.oneStep
      (payloadAtBoundary b copiedRev processed n
        (next :: source) (.core MStarConcreteAlphabet.work :: right)) = _
    simp only [MStarCopierExecution.payloadAtBoundary,
      MStarCopierExecution.afterRightList, List.reverse_reverse]
    cases b <;> rfl
  have h4 : MStarCopierExecution.run 1
      (.running .payloadPlace
        ⟨MStarCopierExecution.coreBit b :: payloadPath copiedRev processed n ++
            MStarParserMicrocode.lenDone :: next :: source,
          .core MStarConcreteAlphabet.work, right⟩) =
      payloadBefore (b :: copiedRev) (processed + 1) n source next right := by
    change MStarCopierExecution.oneStep
      (.running .payloadPlace
        ⟨MStarCopierExecution.coreBit b :: payloadPath copiedRev processed n ++
            MStarParserMicrocode.lenDone :: next :: source,
          .core MStarConcreteAlphabet.work, right⟩) = _
    unfold MStarCopierExecution.payloadBefore
    rw [← MStarCopierExecution.payloadPath_next]
    simp [MStarCopierExecution.beforeLeftList,
      MStarCopierExecution.payloadPlace_step, List.append_assoc]
  unfold copierPayloadIterationFuel
  rw [MStarCopierExecution.run_add, h0, MStarCopierExecution.run_add, h1,
    MStarCopierExecution.run_add, h2, MStarCopierExecution.run_add, h3, h4]

def copierPayloadFoldFuel : List Bool → List Bool → ℕ → ℕ → ℕ
  | [], _, _, _ => 0
  | b :: bs, copiedRev, processed, n =>
      copierPayloadIterationFuel copiedRev processed n +
        copierPayloadFoldFuel bs (b :: copiedRev) (processed + 1) n

theorem run_payload_fold (todo copiedRev : List Bool)
    (processed n : ℕ) (source right : List MStarCopierMicrocode.ConcreteTape) :
    MStarCopierExecution.run (copierPayloadFoldFuel todo copiedRev processed n)
      (payloadLoop copiedRev processed n todo source
        (List.replicate todo.length (.core MStarConcreteAlphabet.work) ++ right)) =
      payloadLoop (todo.reverse ++ copiedRev) (processed + todo.length)
        n [] source right := by
  induction todo generalizing copiedRev processed with
  | nil => simp [copierPayloadFoldFuel, MStarCopierExecution.payloadLoop]
  | cons b bs ih =>
      have hstep : MStarCopierExecution.run
          (copierPayloadIterationFuel copiedRev processed n)
          (payloadLoop copiedRev processed n (b :: bs) source
            (List.replicate (b :: bs).length
              (.core MStarConcreteAlphabet.work) ++ right)) =
          payloadLoop (b :: copiedRev) (processed + 1) n bs source
            (List.replicate bs.length
              (.core MStarConcreteAlphabet.work) ++ right) := by
        cases bs with
        | nil =>
            simpa [MStarCopierExecution.payloadLoop,
              MStarCopierExecution.payloadBefore,
              MStarCopierExecution.payloadPath,
              List.replicate_succ, List.append_assoc] using
              (run_payload_iteration b copiedRev processed n source
                MStarParserMicrocode.sepLen right)
        | cons c cs =>
            convert run_payload_iteration b copiedRev processed n
              (cs.map MStarConcreteAlphabet.payloadMarker ++
                MStarParserMicrocode.sepLen :: source)
              (MStarConcreteAlphabet.payloadMarker c)
              (.core MStarConcreteAlphabet.work ::
                (List.replicate cs.length
                  (.core MStarConcreteAlphabet.work) ++ right)) using 1 <;>
              simp [MStarCopierExecution.payloadLoop,
                MStarCopierExecution.payloadBefore,
                MStarCopierExecution.payloadPath, List.map_reverse,
                List.replicate_succ, List.cons_append, List.append_assoc]
      rw [copierPayloadFoldFuel, MStarCopierExecution.run_add, hstep]
      have hrest := ih (b :: copiedRev) (processed + 1)
      have hnat : processed + 1 + bs.length =
          processed + (bs.length + 1) := by omega
      simpa [MStarCopierExecution.payloadLoop, List.reverse_cons,
        List.append_assoc, hnat] using hrest

theorem payloadPath_length (copiedRev : List Bool) (processed n : ℕ) :
    (payloadPath copiedRev processed n).length =
      copiedRev.length + processed + n + 3 := by
  simp [MStarCopierExecution.payloadPath]
  omega

theorem copierPayloadIterationFuel_closed (copiedRev : List Bool)
    (processed n : ℕ) :
    copierPayloadIterationFuel copiedRev processed n =
      2 * copiedRev.length + 2 * processed + 2 * n + 9 := by
  rw [copierPayloadIterationFuel, payloadPath_length]
  ring

theorem copierPayloadFoldFuel_closed (todo copiedRev : List Bool)
    (processed n : ℕ) :
    copierPayloadFoldFuel todo copiedRev processed n =
      2 * todo.length * copiedRev.length + 2 * todo.length * processed +
        2 * n * todo.length + 2 * todo.length * todo.length + 7 * todo.length := by
  induction todo generalizing copiedRev processed with
  | nil => simp [copierPayloadFoldFuel]
  | cons b bs ih =>
      rw [copierPayloadFoldFuel, copierPayloadIterationFuel_closed, ih]
      simp only [List.length_cons]
      ring

theorem copierPayloadFoldFuel_initial (todo : List Bool) (n : ℕ) :
    copierPayloadFoldFuel todo [] 0 n =
      2 * todo.length * todo.length + 2 * n * todo.length + 7 * todo.length := by
  rw [copierPayloadFoldFuel_closed]
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]
  ring

/-! ## Literal finalization after the payload loop -/

def copierFinalFuel (copiedRev : List Bool) (processed n : ℕ) : ℕ :=
  1 + ((doneReturnPrefix processed).length +
    (1 + ((finalForwardPath n copiedRev).length +
      (1 + (n + (1 + ((finalSpan n copiedRev).length + 1)))))))

theorem run_payload_final (copiedRev : List Bool) (processed n : ℕ)
    (source external : List MStarCopierMicrocode.ConcreteTape) :
    MStarCopierExecution.run (copierFinalFuel copiedRev processed n)
      (payloadAtSource copiedRev processed n source MStarParserMicrocode.sepLen
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external)) =
      .groupReady
        ⟨.markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source,
          .core MStarConcreteAlphabet.work,
          List.replicate n (.core MStarConcreteAlphabet.work) ++
            copiedRev.reverse.map MStarCopierExecution.coreBit ++
              List.replicate (n + 1) (.core MStarConcreteAlphabet.work) ++
                .markR :: external⟩ := by
  have h0 : MStarCopierExecution.run 1
      (payloadAtSource copiedRev processed n source MStarParserMicrocode.sepLen
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external)) =
      payloadDoneStarted copiedRev processed n source
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external) := by
    change MStarCopierExecution.oneStep
      (payloadAtSource copiedRev processed n source MStarParserMicrocode.sepLen
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external)) = _
    have hne : doneReturnPrefix processed ≠ [] := by
      simp [MStarCopierExecution.doneReturnPrefix]
    cases hp : doneReturnPrefix processed with
    | nil => exact (hne hp).elim
    | cons x xs =>
        unfold MStarCopierExecution.payloadAtSource
          MStarCopierExecution.payloadDoneStarted
        simp only [MStarCopierExecution.afterLeftList]
        rw [MStarCopierExecution.payloadPath_reverse]
        simp [MStarCopierExecution.afterLeftList,
          MStarCopierExecution.beforeRightList, hp,
          MStarCopierExecution.payloadSeek_sep_step, List.append_assoc]
  have h1 : MStarCopierExecution.run (doneReturnPrefix processed).length
      (payloadDoneStarted copiedRev processed n source
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external)) =
      payloadDoneAtMark copiedRev processed n source
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external) := by
    apply MStarCopierExecution.run_right_list_of .payloadDoneReturn
      (doneReturnPrefix processed)
    intro x hx left y right
    have hpass : x = MStarParserMicrocode.lenDone ∨
        x = MStarParserMicrocode.endpointMark := by
      simp [MStarCopierExecution.doneReturnPrefix] at hx
      rcases hx with ⟨-, rfl⟩ | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    exact MStarCopierExecution.payloadDoneReturn_pass_step x hpass left y right
  have h2 : MStarCopierExecution.run 1
      (payloadDoneAtMark copiedRev processed n source
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external)) =
      finalSeekStarted copiedRev processed n source
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external) := by
    change MStarCopierExecution.oneStep
      (payloadDoneAtMark copiedRev processed n source
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external)) = _
    have hne : finalForwardPath n copiedRev ≠ [] := by
      simp [MStarCopierExecution.finalForwardPath]
    cases hp : finalForwardPath n copiedRev with
    | nil => exact (hne hp).elim
    | cons x xs =>
        simp [MStarCopierExecution.payloadDoneAtMark,
          MStarCopierExecution.finalSeekStarted,
          MStarCopierExecution.afterRightList,
          MStarCopierExecution.beforeRightList, hp,
          MStarCopierExecution.payloadDoneReturn_mark_step, List.append_assoc]
  have h3 : MStarCopierExecution.run (finalForwardPath n copiedRev).length
      (finalSeekStarted copiedRev processed n source
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external)) =
      finalAtBoundary copiedRev processed n source
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external) := by
    apply MStarCopierExecution.run_right_list_of .finalSeekBoundary
      (finalForwardPath n copiedRev)
    intro x hx left y right
    have hpass : x = .core MStarConcreteAlphabet.work ∨
        x = .core MStarConcreteAlphabet.zero ∨ x = .core MStarConcreteAlphabet.one := by
      simp [MStarCopierExecution.finalForwardPath] at hx
      rcases hx with ⟨-, rfl⟩ | hx
      · exact Or.inl rfl
      · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
          simp [MStarCopierExecution.coreBit]
    exact MStarCopierExecution.finalSeekBoundary_pass_step x hpass left y right
  have h4 : MStarCopierExecution.run 1
      (finalAtBoundary copiedRev processed n source
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external)) =
      rightBufferStarted copiedRev processed n source external := by
    change MStarCopierExecution.oneStep
      (finalAtBoundary copiedRev processed n source
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external)) = _
    cases n <;>
      simp [MStarCopierExecution.rightBufferStarted,
        MStarCopierExecution.finalAtBoundary,
        MStarCopierExecution.afterRightList,
        MStarCopierExecution.beforeRightRepeat,
        MStarCopierExecution.finalSeekBoundary_mark_step,
        List.replicate_succ, List.append_assoc]
  let scanned : MStarCopierExecution.Result :=
    .running .rightBufferScan
      (MStarCopierExecution.afterRightRepeat n
        (.core MStarConcreteAlphabet.work)
        (.core MStarConcreteAlphabet.work ::
          (finalForwardPath n copiedRev).reverse ++ .markL ::
            (doneReturnPrefix processed).reverse ++
              MStarParserMicrocode.sepLen :: source)
        MStarCopierMicrocode.rightEnd external)
  have h5 : MStarCopierExecution.run n
      (rightBufferStarted copiedRev processed n source external) = scanned := by
    unfold MStarCopierExecution.rightBufferStarted scanned
    exact MStarCopierExecution.run_rightBuffer_work n
      (.core MStarConcreteAlphabet.work ::
        (finalForwardPath n copiedRev).reverse ++ .markL ::
          (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source)
      MStarCopierMicrocode.rightEnd external
  let returnStarted : MStarCopierExecution.Result :=
    .running .finalReturn
      (MStarCopierExecution.beforeLeftList (finalSpan n copiedRev).reverse
        ((doneReturnPrefix processed).reverse ++
          MStarParserMicrocode.sepLen :: source)
        .markL (.markR :: external))
  have h6 : MStarCopierExecution.run 1 scanned = returnStarted := by
    have hwalk : List.replicate n (.core MStarConcreteAlphabet.work) ++
          .core MStarConcreteAlphabet.work ::
            (finalForwardPath n copiedRev).reverse =
        (finalSpan n copiedRev).reverse := by
      simp [MStarCopierExecution.finalSpan,
        List.reverse_append, List.replicate_succ,
        MStarCopierExecution.replicate_cons_rotate]
    have hwalk' : List.replicate n (.core MStarConcreteAlphabet.work) ++
          (.core MStarConcreteAlphabet.work ::
            (finalForwardPath n copiedRev).reverse ++ .markL ::
              (doneReturnPrefix processed).reverse ++
                MStarParserMicrocode.sepLen :: source) =
        (finalSpan n copiedRev).reverse ++ .markL ::
          (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source := by
      simpa [List.append_assoc] using congrArg
        (fun xs => xs ++ (.markL :: (doneReturnPrefix processed).reverse ++
          MStarParserMicrocode.sepLen :: source)) hwalk
    have hne : (finalSpan n copiedRev).reverse ≠ [] := by
      simp [MStarCopierExecution.finalSpan,
        MStarCopierExecution.finalForwardPath]
    cases hp : (finalSpan n copiedRev).reverse with
    | nil => exact (hne hp).elim
    | cons x xs =>
        change MStarCopierExecution.oneStep scanned = returnStarted
        unfold scanned returnStarted MStarCopierExecution.afterRightRepeat
        rw [hwalk', hp]
        simp [MStarCopierExecution.beforeLeftList, hp,
          MStarCopierExecution.rightBufferScan_end_step]
  have h7 : MStarCopierExecution.run (finalSpan n copiedRev).length
      returnStarted = finalAtMark copiedRev processed n source external := by
    unfold returnStarted
    rw [show (finalSpan n copiedRev).length =
      (finalSpan n copiedRev).reverse.length by simp]
    apply MStarCopierExecution.run_left_list_of .finalReturn
      (finalSpan n copiedRev).reverse
    intro x hx left y right
    have hx' : x ∈ finalSpan n copiedRev := by
      simpa using (List.mem_reverse.mp hx)
    have hpass : x = .core MStarConcreteAlphabet.work ∨
        x = .core MStarConcreteAlphabet.zero ∨ x = .core MStarConcreteAlphabet.one := by
      simp [MStarCopierExecution.finalSpan,
        MStarCopierExecution.finalForwardPath] at hx'
      rcases hx' with ⟨-, rfl⟩ | hx | ⟨-, rfl⟩
      · exact Or.inl rfl
      · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
          simp [MStarCopierExecution.coreBit]
      · exact Or.inl rfl
    exact MStarCopierExecution.finalReturn_pass_step x hpass left y right
  have h8 : MStarCopierExecution.run 1
      (finalAtMark copiedRev processed n source external) =
      .groupReady
        ⟨.markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source,
          .core MStarConcreteAlphabet.work,
          List.replicate n (.core MStarConcreteAlphabet.work) ++
            copiedRev.reverse.map MStarCopierExecution.coreBit ++
              List.replicate (n + 1) (.core MStarConcreteAlphabet.work) ++
                .markR :: external⟩ := by
    change MStarCopierExecution.oneStep
      (finalAtMark copiedRev processed n source external) = _
    simp [MStarCopierExecution.finalAtMark,
      MStarCopierExecution.finalSpan,
      MStarCopierExecution.finalForwardPath,
      MStarCopierExecution.afterLeftList,
      MStarCopierExecution.finalReturn_mark_step, List.reverse_append,
      List.map_reverse, List.replicate_succ, List.append_assoc]
  unfold copierFinalFuel
  rw [MStarCopierExecution.run_add, h0, MStarCopierExecution.run_add, h1,
    MStarCopierExecution.run_add, h2, MStarCopierExecution.run_add, h3,
    MStarCopierExecution.run_add, h4, MStarCopierExecution.run_add, h5,
    MStarCopierExecution.run_add, h6, MStarCopierExecution.run_add, h7, h8]

theorem copierFinalFuel_closed (copiedRev : List Bool) (processed n : ℕ) :
    copierFinalFuel copiedRev processed n =
      processed + 4 * n + 2 * copiedRev.length + 9 := by
  simp [copierFinalFuel, MStarCopierExecution.doneReturnPrefix,
    MStarCopierExecution.finalForwardPath, MStarCopierExecution.finalSpan]
  ring

/-! ## The single copier fuel ledger -/

def copierCounterFuel (bits : List Bool) (done : ℕ) : ℕ :=
  1 + ((groupPrefix bits done).length +
    (1 + ((groupPrefix bits done).length + 1)))

theorem copierCounterFuel_closed (bits : List Bool) (done : ℕ) :
    copierCounterFuel bits done = 2 * (bits.length + done + 2) + 3 := by
  rw [copierCounterFuel, groupPrefix_length]
  ring

theorem run_counter_started (bits : List Bool) (done : ℕ)
    (junk : List MStarCopierMicrocode.ConcreteTape) (n : ℕ) (hn : 0 < n)
    (blockTail : List MStarCopierMicrocode.ConcreteTape) :
    MStarCopierExecution.run (copierCounterFuel bits done)
      (.running .groupDone
        ⟨groupSource bits done 0 junk, .markL,
          List.replicate n MStarCopierMicrocode.cellA ++ blockTail⟩) =
      (.running .counterToWork
        ⟨.markL :: groupSource bits done 0 junk, MStarCopierMicrocode.cellA,
          List.replicate (n - 1) MStarCopierMicrocode.cellA ++ blockTail⟩) := by
  have h0 : MStarCopierExecution.run 1
      (.running .groupDone
        ⟨groupSource bits done 0 junk, .markL,
          List.replicate n MStarCopierMicrocode.cellA ++ blockTail⟩) =
      finishSeekStarted bits done junk
        (List.replicate n MStarCopierMicrocode.cellA ++ blockTail) := by
    change MStarCopierExecution.oneStep
      (.running .groupDone
        ⟨groupSource bits done 0 junk, .markL,
          List.replicate n MStarCopierMicrocode.cellA ++ blockTail⟩) = _
    have hne : groupPrefix bits done ≠ [] := by
      simp [MStarCopierExecution.groupPrefix]
    cases hp : groupPrefix bits done with
    | nil => exact (hne hp).elim
    | cons x xs =>
        simp [MStarCopierExecution.groupSource,
          MStarCopierExecution.finishSeekStarted,
          MStarCopierExecution.beforeLeftList, hp,
          MStarCopierExecution.groupDone_step]
  have h1 : MStarCopierExecution.run (groupPrefix bits done).length
      (finishSeekStarted bits done junk
        (List.replicate n MStarCopierMicrocode.cellA ++ blockTail)) =
      finishAtPad bits done junk
        (List.replicate n MStarCopierMicrocode.cellA ++ blockTail) := by
    apply MStarCopierExecution.run_left_list_of .groupSeekLen
      (groupPrefix bits done)
    intro x hx left y right
    have hpass : x = MStarParserMicrocode.endpointMark ∨
        x = MStarParserMicrocode.payloadZero ∨
        x = MStarParserMicrocode.payloadOne ∨ x = MStarParserMicrocode.sepLen ∨
        x = MStarParserMicrocode.lenDone := by
      simp [MStarCopierExecution.groupPrefix] at hx
      rcases hx with rfl | hx | rfl | ⟨-, rfl⟩
      · exact Or.inl rfl
      · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
          simp [MStarConcreteAlphabet.payloadMarker]
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    exact MStarCopierExecution.groupSeek_pass_step x hpass left y right
  have h2 : MStarCopierExecution.run 1
      (finishAtPad bits done junk
        (List.replicate n MStarCopierMicrocode.cellA ++ blockTail)) =
      finishReturnStarted bits done junk
        (List.replicate n MStarCopierMicrocode.cellA ++ blockTail) := by
    change MStarCopierExecution.oneStep
      (finishAtPad bits done junk
        (List.replicate n MStarCopierMicrocode.cellA ++ blockTail)) = _
    have hne : (groupPrefix bits done).reverse ≠ [] := by
      simp [MStarCopierExecution.groupPrefix]
    cases hrev : (groupPrefix bits done).reverse with
    | nil => exact (hne hrev).elim
    | cons x xs =>
        simp [MStarCopierExecution.finishAtPad,
          MStarCopierExecution.finishReturnStarted,
          MStarCopierExecution.afterLeftList,
          MStarCopierExecution.beforeRightList, hrev,
          MStarCopierExecution.groupSeek_finished_step]
  have h3 : MStarCopierExecution.run (groupPrefix bits done).length
      (finishReturnStarted bits done junk
        (List.replicate n MStarCopierMicrocode.cellA ++ blockTail)) =
      finishReturnedToMark bits done junk
        (List.replicate n MStarCopierMicrocode.cellA ++ blockTail) := by
    rw [show (groupPrefix bits done).length =
      (groupPrefix bits done).reverse.length by simp]
    apply MStarCopierExecution.run_right_list_of .finishReturn
      (groupPrefix bits done).reverse
    intro x hx left y right
    have hx' : x ∈ groupPrefix bits done := by
      simpa using (List.mem_reverse.mp hx)
    have hpass : x = MStarParserMicrocode.lenDone ∨
        x = MStarParserMicrocode.sepLen ∨
        x = MStarParserMicrocode.payloadZero ∨
        x = MStarParserMicrocode.payloadOne ∨
        x = MStarParserMicrocode.endpointMark := by
      simp [MStarCopierExecution.groupPrefix] at hx'
      rcases hx' with rfl | hx | rfl | ⟨-, rfl⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
          simp [MStarConcreteAlphabet.payloadMarker]
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    exact MStarCopierExecution.finishReturn_pass_step x hpass left y right
  have h4 : MStarCopierExecution.run 1
      (finishReturnedToMark bits done junk
        (List.replicate n MStarCopierMicrocode.cellA ++ blockTail)) =
      (.running .counterToWork
        ⟨.markL :: groupSource bits done 0 junk, MStarCopierMicrocode.cellA,
          List.replicate (n - 1) MStarCopierMicrocode.cellA ++ blockTail⟩) := by
    change MStarCopierExecution.oneStep
      (finishReturnedToMark bits done junk
        (List.replicate n MStarCopierMicrocode.cellA ++ blockTail)) = _
    cases n with
    | zero => omega
    | succ n =>
        simp [MStarCopierExecution.finishReturnedToMark,
          MStarCopierExecution.groupSource,
          MStarCopierExecution.afterRightList,
          MStarCopierExecution.finishReturn_mark_step, List.replicate_succ]
  unfold copierCounterFuel
  rw [MStarCopierExecution.run_add, h0, MStarCopierExecution.run_add, h1,
    MStarCopierExecution.run_add, h2, MStarCopierExecution.run_add, h3, h4]

def copierPayloadSeekFuel (n : ℕ) : ℕ := n + (1 + 1)

/-- The intended literal cost from the parser's `copyStart` hand-off to the
ready simulated workspace.  Each summand is chronologically bracketed. -/
def copierExplicitFuel (x : List Bool) : ℕ :=
  let m := x.length
  let n := MStarCopierExecution.iteratedGroupWidth m 256
  4 + (copierEightRoundFuel 1 +
    (copierGroupFoldFuel x.reverse 0 m 256 +
      (copierCounterFuel x.reverse m +
        (copierPayloadSeekFuel n +
          (copierPayloadFoldFuel x [] 0 n +
            ((payloadPath x.reverse m n).length +
              copierFinalFuel x.reverse m n))))))

theorem run_payloadSeek_started
    (source : List MStarCopierMicrocode.ConcreteTape)
    (n : ℕ) (hn : 0 < n) (right : List MStarCopierMicrocode.ConcreteTape) :
    MStarCopierExecution.run (copierPayloadSeekFuel n)
      (.running .counterToWork
        ⟨.markL :: source, MStarCopierMicrocode.cellA,
          List.replicate (n - 1) MStarCopierMicrocode.cellA ++ .markR ::
            .core MStarConcreteAlphabet.work :: right⟩) =
      (.running .payloadSeek
        ⟨List.replicate n (.core MStarConcreteAlphabet.work) ++ .markL :: source,
          .core MStarConcreteAlphabet.work, .markR :: right⟩) := by
  have h0 : MStarCopierExecution.run n
      (.running .counterToWork
        ⟨.markL :: source, MStarCopierMicrocode.cellA,
          List.replicate (n - 1) MStarCopierMicrocode.cellA ++ .markR ::
            .core MStarConcreteAlphabet.work :: right⟩) =
      (.running .counterToWork
        ⟨List.replicate n (.core MStarConcreteAlphabet.work) ++ .markL :: source,
          .markR, .core MStarConcreteAlphabet.work :: right⟩) := by
    cases n with
    | zero => omega
    | succ n =>
        simpa [MStarCopierExecution.beforeRightRepeat,
          MStarCopierExecution.afterRightRepeat, List.replicate_succ,
          List.append_assoc] using
          (MStarCopierExecution.run_counterToWork_A (n + 1)
            (.markL :: source) .markR
            (.core MStarConcreteAlphabet.work :: right))
  have h1 : MStarCopierExecution.run 1
      (.running .counterToWork
        ⟨List.replicate n (.core MStarConcreteAlphabet.work) ++ .markL :: source,
          .markR, .core MStarConcreteAlphabet.work :: right⟩) =
      (.running .payloadBoundary
        ⟨.core MStarConcreteAlphabet.work ::
            (List.replicate n (.core MStarConcreteAlphabet.work) ++
              .markL :: source),
          .core MStarConcreteAlphabet.work, right⟩) := by
    rw [show 1 = 0 + 1 by omega, MStarCopierExecution.run_succ,
      MStarCopierExecution.run_zero]
    exact MStarCopierExecution.counterToWork_mark_step _ _ _
  have h2 : MStarCopierExecution.run 1
      (.running .payloadBoundary
        ⟨.core MStarConcreteAlphabet.work ::
            (List.replicate n (.core MStarConcreteAlphabet.work) ++
              .markL :: source),
          .core MStarConcreteAlphabet.work, right⟩) =
      (.running .payloadSeek
        ⟨List.replicate n (.core MStarConcreteAlphabet.work) ++ .markL :: source,
          .core MStarConcreteAlphabet.work, .markR :: right⟩) := by
    rw [show 1 = 0 + 1 by omega, MStarCopierExecution.run_succ,
      MStarCopierExecution.run_zero]
    exact MStarCopierExecution.payloadBoundary_step _ _
  unfold copierPayloadSeekFuel
  rw [MStarCopierExecution.run_add, h0, MStarCopierExecution.run_add, h1, h2]

theorem run_payloadAtSource (copiedRev : List Bool) (processed n : ℕ)
    (source : List MStarCopierMicrocode.ConcreteTape)
    (next : MStarCopierMicrocode.ConcreteTape)
    (boundaryTail : List MStarCopierMicrocode.ConcreteTape) :
    MStarCopierExecution.run (payloadPath copiedRev processed n).length
      (payloadBefore copiedRev processed n source next boundaryTail) =
      payloadAtSource copiedRev processed n source next boundaryTail := by
  apply MStarCopierExecution.run_left_list_of .payloadSeek
    (payloadPath copiedRev processed n)
  intro a ha left y right
  exact MStarCopierExecution.payloadSeek_pass_step a
    (MStarCopierExecution.payloadPath_seek_pass copiedRev processed n a ha)
    left y right

theorem run_copier_complete_explicitFuel (x : List Bool)
    (junk external : List MStarCopierMicrocode.ConcreteTape) :
    let m := x.length
    let n := MStarCopierExecution.iteratedGroupWidth m 256
    MStarCopierExecution.run (copierExplicitFuel x)
      (.running .seedCell
        ⟨.markL :: groupSource x.reverse 0 m junk,
          .core MStarConcreteAlphabet.work,
          .core MStarConcreteAlphabet.work ::
            MStarCopierExecution.copierReserve m external⟩) =
      (.groupReady
        ⟨(.markL :: (doneReturnPrefix m).reverse) ++
            MStarParserMicrocode.sepLen ::
              (List.replicate m MStarParserMicrocode.lenDone ++
                MStarParserMicrocode.sepPad :: junk),
          .core MStarConcreteAlphabet.work,
          List.replicate n (.core MStarConcreteAlphabet.work) ++
            x.map MStarCopierExecution.coreBit ++
              List.replicate (n + 1) (.core MStarConcreteAlphabet.work) ++
                .markR :: external⟩) := by
  dsimp only
  let finalTail := List.replicate (x.length + 1)
      (MStarOuterProgram.Tape.core MStarConcreteAlphabet.work) ++
    MStarCopierMicrocode.rightEnd :: external
  let sourceTail := List.replicate x.length MStarParserMicrocode.lenDone ++
    MStarParserMicrocode.sepPad :: junk
  let n := MStarCopierExecution.iteratedGroupWidth x.length 256
  have hn : 0 < n := MStarCopierExecution.iteratedGroupWidth_pos _ _ (by omega)
  have hrep : List.replicate n
      (MStarOuterProgram.Tape.core MStarConcreteAlphabet.work) =
      MStarOuterProgram.Tape.core MStarConcreteAlphabet.work ::
        List.replicate (n - 1)
          (MStarOuterProgram.Tape.core MStarConcreteAlphabet.work) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [hk, List.replicate_succ]
    congr 1
  have hright : List.replicate (n - 1) (.core MStarConcreteAlphabet.work) ++ finalTail =
      List.replicate x.length (.core MStarConcreteAlphabet.work) ++
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external) := by
    dsimp [finalTail]
    have hnsub : n - 1 + (x.length + 1) = x.length + n := by omega
    simp only [← List.append_assoc, ← List.replicate_add]
    rw [hnsub, Nat.add_comm]
  have hseed : MStarCopierExecution.run 4
      (.running .seedCell
        ⟨.markL :: groupSource x.reverse 0 x.length junk,
          .core MStarConcreteAlphabet.work,
          .core MStarConcreteAlphabet.work ::
            MStarCopierExecution.copierReserve x.length external⟩) =
      roundStage 0 0 1 (MStarCopierExecution.copierRoundReserve x.length external)
        (groupSource x.reverse 0 x.length junk) := by
    simpa [MStarCopierExecution.copierReserve, MStarCopierExecution.roundStage] using
      MStarCopierExecution.seed_reaches_round_zero_source
        (MStarCopierExecution.copierReserve x.length external)
        (groupSource x.reverse 0 x.length junk)
  have hbase := run_eight_doublings 1 (by omega)
    (MStarCopierExecution.groupExtraReserve x.length 256 finalTail)
    (groupSource x.reverse 0 x.length junk)
  have hgroups := run_group_fold x.reverse 0 x.length junk 256 (by omega) finalTail
  have hcounter := run_counter_started x.reverse x.length junk n hn
    (.markR :: .core MStarConcreteAlphabet.work ::
      List.replicate (n - 1) (.core MStarConcreteAlphabet.work) ++ finalTail)
  have hseek := run_payloadSeek_started
    (groupSource x.reverse x.length 0 junk) n hn
    (List.replicate (n - 1) (.core MStarConcreteAlphabet.work) ++ finalTail)
  have hfold := run_payload_fold x [] 0 n sourceTail
    (List.replicate n (.core MStarConcreteAlphabet.work) ++
      MStarCopierMicrocode.rightEnd :: external)
  have hat := run_payloadAtSource x.reverse x.length n sourceTail
    MStarParserMicrocode.sepLen
    (List.replicate n (.core MStarConcreteAlphabet.work) ++
      MStarCopierMicrocode.rightEnd :: external)
  have hfinal := run_payload_final x.reverse x.length n sourceTail external
  have hbase' : MStarCopierExecution.run (copierEightRoundFuel 1)
      (roundStage 0 0 1 (MStarCopierExecution.copierRoundReserve x.length external)
        (groupSource x.reverse 0 x.length junk)) =
      (.running .groupDone
        ⟨groupSource x.reverse 0 x.length junk, .markL,
          List.replicate 256 MStarCopierMicrocode.cellA ++ .markR ::
            List.replicate 256 (.core MStarConcreteAlphabet.work) ++
              MStarCopierExecution.groupExtraReserve x.length 256 finalTail⟩) := by
    simpa only [MStarCopierExecution.copierRoundReserve, finalTail,
      Nat.mul_one] using hbase
  have hgroups' : MStarCopierExecution.run
      (copierGroupFoldFuel x.reverse 0 x.length 256)
      (.running .groupDone
        ⟨groupSource x.reverse 0 x.length junk, .markL,
          List.replicate 256 MStarCopierMicrocode.cellA ++ .markR ::
            List.replicate 256 (.core MStarConcreteAlphabet.work) ++
              MStarCopierExecution.groupExtraReserve x.length 256 finalTail⟩) =
      (.running .groupDone
        ⟨groupSource x.reverse x.length 0 junk, .markL,
          List.replicate n MStarCopierMicrocode.cellA ++ .markR ::
            List.replicate n (.core MStarConcreteAlphabet.work) ++ finalTail⟩) := by
    simpa only [Nat.zero_add] using hgroups
  have hcounter' : MStarCopierExecution.run
      (copierCounterFuel x.reverse x.length)
      (.running .groupDone
        ⟨groupSource x.reverse x.length 0 junk, .markL,
          List.replicate n MStarCopierMicrocode.cellA ++ .markR ::
            List.replicate n (.core MStarConcreteAlphabet.work) ++ finalTail⟩) =
      (.running .counterToWork
        ⟨.markL :: groupSource x.reverse x.length 0 junk,
          MStarCopierMicrocode.cellA,
          List.replicate (n - 1) MStarCopierMicrocode.cellA ++ .markR ::
            .core MStarConcreteAlphabet.work ::
              List.replicate (n - 1) (.core MStarConcreteAlphabet.work) ++
                finalTail⟩) := by
    simpa only [hrep, List.append_assoc] using hcounter
  have hseek' : MStarCopierExecution.run (copierPayloadSeekFuel n)
      (.running .counterToWork
        ⟨.markL :: groupSource x.reverse x.length 0 junk,
          MStarCopierMicrocode.cellA,
          List.replicate (n - 1) MStarCopierMicrocode.cellA ++ .markR ::
            .core MStarConcreteAlphabet.work ::
              List.replicate (n - 1) (.core MStarConcreteAlphabet.work) ++
                finalTail⟩) =
      payloadLoop [] 0 n x sourceTail
        (List.replicate (n - 1) (.core MStarConcreteAlphabet.work) ++ finalTail) := by
    cases x with
    | nil =>
        simpa [MStarCopierExecution.payloadLoop,
          MStarCopierExecution.payloadBefore, MStarCopierExecution.payloadPath,
          sourceTail, groupSource, groupPrefix,
          MStarCopierExecution.beforeLeftList,
          List.replicate_succ, List.append_assoc] using hseek
    | cons b bs =>
        simpa [MStarCopierExecution.payloadLoop,
          MStarCopierExecution.payloadBefore, MStarCopierExecution.payloadPath,
          sourceTail, groupSource, groupPrefix,
          MStarCopierExecution.beforeLeftList, List.map_reverse,
          List.replicate_succ, List.append_assoc] using hseek
  have hseek'' : MStarCopierExecution.run (copierPayloadSeekFuel n)
      (.running .counterToWork
        ⟨.markL :: groupSource x.reverse x.length 0 junk,
          MStarCopierMicrocode.cellA,
          List.replicate (n - 1) MStarCopierMicrocode.cellA ++ .markR ::
            .core MStarConcreteAlphabet.work ::
              List.replicate (n - 1) (.core MStarConcreteAlphabet.work) ++
                finalTail⟩) =
      payloadLoop [] 0 n x sourceTail
        (List.replicate x.length (.core MStarConcreteAlphabet.work) ++
          (List.replicate n (.core MStarConcreteAlphabet.work) ++
            MStarCopierMicrocode.rightEnd :: external)) := by
    simpa only [hright] using hseek'
  have hfold' : MStarCopierExecution.run
      (copierPayloadFoldFuel x [] 0 n)
      (payloadLoop [] 0 n x sourceTail
        (List.replicate x.length (.core MStarConcreteAlphabet.work) ++
          (List.replicate n (.core MStarConcreteAlphabet.work) ++
            MStarCopierMicrocode.rightEnd :: external))) =
      payloadLoop x.reverse x.length n [] sourceTail
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external) := by
    simpa only [List.append_nil, Nat.zero_add] using hfold
  unfold copierExplicitFuel
  dsimp only
  rw [MStarCopierExecution.run_add, hseed,
    MStarCopierExecution.run_add, hbase',
    MStarCopierExecution.run_add, hgroups',
    MStarCopierExecution.run_add, hcounter',
    MStarCopierExecution.run_add, hseek'',
    MStarCopierExecution.run_add, hfold',
    MStarCopierExecution.run_add]
  have hat' : MStarCopierExecution.run (payloadPath x.reverse x.length n).length
      (payloadLoop x.reverse x.length n [] sourceTail
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external)) =
      payloadAtSource x.reverse x.length n sourceTail
        MStarParserMicrocode.sepLen
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: external) := by
    simpa [MStarCopierExecution.payloadLoop,
      MStarCopierExecution.payloadBefore] using hat
  rw [hat', hfinal]
  simp only [sourceTail, n, List.reverse_reverse]


theorem copierProcessAllFuel_initial (remaining : ℕ) :
    copierProcessAllFuel 0 remaining = 3 * remaining * (remaining + 1) := by
  rw [copierProcessAllFuel_closed]
  ring

def copierExplicitCoarseFuel (x : List Bool) : ℕ :=
  let m := x.length
  let n := MStarCopierExecution.iteratedGroupWidth m 256
  4 + (copierEightRoundFuel 1 +
    (m * copierGroupFoldStageBound
      (copierGroupFoldEnvelope x.reverse 0 m 256) +
      (copierCounterFuel x.reverse m +
        (copierPayloadSeekFuel n +
          (copierPayloadFoldFuel x [] 0 n +
            ((payloadPath x.reverse m n).length +
              copierFinalFuel x.reverse m n))))))

theorem copierExplicitFuel_le_coarse (x : List Bool) :
    copierExplicitFuel x ≤ copierExplicitCoarseFuel x := by
  unfold copierExplicitFuel copierExplicitCoarseFuel
  dsimp only
  let n := MStarCopierExecution.iteratedGroupWidth x.length 256
  let rest := copierCounterFuel x.reverse x.length +
    (copierPayloadSeekFuel n +
      (copierPayloadFoldFuel x [] 0 n +
        ((payloadPath x.reverse x.length n).length +
          copierFinalFuel x.reverse x.length n)))
  have hg := copierGroupFoldFuel_le_coarse x.reverse 0 x.length 256
  exact Nat.add_le_add_left
    (Nat.add_le_add_left (Nat.add_le_add_right hg rest)
      (copierEightRoundFuel 1)) 4

private theorem length_succ_le_copierWidth (m : ℕ) :
    m + 1 ≤ MStarCopierExecution.iteratedGroupWidth m 256 := by
  rw [MStarCopierExecution.copier_width_eq_time_bound]
  have hself : m + 1 < 2 ^ (m + 1) := Nat.lt_two_pow_self
  have hexp : m + 1 ≤ 8 * (m + 1) := by omega
  exact hself.le.trans (Nat.pow_le_pow_right (by decide) hexp)

private theorem groupEnvelope_le_threeWidth (m : ℕ) :
    copierGroupFoldEnvelope (List.replicate m false) 0 m 256 ≤
      3 * MStarCopierExecution.iteratedGroupWidth m 256 := by
  let n := MStarCopierExecution.iteratedGroupWidth m 256
  have hmn : m + 1 ≤ n := length_succ_le_copierWidth m
  have hnclosed : MStarCopierExecution.iteratedGroupWidth m 256 =
      256 ^ m * 256 := MStarCopierExecution.iteratedGroupWidth_closed m 256
  dsimp [n] at hmn
  dsimp [copierGroupFoldEnvelope, n] at ⊢
  simp only [List.length_replicate]
  rw [hnclosed]
  omega

private theorem groupStage_le_pow20_width_sq (m : ℕ) :
    copierGroupFoldStageBound
        (copierGroupFoldEnvelope (List.replicate m false) 0 m 256) ≤
      2 ^ 20 * (MStarCopierExecution.iteratedGroupWidth m 256) ^ 2 := by
  let E := copierGroupFoldEnvelope (List.replicate m false) 0 m 256
  let n := MStarCopierExecution.iteratedGroupWidth m 256
  have hE : E ≤ 3 * n := groupEnvelope_le_threeWidth m
  have hn : 1 ≤ n := by
    have := length_succ_le_copierWidth m
    omega
  have hsq : E ^ 2 ≤ (3 * n) ^ 2 := Nat.pow_le_pow_left hE 2
  unfold copierGroupFoldStageBound
  dsimp [E, n] at *
  norm_num at ⊢
  nlinarith

private theorem copierExplicitCoarseFuel_le_pow21_width_cube (x : List Bool) :
    copierExplicitCoarseFuel x ≤
      2 ^ 21 * (MStarCopierExecution.iteratedGroupWidth x.length 256) ^ 3 := by
  let m := x.length
  let n := MStarCopierExecution.iteratedGroupWidth m 256
  have hmn1 : m + 1 ≤ n := length_succ_le_copierWidth m
  have hmn : m ≤ n := by omega
  have hn : 1 ≤ n := by omega
  have hstage := groupStage_le_pow20_width_sq m
  have hgroup : m * copierGroupFoldStageBound
        (copierGroupFoldEnvelope x.reverse 0 m 256) ≤
      n * (2 ^ 20 * n ^ 2) := by
    have hlen : x.reverse.length = m := by simp [m]
    have henv : copierGroupFoldEnvelope x.reverse 0 m 256 =
        copierGroupFoldEnvelope (List.replicate m false) 0 m 256 := by
      unfold copierGroupFoldEnvelope
      simp [m]
    rw [henv]
    exact Nat.mul_le_mul hmn hstage
  unfold copierExplicitCoarseFuel
  dsimp only
  rw [copierEightRoundFuel_closed, copierCounterFuel_closed,
    copierPayloadFoldFuel_initial, payloadPath_length,
    copierFinalFuel_closed]
  change 4 + (65535 * 1 * 1 + 1785 * 1 + 16 +
      (m * copierGroupFoldStageBound
        (copierGroupFoldEnvelope x.reverse 0 m 256) +
        (2 * (x.reverse.length + m + 2) + 3 +
          (n + (1 + 1) +
            (2 * x.length * x.length + 2 * n * x.length + 7 * x.length +
              (x.reverse.length + m + n + 3 +
                (m + 4 * n + 2 * x.reverse.length + 9))))))) ≤ _
  simp only [List.length_reverse]
  norm_num at ⊢
  nlinarith

private theorem pow21_width_cube_lt_paddingPow (m : ℕ) :
    2 ^ 21 * (MStarCopierExecution.iteratedGroupWidth m 256) ^ 3 <
      2 ^ ConcretePakSide.paddingLength m := by
  rw [MStarCopierExecution.copier_width_eq_time_bound]
  have heq : 2 ^ 21 * (2 ^ (8 * (m + 1))) ^ 3 =
      2 ^ (24 * m + 45) := by
    rw [← pow_mul]
    rw [← pow_add]
    congr 1
    ring
  rw [heq]
  apply Nat.pow_lt_pow_right (by decide)
  simp [ConcretePakSide.paddingLength]
  omega

theorem copierExplicitFuel_lt_sideValue (x : List Bool) :
    copierExplicitFuel x < ConcretePakSide.sideValue x := by
  have hbit := Nat.ge_two_pow_of_testBit
    (PakSideScanner.sideValue_padding_testBit x)
  exact (copierExplicitFuel_le_coarse x |>.trans
    (copierExplicitCoarseFuel_le_pow21_width_cube x) |>.trans_lt
      (pow21_width_cube_lt_paddingPow x.length)).trans_le hbit

theorem copierExplicitFuel_le_pow24 (x : List Bool) :
    copierExplicitFuel x ≤ 2 ^ (24 * x.length + 45) := by
  have h := copierExplicitFuel_le_coarse x |>.trans
    (copierExplicitCoarseFuel_le_pow21_width_cube x)
  rw [MStarCopierExecution.copier_width_eq_time_bound] at h
  have heq : 2 ^ 21 * (2 ^ (8 * (x.length + 1))) ^ 3 =
      2 ^ (24 * x.length + 45) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  exact h.trans_eq heq

end PakFixedPolyomino.PakOuterFrontNumericBound
