import PakFixedPolyomino.MStarParserExecution
import Mathlib.Tactic

/-!
# Concrete reserved alphabet for `M_star`

The accepted construction allows at most 64 total tape letters.  Eleven are
the outer sentinel/delimiter/scratch constructors, leaving 53 literal slots
for `Gamma_Ulog`.  Reserving slots 0,1,2 for zero, one, and work fixes the
parser and scanner constants without constraining the remaining source-machine
compiler.
-/

namespace PakFixedPolyomino.MStarConcreteAlphabet

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

abbrev CoreTape := Fin 53

def zero : CoreTape := ⟨0, by decide⟩
def one : CoreTape := ⟨1, by decide⟩
def work : CoreTape := ⟨2, by decide⟩

@[simp] theorem zero_ne_one : zero ≠ one := by decide
@[simp] theorem zero_ne_work : zero ≠ work := by decide
@[simp] theorem one_ne_work : one ≠ work := by decide

@[simp] theorem card_coreTape : Fintype.card CoreTape = 53 := by simp

@[simp] theorem card_outerTape :
    Fintype.card (MStarOuterProgram.Tape CoreTape) = 64 := by
  native_decide

@[simp] theorem parser_coreEq_zero :
    MStarParserMicrocode.coreEq zero zero = true := by native_decide

@[simp] theorem parser_coreEq_one :
    MStarParserMicrocode.coreEq one one = true := by native_decide

@[simp] theorem parser_coreEq_work :
    MStarParserMicrocode.coreEq work work = true := by native_decide

@[simp] theorem parser_zero_not_one :
    MStarParserMicrocode.coreEq zero one = false := by native_decide

@[simp] theorem parser_zero_not_work :
    MStarParserMicrocode.coreEq zero work = false := by native_decide

@[simp] theorem parser_one_not_work :
    MStarParserMicrocode.coreEq one work = false := by native_decide

def emptyPayloadFinal :
    MStarParserExecution.Zipper (MStarOuterProgram.Tape CoreTape) :=
  { leftRev :=
      MStarParserMicrocode.endpointMark ::
      MStarParserMicrocode.sepLen ::
      MStarParserMicrocode.sepPad ::
      List.replicate 71 MStarParserMicrocode.padDone ++
      [MStarParserMicrocode.endpointMark]
    focus := .core work
    right := [] }

/-- Base case of the arbitrary-length parser refinement.  The polynomial
trace formula is `75*m^2 + 301*m + 226`, hence 226 at `m=0`. -/
theorem parser_accepts_empty_payload :
    MStarParserExecution.run zero one work 226
      (MStarParserExecution.initial zero one work
        (ConcretePakSide.encodedWord [])) =
      .copyReady emptyPayloadFinal := by
  native_decide

theorem parser_Accepts_empty_payload :
    MStarParserExecution.Accepts zero one work
      (ConcretePakSide.encodedWord []) := by
  exact ⟨226, emptyPayloadFinal, parser_accepts_empty_payload⟩

theorem run_fixed_72
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work 72
      (.running (MStarParserMicrocode.fixed 0)
        ⟨[], .core zero,
          List.replicate 71 (.core zero) ++ y :: right⟩) =
      .running (MStarParserMicrocode.fixed ⟨72, by decide⟩)
        ⟨List.replicate 71 MStarParserMicrocode.padDone ++
            [MStarParserMicrocode.endpointMark], y, right⟩ := by
  rfl

theorem oneStep_fixed_72
    (z : MStarParserExecution.Zipper (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running (MStarParserMicrocode.fixed ⟨72, by decide⟩) z) =
      .running MStarParserMicrocode.scanPad z := by
  cases z
  rfl

theorem oneStep_scanPad_zero
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.scanPad
        ⟨left, .core zero, y :: right⟩) =
      .running MStarParserMicrocode.scanPad
        ⟨.core zero :: left, y, right⟩ := by
  rfl

theorem oneStep_scanPad_separator
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.scanPad
        ⟨left, .core one, y :: right⟩) =
      .running MStarParserMicrocode.scanLen
        ⟨MStarParserMicrocode.sepPad :: left, y, right⟩ := by
  rfl

theorem oneStep_scanLen_zero
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.scanLen
        ⟨y :: left, .core zero, right⟩) =
      .running MStarParserMicrocode.seekSepPad
        ⟨left, y, MStarParserMicrocode.lenDone :: right⟩ := by
  rfl

theorem oneStep_seekSepPad_lenDone
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.seekSepPad
        ⟨y :: left, MStarParserMicrocode.lenDone, right⟩) =
      .running MStarParserMicrocode.seekSepPad
        ⟨left, y, MStarParserMicrocode.lenDone :: right⟩ := by
  rfl

theorem oneStep_seekSepPad_separator
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.seekSepPad
        ⟨y :: left, MStarParserMicrocode.sepPad, right⟩) =
      .running MStarParserMicrocode.seekUnmarkedPad
        ⟨left, y, MStarParserMicrocode.sepPad :: right⟩ := by
  rfl

theorem oneStep_seekUnmarked_padDone
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.seekUnmarkedPad
        ⟨y :: left, MStarParserMicrocode.padDone, right⟩) =
      .running MStarParserMicrocode.seekUnmarkedPad
        ⟨left, y, MStarParserMicrocode.padDone :: right⟩ := by
  rfl

theorem oneStep_seekUnmarked_zero
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.seekUnmarkedPad
        ⟨y :: left, .core zero, right⟩) =
      .running (MStarParserMicrocode.cross 1)
        ⟨left, y, MStarParserMicrocode.padDone :: right⟩ := by
  rfl

theorem run_cross_remaining_71
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work 72
      (.running (MStarParserMicrocode.cross 1)
        ⟨List.replicate 70 (.core zero) ++ y :: left,
          .core zero, right⟩) =
      .running MStarParserMicrocode.returnSepPad
        ⟨left, y,
          List.replicate 71 MStarParserMicrocode.padDone ++ right⟩ := by
  rfl

theorem run_seekSepPad_lenDone (n : ℕ)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work n
      (.running MStarParserMicrocode.seekSepPad
        (MStarParserExecution.beforeLeftRepeat n MStarParserMicrocode.lenDone
          left y right)) =
      .running MStarParserMicrocode.seekSepPad
        (MStarParserExecution.afterLeftRepeat n MStarParserMicrocode.lenDone
          left y right) := by
  exact MStarParserExecution.run_left_repeat_of zero one work
    MStarParserMicrocode.seekSepPad MStarParserMicrocode.lenDone
    oneStep_seekSepPad_lenDone n left y right

theorem run_seekUnmarked_padDone (n : ℕ)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work n
      (.running MStarParserMicrocode.seekUnmarkedPad
        (MStarParserExecution.beforeLeftRepeat n MStarParserMicrocode.padDone
          left y right)) =
      .running MStarParserMicrocode.seekUnmarkedPad
        (MStarParserExecution.afterLeftRepeat n MStarParserMicrocode.padDone
          left y right) := by
  exact MStarParserExecution.run_left_repeat_of zero one work
    MStarParserMicrocode.seekUnmarkedPad MStarParserMicrocode.padDone
    oneStep_seekUnmarked_padDone n left y right

theorem separator_enters_left_repeat (n : ℕ)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.seekSepPad
        ⟨List.replicate n MStarParserMicrocode.padDone ++ y :: left,
          MStarParserMicrocode.sepPad, right⟩) =
      .running MStarParserMicrocode.seekUnmarkedPad
        (MStarParserExecution.beforeLeftRepeat n MStarParserMicrocode.padDone
          left y (MStarParserMicrocode.sepPad :: right)) := by
  cases n <;>
    simp [MStarParserExecution.beforeLeftRepeat, List.replicate_succ,
      oneStep_seekSepPad_separator]

def fixedPaddingTail : List (MStarOuterProgram.Tape CoreTape) :=
  List.replicate 71 MStarParserMicrocode.padDone ++
    [MStarParserMicrocode.endpointMark]

theorem unpaid_padding_shape (r : ℕ) :
    List.replicate (72 * (r + 1)) (MStarOuterProgram.Tape.core zero) ++
        fixedPaddingTail =
      MStarOuterProgram.Tape.core zero ::
        (List.replicate (72 * (r + 1) - 1)
          (MStarOuterProgram.Tape.core zero) ++ fixedPaddingTail) := by
  have hr : 72 * (r + 1) = (72 * (r + 1) - 1) + 1 := by omega
  rw [hr, List.replicate_succ]
  simp

theorem oneStep_returnSepPad_zero
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.returnSepPad
        ⟨left, .core zero, y :: right⟩) =
      .running MStarParserMicrocode.returnSepPad
        ⟨.core zero :: left, y, right⟩ := by
  rfl

theorem oneStep_returnSepPad_done
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.returnSepPad
        ⟨left, MStarParserMicrocode.padDone, y :: right⟩) =
      .running MStarParserMicrocode.returnSepPad
        ⟨MStarParserMicrocode.padDone :: left, y, right⟩ := by
  rfl

theorem oneStep_returnSepPad_separator
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.returnSepPad
        ⟨left, MStarParserMicrocode.sepPad, y :: right⟩) =
      .running MStarParserMicrocode.returnLen
        ⟨MStarParserMicrocode.sepPad :: left, y, right⟩ := by
  rfl

theorem oneStep_returnLen_done
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.returnLen
        ⟨left, MStarParserMicrocode.lenDone, y :: right⟩) =
      .running MStarParserMicrocode.returnLen
        ⟨MStarParserMicrocode.lenDone :: left, y, right⟩ := by
  rfl

theorem oneStep_returnLen_zero
    (left : List (MStarOuterProgram.Tape CoreTape))
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.returnLen
        ⟨left, .core zero, right⟩) =
      .running MStarParserMicrocode.scanLen
        ⟨left, .core zero, right⟩ := by
  rfl

theorem oneStep_returnLen_one
    (left : List (MStarOuterProgram.Tape CoreTape))
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.returnLen
        ⟨left, .core one, right⟩) =
      .running MStarParserMicrocode.scanLen
        ⟨left, .core one, right⟩ := by
  rfl

theorem run_returnSepPad_zeros (n : ℕ)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work n
      (.running MStarParserMicrocode.returnSepPad
        (MStarParserExecution.beforeRightRepeat n (.core zero) left y right)) =
      .running MStarParserMicrocode.returnSepPad
        (MStarParserExecution.afterRightRepeat n (.core zero) left y right) := by
  exact MStarParserExecution.run_right_repeat_of zero one work
    MStarParserMicrocode.returnSepPad (.core zero)
    oneStep_returnSepPad_zero n left y right

theorem run_returnSepPad_done (n : ℕ)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work n
      (.running MStarParserMicrocode.returnSepPad
        (MStarParserExecution.beforeRightRepeat n MStarParserMicrocode.padDone
          left y right)) =
      .running MStarParserMicrocode.returnSepPad
        (MStarParserExecution.afterRightRepeat n MStarParserMicrocode.padDone
          left y right) := by
  exact MStarParserExecution.run_right_repeat_of zero one work
    MStarParserMicrocode.returnSepPad MStarParserMicrocode.padDone
    oneStep_returnSepPad_done n left y right

theorem run_returnLen_done (n : ℕ)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work n
      (.running MStarParserMicrocode.returnLen
        (MStarParserExecution.beforeRightRepeat n MStarParserMicrocode.lenDone
          left y right)) =
      .running MStarParserMicrocode.returnLen
        (MStarParserExecution.afterRightRepeat n MStarParserMicrocode.lenDone
          left y right) := by
  exact MStarParserExecution.run_right_repeat_of zero one work
    MStarParserMicrocode.returnLen MStarParserMicrocode.lenDone
    oneStep_returnLen_done n left y right

def beforeLenIteration (j r : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.scanLen
    ⟨List.replicate j MStarParserMicrocode.lenDone ++
        MStarParserMicrocode.sepPad ::
        (List.replicate (72 * j) MStarParserMicrocode.padDone ++
        List.replicate (72 * (r + 1)) (.core zero) ++ fixedPaddingTail),
      .core zero,
      List.replicate r (.core zero) ++ .core one :: tail⟩

def afterLenIteration (j r : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.scanLen
    (MStarParserExecution.beforeRightRepeat r (.core zero)
      (List.replicate (j + 1) MStarParserMicrocode.lenDone ++
        MStarParserMicrocode.sepPad ::
        (List.replicate (72 * (j + 1)) MStarParserMicrocode.padDone ++
        List.replicate (72 * r) (.core zero) ++ fixedPaddingTail))
      (.core one) tail)

def firstUnmarkedState (j r : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.seekUnmarkedPad
    ⟨List.replicate (72 * (r + 1) - 1) (.core zero) ++ fixedPaddingTail,
      .core zero,
      List.replicate (72 * j) MStarParserMicrocode.padDone ++
        MStarParserMicrocode.sepPad ::
        (List.replicate (j + 1) MStarParserMicrocode.lenDone ++
          List.replicate r (.core zero) ++ .core one :: tail)⟩

/-- Common prefix of one length-marker iteration: mark the current length
cell, pass the `j` older length markers and their `72*j` paid padding cells,
and stop at the first cell of the next unpaid 72-block. -/
theorem reaches_first_unmarked (j r : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.Reaches zero one work
      (beforeLenIteration j r tail) (firstUnmarkedState j r tail) := by
  let padBelow : List (MStarOuterProgram.Tape CoreTape) :=
    List.replicate (72 * j) MStarParserMicrocode.padDone ++
      List.replicate (72 * (r + 1)) (.core zero) ++ fixedPaddingTail
  let rightRest : List (MStarOuterProgram.Tape CoreTape) :=
    List.replicate r (.core zero) ++ .core one :: tail
  let z₁ : MStarParserExecution.Result CoreTape :=
    .running MStarParserMicrocode.seekSepPad
      (MStarParserExecution.beforeLeftRepeat j MStarParserMicrocode.lenDone
        padBelow MStarParserMicrocode.sepPad
        (MStarParserMicrocode.lenDone :: rightRest))
  let z₂ : MStarParserExecution.Result CoreTape :=
    .running MStarParserMicrocode.seekSepPad
      (MStarParserExecution.afterLeftRepeat j MStarParserMicrocode.lenDone
        padBelow MStarParserMicrocode.sepPad
        (MStarParserMicrocode.lenDone :: rightRest))
  have h₀₁ : MStarParserExecution.Reaches zero one work
      (beforeLenIteration j r tail) z₁ := by
    apply MStarParserExecution.reaches_of_oneStep
    cases j <;>
      simp [beforeLenIteration, z₁, padBelow, rightRest,
        MStarParserExecution.beforeLeftRepeat, oneStep_scanLen_zero,
        List.replicate_succ, List.append_assoc]
  have h₁₂ : MStarParserExecution.Reaches zero one work z₁ z₂ := by
    exact ⟨j, run_seekSepPad_lenDone j padBelow MStarParserMicrocode.sepPad
      (MStarParserMicrocode.lenDone :: rightRest)⟩
  have h₂f : MStarParserExecution.Reaches zero one work z₂
      (firstUnmarkedState j r tail) := by
    let low : List (MStarOuterProgram.Tape CoreTape) :=
      List.replicate (72 * (r + 1) - 1) (.core zero) ++ fixedPaddingTail
    let lenRight : List (MStarOuterProgram.Tape CoreTape) :=
      List.replicate (j + 1) MStarParserMicrocode.lenDone ++ rightRest
    let z₃ : MStarParserExecution.Result CoreTape :=
      .running MStarParserMicrocode.seekUnmarkedPad
        (MStarParserExecution.beforeLeftRepeat (72 * j)
          MStarParserMicrocode.padDone low (.core zero)
          (MStarParserMicrocode.sepPad :: lenRight))
    let z₄ : MStarParserExecution.Result CoreTape :=
      .running MStarParserMicrocode.seekUnmarkedPad
        (MStarParserExecution.afterLeftRepeat (72 * j)
          MStarParserMicrocode.padDone low (.core zero)
          (MStarParserMicrocode.sepPad :: lenRight))
    have h₂₃ : MStarParserExecution.Reaches zero one work z₂ z₃ := by
      apply MStarParserExecution.reaches_of_oneStep
      have hpad : padBelow =
          List.replicate (72 * j) MStarParserMicrocode.padDone ++
            .core zero :: low := by
        simp only [padBelow, low]
        rw [List.append_assoc]
        rw [unpaid_padding_shape]
      have hright : List.replicate j MStarParserMicrocode.lenDone ++
          MStarParserMicrocode.lenDone :: rightRest = lenRight := by
        simp only [lenRight, List.replicate_succ']
        exact (List.append_assoc (List.replicate j MStarParserMicrocode.lenDone)
          [MStarParserMicrocode.lenDone] rightRest).symm
      rw [show z₂ = .running MStarParserMicrocode.seekSepPad
          ⟨List.replicate (72 * j) MStarParserMicrocode.padDone ++
              .core zero :: low,
            MStarParserMicrocode.sepPad, lenRight⟩ by
        simp only [z₂, MStarParserExecution.afterLeftRepeat]
        rw [hpad, hright]]
      exact separator_enters_left_repeat (72 * j) low (.core zero) lenRight
    have h₃₄ : MStarParserExecution.Reaches zero one work z₃ z₄ := by
      exact ⟨72 * j, run_seekUnmarked_padDone (72 * j) low (.core zero)
        (MStarParserMicrocode.sepPad :: lenRight)⟩
    have h₄f : z₄ = firstUnmarkedState j r tail := by
      simp [z₄, firstUnmarkedState, low, lenRight, rightRest,
        MStarParserExecution.afterLeftRepeat, List.append_assoc]
    rw [h₄f] at h₃₄
    exact MStarParserExecution.reaches_trans zero one work h₂₃ h₃₄
  exact MStarParserExecution.reaches_trans zero one work
    (MStarParserExecution.reaches_trans zero one work h₀₁ h₁₂) h₂f

def afterCrossLast (j : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.returnSepPad
    ⟨List.replicate 70 MStarParserMicrocode.padDone ++
        [MStarParserMicrocode.endpointMark],
      MStarParserMicrocode.padDone,
      List.replicate (72 * (j + 1)) MStarParserMicrocode.padDone ++
        MStarParserMicrocode.sepPad ::
        (List.replicate (j + 1) MStarParserMicrocode.lenDone ++
          .core one :: tail)⟩

theorem donePrefixMerge (j : ℕ) :
    List.replicate 71
        (MStarParserMicrocode.padDone : MStarOuterProgram.Tape CoreTape) ++
        MStarParserMicrocode.padDone ::
          List.replicate (72 * j) MStarParserMicrocode.padDone =
      List.replicate (72 * (j + 1)) MStarParserMicrocode.padDone := by
  calc
    List.replicate 71 MStarParserMicrocode.padDone ++
          MStarParserMicrocode.padDone ::
            List.replicate (72 * j) MStarParserMicrocode.padDone =
        List.replicate 71 MStarParserMicrocode.padDone ++
          (List.replicate 1 MStarParserMicrocode.padDone ++
            List.replicate (72 * j) MStarParserMicrocode.padDone) := rfl
    _ = (List.replicate 71 MStarParserMicrocode.padDone ++
          List.replicate 1 MStarParserMicrocode.padDone) ++
            List.replicate (72 * j) MStarParserMicrocode.padDone :=
      (List.append_assoc _ _ _).symm
    _ = List.replicate (71 + 1) MStarParserMicrocode.padDone ++
          List.replicate (72 * j) MStarParserMicrocode.padDone := by
      rw [List.replicate_add]
    _ = List.replicate ((71 + 1) + 72 * j) MStarParserMicrocode.padDone := by
      exact (List.replicate_add (71 + 1) (72 * j)
        (MStarParserMicrocode.padDone : MStarOuterProgram.Tape CoreTape)).symm
    _ = List.replicate (72 * (j + 1)) MStarParserMicrocode.padDone := by
      apply congrArg (fun n => List.replicate n
        (MStarParserMicrocode.padDone : MStarOuterProgram.Tape CoreTape))
      omega

theorem lenPrefixMerge (j : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    List.replicate j MStarParserMicrocode.lenDone ++
        MStarParserMicrocode.lenDone :: tail =
      List.replicate (j + 1) MStarParserMicrocode.lenDone ++ tail := by
  calc
    List.replicate j MStarParserMicrocode.lenDone ++
          MStarParserMicrocode.lenDone :: tail =
        List.replicate j MStarParserMicrocode.lenDone ++
          ([MStarParserMicrocode.lenDone] ++ tail) := rfl
    _ = (List.replicate j MStarParserMicrocode.lenDone ++
          [MStarParserMicrocode.lenDone]) ++ tail :=
      (List.append_assoc _ _ _).symm
    _ = List.replicate (j + 1) MStarParserMicrocode.lenDone ++ tail := by
      rw [List.replicate_succ']

theorem reaches_afterCrossLast (j : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.Reaches zero one work
      (firstUnmarkedState j 0 tail) (afterCrossLast j tail) := by
  let oldRight : List (MStarOuterProgram.Tape CoreTape) :=
    List.replicate (72 * j) MStarParserMicrocode.padDone ++
      MStarParserMicrocode.sepPad ::
      (List.replicate (j + 1) MStarParserMicrocode.lenDone ++ .core one :: tail)
  let z₁ : MStarParserExecution.Result CoreTape :=
    .running (MStarParserMicrocode.cross 1)
      ⟨List.replicate 70 (.core zero) ++
          MStarParserMicrocode.padDone ::
          (List.replicate 70 MStarParserMicrocode.padDone ++
            [MStarParserMicrocode.endpointMark]),
        .core zero, MStarParserMicrocode.padDone :: oldRight⟩
  have h₀₁ : MStarParserExecution.Reaches zero one work
      (firstUnmarkedState j 0 tail) z₁ := by
    apply MStarParserExecution.reaches_of_oneStep
    simp [firstUnmarkedState, z₁, oldRight, fixedPaddingTail,
      oneStep_seekUnmarked_zero, List.replicate_add,
      List.replicate_succ, List.append_assoc]
  have h₁f : MStarParserExecution.Reaches zero one work z₁
      (afterCrossLast j tail) := by
    refine ⟨72, ?_⟩
    rw [run_cross_remaining_71]
    apply congrArg (MStarParserExecution.Result.running
      MStarParserMicrocode.returnSepPad)
    apply MStarParserExecution.Zipper.ext
    · rfl
    · rfl
    · simp only [afterCrossLast, oldRight]
      change (List.replicate 71 MStarParserMicrocode.padDone ++
          MStarParserMicrocode.padDone ::
            List.replicate (72 * j) MStarParserMicrocode.padDone) ++
          (MStarParserMicrocode.sepPad ::
            (List.replicate (j + 1) MStarParserMicrocode.lenDone ++
              .core one :: tail)) = _
      rw [donePrefixMerge]
  exact MStarParserExecution.reaches_trans zero one work h₀₁ h₁f

theorem reaches_afterLenLast (j : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.Reaches zero one work
      (afterCrossLast j tail) (afterLenIteration j 0 tail) := by
  let low : List (MStarOuterProgram.Tape CoreTape) :=
    List.replicate 70 MStarParserMicrocode.padDone ++
      [MStarParserMicrocode.endpointMark]
  let lenRight : List (MStarOuterProgram.Tape CoreTape) :=
    List.replicate (j + 1) MStarParserMicrocode.lenDone ++ .core one :: tail
  let nPad := 72 * (j + 1) + 1
  let z₁ : MStarParserExecution.Result CoreTape :=
    .running MStarParserMicrocode.returnSepPad
      (MStarParserExecution.afterRightRepeat nPad MStarParserMicrocode.padDone
        low MStarParserMicrocode.sepPad lenRight)
  have h₀₁ : MStarParserExecution.Reaches zero one work
      (afterCrossLast j tail) z₁ := by
    refine ⟨nPad, ?_⟩
    have hrun := run_returnSepPad_done nPad low MStarParserMicrocode.sepPad lenRight
    rw [show afterCrossLast j tail =
        .running MStarParserMicrocode.returnSepPad
          (MStarParserExecution.beforeRightRepeat nPad
            MStarParserMicrocode.padDone low MStarParserMicrocode.sepPad lenRight) by
      simp [afterCrossLast, nPad, low, lenRight,
        MStarParserExecution.beforeRightRepeat, List.replicate_succ,
        List.append_assoc]]
    exact hrun
  let padLeft : List (MStarOuterProgram.Tape CoreTape) :=
    List.replicate nPad MStarParserMicrocode.padDone ++ low
  let z₂ : MStarParserExecution.Result CoreTape :=
    .running MStarParserMicrocode.returnLen
      (MStarParserExecution.beforeRightRepeat (j + 1)
        MStarParserMicrocode.lenDone
        (MStarParserMicrocode.sepPad :: padLeft) (.core one) tail)
  have h₁₂ : MStarParserExecution.Reaches zero one work z₁ z₂ := by
    apply MStarParserExecution.reaches_of_oneStep
    rw [show z₁ = .running MStarParserMicrocode.returnSepPad
        ⟨padLeft, MStarParserMicrocode.sepPad, lenRight⟩ by
      simp [z₁, padLeft, nPad, low, lenRight,
        MStarParserExecution.afterRightRepeat]]
    rw [show lenRight = MStarParserMicrocode.lenDone ::
        (List.replicate j MStarParserMicrocode.lenDone ++ .core one :: tail) by
      simp [lenRight, List.replicate_succ, List.append_assoc]]
    rw [oneStep_returnSepPad_separator]
    simp [z₂, lenRight, MStarParserExecution.beforeRightRepeat,
      List.replicate_succ, List.append_assoc]
  let z₃ : MStarParserExecution.Result CoreTape :=
    .running MStarParserMicrocode.returnLen
      (MStarParserExecution.afterRightRepeat (j + 1)
        MStarParserMicrocode.lenDone
        (MStarParserMicrocode.sepPad :: padLeft) (.core one) tail)
  have h₂₃ : MStarParserExecution.Reaches zero one work z₂ z₃ := by
    exact ⟨j + 1, run_returnLen_done (j + 1)
      (MStarParserMicrocode.sepPad :: padLeft) (.core one) tail⟩
  have h₃f : MStarParserExecution.Reaches zero one work z₃
      (afterLenIteration j 0 tail) := by
    apply MStarParserExecution.reaches_of_oneStep
    rw [show z₃ = .running MStarParserMicrocode.returnLen
        ⟨List.replicate (j + 1) MStarParserMicrocode.lenDone ++
            MStarParserMicrocode.sepPad :: padLeft,
          .core one, tail⟩ by
      rfl]
    rw [oneStep_returnLen_one]
    simp [afterLenIteration, padLeft, low, nPad, fixedPaddingTail,
      MStarParserExecution.beforeRightRepeat, List.replicate_add,
      List.append_assoc]
  exact MStarParserExecution.reaches_trans zero one work
    (MStarParserExecution.reaches_trans zero one work
      (MStarParserExecution.reaches_trans zero one work h₀₁ h₁₂) h₂₃) h₃f

def afterCrossSucc (j k : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.returnSepPad
    ⟨List.replicate (72 * (k + 1) - 1) (.core zero) ++ fixedPaddingTail,
      .core zero,
      List.replicate (72 * (j + 1)) MStarParserMicrocode.padDone ++
        MStarParserMicrocode.sepPad ::
        (List.replicate (j + 1) MStarParserMicrocode.lenDone ++
          List.replicate (k + 1) (.core zero) ++ .core one :: tail)⟩

theorem reaches_afterCrossSucc (j k : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.Reaches zero one work
      (firstUnmarkedState j (k + 1) tail) (afterCrossSucc j k tail) := by
  let low : List (MStarOuterProgram.Tape CoreTape) :=
    List.replicate (72 * (k + 1) - 1) (.core zero) ++ fixedPaddingTail
  let oldRight : List (MStarOuterProgram.Tape CoreTape) :=
    List.replicate (72 * j) MStarParserMicrocode.padDone ++
      MStarParserMicrocode.sepPad ::
      (List.replicate (j + 1) MStarParserMicrocode.lenDone ++
        List.replicate (k + 1) (.core zero) ++ .core one :: tail)
  let z₁ : MStarParserExecution.Result CoreTape :=
    .running (MStarParserMicrocode.cross 1)
      ⟨List.replicate 70 (.core zero) ++ .core zero :: low,
        .core zero, MStarParserMicrocode.padDone :: oldRight⟩
  have h₀₁ : MStarParserExecution.Reaches zero one work
      (firstUnmarkedState j (k + 1) tail) z₁ := by
    apply MStarParserExecution.reaches_of_oneStep
    have hcount : 72 * (k + 1 + 1) - 1 =
        1 + (70 + 1 + (72 * (k + 1) - 1)) := by omega
    simp [firstUnmarkedState, z₁, low, oldRight,
      oneStep_seekUnmarked_zero, hcount, List.replicate_add,
      List.replicate_succ, List.append_assoc]
  have h₁f : MStarParserExecution.Reaches zero one work z₁
      (afterCrossSucc j k tail) := by
    refine ⟨72, ?_⟩
    rw [run_cross_remaining_71]
    apply congrArg (MStarParserExecution.Result.running
      MStarParserMicrocode.returnSepPad)
    apply MStarParserExecution.Zipper.ext
    · rfl
    · rfl
    · simp only [afterCrossSucc, oldRight, low]
      change (List.replicate 71 MStarParserMicrocode.padDone ++
          MStarParserMicrocode.padDone ::
            List.replicate (72 * j) MStarParserMicrocode.padDone) ++
          (MStarParserMicrocode.sepPad ::
            (List.replicate (j + 1) MStarParserMicrocode.lenDone ++
              List.replicate (k + 1) (.core zero) ++ .core one :: tail)) = _
      rw [donePrefixMerge]
  exact MStarParserExecution.reaches_trans zero one work h₀₁ h₁f

theorem reaches_afterLenSucc (j k : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.Reaches zero one work
      (afterCrossSucc j k tail) (afterLenIteration j (k + 1) tail) := by
  let low : List (MStarOuterProgram.Tape CoreTape) :=
    List.replicate (72 * (k + 1) - 1) (.core zero) ++ fixedPaddingTail
  let lenRight : List (MStarOuterProgram.Tape CoreTape) :=
    List.replicate (j + 1) MStarParserMicrocode.lenDone ++
      List.replicate (k + 1) (.core zero) ++ .core one :: tail
  let nPad := 72 * (j + 1)
  let z₀ : MStarParserExecution.Result CoreTape :=
    .running MStarParserMicrocode.returnSepPad
      (MStarParserExecution.beforeRightRepeat nPad MStarParserMicrocode.padDone
        (.core zero :: low) MStarParserMicrocode.sepPad lenRight)
  have hstart : MStarParserExecution.Reaches zero one work
      (afterCrossSucc j k tail) z₀ := by
    apply MStarParserExecution.reaches_of_oneStep
    have hn : nPad = (nPad - 1) + 1 := by
      dsimp [nPad]
      omega
    have hz₀ : z₀ = .running MStarParserMicrocode.returnSepPad
        ⟨.core zero :: low, MStarParserMicrocode.padDone,
          List.replicate (nPad - 1) MStarParserMicrocode.padDone ++
            MStarParserMicrocode.sepPad :: lenRight⟩ := by
      dsimp [z₀]
      rw [hn]
      rfl
    rw [show afterCrossSucc j k tail = .running MStarParserMicrocode.returnSepPad
        ⟨low, .core zero,
          List.replicate nPad MStarParserMicrocode.padDone ++
            MStarParserMicrocode.sepPad :: lenRight⟩ by
      simp [afterCrossSucc, low, lenRight, nPad]]
    rw [show List.replicate nPad MStarParserMicrocode.padDone ++
          MStarParserMicrocode.sepPad :: lenRight =
        MStarParserMicrocode.padDone ::
          (List.replicate (nPad - 1) MStarParserMicrocode.padDone ++
            MStarParserMicrocode.sepPad :: lenRight) by
      rw [hn]
      simp only [List.replicate_succ, Nat.add_sub_cancel]
      rfl]
    rw [oneStep_returnSepPad_zero]
    rw [hz₀]
  let padLeft : List (MStarOuterProgram.Tape CoreTape) :=
    List.replicate nPad MStarParserMicrocode.padDone ++ .core zero :: low
  let z₁ : MStarParserExecution.Result CoreTape :=
    .running MStarParserMicrocode.returnSepPad
      (MStarParserExecution.afterRightRepeat nPad MStarParserMicrocode.padDone
        (.core zero :: low) MStarParserMicrocode.sepPad lenRight)
  have h₀₁ : MStarParserExecution.Reaches zero one work z₀ z₁ := by
    exact ⟨nPad, run_returnSepPad_done nPad (.core zero :: low)
      MStarParserMicrocode.sepPad lenRight⟩
  let z₂ : MStarParserExecution.Result CoreTape :=
    .running MStarParserMicrocode.returnLen
      (MStarParserExecution.beforeRightRepeat (j + 1)
        MStarParserMicrocode.lenDone
        (MStarParserMicrocode.sepPad :: padLeft) (.core zero)
        (List.replicate k (.core zero) ++ .core one :: tail))
  have h₁₂ : MStarParserExecution.Reaches zero one work z₁ z₂ := by
    apply MStarParserExecution.reaches_of_oneStep
    rw [show z₁ = .running MStarParserMicrocode.returnSepPad
        ⟨padLeft, MStarParserMicrocode.sepPad, lenRight⟩ by
      simp [z₁, padLeft, MStarParserExecution.afterRightRepeat]]
    rw [show lenRight = MStarParserMicrocode.lenDone ::
        (List.replicate j MStarParserMicrocode.lenDone ++
          .core zero :: (List.replicate k (.core zero) ++ .core one :: tail)) by
      simp [lenRight, List.replicate_succ, List.append_assoc]]
    rw [oneStep_returnSepPad_separator]
    simp [z₂, MStarParserExecution.beforeRightRepeat,
      List.replicate_succ, List.append_assoc]
  let z₃ : MStarParserExecution.Result CoreTape :=
    .running MStarParserMicrocode.returnLen
      (MStarParserExecution.afterRightRepeat (j + 1)
        MStarParserMicrocode.lenDone
        (MStarParserMicrocode.sepPad :: padLeft) (.core zero)
        (List.replicate k (.core zero) ++ .core one :: tail))
  have h₂₃ : MStarParserExecution.Reaches zero one work z₂ z₃ := by
    exact ⟨j + 1, run_returnLen_done (j + 1)
      (MStarParserMicrocode.sepPad :: padLeft) (.core zero)
      (List.replicate k (.core zero) ++ .core one :: tail)⟩
  have h₃f : MStarParserExecution.Reaches zero one work z₃
      (afterLenIteration j (k + 1) tail) := by
    apply MStarParserExecution.reaches_of_oneStep
    rw [show z₃ = .running MStarParserMicrocode.returnLen
        ⟨List.replicate (j + 1) MStarParserMicrocode.lenDone ++
            MStarParserMicrocode.sepPad :: padLeft,
          .core zero, List.replicate k (.core zero) ++ .core one :: tail⟩ by
      rfl]
    rw [oneStep_returnLen_zero]
    have hlow : .core zero :: low =
        List.replicate (72 * (k + 1)) (.core zero) ++ fixedPaddingTail := by
      exact (unpaid_padding_shape k).symm
    simp [afterLenIteration, padLeft, nPad,
      MStarParserExecution.beforeRightRepeat, List.replicate_succ,
      List.append_assoc]
    rw [hlow]
  exact MStarParserExecution.reaches_trans zero one work hstart
    (MStarParserExecution.reaches_trans zero one work h₀₁
      (MStarParserExecution.reaches_trans zero one work h₁₂
        (MStarParserExecution.reaches_trans zero one work h₂₃ h₃f)))

/-- One complete arbitrary-position length iteration, including the last-block
and nonlast-block return cases. -/
theorem reaches_len_iteration (j r : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.Reaches zero one work
      (beforeLenIteration j r tail) (afterLenIteration j r tail) := by
  have hfirst := reaches_first_unmarked j r tail
  cases r with
  | zero =>
      exact MStarParserExecution.reaches_trans zero one work hfirst
        (MStarParserExecution.reaches_trans zero one work
          (reaches_afterCrossLast j tail) (reaches_afterLenLast j tail))
  | succ k =>
      exact MStarParserExecution.reaches_trans zero one work hfirst
        (MStarParserExecution.reaches_trans zero one work
          (reaches_afterCrossSucc j k tail) (reaches_afterLenSucc j k tail))

def lenFinished (m : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.scanLen
    ⟨List.replicate m MStarParserMicrocode.lenDone ++
        MStarParserMicrocode.sepPad ::
          (List.replicate (72 * m) MStarParserMicrocode.padDone ++
            fixedPaddingTail),
      .core one, tail⟩

theorem afterLenIteration_zero_eq_finished (j : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    afterLenIteration j 0 tail = lenFinished (j + 1) tail := by
  simp [afterLenIteration, lenFinished, MStarParserExecution.beforeRightRepeat,
    List.append_assoc]

theorem afterLenIteration_succ_eq_before (j r : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    afterLenIteration j (r + 1) tail = beforeLenIteration (j + 1) r tail := by
  simp [afterLenIteration, beforeLenIteration,
    MStarParserExecution.beforeRightRepeat, List.replicate_succ,
    List.append_assoc]

/-- Fold all remaining length markers. -/
theorem reaches_len_suffix (j r : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.Reaches zero one work
      (beforeLenIteration j r tail) (lenFinished (j + r + 1) tail) := by
  induction r generalizing j with
  | zero =>
      have h := reaches_len_iteration j 0 tail
      rw [afterLenIteration_zero_eq_finished] at h
      simpa using h
  | succ r ih =>
      have hstep := reaches_len_iteration j (r + 1) tail
      rw [afterLenIteration_succ_eq_before] at hstep
      have hrest := ih (j + 1)
      have h := MStarParserExecution.reaches_trans zero one work hstep hrest
      rw [show j + (r + 1) + 1 = (j + 1) + r + 1 by omega]
      exact h

def lenStarted (m : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.scanLen
    (MStarParserExecution.beforeRightRepeat m (.core zero)
      (MStarParserMicrocode.sepPad ::
        (List.replicate (72 * m) (.core zero) ++ fixedPaddingTail))
      (.core one) tail)

theorem lenStarted_zero_eq_finished
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    lenStarted 0 tail = lenFinished 0 tail := by
  rfl

theorem lenStarted_succ_eq_before (m : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    lenStarted (m + 1) tail = beforeLenIteration 0 m tail := by
  simp [lenStarted, beforeLenIteration,
    MStarParserExecution.beforeRightRepeat, List.replicate_succ,
    List.append_assoc]

theorem reaches_all_length_markers (m : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.Reaches zero one work
      (lenStarted m tail) (lenFinished m tail) := by
  cases m with
  | zero =>
      rw [lenStarted_zero_eq_finished]
      exact MStarParserExecution.reaches_refl zero one work _
  | succ m =>
      rw [lenStarted_succ_eq_before]
      simpa using reaches_len_suffix 0 m tail

/-! ## Separator validation and entry to payload pairing -/

theorem oneStep_scanLen_separator
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.scanLen
        ⟨y :: left, .core one, right⟩) =
      .running MStarParserMicrocode.checkSeekSepPad
        ⟨left, y, MStarParserMicrocode.sepLen :: right⟩ := by rfl

theorem oneStep_checkSeek_lenDone
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.checkSeekSepPad
        ⟨y :: left, MStarParserMicrocode.lenDone, right⟩) =
      .running MStarParserMicrocode.checkSeekSepPad
        ⟨left, y, MStarParserMicrocode.lenDone :: right⟩ := by rfl

theorem oneStep_checkSeek_sepPad
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.checkSeekSepPad
        ⟨y :: left, MStarParserMicrocode.sepPad, right⟩) =
      .running MStarParserMicrocode.checkPad
        ⟨left, y, MStarParserMicrocode.sepPad :: right⟩ := by rfl

theorem oneStep_checkPad_done
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.checkPad
        ⟨y :: left, MStarParserMicrocode.padDone, right⟩) =
      .running MStarParserMicrocode.checkPad
        ⟨left, y, MStarParserMicrocode.padDone :: right⟩ := by rfl

theorem oneStep_checkPad_endpoint
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.checkPad
        ⟨left, MStarParserMicrocode.endpointMark, y :: right⟩) =
      .running MStarParserMicrocode.checkReturnSepPad
        ⟨MStarParserMicrocode.endpointMark :: left, y, right⟩ := by rfl

theorem oneStep_checkReturnPad_done
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.checkReturnSepPad
        ⟨left, MStarParserMicrocode.padDone, y :: right⟩) =
      .running MStarParserMicrocode.checkReturnSepPad
        ⟨MStarParserMicrocode.padDone :: left, y, right⟩ := by rfl

theorem oneStep_checkReturnPad_sep
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.checkReturnSepPad
        ⟨left, MStarParserMicrocode.sepPad, y :: right⟩) =
      .running MStarParserMicrocode.checkReturnSepLen
        ⟨MStarParserMicrocode.sepPad :: left, y, right⟩ := by rfl

theorem oneStep_checkReturnLen_done
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.checkReturnSepLen
        ⟨left, MStarParserMicrocode.lenDone, y :: right⟩) =
      .running MStarParserMicrocode.checkReturnSepLen
        ⟨MStarParserMicrocode.lenDone :: left, y, right⟩ := by rfl

theorem oneStep_checkReturnLen_sep
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.checkReturnSepLen
        ⟨y :: left, MStarParserMicrocode.sepLen, right⟩) =
      .running MStarParserMicrocode.findLen
        ⟨left, y, MStarParserMicrocode.sepLen :: right⟩ := by rfl

theorem run_checkSeek_lenDone (n : ℕ)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work n
      (.running MStarParserMicrocode.checkSeekSepPad
        (MStarParserExecution.beforeLeftRepeat n MStarParserMicrocode.lenDone
          left y right)) =
      .running MStarParserMicrocode.checkSeekSepPad
        (MStarParserExecution.afterLeftRepeat n MStarParserMicrocode.lenDone
          left y right) :=
  MStarParserExecution.run_left_repeat_of zero one work _ _
    oneStep_checkSeek_lenDone n left y right

theorem run_checkPad_done (n : ℕ)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work n
      (.running MStarParserMicrocode.checkPad
        (MStarParserExecution.beforeLeftRepeat n MStarParserMicrocode.padDone
          left y right)) =
      .running MStarParserMicrocode.checkPad
        (MStarParserExecution.afterLeftRepeat n MStarParserMicrocode.padDone
          left y right) :=
  MStarParserExecution.run_left_repeat_of zero one work _ _
    oneStep_checkPad_done n left y right

theorem run_checkReturnPad_done (n : ℕ)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work n
      (.running MStarParserMicrocode.checkReturnSepPad
        (MStarParserExecution.beforeRightRepeat n MStarParserMicrocode.padDone
          left y right)) =
      .running MStarParserMicrocode.checkReturnSepPad
        (MStarParserExecution.afterRightRepeat n MStarParserMicrocode.padDone
          left y right) :=
  MStarParserExecution.run_right_repeat_of zero one work _ _
    oneStep_checkReturnPad_done n left y right

theorem run_checkReturnLen_done (n : ℕ)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work n
      (.running MStarParserMicrocode.checkReturnSepLen
        (MStarParserExecution.beforeRightRepeat n MStarParserMicrocode.lenDone
          left y right)) =
      .running MStarParserMicrocode.checkReturnSepLen
        (MStarParserExecution.afterRightRepeat n MStarParserMicrocode.lenDone
          left y right) :=
  MStarParserExecution.run_right_repeat_of zero one work _ _
    oneStep_checkReturnLen_done n left y right

/-! ## Payload pairing micro-steps -/

def payloadMarker : Bool → MStarOuterProgram.Tape CoreTape
  | false => MStarParserMicrocode.payloadZero
  | true => MStarParserMicrocode.payloadOne

theorem oneStep_findLen_paired
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.findLen
        ⟨y :: left, MStarParserMicrocode.pairedLen, right⟩) =
      .running MStarParserMicrocode.findLen
        ⟨left, y, MStarParserMicrocode.pairedLen :: right⟩ := by rfl

theorem oneStep_findLen_fresh
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.findLen
        ⟨left, MStarParserMicrocode.lenDone, y :: right⟩) =
      .running MStarParserMicrocode.seekSepLenForPayload
        ⟨MStarParserMicrocode.pairedLen :: left, y, right⟩ := by rfl

theorem oneStep_findLen_finished
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.findLen
        ⟨left, MStarParserMicrocode.sepPad, y :: right⟩) =
      .running MStarParserMicrocode.verifySeekSepLen
        ⟨MStarParserMicrocode.sepPad :: left, y, right⟩ := by rfl

theorem oneStep_seekSepLen_paired
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.seekSepLenForPayload
        ⟨left, MStarParserMicrocode.pairedLen, y :: right⟩) =
      .running MStarParserMicrocode.seekSepLenForPayload
        ⟨MStarParserMicrocode.pairedLen :: left, y, right⟩ := by rfl

theorem oneStep_seekSepLen_fresh
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.seekSepLenForPayload
        ⟨left, MStarParserMicrocode.lenDone, y :: right⟩) =
      .running MStarParserMicrocode.seekSepLenForPayload
        ⟨MStarParserMicrocode.lenDone :: left, y, right⟩ := by rfl

theorem oneStep_seekSepLen_separator
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.seekSepLenForPayload
        ⟨left, MStarParserMicrocode.sepLen, y :: right⟩) =
      .running MStarParserMicrocode.seekPayload
        ⟨MStarParserMicrocode.sepLen :: left, y, right⟩ := by rfl

theorem oneStep_seekPayload_marked (b : Bool)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.seekPayload
        ⟨left, payloadMarker b, y :: right⟩) =
      .running MStarParserMicrocode.seekPayload
        ⟨payloadMarker b :: left, y, right⟩ := by
  cases b <;> rfl

theorem oneStep_seekPayload_bit (b : Bool)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.seekPayload
        ⟨y :: left, MStarParserExecution.bitCell zero one b, right⟩) =
      .running MStarParserMicrocode.returnSepLenAfterPayload
        ⟨left, y, payloadMarker b :: right⟩ := by
  cases b <;> rfl

theorem oneStep_returnPayload_marked (b : Bool)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.returnSepLenAfterPayload
        ⟨y :: left, payloadMarker b, right⟩) =
      .running MStarParserMicrocode.returnSepLenAfterPayload
        ⟨left, y, payloadMarker b :: right⟩ := by
  cases b <;> rfl

theorem oneStep_returnPayload_separator
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.returnSepLenAfterPayload
        ⟨y :: left, MStarParserMicrocode.sepLen, right⟩) =
      .running MStarParserMicrocode.findLen
        ⟨left, y, MStarParserMicrocode.sepLen :: right⟩ := by rfl

theorem run_findLen_paired (n : ℕ)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work n
      (.running MStarParserMicrocode.findLen
        (MStarParserExecution.beforeLeftRepeat n MStarParserMicrocode.pairedLen
          left y right)) =
      .running MStarParserMicrocode.findLen
        (MStarParserExecution.afterLeftRepeat n MStarParserMicrocode.pairedLen
          left y right) :=
  MStarParserExecution.run_left_repeat_of zero one work _ _
    oneStep_findLen_paired n left y right

theorem run_seekSepLen_paired (n : ℕ)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work n
      (.running MStarParserMicrocode.seekSepLenForPayload
        (MStarParserExecution.beforeRightRepeat n MStarParserMicrocode.pairedLen
          left y right)) =
      .running MStarParserMicrocode.seekSepLenForPayload
        (MStarParserExecution.afterRightRepeat n MStarParserMicrocode.pairedLen
          left y right) :=
  MStarParserExecution.run_right_repeat_of zero one work _ _
    oneStep_seekSepLen_paired n left y right

theorem run_seekSepLen_fresh (n : ℕ)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work n
      (.running MStarParserMicrocode.seekSepLenForPayload
        (MStarParserExecution.beforeRightRepeat n MStarParserMicrocode.lenDone
          left y right)) =
      .running MStarParserMicrocode.seekSepLenForPayload
        (MStarParserExecution.afterRightRepeat n MStarParserMicrocode.lenDone
          left y right) :=
  MStarParserExecution.run_right_repeat_of zero one work _ _
    oneStep_seekSepLen_fresh n left y right

theorem run_seekPayload_marked (bits : List Bool)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work bits.length
      (.running MStarParserMicrocode.seekPayload
        (MStarParserExecution.beforeRightList payloadMarker bits left y right)) =
      .running MStarParserMicrocode.seekPayload
        (MStarParserExecution.afterRightList payloadMarker bits left y right) :=
  MStarParserExecution.run_right_bool_list_of zero one work _ _
    oneStep_seekPayload_marked bits left y right

theorem run_returnPayload_marked (bits : List Bool)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work bits.length
      (.running MStarParserMicrocode.returnSepLenAfterPayload
        (MStarParserExecution.beforeLeftList payloadMarker bits left y right)) =
      .running MStarParserMicrocode.returnSepLenAfterPayload
        (MStarParserExecution.afterLeftList payloadMarker bits left y right) :=
  MStarParserExecution.run_left_bool_list_of zero one work _ _
    oneStep_returnPayload_marked bits left y right

def pairingStarted (bits : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.findLen
    (MStarParserExecution.beforeLeftRepeat bits.length
      MStarParserMicrocode.lenDone
      (List.replicate (72 * bits.length + 71) MStarParserMicrocode.padDone ++
        [MStarParserMicrocode.endpointMark])
      MStarParserMicrocode.sepPad
      (MStarParserMicrocode.sepLen ::
        bits.map (MStarParserExecution.bitCell zero one) ++
          [.core one, .core work]))

def separatorCheckStarted (bits : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.checkSeekSepPad
    (MStarParserExecution.beforeLeftRepeat bits.length
      MStarParserMicrocode.lenDone
      (List.replicate (72 * bits.length + 71) MStarParserMicrocode.padDone ++
        [MStarParserMicrocode.endpointMark])
      MStarParserMicrocode.sepPad
      (MStarParserMicrocode.sepLen ::
        bits.map (MStarParserExecution.bitCell zero one) ++
              [.core one, .core work]))

theorem paddingDoneTailMerge (m : ℕ) :
    List.replicate (72 * m) MStarParserMicrocode.padDone ++ fixedPaddingTail =
      List.replicate (72 * m + 71) MStarParserMicrocode.padDone ++
        [MStarParserMicrocode.endpointMark] := by
  unfold fixedPaddingTail
  rw [← List.append_assoc, ← List.replicate_add]

theorem reaches_separatorCheckStarted (bits : List Bool) :
    MStarParserExecution.Reaches zero one work
      (lenFinished bits.length
        (bits.map (MStarParserExecution.bitCell zero one) ++
          [.core one, .core work]))
      (separatorCheckStarted bits) := by
  apply MStarParserExecution.reaches_of_oneStep
  unfold lenFinished
  rw [paddingDoneTailMerge]
  cases bits with
  | nil =>
      simp [lenFinished, separatorCheckStarted,
        MStarParserExecution.beforeLeftRepeat, fixedPaddingTail,
        oneStep_scanLen_separator]
  | cons b bs =>
      simp [lenFinished, separatorCheckStarted,
        MStarParserExecution.beforeLeftRepeat, fixedPaddingTail,
        oneStep_scanLen_separator, List.replicate_succ,
        List.append_assoc]

def separatorCheckAtPad (bits : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.checkSeekSepPad
    ⟨List.replicate (72 * bits.length + 71) MStarParserMicrocode.padDone ++
        [MStarParserMicrocode.endpointMark],
      MStarParserMicrocode.sepPad,
      List.replicate bits.length MStarParserMicrocode.lenDone ++
        MStarParserMicrocode.sepLen ::
        (bits.map (MStarParserExecution.bitCell zero one) ++
          [.core one, .core work])⟩

theorem reaches_separatorCheckAtPad (bits : List Bool) :
    MStarParserExecution.Reaches zero one work
      (separatorCheckStarted bits) (separatorCheckAtPad bits) := by
  refine ⟨bits.length, ?_⟩
  rw [show separatorCheckStarted bits =
      .running MStarParserMicrocode.checkSeekSepPad
        (MStarParserExecution.beforeLeftRepeat bits.length
          MStarParserMicrocode.lenDone
          (List.replicate (72 * bits.length + 71) MStarParserMicrocode.padDone ++
            [MStarParserMicrocode.endpointMark])
          MStarParserMicrocode.sepPad
          (MStarParserMicrocode.sepLen ::
            bits.map (MStarParserExecution.bitCell zero one) ++
              [.core one, .core work])) by rfl]
  rw [run_checkSeek_lenDone]
  rfl

def paddingCheckStarted (bits : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.checkPad
    ⟨List.replicate (72 * bits.length + 70) MStarParserMicrocode.padDone ++
        [MStarParserMicrocode.endpointMark],
      MStarParserMicrocode.padDone,
      MStarParserMicrocode.sepPad ::
        (List.replicate bits.length MStarParserMicrocode.lenDone ++
          MStarParserMicrocode.sepLen ::
          (bits.map (MStarParserExecution.bitCell zero one) ++
            [.core one, .core work]))⟩

theorem reaches_paddingCheckStarted (bits : List Bool) :
    MStarParserExecution.Reaches zero one work
      (separatorCheckAtPad bits) (paddingCheckStarted bits) := by
  apply MStarParserExecution.reaches_of_oneStep
  have hn : 72 * bits.length + 71 = (72 * bits.length + 70) + 1 := by omega
  simp [separatorCheckAtPad, paddingCheckStarted, hn,
    List.replicate_succ, oneStep_checkSeek_sepPad,
    List.append_assoc]

def paddingCheckAtEndpoint (bits : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.checkPad
    ⟨[], MStarParserMicrocode.endpointMark,
      List.replicate (72 * bits.length + 71) MStarParserMicrocode.padDone ++
      MStarParserMicrocode.sepPad ::
        (List.replicate bits.length MStarParserMicrocode.lenDone ++
          MStarParserMicrocode.sepLen ::
          (bits.map (MStarParserExecution.bitCell zero one) ++
            [.core one, .core work]))⟩

theorem reaches_paddingCheckAtEndpoint (bits : List Bool) :
    MStarParserExecution.Reaches zero one work
      (paddingCheckStarted bits) (paddingCheckAtEndpoint bits) := by
  refine ⟨72 * bits.length + 71, ?_⟩
  have hn : 72 * bits.length + 71 = (72 * bits.length + 70) + 1 := by omega
  rw [show paddingCheckStarted bits =
      .running MStarParserMicrocode.checkPad
        (MStarParserExecution.beforeLeftRepeat (72 * bits.length + 71)
          MStarParserMicrocode.padDone [] MStarParserMicrocode.endpointMark
          (MStarParserMicrocode.sepPad ::
            (List.replicate bits.length MStarParserMicrocode.lenDone ++
              MStarParserMicrocode.sepLen ::
              (bits.map (MStarParserExecution.bitCell zero one) ++
                [.core one, .core work])))) by
    unfold paddingCheckStarted
    rw [hn]
    rfl]
  rw [run_checkPad_done]
  rfl

def paddingReturnStarted (bits : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.checkReturnSepPad
    ⟨[MStarParserMicrocode.endpointMark], MStarParserMicrocode.padDone,
      List.replicate (72 * bits.length + 70) MStarParserMicrocode.padDone ++
      MStarParserMicrocode.sepPad ::
        (List.replicate bits.length MStarParserMicrocode.lenDone ++
          MStarParserMicrocode.sepLen ::
          (bits.map (MStarParserExecution.bitCell zero one) ++
            [.core one, .core work]))⟩

theorem reaches_paddingReturnStarted (bits : List Bool) :
    MStarParserExecution.Reaches zero one work
      (paddingCheckAtEndpoint bits) (paddingReturnStarted bits) := by
  apply MStarParserExecution.reaches_of_oneStep
  have hn : 72 * bits.length + 71 = (72 * bits.length + 70) + 1 := by omega
  simp [paddingCheckAtEndpoint, paddingReturnStarted, hn,
    List.replicate_succ, oneStep_checkPad_endpoint,
    List.append_assoc]

def paddingReturnAtSep (bits : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.checkReturnSepPad
    ⟨List.replicate (72 * bits.length + 71) MStarParserMicrocode.padDone ++
        [MStarParserMicrocode.endpointMark],
      MStarParserMicrocode.sepPad,
      List.replicate bits.length MStarParserMicrocode.lenDone ++
        MStarParserMicrocode.sepLen ::
        (bits.map (MStarParserExecution.bitCell zero one) ++
          [.core one, .core work])⟩

theorem reaches_paddingReturnAtSep (bits : List Bool) :
    MStarParserExecution.Reaches zero one work
      (paddingReturnStarted bits) (paddingReturnAtSep bits) := by
  refine ⟨72 * bits.length + 71, ?_⟩
  rw [show paddingReturnStarted bits =
      .running MStarParserMicrocode.checkReturnSepPad
        (MStarParserExecution.beforeRightRepeat (72 * bits.length + 71)
          MStarParserMicrocode.padDone [MStarParserMicrocode.endpointMark]
          MStarParserMicrocode.sepPad
          (List.replicate bits.length MStarParserMicrocode.lenDone ++
            MStarParserMicrocode.sepLen ::
            (bits.map (MStarParserExecution.bitCell zero one) ++
              [.core one, .core work]))) by
    have hn : 72 * bits.length + 71 = (72 * bits.length + 70) + 1 := by omega
    unfold paddingReturnStarted MStarParserExecution.beforeRightRepeat
    rw [hn]]
  rw [run_checkReturnPad_done]
  rfl

def lengthReturnStarted (bits : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.checkReturnSepLen
    (MStarParserExecution.beforeRightRepeat bits.length
      MStarParserMicrocode.lenDone
      (MStarParserMicrocode.sepPad ::
        (List.replicate (72 * bits.length + 71) MStarParserMicrocode.padDone ++
          [MStarParserMicrocode.endpointMark]))
      MStarParserMicrocode.sepLen
      (bits.map (MStarParserExecution.bitCell zero one) ++
        [.core one, .core work]))

theorem reaches_lengthReturnStarted (bits : List Bool) :
    MStarParserExecution.Reaches zero one work
      (paddingReturnAtSep bits) (lengthReturnStarted bits) := by
  apply MStarParserExecution.reaches_of_oneStep
  cases bits with
  | nil =>
      simp [paddingReturnAtSep, lengthReturnStarted,
        MStarParserExecution.beforeRightRepeat,
        oneStep_checkReturnPad_sep]
  | cons b bs =>
      simp [paddingReturnAtSep, lengthReturnStarted,
        MStarParserExecution.beforeRightRepeat,
        oneStep_checkReturnPad_sep, List.replicate_succ,
        List.append_assoc]

def lengthReturnAtSep (bits : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.checkReturnSepLen
    ⟨List.replicate bits.length MStarParserMicrocode.lenDone ++
        MStarParserMicrocode.sepPad ::
        (List.replicate (72 * bits.length + 71) MStarParserMicrocode.padDone ++
          [MStarParserMicrocode.endpointMark]),
      MStarParserMicrocode.sepLen,
      bits.map (MStarParserExecution.bitCell zero one) ++
        [.core one, .core work]⟩

theorem reaches_lengthReturnAtSep (bits : List Bool) :
    MStarParserExecution.Reaches zero one work
      (lengthReturnStarted bits) (lengthReturnAtSep bits) := by
  exact ⟨bits.length, run_checkReturnLen_done bits.length
    (MStarParserMicrocode.sepPad ::
      (List.replicate (72 * bits.length + 71) MStarParserMicrocode.padDone ++
        [MStarParserMicrocode.endpointMark]))
    MStarParserMicrocode.sepLen
    (bits.map (MStarParserExecution.bitCell zero one) ++
      [(MStarOuterProgram.Tape.core one : MStarOuterProgram.Tape CoreTape),
        MStarOuterProgram.Tape.core work])⟩

theorem reaches_pairingStarted (bits : List Bool) :
    MStarParserExecution.Reaches zero one work
      (lengthReturnAtSep bits) (pairingStarted bits) := by
  apply MStarParserExecution.reaches_of_oneStep
  cases bits with
  | nil =>
      simp [lengthReturnAtSep, pairingStarted,
        MStarParserExecution.beforeLeftRepeat,
        oneStep_checkReturnLen_sep]
  | cons b bs =>
      simp [lengthReturnAtSep, pairingStarted,
        MStarParserExecution.beforeLeftRepeat,
        oneStep_checkReturnLen_sep, List.replicate_succ,
        List.append_assoc]

def pairingPad (m : ℕ) : List (MStarOuterProgram.Tape CoreTape) :=
  List.replicate (72 * m + 71) MStarParserMicrocode.padDone ++
    [MStarParserMicrocode.endpointMark]

theorem replicate_cons_rotate {A : Type*} (n : ℕ) (a : A) (tail : List A) :
    List.replicate n a ++ a :: tail =
      a :: (List.replicate n a ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

def pairBefore (done : List Bool) (b : Bool) (rest : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.findLen
    (MStarParserExecution.beforeLeftRepeat done.length
      MStarParserMicrocode.pairedLen
      (List.replicate rest.length MStarParserMicrocode.lenDone ++
        MStarParserMicrocode.sepPad :: pairingPad (done.length + rest.length + 1))
      MStarParserMicrocode.lenDone
      (MStarParserMicrocode.sepLen ::
        done.map payloadMarker ++
        MStarParserExecution.bitCell zero one b ::
        (rest.map (MStarParserExecution.bitCell zero one) ++
          [.core one, .core work])))

def pairAfter (done : List Bool) (rest : List Bool) :
    MStarParserExecution.Result CoreTape :=
  match rest with
  | [] =>
      .running MStarParserMicrocode.findLen
        ⟨pairingPad done.length, MStarParserMicrocode.sepPad,
          List.replicate done.length MStarParserMicrocode.pairedLen ++
            MStarParserMicrocode.sepLen :: done.map payloadMarker ++
              [.core one, .core work]⟩
  | b :: bs => pairBefore done b bs

theorem pairingStarted_eq_pairAfter_nil (bits : List Bool) :
    pairingStarted bits = pairAfter [] bits := by
  cases bits with
  | nil =>
      rfl
  | cons b bs =>
      simp [pairingStarted, pairAfter, pairBefore,
        MStarParserExecution.beforeLeftRepeat, pairingPad,
        List.append_assoc]

def pairFindAtFresh (done : List Bool) (b : Bool) (rest : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.findLen
    (MStarParserExecution.afterLeftRepeat done.length
      MStarParserMicrocode.pairedLen
      (List.replicate rest.length MStarParserMicrocode.lenDone ++
        MStarParserMicrocode.sepPad :: pairingPad (done.length + rest.length + 1))
      MStarParserMicrocode.lenDone
      (MStarParserMicrocode.sepLen :: done.map payloadMarker ++
        MStarParserExecution.bitCell zero one b ::
        (rest.map (MStarParserExecution.bitCell zero one) ++
          [.core one, .core work])))

theorem reaches_pairFindAtFresh (done : List Bool) (b : Bool)
    (rest : List Bool) :
    MStarParserExecution.Reaches zero one work
      (pairBefore done b rest) (pairFindAtFresh done b rest) := by
  refine ⟨done.length, ?_⟩
  simpa [pairBefore, pairFindAtFresh] using
    (run_findLen_paired done.length
    (List.replicate rest.length MStarParserMicrocode.lenDone ++
      MStarParserMicrocode.sepPad :: pairingPad (done.length + rest.length + 1))
    MStarParserMicrocode.lenDone
    (MStarParserMicrocode.sepLen :: done.map payloadMarker ++
      MStarParserExecution.bitCell zero one b ::
      (rest.map (MStarParserExecution.bitCell zero one) ++
        [(MStarOuterProgram.Tape.core one : MStarOuterProgram.Tape CoreTape),
          MStarOuterProgram.Tape.core work])))

def pairFreshMarked (done : List Bool) (b : Bool) (rest : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.seekSepLenForPayload
    (MStarParserExecution.beforeRightRepeat done.length
      MStarParserMicrocode.pairedLen
      (MStarParserMicrocode.pairedLen ::
        List.replicate rest.length MStarParserMicrocode.lenDone ++
        MStarParserMicrocode.sepPad :: pairingPad (done.length + rest.length + 1))
      MStarParserMicrocode.sepLen
      (done.map payloadMarker ++
        MStarParserExecution.bitCell zero one b ::
        (rest.map (MStarParserExecution.bitCell zero one) ++
          [.core one, .core work])))

theorem reaches_pairFreshMarked (done : List Bool) (b : Bool)
    (rest : List Bool) :
    MStarParserExecution.Reaches zero one work
      (pairFindAtFresh done b rest) (pairFreshMarked done b rest) := by
  apply MStarParserExecution.reaches_of_oneStep
  cases done with
  | nil =>
      simp [pairFindAtFresh, pairFreshMarked,
        MStarParserExecution.afterLeftRepeat,
        MStarParserExecution.beforeRightRepeat, oneStep_findLen_fresh]
  | cons d ds =>
      simp [pairFindAtFresh, pairFreshMarked,
        MStarParserExecution.afterLeftRepeat,
        MStarParserExecution.beforeRightRepeat, oneStep_findLen_fresh,
        List.replicate_succ, List.append_assoc]

def pairAtSepLen (done : List Bool) (b : Bool) (rest : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.seekSepLenForPayload
    (MStarParserExecution.afterRightRepeat done.length
      MStarParserMicrocode.pairedLen
      (MStarParserMicrocode.pairedLen ::
        List.replicate rest.length MStarParserMicrocode.lenDone ++
        MStarParserMicrocode.sepPad :: pairingPad (done.length + rest.length + 1))
      MStarParserMicrocode.sepLen
      (done.map payloadMarker ++
        MStarParserExecution.bitCell zero one b ::
        (rest.map (MStarParserExecution.bitCell zero one) ++
          [.core one, .core work])))

theorem reaches_pairAtSepLen (done : List Bool) (b : Bool)
    (rest : List Bool) :
    MStarParserExecution.Reaches zero one work
      (pairFreshMarked done b rest) (pairAtSepLen done b rest) := by
  refine ⟨done.length, ?_⟩
  simpa [pairFreshMarked, pairAtSepLen] using
    (run_seekSepLen_paired done.length
    (MStarParserMicrocode.pairedLen ::
      (List.replicate rest.length MStarParserMicrocode.lenDone ++
        MStarParserMicrocode.sepPad :: pairingPad (done.length + rest.length + 1)))
    MStarParserMicrocode.sepLen
    (done.map payloadMarker ++
      MStarParserExecution.bitCell zero one b ::
      (rest.map (MStarParserExecution.bitCell zero one) ++
        [(MStarOuterProgram.Tape.core one : MStarOuterProgram.Tape CoreTape),
          MStarOuterProgram.Tape.core work])))

def pairPayloadStarted (done : List Bool) (b : Bool) (rest : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.seekPayload
    (MStarParserExecution.beforeRightList payloadMarker done
      (MStarParserMicrocode.sepLen ::
        List.replicate (done.length + 1) MStarParserMicrocode.pairedLen ++
        List.replicate rest.length MStarParserMicrocode.lenDone ++
        MStarParserMicrocode.sepPad :: pairingPad (done.length + rest.length + 1))
      (MStarParserExecution.bitCell zero one b)
      (rest.map (MStarParserExecution.bitCell zero one) ++
        [.core one, .core work]))

theorem reaches_pairPayloadStarted (done : List Bool) (b : Bool)
    (rest : List Bool) :
    MStarParserExecution.Reaches zero one work
      (pairAtSepLen done b rest) (pairPayloadStarted done b rest) := by
  apply MStarParserExecution.reaches_of_oneStep
  cases done with
  | nil =>
      simp [pairAtSepLen, pairPayloadStarted,
        MStarParserExecution.afterRightRepeat,
        MStarParserExecution.beforeRightList, oneStep_seekSepLen_separator]
  | cons d ds =>
      simp [pairAtSepLen, pairPayloadStarted,
        MStarParserExecution.afterRightRepeat,
        MStarParserExecution.beforeRightList, oneStep_seekSepLen_separator,
        List.replicate_succ, replicate_cons_rotate, List.append_assoc]

def pairAtPayloadBit (done : List Bool) (b : Bool) (rest : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.seekPayload
    (MStarParserExecution.afterRightList payloadMarker done
      (MStarParserMicrocode.sepLen ::
        List.replicate (done.length + 1) MStarParserMicrocode.pairedLen ++
        List.replicate rest.length MStarParserMicrocode.lenDone ++
        MStarParserMicrocode.sepPad :: pairingPad (done.length + rest.length + 1))
      (MStarParserExecution.bitCell zero one b)
      (rest.map (MStarParserExecution.bitCell zero one) ++
        [.core one, .core work]))

theorem reaches_pairAtPayloadBit (done : List Bool) (b : Bool)
    (rest : List Bool) :
    MStarParserExecution.Reaches zero one work
      (pairPayloadStarted done b rest) (pairAtPayloadBit done b rest) := by
  refine ⟨done.length, ?_⟩
  simpa [pairPayloadStarted, pairAtPayloadBit] using
    (run_seekPayload_marked done
    (MStarParserMicrocode.sepLen ::
      (List.replicate (done.length + 1) MStarParserMicrocode.pairedLen ++
        (List.replicate rest.length MStarParserMicrocode.lenDone ++
          MStarParserMicrocode.sepPad :: pairingPad (done.length + rest.length + 1))))
    (MStarParserExecution.bitCell zero one b)
    (rest.map (MStarParserExecution.bitCell zero one) ++
      [(MStarOuterProgram.Tape.core one : MStarOuterProgram.Tape CoreTape),
        MStarOuterProgram.Tape.core work]))

def pairReturnStarted (done : List Bool) (b : Bool) (rest : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.returnSepLenAfterPayload
    (MStarParserExecution.beforeLeftList payloadMarker done.reverse
      (List.replicate (done.length + 1) MStarParserMicrocode.pairedLen ++
        List.replicate rest.length MStarParserMicrocode.lenDone ++
        MStarParserMicrocode.sepPad :: pairingPad (done.length + rest.length + 1))
      MStarParserMicrocode.sepLen
      (payloadMarker b ::
        rest.map (MStarParserExecution.bitCell zero one) ++
          [.core one, .core work]))

theorem reaches_pairReturnStarted (done : List Bool) (b : Bool)
    (rest : List Bool) :
    MStarParserExecution.Reaches zero one work
      (pairAtPayloadBit done b rest) (pairReturnStarted done b rest) := by
  apply MStarParserExecution.reaches_of_oneStep
  cases hrev : done.reverse with
  | nil =>
      simp [pairAtPayloadBit, pairReturnStarted,
        MStarParserExecution.afterRightList,
        MStarParserExecution.beforeLeftList, hrev,
        oneStep_seekPayload_bit]
  | cons c cs =>
      simp [pairAtPayloadBit, pairReturnStarted,
        MStarParserExecution.afterRightList,
        MStarParserExecution.beforeLeftList, hrev,
        oneStep_seekPayload_bit, List.append_assoc]

def pairReturnedAtSep (done : List Bool) (b : Bool) (rest : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.returnSepLenAfterPayload
    (MStarParserExecution.afterLeftList payloadMarker done.reverse
      (List.replicate (done.length + 1) MStarParserMicrocode.pairedLen ++
        List.replicate rest.length MStarParserMicrocode.lenDone ++
        MStarParserMicrocode.sepPad :: pairingPad (done.length + rest.length + 1))
      MStarParserMicrocode.sepLen
      (payloadMarker b ::
        rest.map (MStarParserExecution.bitCell zero one) ++
          [.core one, .core work]))

theorem reaches_pairReturnedAtSep (done : List Bool) (b : Bool)
    (rest : List Bool) :
    MStarParserExecution.Reaches zero one work
      (pairReturnStarted done b rest) (pairReturnedAtSep done b rest) := by
  refine ⟨done.length, ?_⟩
  simpa [pairReturnStarted, pairReturnedAtSep] using
    (run_returnPayload_marked done.reverse
      (List.replicate (done.length + 1) MStarParserMicrocode.pairedLen ++
        (List.replicate rest.length MStarParserMicrocode.lenDone ++
          MStarParserMicrocode.sepPad :: pairingPad (done.length + rest.length + 1)))
      MStarParserMicrocode.sepLen
      (payloadMarker b ::
        rest.map (MStarParserExecution.bitCell zero one) ++
          [(MStarOuterProgram.Tape.core one : MStarOuterProgram.Tape CoreTape),
            MStarOuterProgram.Tape.core work]))

def pairAfterSep (done : List Bool) (b : Bool) (rest : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.findLen
    ⟨List.replicate done.length MStarParserMicrocode.pairedLen ++
        List.replicate rest.length MStarParserMicrocode.lenDone ++
        MStarParserMicrocode.sepPad :: pairingPad (done.length + rest.length + 1),
      MStarParserMicrocode.pairedLen,
      MStarParserMicrocode.sepLen :: done.map payloadMarker ++
        payloadMarker b ::
          rest.map (MStarParserExecution.bitCell zero one) ++
            [.core one, .core work]⟩

theorem reaches_pairAfterSep (done : List Bool) (b : Bool)
    (rest : List Bool) :
    MStarParserExecution.Reaches zero one work
      (pairReturnedAtSep done b rest) (pairAfterSep done b rest) := by
  apply MStarParserExecution.reaches_of_oneStep
  unfold pairReturnedAtSep pairAfterSep
  simp only [MStarParserExecution.afterLeftList, List.length_reverse,
    List.reverse_reverse]
  rw [show done.length + 1 = Nat.succ done.length by omega,
    List.replicate_succ]
  simpa only [List.cons_append, List.append_assoc] using
    (oneStep_returnPayload_separator
    (List.replicate done.length MStarParserMicrocode.pairedLen ++
      (List.replicate rest.length MStarParserMicrocode.lenDone ++
        MStarParserMicrocode.sepPad :: pairingPad (done.length + rest.length + 1)))
    MStarParserMicrocode.pairedLen
    (done.map payloadMarker ++ payloadMarker b ::
      rest.map (MStarParserExecution.bitCell zero one) ++
        [(MStarOuterProgram.Tape.core one : MStarOuterProgram.Tape CoreTape),
          MStarOuterProgram.Tape.core work]))

theorem pairAfterSep_eq_pairBefore (done : List Bool) (b c : Bool)
    (rest : List Bool) :
    pairAfterSep done b (c :: rest) = pairBefore (done ++ [b]) c rest := by
  cases done with
  | nil =>
      simp [pairAfterSep, pairBefore, MStarParserExecution.beforeLeftRepeat,
        List.map_append, List.replicate_succ, List.append_assoc]
      congr 1 <;> omega
  | cons d ds =>
      simp [pairAfterSep, pairBefore, MStarParserExecution.beforeLeftRepeat,
        List.map_append, List.replicate_succ, replicate_cons_rotate,
        List.append_assoc]
      congr 1 <;> omega

theorem reaches_pairAfter_nil (done : List Bool) (b : Bool) :
    MStarParserExecution.Reaches zero one work
      (pairAfterSep done b []) (pairAfter (done ++ [b]) []) := by
  let right : List (MStarOuterProgram.Tape CoreTape) :=
    MStarParserMicrocode.sepLen ::
      (done ++ [b]).map payloadMarker ++ [.core one, .core work]
  let z₀ : MStarParserExecution.Result CoreTape :=
    .running MStarParserMicrocode.findLen
      (MStarParserExecution.beforeLeftRepeat (done.length + 1)
        MStarParserMicrocode.pairedLen (pairingPad (done.length + 1))
        MStarParserMicrocode.sepPad right)
  let z₁ : MStarParserExecution.Result CoreTape :=
    .running MStarParserMicrocode.findLen
      (MStarParserExecution.afterLeftRepeat (done.length + 1)
        MStarParserMicrocode.pairedLen (pairingPad (done.length + 1))
        MStarParserMicrocode.sepPad right)
  have h₀ : pairAfterSep done b [] = z₀ := by
    simp [pairAfterSep, z₀, right, MStarParserExecution.beforeLeftRepeat,
      List.map_append, List.replicate_succ, pairingPad, List.append_assoc]
  have h₁ : z₁ = pairAfter (done ++ [b]) [] := by
    simp [z₁, right, pairAfter, MStarParserExecution.afterLeftRepeat,
      List.map_append, pairingPad, List.append_assoc]
  rw [h₀, ← h₁]
  exact ⟨done.length + 1, run_findLen_paired (done.length + 1)
    (pairingPad (done.length + 1)) MStarParserMicrocode.sepPad right⟩

theorem reaches_pairAfter (done : List Bool) (b : Bool) (rest : List Bool) :
    MStarParserExecution.Reaches zero one work
      (pairAfterSep done b rest) (pairAfter (done ++ [b]) rest) := by
  cases rest with
  | nil => exact reaches_pairAfter_nil done b
  | cons c cs =>
      rw [pairAfterSep_eq_pairBefore]
      exact MStarParserExecution.reaches_refl zero one work _

theorem reaches_pair_iteration (done : List Bool) (b : Bool)
    (rest : List Bool) :
    MStarParserExecution.Reaches zero one work
      (pairBefore done b rest) (pairAfter (done ++ [b]) rest) := by
  exact MStarParserExecution.reaches_trans zero one work
    (reaches_pairFindAtFresh done b rest)
    (MStarParserExecution.reaches_trans zero one work
      (reaches_pairFreshMarked done b rest)
      (MStarParserExecution.reaches_trans zero one work
        (reaches_pairAtSepLen done b rest)
        (MStarParserExecution.reaches_trans zero one work
          (reaches_pairPayloadStarted done b rest)
          (MStarParserExecution.reaches_trans zero one work
            (reaches_pairAtPayloadBit done b rest)
            (MStarParserExecution.reaches_trans zero one work
              (reaches_pairReturnStarted done b rest)
              (MStarParserExecution.reaches_trans zero one work
                (reaches_pairReturnedAtSep done b rest)
                (MStarParserExecution.reaches_trans zero one work
                  (reaches_pairAfterSep done b rest)
                  (reaches_pairAfter done b rest))))))))

theorem reaches_pairing_fold (done bits : List Bool) :
    MStarParserExecution.Reaches zero one work
      (pairAfter done bits) (pairAfter (done ++ bits) []) := by
  induction bits generalizing done with
  | nil =>
      simpa using MStarParserExecution.reaches_refl zero one work
        (pairAfter done [])
  | cons b rest ih =>
      have h := MStarParserExecution.reaches_trans zero one work
        (reaches_pair_iteration done b rest) (ih (done ++ [b]))
      simpa [pairAfter, List.append_assoc] using h

theorem oneStep_verifySeek_paired
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.verifySeekSepLen
        ⟨left, MStarParserMicrocode.pairedLen, y :: right⟩) =
      .running MStarParserMicrocode.verifySeekSepLen
        ⟨MStarParserMicrocode.pairedLen :: left, y, right⟩ := by rfl

theorem oneStep_verifySeek_separator
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.verifySeekSepLen
        ⟨left, MStarParserMicrocode.sepLen, y :: right⟩) =
      .running MStarParserMicrocode.verifyPayload
        ⟨MStarParserMicrocode.sepLen :: left, y, right⟩ := by rfl

theorem oneStep_verifyPayload_marked (b : Bool)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.verifyPayload
        ⟨left, payloadMarker b, y :: right⟩) =
      .running MStarParserMicrocode.verifyPayload
        ⟨payloadMarker b :: left, y, right⟩ := by
  cases b <;> rfl

theorem run_verifySeek_paired (n : ℕ)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work n
      (.running MStarParserMicrocode.verifySeekSepLen
        (MStarParserExecution.beforeRightRepeat n MStarParserMicrocode.pairedLen
          left y right)) =
      .running MStarParserMicrocode.verifySeekSepLen
        (MStarParserExecution.afterRightRepeat n MStarParserMicrocode.pairedLen
          left y right) :=
  MStarParserExecution.run_right_repeat_of zero one work _ _
    oneStep_verifySeek_paired n left y right

theorem run_verifyPayload_marked (bits : List Bool)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work bits.length
      (.running MStarParserMicrocode.verifyPayload
        (MStarParserExecution.beforeRightList payloadMarker bits left y right)) =
      .running MStarParserMicrocode.verifyPayload
        (MStarParserExecution.afterRightList payloadMarker bits left y right) :=
  MStarParserExecution.run_right_bool_list_of zero one work _ _
    oneStep_verifyPayload_marked bits left y right

def verificationStarted (bits : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.verifySeekSepLen
    (MStarParserExecution.beforeRightRepeat bits.length
      MStarParserMicrocode.pairedLen
      (MStarParserMicrocode.sepPad :: pairingPad bits.length)
      MStarParserMicrocode.sepLen
      (bits.map payloadMarker ++ [.core one, .core work]))

theorem reaches_verificationStarted (bits : List Bool) :
    MStarParserExecution.Reaches zero one work
      (pairAfter bits []) (verificationStarted bits) := by
  apply MStarParserExecution.reaches_of_oneStep
  cases bits with
  | nil =>
      simp [pairAfter, verificationStarted,
        MStarParserExecution.beforeRightRepeat, oneStep_findLen_finished]
  | cons b bs =>
      simp [pairAfter, verificationStarted,
        MStarParserExecution.beforeRightRepeat, oneStep_findLen_finished,
        List.replicate_succ, List.append_assoc]

def verificationAtSepLen (bits : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.verifySeekSepLen
    (MStarParserExecution.afterRightRepeat bits.length
      MStarParserMicrocode.pairedLen
      (MStarParserMicrocode.sepPad :: pairingPad bits.length)
      MStarParserMicrocode.sepLen
      (bits.map payloadMarker ++ [.core one, .core work]))

theorem reaches_verificationAtSepLen (bits : List Bool) :
    MStarParserExecution.Reaches zero one work
      (verificationStarted bits) (verificationAtSepLen bits) :=
  ⟨bits.length, run_verifySeek_paired bits.length
    (MStarParserMicrocode.sepPad :: pairingPad bits.length)
    MStarParserMicrocode.sepLen
    (bits.map payloadMarker ++
      [(MStarOuterProgram.Tape.core one : MStarOuterProgram.Tape CoreTape),
        MStarOuterProgram.Tape.core work])⟩

def payloadVerificationStarted (bits : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.verifyPayload
    (MStarParserExecution.beforeRightList payloadMarker bits
      (MStarParserMicrocode.sepLen ::
        List.replicate bits.length MStarParserMicrocode.pairedLen ++
          MStarParserMicrocode.sepPad :: pairingPad bits.length)
      (.core one) [.core work])

theorem reaches_payloadVerificationStarted (bits : List Bool) :
    MStarParserExecution.Reaches zero one work
      (verificationAtSepLen bits) (payloadVerificationStarted bits) := by
  apply MStarParserExecution.reaches_of_oneStep
  cases bits with
  | nil =>
      simp [verificationAtSepLen, payloadVerificationStarted,
        MStarParserExecution.afterRightRepeat,
        MStarParserExecution.beforeRightList, oneStep_verifySeek_separator]
  | cons b bs =>
      simp [verificationAtSepLen, payloadVerificationStarted,
        MStarParserExecution.afterRightRepeat,
        MStarParserExecution.beforeRightList, oneStep_verifySeek_separator,
        List.replicate_succ, List.append_assoc]

def verificationAtLeadingOne (bits : List Bool) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.verifyPayload
    (MStarParserExecution.afterRightList payloadMarker bits
      (MStarParserMicrocode.sepLen ::
        List.replicate bits.length MStarParserMicrocode.pairedLen ++
          MStarParserMicrocode.sepPad :: pairingPad bits.length)
      (.core one) [.core work])

theorem reaches_verificationAtLeadingOne (bits : List Bool) :
    MStarParserExecution.Reaches zero one work
      (payloadVerificationStarted bits) (verificationAtLeadingOne bits) :=
  ⟨bits.length, by
    simpa [payloadVerificationStarted, verificationAtLeadingOne] using
      (run_verifyPayload_marked bits
        (MStarParserMicrocode.sepLen ::
          (List.replicate bits.length MStarParserMicrocode.pairedLen ++
            MStarParserMicrocode.sepPad :: pairingPad bits.length))
        (.core one) [(.core work : MStarOuterProgram.Tape CoreTape)])⟩

def finalZipper (bits : List Bool) :
    MStarParserExecution.Zipper (MStarOuterProgram.Tape CoreTape) :=
  ⟨MStarParserMicrocode.endpointMark :: bits.reverse.map payloadMarker ++
      MStarParserMicrocode.sepLen ::
        List.replicate bits.length MStarParserMicrocode.pairedLen ++
          MStarParserMicrocode.sepPad :: pairingPad bits.length,
    .core work, []⟩

theorem run_final_three
    (left : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work 3
      (.running MStarParserMicrocode.verifyPayload
        ⟨left, .core one, [.core work]⟩) =
      .copyReady
        ⟨MStarParserMicrocode.endpointMark :: left, .core work, []⟩ := by
  rfl

theorem reaches_final_copyReady (bits : List Bool) :
    MStarParserExecution.Reaches zero one work
      (verificationAtLeadingOne bits) (.copyReady (finalZipper bits)) := by
  refine ⟨3, ?_⟩
  simpa [verificationAtLeadingOne, finalZipper,
    MStarParserExecution.afterRightList, List.map_reverse] using
    run_final_three
      (bits.reverse.map payloadMarker ++
        (MStarParserMicrocode.sepLen ::
          (List.replicate bits.length MStarParserMicrocode.pairedLen ++
            MStarParserMicrocode.sepPad :: pairingPad bits.length)))

theorem reaches_pairing_and_final_accept (bits : List Bool) :
    MStarParserExecution.Reaches zero one work
      (pairingStarted bits) (.copyReady (finalZipper bits)) := by
  rw [pairingStarted_eq_pairAfter_nil]
  exact MStarParserExecution.reaches_trans zero one work
    (reaches_pairing_fold [] bits)
    (MStarParserExecution.reaches_trans zero one work
      (reaches_verificationStarted bits)
      (MStarParserExecution.reaches_trans zero one work
        (reaches_verificationAtSepLen bits)
        (MStarParserExecution.reaches_trans zero one work
          (reaches_payloadVerificationStarted bits)
          (MStarParserExecution.reaches_trans zero one work
            (reaches_verificationAtLeadingOne bits)
            (reaches_final_copyReady bits)))))

def beforeScanZeros (n : ℕ)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.Zipper (MStarOuterProgram.Tape CoreTape) :=
  match n with
  | 0 => ⟨left, y, right⟩
  | k + 1 => ⟨left, .core zero,
      List.replicate k (.core zero) ++ y :: right⟩

def afterScanZeros (n : ℕ)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.Zipper (MStarOuterProgram.Tape CoreTape) :=
  ⟨List.replicate n (.core zero) ++ left, y, right⟩

theorem oneStep_beforeScanZeros_succ (n : ℕ)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.oneStep zero one work
      (.running MStarParserMicrocode.scanPad
        (beforeScanZeros (n + 1) left y right)) =
      .running MStarParserMicrocode.scanPad
        (beforeScanZeros n (.core zero :: left) y right) := by
  cases n <;>
    simp [beforeScanZeros, List.replicate_succ,
      oneStep_scanPad_zero, List.append_assoc]

theorem run_scanPad_zeros (n : ℕ)
    (left : List (MStarOuterProgram.Tape CoreTape))
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work n
      (.running MStarParserMicrocode.scanPad
        (beforeScanZeros n left y right)) =
      .running MStarParserMicrocode.scanPad
        (afterScanZeros n left y right) := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      rw [MStarParserExecution.run_succ,
        oneStep_beforeScanZeros_succ]
      rw [ih]
      rw [show afterScanZeros n (.core zero :: left) y right =
          afterScanZeros (n + 1) left y right by
        apply MStarParserExecution.Zipper.ext <;>
          simp [afterScanZeros, List.replicate_succ', List.append_assoc]]

theorem run_fixed_72_beforeScanZeros (n : ℕ)
    (y : MStarOuterProgram.Tape CoreTape)
    (right : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work 72
      (.running (MStarParserMicrocode.fixed 0)
        ⟨[], .core zero,
          List.replicate 71 (.core zero) ++
            List.replicate n (.core zero) ++ y :: right⟩) =
      .running (MStarParserMicrocode.fixed ⟨72, by decide⟩)
        (beforeScanZeros n fixedPaddingTail y right) := by
  cases n with
  | zero =>
      simpa [beforeScanZeros, fixedPaddingTail, List.append_assoc] using
        run_fixed_72 y right
  | succ n =>
      simpa [beforeScanZeros, fixedPaddingTail, List.replicate_succ,
        List.append_assoc] using
        run_fixed_72 (.core zero)
          (List.replicate n (.core zero) ++ y :: right)

def fixedPaddingPassed (x : ConcretePakSide.Word) :
    MStarParserExecution.Result CoreTape :=
  .running (MStarParserMicrocode.fixed ⟨72, by decide⟩)
    (beforeScanZeros (72 * x.length) fixedPaddingTail (.core one)
      (List.replicate x.length (.core zero) ++ .core one ::
        x.reverse.map (MStarParserExecution.bitCell zero one) ++
          [.core one, .core work]))

theorem reaches_fixedPaddingPassed (x : ConcretePakSide.Word) :
    MStarParserExecution.Reaches zero one work
      (MStarParserExecution.initial zero one work
        (ConcretePakSide.encodedWord x)) (fixedPaddingPassed x) := by
  refine ⟨72, ?_⟩
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

def paddingScanStarted (x : ConcretePakSide.Word) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.scanPad
    (beforeScanZeros (72 * x.length) fixedPaddingTail (.core one)
      (List.replicate x.length (.core zero) ++ .core one ::
        x.reverse.map (MStarParserExecution.bitCell zero one) ++
          [.core one, .core work]))

theorem reaches_paddingScanStarted (x : ConcretePakSide.Word) :
    MStarParserExecution.Reaches zero one work
      (fixedPaddingPassed x) (paddingScanStarted x) := by
  apply MStarParserExecution.reaches_of_oneStep
  unfold fixedPaddingPassed paddingScanStarted
  exact oneStep_fixed_72 _

def paddingScanAtSeparator (x : ConcretePakSide.Word) :
    MStarParserExecution.Result CoreTape :=
  .running MStarParserMicrocode.scanPad
    (afterScanZeros (72 * x.length) fixedPaddingTail (.core one)
      (List.replicate x.length (.core zero) ++ .core one ::
        x.reverse.map (MStarParserExecution.bitCell zero one) ++
          [.core one, .core work]))

theorem reaches_paddingScanAtSeparator (x : ConcretePakSide.Word) :
    MStarParserExecution.Reaches zero one work
      (paddingScanStarted x) (paddingScanAtSeparator x) :=
  ⟨72 * x.length, by
    simpa [paddingScanStarted, paddingScanAtSeparator] using
      (run_scanPad_zeros (72 * x.length) fixedPaddingTail (.core one)
        (List.replicate x.length
            (MStarOuterProgram.Tape.core zero : MStarOuterProgram.Tape CoreTape) ++
          (.core one ::
            (x.reverse.map (MStarParserExecution.bitCell zero one) ++
              [.core one, .core work]))))⟩

theorem reaches_lenStarted (x : ConcretePakSide.Word) :
    MStarParserExecution.Reaches zero one work
      (paddingScanAtSeparator x)
      (lenStarted x.length
        (x.reverse.map (MStarParserExecution.bitCell zero one) ++
          [.core one, .core work])) := by
  apply MStarParserExecution.reaches_of_oneStep
  cases x with
  | nil =>
      simp [paddingScanAtSeparator, afterScanZeros, lenStarted,
        MStarParserExecution.beforeRightRepeat, fixedPaddingTail,
        oneStep_scanPad_separator]
  | cons b bs =>
      simp [paddingScanAtSeparator, afterScanZeros, lenStarted,
        MStarParserExecution.beforeRightRepeat, fixedPaddingTail,
        oneStep_scanPad_separator, List.replicate_succ, List.append_assoc]

theorem reaches_parser_encodedWord (x : ConcretePakSide.Word) :
    MStarParserExecution.Reaches zero one work
      (MStarParserExecution.initial zero one work
        (ConcretePakSide.encodedWord x))
      (.copyReady (finalZipper x.reverse)) := by
  have h₀ := reaches_fixedPaddingPassed x
  have h₁ := reaches_paddingScanStarted x
  have h₂ := reaches_paddingScanAtSeparator x
  have h₃ := reaches_lenStarted x
  have h₄ := reaches_all_length_markers x.length
    (x.reverse.map (MStarParserExecution.bitCell zero one) ++
      [(MStarOuterProgram.Tape.core one : MStarOuterProgram.Tape CoreTape),
        MStarOuterProgram.Tape.core work])
  have h₅ : MStarParserExecution.Reaches zero one work
      (lenFinished x.length
        (x.reverse.map (MStarParserExecution.bitCell zero one) ++
          [.core one, .core work]))
      (separatorCheckStarted x.reverse) := by
    simpa using reaches_separatorCheckStarted x.reverse
  have h₆ := reaches_separatorCheckAtPad x.reverse
  have h₇ := reaches_paddingCheckStarted x.reverse
  have h₈ := reaches_paddingCheckAtEndpoint x.reverse
  have h₉ := reaches_paddingReturnStarted x.reverse
  have h₁₀ := reaches_paddingReturnAtSep x.reverse
  have h₁₁ := reaches_lengthReturnStarted x.reverse
  have h₁₂ := reaches_lengthReturnAtSep x.reverse
  have h₁₃ := reaches_pairingStarted x.reverse
  have h₁₄ := reaches_pairing_and_final_accept x.reverse
  have h₀₁ := MStarParserExecution.reaches_trans zero one work h₀ h₁
  have h₀₂ := MStarParserExecution.reaches_trans zero one work h₀₁ h₂
  have h₀₃ := MStarParserExecution.reaches_trans zero one work h₀₂ h₃
  have h₀₄ := MStarParserExecution.reaches_trans zero one work h₀₃ h₄
  have h₀₅ := MStarParserExecution.reaches_trans zero one work h₀₄ h₅
  have h₀₆ := MStarParserExecution.reaches_trans zero one work h₀₅ h₆
  have h₀₇ := MStarParserExecution.reaches_trans zero one work h₀₆ h₇
  have h₀₈ := MStarParserExecution.reaches_trans zero one work h₀₇ h₈
  have h₀₉ := MStarParserExecution.reaches_trans zero one work h₀₈ h₉
  have h₀₁₀ := MStarParserExecution.reaches_trans zero one work h₀₉ h₁₀
  have h₀₁₁ := MStarParserExecution.reaches_trans zero one work h₀₁₀ h₁₁
  have h₀₁₂ := MStarParserExecution.reaches_trans zero one work h₀₁₁ h₁₂
  have h₀₁₃ := MStarParserExecution.reaches_trans zero one work h₀₁₂ h₁₃
  have hall := MStarParserExecution.reaches_trans zero one work h₀₁₃ h₁₄
  exact hall

theorem parser_accepts_encodedWord (x : ConcretePakSide.Word) :
    MStarParserExecution.Accepts zero one work
      (ConcretePakSide.encodedWord x) := by
  rcases reaches_parser_encodedWord x with ⟨fuel, hrun⟩
  exact ⟨fuel, finalZipper x.reverse, hrun⟩

theorem parser_encodedWord_output_unique (x : ConcretePakSide.Word)
    (fuel : ℕ) (z : MStarParserExecution.Zipper
      (MStarOuterProgram.Tape CoreTape))
    (h : MStarParserExecution.run zero one work fuel
      (MStarParserExecution.initial zero one work
        (ConcretePakSide.encodedWord x)) = .copyReady z) :
    z = finalZipper x.reverse := by
  rcases reaches_parser_encodedWord x with ⟨canonicalFuel, hcanonical⟩
  exact MStarParserExecution.copyReady_output_unique zero one work _
    fuel canonicalFuel z (finalZipper x.reverse) h hcanonical

/-- The successful parser trace remains valid after appending any finite
workspace suffix at the far right of the encoded input row. -/
theorem reaches_parser_encodedWord_with_tail (x : ConcretePakSide.Word)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.Reaches zero one work
      (MStarParserExecution.extendResultRight
        (MStarParserExecution.initial zero one work
          (ConcretePakSide.encodedWord x)) tail)
      (.copyReady (MStarParserExecution.extendRight
        (finalZipper x.reverse) tail)) :=
  MStarParserExecution.reaches_extendResultRight_to_copyReady zero one work
    _ _ tail (reaches_parser_encodedWord x)

end PakFixedPolyomino.MStarConcreteAlphabet
