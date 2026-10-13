import PakFixedPolyomino.PakOuterFrontNumericBound

/-! # Explicit fuel for the remaining parser phases -/

namespace PakFixedPolyomino.PakOuterParserNumericSuffix

open MStarConcreteAlphabet

/-- Exact cost of marking one length cell, crossing the already-paid length
and padding blocks, and stopping on the first unpaid padding cell. -/
def firstUnmarkedFuel (j : ℕ) : ℕ := 1 + (j + (1 + 72 * j))

theorem firstUnmarkedFuel_closed (j : ℕ) :
    firstUnmarkedFuel j = 73 * j + 2 := by
  simp [firstUnmarkedFuel]
  ring

theorem run_first_unmarked (j r : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work (firstUnmarkedFuel j)
      (beforeLenIteration j r tail) = firstUnmarkedState j r tail := by
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
  have h₀₁ : MStarParserExecution.run zero one work 1
      (beforeLenIteration j r tail) = z₁ := by
    change MStarParserExecution.oneStep zero one work
      (beforeLenIteration j r tail) = z₁
    cases j <;>
      simp [beforeLenIteration, z₁, padBelow, rightRest,
        MStarParserExecution.beforeLeftRepeat, oneStep_scanLen_zero,
        List.replicate_succ, List.append_assoc]
  have h₁₂ : MStarParserExecution.run zero one work j z₁ = z₂ := by
    exact run_seekSepPad_lenDone j padBelow MStarParserMicrocode.sepPad
      (MStarParserMicrocode.lenDone :: rightRest)
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
  have h₂₃ : MStarParserExecution.run zero one work 1 z₂ = z₃ := by
    change MStarParserExecution.oneStep zero one work z₂ = z₃
    have hpad : padBelow =
        List.replicate (72 * j) MStarParserMicrocode.padDone ++
          .core zero :: low := by
      simp only [padBelow, low]
      rw [List.append_assoc, unpaid_padding_shape]
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
  have h₃₄ : MStarParserExecution.run zero one work (72 * j) z₃ = z₄ := by
    exact run_seekUnmarked_padDone (72 * j) low (.core zero)
      (MStarParserMicrocode.sepPad :: lenRight)
  have h₄f : z₄ = firstUnmarkedState j r tail := by
    simp [z₄, firstUnmarkedState, low, lenRight, rightRest,
      MStarParserExecution.afterLeftRepeat, List.append_assoc]
  unfold firstUnmarkedFuel
  rw [MStarParserExecution.run_add, h₀₁,
    MStarParserExecution.run_add, h₁₂,
    MStarParserExecution.run_add, h₂₃, h₃₄, h₄f]

def crossFuel : ℕ := 73

theorem run_afterCrossLast (j : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work crossFuel
      (firstUnmarkedState j 0 tail) = afterCrossLast j tail := by
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
  have h₀₁ : MStarParserExecution.run zero one work 1
      (firstUnmarkedState j 0 tail) = z₁ := by
    change MStarParserExecution.oneStep zero one work
      (firstUnmarkedState j 0 tail) = z₁
    simp [firstUnmarkedState, z₁, oldRight, fixedPaddingTail,
      oneStep_seekUnmarked_zero, List.replicate_add,
      List.replicate_succ, List.append_assoc]
  have h₁f : MStarParserExecution.run zero one work 72 z₁ =
      afterCrossLast j tail := by
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
  unfold crossFuel
  rw [show 73 = 1 + 72 by omega, MStarParserExecution.run_add, h₀₁, h₁f]

theorem run_afterCrossSucc (j k : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work crossFuel
      (firstUnmarkedState j (k + 1) tail) = afterCrossSucc j k tail := by
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
  have h₀₁ : MStarParserExecution.run zero one work 1
      (firstUnmarkedState j (k + 1) tail) = z₁ := by
    change MStarParserExecution.oneStep zero one work
      (firstUnmarkedState j (k + 1) tail) = z₁
    have hcount : 72 * (k + 1 + 1) - 1 =
        1 + (70 + 1 + (72 * (k + 1) - 1)) := by omega
    simp [firstUnmarkedState, z₁, low, oldRight,
      oneStep_seekUnmarked_zero, hcount, List.replicate_add,
      List.replicate_succ, List.append_assoc]
  have h₁f : MStarParserExecution.run zero one work 72 z₁ =
      afterCrossSucc j k tail := by
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
  unfold crossFuel
  rw [show 73 = 1 + 72 by omega, MStarParserExecution.run_add, h₀₁, h₁f]

def returnFuel (j : ℕ) : ℕ := 73 * j + 76

theorem run_afterLenLast (j : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work (returnFuel j)
      (afterCrossLast j tail) = afterLenIteration j 0 tail := by
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
  have h₀₁ : MStarParserExecution.run zero one work nPad
      (afterCrossLast j tail) = z₁ := by
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
  have h₁₂ : MStarParserExecution.run zero one work 1 z₁ = z₂ := by
    change MStarParserExecution.oneStep zero one work z₁ = z₂
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
  have h₂₃ : MStarParserExecution.run zero one work (j + 1) z₂ = z₃ := by
    exact run_returnLen_done (j + 1)
      (MStarParserMicrocode.sepPad :: padLeft) (.core one) tail
  have h₃f : MStarParserExecution.run zero one work 1 z₃ =
      afterLenIteration j 0 tail := by
    change MStarParserExecution.oneStep zero one work z₃ = _
    rw [show z₃ = .running MStarParserMicrocode.returnLen
        ⟨List.replicate (j + 1) MStarParserMicrocode.lenDone ++
            MStarParserMicrocode.sepPad :: padLeft,
          .core one, tail⟩ by rfl]
    rw [oneStep_returnLen_one]
    simp [afterLenIteration, padLeft, low, nPad, fixedPaddingTail,
      MStarParserExecution.beforeRightRepeat, List.replicate_add,
      List.append_assoc]
  unfold returnFuel
  rw [show 73 * j + 76 = nPad + (1 + ((j + 1) + 1)) by
      dsimp [nPad]; omega,
    MStarParserExecution.run_add, h₀₁,
    MStarParserExecution.run_add, h₁₂,
    MStarParserExecution.run_add, h₂₃, h₃f]

def lenIterationFuel (j : ℕ) : ℕ :=
  firstUnmarkedFuel j + (crossFuel + returnFuel j)

theorem lenIterationFuel_closed (j : ℕ) :
    lenIterationFuel j = 146 * j + 151 := by
  rw [lenIterationFuel, firstUnmarkedFuel_closed]
  simp [crossFuel, returnFuel]
  omega

theorem run_len_iteration_last (j : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work (lenIterationFuel j)
      (beforeLenIteration j 0 tail) = afterLenIteration j 0 tail := by
  unfold lenIterationFuel
  rw [MStarParserExecution.run_add, run_first_unmarked,
    MStarParserExecution.run_add, run_afterCrossLast, run_afterLenLast]

theorem run_afterLenSucc (j k : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work (returnFuel j)
      (afterCrossSucc j k tail) = afterLenIteration j (k + 1) tail := by
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
  have hstart : MStarParserExecution.run zero one work 1
      (afterCrossSucc j k tail) = z₀ := by
    change MStarParserExecution.oneStep zero one work
      (afterCrossSucc j k tail) = z₀
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
    rw [oneStep_returnSepPad_zero, hz₀]
  let padLeft : List (MStarOuterProgram.Tape CoreTape) :=
    List.replicate nPad MStarParserMicrocode.padDone ++ .core zero :: low
  let z₁ : MStarParserExecution.Result CoreTape :=
    .running MStarParserMicrocode.returnSepPad
      (MStarParserExecution.afterRightRepeat nPad MStarParserMicrocode.padDone
        (.core zero :: low) MStarParserMicrocode.sepPad lenRight)
  have h₀₁ : MStarParserExecution.run zero one work nPad z₀ = z₁ := by
    exact run_returnSepPad_done nPad (.core zero :: low)
      MStarParserMicrocode.sepPad lenRight
  let z₂ : MStarParserExecution.Result CoreTape :=
    .running MStarParserMicrocode.returnLen
      (MStarParserExecution.beforeRightRepeat (j + 1)
        MStarParserMicrocode.lenDone
        (MStarParserMicrocode.sepPad :: padLeft) (.core zero)
        (List.replicate k (.core zero) ++ .core one :: tail))
  have h₁₂ : MStarParserExecution.run zero one work 1 z₁ = z₂ := by
    change MStarParserExecution.oneStep zero one work z₁ = z₂
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
  have h₂₃ : MStarParserExecution.run zero one work (j + 1) z₂ = z₃ := by
    exact run_returnLen_done (j + 1)
      (MStarParserMicrocode.sepPad :: padLeft) (.core zero)
      (List.replicate k (.core zero) ++ .core one :: tail)
  have h₃f : MStarParserExecution.run zero one work 1 z₃ =
      afterLenIteration j (k + 1) tail := by
    change MStarParserExecution.oneStep zero one work z₃ = _
    rw [show z₃ = .running MStarParserMicrocode.returnLen
        ⟨List.replicate (j + 1) MStarParserMicrocode.lenDone ++
            MStarParserMicrocode.sepPad :: padLeft,
          .core zero, List.replicate k (.core zero) ++ .core one :: tail⟩ by rfl]
    rw [oneStep_returnLen_zero]
    have hlow : .core zero :: low =
        List.replicate (72 * (k + 1)) (.core zero) ++ fixedPaddingTail :=
      (unpaid_padding_shape k).symm
    simp [afterLenIteration, padLeft, nPad,
      MStarParserExecution.beforeRightRepeat, List.replicate_succ,
      List.append_assoc]
    rw [hlow]
  unfold returnFuel
  rw [show 73 * j + 76 = 1 + (nPad + (1 + ((j + 1) + 1))) by
      dsimp [nPad]; omega,
    MStarParserExecution.run_add, hstart,
    MStarParserExecution.run_add, h₀₁,
    MStarParserExecution.run_add, h₁₂,
    MStarParserExecution.run_add, h₂₃, h₃f]

theorem run_len_iteration_succ (j k : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work (lenIterationFuel j)
      (beforeLenIteration j (k + 1) tail) =
        afterLenIteration j (k + 1) tail := by
  unfold lenIterationFuel
  rw [MStarParserExecution.run_add, run_first_unmarked,
    MStarParserExecution.run_add, run_afterCrossSucc, run_afterLenSucc]

theorem run_len_iteration (j r : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work (lenIterationFuel j)
      (beforeLenIteration j r tail) = afterLenIteration j r tail := by
  cases r with
  | zero => exact run_len_iteration_last j tail
  | succ k => exact run_len_iteration_succ j k tail

def lenFoldFuel : ℕ → ℕ → ℕ
  | _, 0 => 0
  | j, count + 1 => lenIterationFuel j + lenFoldFuel (j + 1) count

theorem lenFoldFuel_closed (j count : ℕ) :
    lenFoldFuel j count =
      count * (146 * j + 151) + 73 * count * (count - 1) := by
  induction count generalizing j with
  | zero => simp [lenFoldFuel]
  | succ count ih =>
      rw [lenFoldFuel, ih, lenIterationFuel_closed]
      cases count <;> simp <;> ring

theorem run_len_fold (j r : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work (lenFoldFuel j (r + 1))
      (beforeLenIteration j r tail) = lenFinished (j + r + 1) tail := by
  induction r generalizing j with
  | zero =>
      rw [lenFoldFuel, MStarParserExecution.run_add, run_len_iteration_last]
      simp [lenFoldFuel, afterLenIteration_zero_eq_finished]
  | succ r ih =>
      rw [lenFoldFuel, MStarParserExecution.run_add, run_len_iteration_succ,
        afterLenIteration_succ_eq_before, ih]
      congr 2
      omega

def allLengthFuel (m : ℕ) : ℕ := lenFoldFuel 0 m

theorem allLengthFuel_closed (m : ℕ) :
    allLengthFuel m = 73 * m * m + 78 * m := by
  rw [allLengthFuel, lenFoldFuel_closed]
  cases m with
  | zero => simp
  | succ m =>
      simp only [Nat.succ_sub_one]
      ring

theorem run_all_length_markers (m : ℕ)
    (tail : List (MStarOuterProgram.Tape CoreTape)) :
    MStarParserExecution.run zero one work (allLengthFuel m)
      (lenStarted m tail) = lenFinished m tail := by
  cases m with
  | zero => rfl
  | succ m =>
      rw [allLengthFuel, lenStarted_succ_eq_before]
      simpa using run_len_fold 0 m tail

/-! ## Validation and entry to the payload-pairing loop -/

def validationFuel (bits : List Bool) : ℕ := 146 * bits.length + 147

theorem run_length_validation_to_pairing (bits : List Bool) :
    MStarParserExecution.run zero one work (validationFuel bits)
      (lenFinished bits.length
        (bits.map (MStarParserExecution.bitCell zero one) ++
          [.core one, .core work])) = pairingStarted bits := by
  let tail := bits.map (MStarParserExecution.bitCell zero one) ++
    [.core one, .core work]
  have h₀ : MStarParserExecution.run zero one work 1
      (lenFinished bits.length tail) = separatorCheckStarted bits := by
    change MStarParserExecution.oneStep zero one work
      (lenFinished bits.length tail) = separatorCheckStarted bits
    unfold lenFinished
    rw [paddingDoneTailMerge]
    cases bits with
    | nil =>
        simp [tail, lenFinished, separatorCheckStarted,
          MStarParserExecution.beforeLeftRepeat, fixedPaddingTail,
          oneStep_scanLen_separator]
    | cons b bs =>
        simp [tail, lenFinished, separatorCheckStarted,
          MStarParserExecution.beforeLeftRepeat, fixedPaddingTail,
          oneStep_scanLen_separator, List.replicate_succ,
          List.append_assoc]
  have h₁ : MStarParserExecution.run zero one work bits.length
      (separatorCheckStarted bits) = separatorCheckAtPad bits := by
    rw [show separatorCheckStarted bits =
      .running MStarParserMicrocode.checkSeekSepPad
        (MStarParserExecution.beforeLeftRepeat bits.length
          MStarParserMicrocode.lenDone
          (List.replicate (72 * bits.length + 71) MStarParserMicrocode.padDone ++
            [MStarParserMicrocode.endpointMark])
          MStarParserMicrocode.sepPad
          (MStarParserMicrocode.sepLen :: tail)) by rfl]
    rw [run_checkSeek_lenDone]
    rfl
  have h₂ : MStarParserExecution.run zero one work 1
      (separatorCheckAtPad bits) = paddingCheckStarted bits := by
    change MStarParserExecution.oneStep zero one work
      (separatorCheckAtPad bits) = paddingCheckStarted bits
    have hn : 72 * bits.length + 71 = (72 * bits.length + 70) + 1 := by omega
    simp [separatorCheckAtPad, paddingCheckStarted, hn,
      List.replicate_succ, oneStep_checkSeek_sepPad, List.append_assoc]
  have h₃ : MStarParserExecution.run zero one work (72 * bits.length + 71)
      (paddingCheckStarted bits) = paddingCheckAtEndpoint bits := by
    have hn : 72 * bits.length + 71 = (72 * bits.length + 70) + 1 := by omega
    rw [show paddingCheckStarted bits =
      .running MStarParserMicrocode.checkPad
        (MStarParserExecution.beforeLeftRepeat (72 * bits.length + 71)
          MStarParserMicrocode.padDone [] MStarParserMicrocode.endpointMark
          (MStarParserMicrocode.sepPad ::
            (List.replicate bits.length MStarParserMicrocode.lenDone ++
              MStarParserMicrocode.sepLen :: tail))) by
      unfold paddingCheckStarted
      rw [hn]
      rfl]
    rw [run_checkPad_done]
    rfl
  have h₄ : MStarParserExecution.run zero one work 1
      (paddingCheckAtEndpoint bits) = paddingReturnStarted bits := by
    change MStarParserExecution.oneStep zero one work
      (paddingCheckAtEndpoint bits) = paddingReturnStarted bits
    have hn : 72 * bits.length + 71 = (72 * bits.length + 70) + 1 := by omega
    simp [paddingCheckAtEndpoint, paddingReturnStarted, hn,
      List.replicate_succ, oneStep_checkPad_endpoint, List.append_assoc]
  have h₅ : MStarParserExecution.run zero one work (72 * bits.length + 71)
      (paddingReturnStarted bits) = paddingReturnAtSep bits := by
    rw [show paddingReturnStarted bits =
      .running MStarParserMicrocode.checkReturnSepPad
        (MStarParserExecution.beforeRightRepeat (72 * bits.length + 71)
          MStarParserMicrocode.padDone [MStarParserMicrocode.endpointMark]
          MStarParserMicrocode.sepPad
          (List.replicate bits.length MStarParserMicrocode.lenDone ++
            MStarParserMicrocode.sepLen :: tail)) by
      have hn : 72 * bits.length + 71 = (72 * bits.length + 70) + 1 := by omega
      unfold paddingReturnStarted MStarParserExecution.beforeRightRepeat
      rw [hn]]
    rw [run_checkReturnPad_done]
    rfl
  have h₆ : MStarParserExecution.run zero one work 1
      (paddingReturnAtSep bits) = lengthReturnStarted bits := by
    change MStarParserExecution.oneStep zero one work
      (paddingReturnAtSep bits) = lengthReturnStarted bits
    cases bits with
    | nil =>
        simp [tail, paddingReturnAtSep, lengthReturnStarted,
          MStarParserExecution.beforeRightRepeat, oneStep_checkReturnPad_sep]
    | cons b bs =>
        simp [tail, paddingReturnAtSep, lengthReturnStarted,
          MStarParserExecution.beforeRightRepeat, oneStep_checkReturnPad_sep,
          List.replicate_succ, List.append_assoc]
  have h₇ : MStarParserExecution.run zero one work bits.length
      (lengthReturnStarted bits) = lengthReturnAtSep bits := by
    exact run_checkReturnLen_done bits.length
      (MStarParserMicrocode.sepPad ::
        (List.replicate (72 * bits.length + 71) MStarParserMicrocode.padDone ++
          [MStarParserMicrocode.endpointMark]))
      MStarParserMicrocode.sepLen tail
  have h₈ : MStarParserExecution.run zero one work 1
      (lengthReturnAtSep bits) = pairingStarted bits := by
    change MStarParserExecution.oneStep zero one work
      (lengthReturnAtSep bits) = pairingStarted bits
    cases bits with
    | nil =>
        simp [tail, lengthReturnAtSep, pairingStarted,
          MStarParserExecution.beforeLeftRepeat, oneStep_checkReturnLen_sep]
    | cons b bs =>
        simp [tail, lengthReturnAtSep, pairingStarted,
          MStarParserExecution.beforeLeftRepeat, oneStep_checkReturnLen_sep,
          List.replicate_succ, List.append_assoc]
  unfold validationFuel
  rw [show 146 * bits.length + 147 =
      1 + (bits.length + (1 + ((72 * bits.length + 71) +
        (1 + ((72 * bits.length + 71) + (1 + (bits.length + 1))))))) by omega,
    MStarParserExecution.run_add, h₀,
    MStarParserExecution.run_add, h₁,
    MStarParserExecution.run_add, h₂,
    MStarParserExecution.run_add, h₃,
    MStarParserExecution.run_add, h₄,
    MStarParserExecution.run_add, h₅,
    MStarParserExecution.run_add, h₆,
    MStarParserExecution.run_add, h₇, h₈]

/-! ## Payload pairing -/

def pairIterationFuel (done rest : List Bool) : ℕ :=
  4 * done.length + 4 + if rest = [] then done.length + 1 else 0

theorem run_pair_iteration (done : List Bool) (b : Bool) (rest : List Bool) :
    MStarParserExecution.run zero one work (pairIterationFuel done rest)
      (pairBefore done b rest) = pairAfter (done ++ [b]) rest := by
  have h₀ : MStarParserExecution.run zero one work done.length
      (pairBefore done b rest) = pairFindAtFresh done b rest := by
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
  have h₁ : MStarParserExecution.run zero one work 1
      (pairFindAtFresh done b rest) = pairFreshMarked done b rest := by
    change MStarParserExecution.oneStep zero one work
      (pairFindAtFresh done b rest) = pairFreshMarked done b rest
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
  have h₂ : MStarParserExecution.run zero one work done.length
      (pairFreshMarked done b rest) = pairAtSepLen done b rest := by
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
  have h₃ : MStarParserExecution.run zero one work 1
      (pairAtSepLen done b rest) = pairPayloadStarted done b rest := by
    change MStarParserExecution.oneStep zero one work
      (pairAtSepLen done b rest) = pairPayloadStarted done b rest
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
  have h₄ : MStarParserExecution.run zero one work done.length
      (pairPayloadStarted done b rest) = pairAtPayloadBit done b rest := by
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
  have h₅ : MStarParserExecution.run zero one work 1
      (pairAtPayloadBit done b rest) = pairReturnStarted done b rest := by
    change MStarParserExecution.oneStep zero one work
      (pairAtPayloadBit done b rest) = pairReturnStarted done b rest
    cases hrev : done.reverse with
    | nil =>
        simp [pairAtPayloadBit, pairReturnStarted,
          MStarParserExecution.afterRightList,
          MStarParserExecution.beforeLeftList, hrev, oneStep_seekPayload_bit]
    | cons c cs =>
        simp [pairAtPayloadBit, pairReturnStarted,
          MStarParserExecution.afterRightList,
          MStarParserExecution.beforeLeftList, hrev,
          oneStep_seekPayload_bit, List.append_assoc]
  have h₆ : MStarParserExecution.run zero one work done.length
      (pairReturnStarted done b rest) = pairReturnedAtSep done b rest := by
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
  have h₇ : MStarParserExecution.run zero one work 1
      (pairReturnedAtSep done b rest) = pairAfterSep done b rest := by
    change MStarParserExecution.oneStep zero one work
      (pairReturnedAtSep done b rest) = pairAfterSep done b rest
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
  have h₈ : MStarParserExecution.run zero one work
      (if rest = [] then done.length + 1 else 0)
      (pairAfterSep done b rest) = pairAfter (done ++ [b]) rest := by
    cases rest with
    | nil =>
        simp only [if_pos rfl]
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
        have hz₀ : pairAfterSep done b [] = z₀ := by
          simp [pairAfterSep, z₀, right,
            MStarParserExecution.beforeLeftRepeat, List.map_append,
            List.replicate_succ, pairingPad, List.append_assoc]
        have hz₁ : z₁ = pairAfter (done ++ [b]) [] := by
          simp [z₁, right, pairAfter, MStarParserExecution.afterLeftRepeat,
            List.map_append, pairingPad, List.append_assoc]
        rw [hz₀, ← hz₁]
        exact run_findLen_paired (done.length + 1)
          (pairingPad (done.length + 1)) MStarParserMicrocode.sepPad right
    | cons c cs =>
        simp only [List.cons_ne_nil, if_false, MStarParserExecution.run_zero]
        exact pairAfterSep_eq_pairBefore done b c cs
  unfold pairIterationFuel
  let extra := if rest = [] then done.length + 1 else 0
  have hfuel : 4 * done.length + 4 + extra =
      done.length + (1 + (done.length + (1 +
        (done.length + (1 + (done.length + (1 + extra))))))) := by omega
  rw [show (if rest = [] then done.length + 1 else 0) = extra by rfl,
    hfuel,
    MStarParserExecution.run_add, h₀,
    MStarParserExecution.run_add, h₁,
    MStarParserExecution.run_add, h₂,
    MStarParserExecution.run_add, h₃,
    MStarParserExecution.run_add, h₄,
    MStarParserExecution.run_add, h₅,
    MStarParserExecution.run_add, h₆,
    MStarParserExecution.run_add, h₇, h₈]

def pairFoldFuel : List Bool → List Bool → ℕ
  | _, [] => 0
  | done, b :: rest =>
      pairIterationFuel done rest + pairFoldFuel (done ++ [b]) rest

theorem run_pair_fold (done bits : List Bool) :
    MStarParserExecution.run zero one work (pairFoldFuel done bits)
      (pairAfter done bits) = pairAfter (done ++ bits) [] := by
  induction bits generalizing done with
  | nil => simp [pairFoldFuel]
  | cons b rest ih =>
      rw [pairFoldFuel, MStarParserExecution.run_add]
      have hstart : pairAfter done (b :: rest) = pairBefore done b rest := by rfl
      rw [hstart, run_pair_iteration]
      have hrest := ih (done ++ [b])
      rw [hrest]
      simp [List.append_assoc]

def allPairingFuel (bits : List Bool) : ℕ := pairFoldFuel [] bits

theorem run_all_pairing (bits : List Bool) :
    MStarParserExecution.run zero one work (allPairingFuel bits)
      (pairingStarted bits) = pairAfter bits [] := by
  rw [allPairingFuel, pairingStarted_eq_pairAfter_nil]
  simpa using run_pair_fold [] bits

theorem pairFoldFuel_closed (done bits : List Bool) :
    pairFoldFuel done bits =
      if bits = [] then 0 else
        (4 * bits.length + 1) * done.length +
          2 * bits.length * bits.length + 3 * bits.length := by
  induction bits generalizing done with
  | nil => simp [pairFoldFuel]
  | cons b rest ih =>
      cases rest with
      | nil =>
          simp [pairFoldFuel, pairIterationFuel]
          omega
      | cons c cs =>
          rw [pairFoldFuel, ih]
          simp [pairIterationFuel]
          ring

theorem allPairingFuel_closed (bits : List Bool) :
    allPairingFuel bits = 2 * bits.length * bits.length + 3 * bits.length := by
  rw [allPairingFuel, pairFoldFuel_closed]
  cases bits <;> simp

def verificationFuel (bits : List Bool) : ℕ := 2 * bits.length + 5

theorem run_verification_to_copyReady (bits : List Bool) :
    MStarParserExecution.run zero one work (verificationFuel bits)
      (pairAfter bits []) = .copyReady (finalZipper bits) := by
  have h₀ : MStarParserExecution.run zero one work 1
      (pairAfter bits []) = verificationStarted bits := by
    change MStarParserExecution.oneStep zero one work (pairAfter bits []) = _
    cases bits with
    | nil =>
        simp [pairAfter, verificationStarted,
          MStarParserExecution.beforeRightRepeat, oneStep_findLen_finished]
    | cons b bs =>
        simp [pairAfter, verificationStarted,
          MStarParserExecution.beforeRightRepeat, oneStep_findLen_finished,
          List.replicate_succ, List.append_assoc]
  have h₁ : MStarParserExecution.run zero one work bits.length
      (verificationStarted bits) = verificationAtSepLen bits := by
    exact run_verifySeek_paired bits.length
      (MStarParserMicrocode.sepPad :: pairingPad bits.length)
      MStarParserMicrocode.sepLen
      (bits.map payloadMarker ++
        [(MStarOuterProgram.Tape.core one : MStarOuterProgram.Tape CoreTape),
          MStarOuterProgram.Tape.core work])
  have h₂ : MStarParserExecution.run zero one work 1
      (verificationAtSepLen bits) = payloadVerificationStarted bits := by
    change MStarParserExecution.oneStep zero one work
      (verificationAtSepLen bits) = payloadVerificationStarted bits
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
  have h₃ : MStarParserExecution.run zero one work bits.length
      (payloadVerificationStarted bits) = verificationAtLeadingOne bits := by
    simpa [payloadVerificationStarted, verificationAtLeadingOne] using
      (run_verifyPayload_marked bits
        (MStarParserMicrocode.sepLen ::
          (List.replicate bits.length MStarParserMicrocode.pairedLen ++
            MStarParserMicrocode.sepPad :: pairingPad bits.length))
        (.core one) [(.core work : MStarOuterProgram.Tape CoreTape)])
  have h₄ : MStarParserExecution.run zero one work 3
      (verificationAtLeadingOne bits) = .copyReady (finalZipper bits) := by
    simpa [verificationAtLeadingOne, finalZipper,
      MStarParserExecution.afterRightList, List.map_reverse] using
      run_final_three
        (bits.reverse.map payloadMarker ++
          (MStarParserMicrocode.sepLen ::
            (List.replicate bits.length MStarParserMicrocode.pairedLen ++
              MStarParserMicrocode.sepPad :: pairingPad bits.length)))
  unfold verificationFuel
  rw [show 2 * bits.length + 5 =
      1 + (bits.length + (1 + (bits.length + 3))) by omega,
    MStarParserExecution.run_add, h₀,
    MStarParserExecution.run_add, h₁,
    MStarParserExecution.run_add, h₂,
    MStarParserExecution.run_add, h₃, h₄]

def parserExplicitFuel (x : ConcretePakSide.Word) : ℕ :=
  PakOuterFrontNumericBound.parserPrefixFuel x +
    (allLengthFuel x.length +
      (validationFuel x.reverse +
        (allPairingFuel x.reverse + verificationFuel x.reverse)))

theorem parserExplicitFuel_closed (x : ConcretePakSide.Word) :
    parserExplicitFuel x = 75 * x.length * x.length + 301 * x.length + 226 := by
  rw [parserExplicitFuel, PakOuterFrontNumericBound.parserPrefixFuel_closed,
    allLengthFuel_closed, allPairingFuel_closed]
  simp [validationFuel, verificationFuel]
  ring

theorem run_parser_encodedWord_explicitFuel (x : ConcretePakSide.Word) :
    MStarParserExecution.run zero one work (parserExplicitFuel x)
      (MStarParserExecution.initial zero one work (ConcretePakSide.encodedWord x)) =
      .copyReady (finalZipper x.reverse) := by
  have hvalidation : MStarParserExecution.run zero one work
      (validationFuel x.reverse)
      (lenFinished x.length
        (x.reverse.map (MStarParserExecution.bitCell zero one) ++
          [.core one, .core work])) = pairingStarted x.reverse := by
    simpa using run_length_validation_to_pairing x.reverse
  unfold parserExplicitFuel
  rw [MStarParserExecution.run_add,
    PakOuterFrontNumericBound.parserPrefix_runs,
    MStarParserExecution.run_add, run_all_length_markers,
    MStarParserExecution.run_add, hvalidation,
    MStarParserExecution.run_add, run_all_pairing,
    run_verification_to_copyReady]

private theorem parserLinear_le_pow (m : ℕ) :
    150 * m + 376 ≤ 2 ^ (m + 9) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      calc
        150 * (m + 1) + 376 ≤ 2 * (150 * m + 376) := by omega
        _ ≤ 2 * 2 ^ (m + 9) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ ((m + 1) + 9) := by
          rw [show (m + 1) + 9 = (m + 9) + 1 by omega, pow_succ]
          ring

private theorem parserPolynomial_lt_pow (m : ℕ) :
    75 * m * m + 301 * m + 226 < 2 ^ (m + 9) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      have hlin := parserLinear_le_pow m
      calc
        75 * (m + 1) * (m + 1) + 301 * (m + 1) + 226 =
            (75 * m * m + 301 * m + 226) + (150 * m + 376) := by ring
        _ < 2 ^ (m + 9) + 2 ^ (m + 9) := Nat.add_lt_add_of_lt_of_le ih hlin
        _ = 2 ^ ((m + 1) + 9) := by
          rw [show (m + 1) + 9 = (m + 9) + 1 by omega, pow_succ]
          ring

theorem parserExplicitFuel_lt_sideValue (x : ConcretePakSide.Word) :
    parserExplicitFuel x < ConcretePakSide.sideValue x := by
  rw [parserExplicitFuel_closed]
  have hpoly := parserPolynomial_lt_pow x.length
  have hexp : x.length + 9 ≤ ConcretePakSide.paddingLength x.length := by
    simp [ConcretePakSide.paddingLength]
    omega
  have hbit := Nat.ge_two_pow_of_testBit
    (PakSideScanner.sideValue_padding_testBit x)
  exact hpoly.trans_le ((Nat.pow_le_pow_right (by decide) hexp).trans hbit)

/-- Literal cost of the complete physical front end, including the outer
slot-one start edge and the single parser-to-copier entry edge. -/
def frontExplicitFuel (x : ConcretePakSide.Word) : ℕ :=
  1 + parserExplicitFuel x + (1 + PakOuterFrontNumericBound.copierExplicitFuel x)

theorem frontExplicitFuel_lt_sideValue (x : ConcretePakSide.Word) :
    frontExplicitFuel x < ConcretePakSide.sideValue x := by
  let P := 2 ^ (24 * x.length + 45)
  have hcopier : PakOuterFrontNumericBound.copierExplicitFuel x ≤ P := by
    exact PakOuterFrontNumericBound.copierExplicitFuel_le_pow24 x
  have hparser0 := parserPolynomial_lt_pow x.length
  have hexp : x.length + 9 ≤ 24 * x.length + 45 := by omega
  have hparser : parserExplicitFuel x ≤ P := by
    rw [parserExplicitFuel_closed]
    exact hparser0.le.trans (Nat.pow_le_pow_right (by decide) hexp)
  have hP : 1 ≤ P := Nat.one_le_pow _ _ (by decide)
  have hfront : frontExplicitFuel x ≤ 4 * P := by
    unfold frontExplicitFuel
    omega
  have hfour : 4 * P = 2 ^ (24 * x.length + 47) := by
    dsimp [P]
    rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  have hexpPad : 24 * x.length + 47 < ConcretePakSide.paddingLength x.length := by
    simp [ConcretePakSide.paddingLength]
    omega
  have hpow : 4 * P < 2 ^ ConcretePakSide.paddingLength x.length := by
    rw [hfour]
    exact Nat.pow_lt_pow_right (by decide) hexpPad
  have hbit := Nat.ge_two_pow_of_testBit
    (PakSideScanner.sideValue_padding_testBit x)
  exact hfront.trans_lt (hpow.trans_le hbit)

end PakFixedPolyomino.PakOuterParserNumericSuffix
