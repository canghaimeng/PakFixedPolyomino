import PakFixedPolyomino.ULogRuleCursorStep

/-! Equal-source restoration and read/action entry at an arbitrary cursor. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def restoredSourceBoundaryTape (boundary : ULogLetter) : Tape :=
  if boundary = sourceBoundaryZero then ulogCore codeZero
  else ulogCore codeOne

def sourceFieldRestoredAt (slot : Bool) (q : ℕ)
    (boundary : ULogLetter) (base corridor suffix : List Tape) : Result :=
  match q with
  | 0 => .running (.fieldCompare .matchedSource slot)
      ⟨ulogCore boundary :: base, ulogCore codeOne,
        corridor ++ ulogCore stateOne :: suffix⟩
  | n + 1 => .running (.fieldCompare .matchedSource slot)
      ⟨ulogCore boundary :: base, ulogCore codeZero,
        List.replicate n (ulogCore codeZero) ++ ulogCore codeOne ::
          corridor ++ List.replicate (n + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix⟩

theorem reaches_sourceMatchRestoredAt (slot : Bool) (q : ℕ)
    (corridor : List Tape) (hcorridor : SourceCompareCorridorSafe corridor)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (base suffix : List Tape) :
    Reaches
      (sourceCompareStart slot q 0 corridor (ulogCore boundary :: base) suffix)
      (sourceFieldRestoredAt slot q boundary base corridor suffix) := by
  have h₀ := reaches_sourceCompareZeros slot q 0 corridor hcorridor
    (ulogCore boundary :: base) suffix
  let finishPath := sourceFinishPath q corridor
  let restorePath := sourceRestorePath q corridor
  have h₁ : Reaches
      (sourceCompareAllMarked slot q 0 corridor
        (ulogCore boundary :: base) suffix)
      (.running (.compareFinishSource slot)
        (beforeRightPath finishPath
          (ulogCore codeOne :: List.replicate q (ulogCore sourceMark) ++
            ulogCore boundary :: base)
          (ulogCore stateOne) suffix)) := by
    rw [show sourceCompareAllMarked slot q 0 corridor
          (ulogCore boundary :: base) suffix =
        .running (.fieldCompare .source slot)
          ⟨List.replicate q (ulogCore sourceMark) ++
              ulogCore boundary :: base,
            ulogCore codeOne, finishPath ++ ulogCore stateOne :: suffix⟩ by
      simp [sourceCompareAllMarked, finishPath, sourceFinishPath]]
    apply reaches_step
    cases he : finishPath with
    | nil =>
        simpa [beforeRightPath, he] using
          (fieldCompare_source_one slot
            (List.replicate q (ulogCore sourceMark) ++
              ulogCore boundary :: base)
            (ulogCore stateOne) suffix)
    | cons x xs =>
        simpa [beforeRightPath, he, List.append_assoc] using
          (fieldCompare_source_one slot
            (List.replicate q (ulogCore sourceMark) ++
              ulogCore boundary :: base)
            x (xs ++ ulogCore stateOne :: suffix))
  have h₂ : Reaches
      (.running (.compareFinishSource slot)
        (beforeRightPath finishPath
          (ulogCore codeOne :: List.replicate q (ulogCore sourceMark) ++
            ulogCore boundary :: base)
          (ulogCore stateOne) suffix))
      (.running (.compareFinishSource slot)
        (afterRightPath finishPath
          (ulogCore codeOne :: List.replicate q (ulogCore sourceMark) ++
            ulogCore boundary :: base)
          (ulogCore stateOne) suffix)) := by
    refine ⟨finishPath.length, run_right_path_of
      (.compareFinishSource slot) finishPath ?_ _ _ _⟩
    intro x hx l y r
    unfold finishPath sourceFinishPath at hx
    rcases List.mem_append.mp hx with hc | hs
    · have h := hcorridor x hc
      exact compareFinishSource_pass slot x h.2.2.2.2.2.1 h.1
        h.2.1 h.2.2.1 l y r
    · have heq : x = ulogCore stateMark :=
        (by simpa only [List.mem_replicate] using hs :
          q ≠ 0 ∧ x = ulogCore stateMark).2
      rw [heq]
      exact compareFinishSource_mark slot l y r
  have h₃ : Reaches
      (.running (.compareFinishSource slot)
        (afterRightPath finishPath
          (ulogCore codeOne :: List.replicate q (ulogCore sourceMark) ++
            ulogCore boundary :: base)
          (ulogCore stateOne) suffix))
      (.running (.compareRestoreSource slot)
        (beforeLeftPath restorePath base (ulogCore boundary)
          (ulogCore stateOne :: suffix))) := by
    apply reaches_step
    simpa [finishPath, restorePath, sourceRestorePath, afterRightPath,
      List.append_assoc] using
      (compareFinishSource_one_over_path slot restorePath base
        (ulogCore boundary) suffix)
  have h₄ : Reaches
      (.running (.compareRestoreSource slot)
        (beforeLeftPath restorePath base (ulogCore boundary)
          (ulogCore stateOne :: suffix)))
      (.running (.compareRestoreSource slot)
        (afterLeftPathMap restorePath restoreSourceCell base
          (ulogCore boundary) (ulogCore stateOne :: suffix))) := by
    refine ⟨restorePath.length, run_left_path_map_of
      (.compareRestoreSource slot) restorePath restoreSourceCell ?_
      base (ulogCore boundary) (ulogCore stateOne :: suffix)⟩
    intro x hx l y r
    have hsafe := sourceRestorePath_safe q corridor hcorridor
      (by simpa [restorePath] using hx)
    exact compareRestoreSource_step slot x hsafe.1 hsafe.2.1
      hsafe.2.2.1 hsafe.2.2.2 l y r
  have h₅ : Reaches
      (.running (.compareRestoreSource slot)
        (afterLeftPathMap restorePath restoreSourceCell base
          (ulogCore boundary) (ulogCore stateOne :: suffix)))
      (sourceFieldRestoredAt slot q boundary base corridor suffix) := by
    apply reaches_step
    have hmap : restorePath.reverse.map restoreSourceCell =
        List.replicate q (ulogCore codeZero) ++ ulogCore codeOne ::
          corridor ++ List.replicate q (ulogCore stateZero) := by
      simpa [restorePath] using sourceRestorePath_map q corridor hcorridor
    rw [show afterLeftPathMap restorePath restoreSourceCell base
          (ulogCore boundary) (ulogCore stateOne :: suffix) =
        ⟨base, ulogCore boundary,
          List.replicate q (ulogCore codeZero) ++ ulogCore codeOne ::
            corridor ++ List.replicate q (ulogCore stateZero) ++
              ulogCore stateOne :: suffix⟩ by
      simp [afterLeftPathMap, hmap, List.append_assoc]]
    rcases hboundary with rfl | rfl | rfl
    · cases q with
      | zero =>
          simpa [sourceFieldRestoredAt, restoredSourceBoundaryTape,
            List.append_assoc] using
            (compareRestoreSource_boundary slot base (ulogCore codeOne)
              (corridor ++ ulogCore stateOne :: suffix))
      | succ q =>
          simpa [sourceFieldRestoredAt, restoredSourceBoundaryTape,
            List.replicate_succ, List.append_assoc] using
            (compareRestoreSource_boundary slot base (ulogCore codeZero)
              (List.replicate q (ulogCore codeZero) ++ ulogCore codeOne ::
                corridor ++ List.replicate (q + 1) (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix))
    · cases q with
      | zero =>
          simpa [sourceFieldRestoredAt, restoredSourceBoundaryTape,
            List.append_assoc] using
            (compareRestoreSource_boundaryZero slot base (ulogCore codeOne)
              (corridor ++ ulogCore stateOne :: suffix))
      | succ q =>
          simpa [sourceFieldRestoredAt, restoredSourceBoundaryTape,
            List.replicate_succ, List.append_assoc] using
            (compareRestoreSource_boundaryZero slot base (ulogCore codeZero)
              (List.replicate q (ulogCore codeZero) ++ ulogCore codeOne ::
                corridor ++ List.replicate (q + 1) (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix))
    · cases q with
      | zero =>
          simpa [sourceFieldRestoredAt, restoredSourceBoundaryTape,
            List.append_assoc] using
            (compareRestoreSource_boundaryOne slot base (ulogCore codeOne)
              (corridor ++ ulogCore stateOne :: suffix))
      | succ q =>
          simpa [sourceFieldRestoredAt, restoredSourceBoundaryTape,
            List.replicate_succ, List.append_assoc] using
            (compareRestoreSource_boundaryOne slot base (ulogCore codeZero)
              (List.replicate q (ulogCore codeZero) ++ ulogCore codeOne ::
                corridor ++ List.replicate (q + 1) (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix))
  exact reaches_trans h₀ (reaches_trans h₁
    (reaches_trans h₂ (reaches_trans h₃ (reaches_trans h₄ h₅))))

def sourceReadStartedAt (slot : Bool) (q : ℕ) (boundary : ULogLetter)
    (b : Bool) (base corridor suffix : List Tape) : Result :=
  .running (.fieldCompare .read slot)
    ⟨ulogCore codeOne ::
        (List.replicate q (ulogCore codeZero) ++
          ulogCore boundary :: base),
      codeTape b,
      corridor ++ List.replicate q (ulogCore stateZero) ++
        ulogCore stateOne :: suffix⟩

theorem reaches_sourceFieldRestoredAt_read (slot : Bool) (q : ℕ)
    (boundary : ULogLetter) (b : Bool)
    (base corridor suffix : List Tape) :
    Reaches
      (sourceFieldRestoredAt slot q boundary base (codeTape b :: corridor)
        suffix)
      (sourceReadStartedAt slot q boundary b base corridor suffix) := by
  have h := reaches_unaryState_of (.fieldCompare .matchedSource slot)
    (.fieldCompare .read slot) q (matchedSourceSeek_zero slot)
    (matchedSourceSeek_one slot)
    (ulogCore boundary :: base) (codeTape b)
    (corridor ++ List.replicate q (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  cases q <;>
    simpa [sourceFieldRestoredAt, sourceReadStartedAt, beforeUnaryState,
      List.replicate_succ, List.append_assoc] using h

def matchedReadLeftAt (slot : Bool) (source read : ℕ)
    (boundary : ULogLetter) (base : List Tape) : List Tape :=
  codeTape slot :: ulogCore codeOne ::
    List.replicate read (ulogCore codeZero) ++ ulogCore codeOne ::
      List.replicate source (ulogCore codeZero) ++
        ulogCore boundary :: base

theorem reaches_sourceReadAtZero_slotMatch (slot : Bool) (q : ℕ)
    (boundary : ULogLetter) (base path runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe (codeTape slot :: path)) :
    Reaches
      (sourceReadStartedAt slot q boundary true base
        (codeTape slot :: path ++ ulogCore payloadHeadZero :: runtime) suffix)
      (.running .actionWrite
        (beforeRightPath path (matchedReadLeftAt slot q 0 boundary base)
          (ulogCore payloadHeadZero)
          (runtime ++ List.replicate q (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
  have h := reaches_readZero_slotMatch slot path hsafe
    (ulogCore codeOne :: List.replicate q (ulogCore codeZero) ++
      ulogCore boundary :: base)
    (runtime ++ List.replicate q (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  simpa [sourceReadStartedAt, matchedReadLeftAt,
    codeTape, List.append_assoc] using h

theorem reaches_sourceReadAtOne_slotMatch (slot : Bool) (q : ℕ)
    (boundary : ULogLetter) (base path runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe (codeTape slot :: path)) :
    Reaches
      (sourceReadStartedAt slot q boundary false base
        (ulogCore codeOne :: codeTape slot :: path ++
          ulogCore payloadHeadOne :: runtime) suffix)
      (.running .actionWrite
        (beforeRightPath path (matchedReadLeftAt slot q 1 boundary base)
          (ulogCore payloadHeadOne)
          (runtime ++ List.replicate q (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
  have h := reaches_readOne_slotMatch slot path hsafe
    (ulogCore codeOne :: List.replicate q (ulogCore codeZero) ++
      ulogCore boundary :: base)
    (runtime ++ List.replicate q (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  simpa [sourceReadStartedAt, matchedReadLeftAt,
    codeTape, List.append_assoc] using h

theorem reaches_sourceReadAtBlank_slotMatch (slot : Bool) (q : ℕ)
    (boundary : ULogLetter) (base path runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe (codeTape slot :: path)) :
    Reaches
      (sourceReadStartedAt slot q boundary false base
        (ulogCore codeZero :: ulogCore codeOne :: codeTape slot ::
          path ++ ulogCore payloadHeadBlank :: runtime) suffix)
      (.running .actionWrite
        (beforeRightPath path (matchedReadLeftAt slot q 2 boundary base)
          (ulogCore payloadHeadBlank)
          (runtime ++ List.replicate q (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
  have h := reaches_readBlank_slotMatch slot path hsafe
    (ulogCore codeOne :: List.replicate q (ulogCore codeZero) ++
      ulogCore boundary :: base)
    (runtime ++ List.replicate q (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  simpa [sourceReadStartedAt, matchedReadLeftAt,
    codeTape, List.append_assoc] using h

theorem reaches_sourceReadAtValid_actionWrite
    (slot : Bool) (source read write target : ℕ)
    (boundary : ULogLetter) (m : OneTapeTableau.Move)
    (hread : read < 3) (base movePath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe
      (codeTape slot :: encodedActionPath write target m movePath)) :
    Reaches
      (sourceReadStartedAt slot source boundary (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape slot :: encodedActionPath write target m movePath ++
            readHeadNat read :: runtime) suffix)
      (actionWriteStart write
        (matchedReadLeftAt slot source read boundary base)
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        (readHeadNat read)
      (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)) := by
  cases slot <;> interval_cases read
  · have h := reaches_sourceReadAtZero_slotMatch false source boundary base
      (encodedActionPath write target m movePath) runtime suffix hsafe
    cases write <;> simpa [encodedActionPath, ULogBytecode.encodeNatField,
      actionWriteStart, unaryFieldFirst, readHeadNat, beforeRightPath,
      List.map_append, List.replicate_succ, List.append_assoc, codeTape]
      using h
  · have h := reaches_sourceReadAtOne_slotMatch false source boundary base
      (encodedActionPath write target m movePath) runtime suffix hsafe
    cases write <;> simpa [encodedActionPath, ULogBytecode.encodeNatField,
      actionWriteStart, unaryFieldFirst, readHeadNat, beforeRightPath,
      List.map_append, List.replicate_succ, List.append_assoc, codeTape]
      using h
  · have h := reaches_sourceReadAtBlank_slotMatch false source boundary base
      (encodedActionPath write target m movePath) runtime suffix hsafe
    cases write <;> simpa [encodedActionPath, ULogBytecode.encodeNatField,
      actionWriteStart, unaryFieldFirst, readHeadNat, beforeRightPath,
      List.map_append, List.replicate_succ, List.append_assoc, codeTape]
      using h
  · have h := reaches_sourceReadAtZero_slotMatch true source boundary base
      (encodedActionPath write target m movePath) runtime suffix hsafe
    cases write <;> simpa [encodedActionPath, ULogBytecode.encodeNatField,
      actionWriteStart, unaryFieldFirst, readHeadNat, beforeRightPath,
      List.map_append, List.replicate_succ, List.append_assoc, codeTape]
      using h
  · have h := reaches_sourceReadAtOne_slotMatch true source boundary base
      (encodedActionPath write target m movePath) runtime suffix hsafe
    cases write <;> simpa [encodedActionPath, ULogBytecode.encodeNatField,
      actionWriteStart, unaryFieldFirst, readHeadNat, beforeRightPath,
      List.map_append, List.replicate_succ, List.append_assoc, codeTape]
      using h
  · have h := reaches_sourceReadAtBlank_slotMatch true source boundary base
      (encodedActionPath write target m movePath) runtime suffix hsafe
    cases write <;> simpa [encodedActionPath, ULogBytecode.encodeNatField,
      actionWriteStart, unaryFieldFirst, readHeadNat, beforeRightPath,
      List.map_append, List.replicate_succ, List.append_assoc, codeTape]
      using h

end PakFixedPolyomino.ULogBootstrapExecution
