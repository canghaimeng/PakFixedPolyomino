import PakFixedPolyomino.ULogSourceComparisonGeneral

/-! Both strict source-length mismatch exits into marker restoration. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def sourceShortFinishPath (done : ℕ) (corridor : List Tape) : List Tape :=
  corridor ++ List.replicate done (ulogCore stateMark)

def sourceShortRestorePath (done : ℕ) (corridor : List Tape) : List Tape :=
  (sourceShortFinishPath done corridor).reverse ++
    ulogCore codeOne :: List.replicate done (ulogCore sourceMark)

theorem sourceShortFinishPath_pass (slot : Bool) (done : ℕ)
    (corridor : List Tape) (hcorridor : SourceCompareCorridorSafe corridor)
    (x : Tape) (hx : x ∈ sourceShortFinishPath done corridor)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running (.compareFinishSource slot) ⟨left, x, y :: right⟩) =
      .running (.compareFinishSource slot) ⟨x :: left, y, right⟩ := by
  rcases List.mem_append.mp hx with hc | hm
  · have h := hcorridor x hc
    exact compareFinishSource_pass slot x h.2.2.2.2.2.1 h.1
      h.2.1 h.2.2.1 left y right
  · have heq : x = ulogCore stateMark := by
      exact (by simpa only [List.mem_replicate] using hm :
        done ≠ 0 ∧ x = ulogCore stateMark).2
    rw [heq]
    exact compareFinishSource_mark slot left y right

theorem reaches_sourceShortMismatch_restore
    (slot : Bool) (done extra : ℕ) (corridor : List Tape)
    (hcorridor : SourceCompareCorridorSafe corridor)
    (boundary : Tape) (pcBase suffix : List Tape) :
    Reaches
      (sourceCompareStartAgainst slot 0 (extra + 1) done corridor
        (List.replicate done (ulogCore sourceMark) ++
          boundary :: pcBase)
        suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath (sourceShortRestorePath done corridor)
          pcBase (boundary)
          (ulogCore stateZero ::
            List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) := by
  let finishPath := sourceShortFinishPath done corridor
  have h₀ : Reaches
      (sourceCompareStartAgainst slot 0 (extra + 1) done corridor
        (List.replicate done (ulogCore sourceMark) ++
          boundary :: pcBase) suffix)
      (.running (.compareFinishSource slot)
        (beforeRightPath finishPath
          (ulogCore codeOne ::
            List.replicate done (ulogCore sourceMark) ++
              boundary :: pcBase)
          (ulogCore stateZero)
        (List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
    apply reaches_step
    unfold sourceCompareStartAgainst
    rw [show corridor ++ List.replicate done (ulogCore stateMark) =
      finishPath by rfl]
    rw [List.replicate_succ]
    cases he : finishPath with
    | nil =>
        simpa [beforeRightPath, he] using
          (fieldCompare_source_one slot
            (List.replicate done (ulogCore sourceMark) ++
              boundary :: pcBase)
            (ulogCore stateZero)
            (List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))
    | cons x xs =>
        simpa [beforeRightPath, he, List.append_assoc] using
          (fieldCompare_source_one slot
            (List.replicate done (ulogCore sourceMark) ++
              boundary :: pcBase)
            x
            (xs ++ ulogCore stateZero ::
              List.replicate extra (ulogCore stateZero) ++
                ulogCore stateOne :: suffix))
  have h₁ : Reaches
      (.running (.compareFinishSource slot)
        (beforeRightPath finishPath
          (ulogCore codeOne ::
            List.replicate done (ulogCore sourceMark) ++
              boundary :: pcBase)
          (ulogCore stateZero)
          (List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)))
      (.running (.compareFinishSource slot)
        (afterRightPath finishPath
          (ulogCore codeOne ::
            List.replicate done (ulogCore sourceMark) ++
              boundary :: pcBase)
          (ulogCore stateZero)
          (List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) :=
    ⟨finishPath.length,
      run_right_path_of (.compareFinishSource slot) finishPath (by
        intro x hx l y r
        exact sourceShortFinishPath_pass slot done corridor hcorridor x
          (by simpa [finishPath] using hx) l y r)
      (ulogCore codeOne ::
        List.replicate done (ulogCore sourceMark) ++
          boundary :: pcBase)
      (ulogCore stateZero)
      (List.replicate extra (ulogCore stateZero) ++
        ulogCore stateOne :: suffix)⟩
  have h₂ : Reaches
      (.running (.compareFinishSource slot)
        (afterRightPath finishPath
          (ulogCore codeOne ::
            List.replicate done (ulogCore sourceMark) ++
              boundary :: pcBase)
          (ulogCore stateZero)
          (List.replicate extra (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)))
      (.running (.restoreRule slot)
        (beforeLeftPath (sourceShortRestorePath done corridor)
          pcBase (boundary)
          (ulogCore stateZero ::
            List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) := by
    apply reaches_step
    cases hr : finishPath.reverse with
    | nil =>
        simpa [afterRightPath, beforeLeftPath, sourceShortRestorePath,
          finishPath, hr, List.append_assoc] using
          (compareFinishSource_zero_mismatch slot
            (List.replicate done (ulogCore sourceMark) ++
              boundary :: pcBase)
            (ulogCore codeOne)
            (List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))
    | cons x xs =>
        simpa [afterRightPath, beforeLeftPath, sourceShortRestorePath,
          finishPath, hr, List.append_assoc] using
          (compareFinishSource_zero_mismatch slot
            (xs ++ ulogCore codeOne ::
              List.replicate done (ulogCore sourceMark) ++
                boundary :: pcBase)
            x
            (List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))
  exact reaches_trans h₀ (reaches_trans h₁ h₂)

def sourceLongSeekPath (remaining done : ℕ)
    (corridor : List Tape) : List Tape :=
  sourceCompareScanPath remaining corridor done

def sourceLongRestorePath (remaining done : ℕ)
    (corridor : List Tape) : List Tape :=
  (sourceLongSeekPath remaining done corridor).reverse ++
    ulogCore sourceMark :: List.replicate done (ulogCore sourceMark)

theorem reaches_sourceLongMismatch_restore
    (slot : Bool) (done extra : ℕ) (corridor : List Tape)
    (hcorridor : SourceCompareCorridorSafe corridor)
    (boundary : Tape) (pcBase suffix : List Tape) :
    Reaches
      (sourceCompareStartAgainst slot extra.succ 0 done corridor
        (List.replicate done (ulogCore sourceMark) ++
          boundary :: pcBase)
        suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath (sourceLongRestorePath extra done corridor)
          pcBase (boundary)
          (ulogCore stateOne :: suffix))) := by
  let seekPath := sourceLongSeekPath extra done corridor
  have h₀ : Reaches
      (sourceCompareStartAgainst slot extra.succ 0 done corridor
        (List.replicate done (ulogCore sourceMark) ++
          boundary :: pcBase) suffix)
      (.running (.compareSeekState slot)
        (beforeRightPath seekPath
          (ulogCore sourceMark ::
            List.replicate done (ulogCore sourceMark) ++
              boundary :: pcBase)
          (ulogCore stateOne) suffix)) := by
    apply reaches_step
    unfold sourceCompareStartAgainst
    cases he : seekPath with
    | nil =>
        have hne : seekPath ≠ [] := by
          simp [seekPath, sourceLongSeekPath, sourceCompareScanPath]
        exact (hne he).elim
    | cons x xs =>
        have hseekEq : sourceCompareScanPath extra corridor done =
            x :: xs := by
          simpa [seekPath, sourceLongSeekPath] using he
        simp only [sourceCompareStartAgainst]
        rw [hseekEq]
        simpa [beforeRightPath,
          List.append_assoc] using
          (fieldCompare_source_zero slot
            (List.replicate done (ulogCore sourceMark) ++
              boundary :: pcBase)
            x (xs ++ ulogCore stateOne :: suffix))
  have h₁ : Reaches
      (.running (.compareSeekState slot)
        (beforeRightPath seekPath
          (ulogCore sourceMark ::
            List.replicate done (ulogCore sourceMark) ++
              boundary :: pcBase)
          (ulogCore stateOne) suffix))
      (.running (.compareSeekState slot)
        (afterRightPath seekPath
          (ulogCore sourceMark ::
            List.replicate done (ulogCore sourceMark) ++
              boundary :: pcBase)
          (ulogCore stateOne) suffix)) :=
    ⟨seekPath.length,
      run_right_path_of (.compareSeekState slot) seekPath (by
        intro x hx l y r
        have hs := sourceCompareScanPath_seek_safe hcorridor
          (by simpa [seekPath, sourceLongSeekPath] using hx)
        exact compareSeekState_pass slot x hs.1 hs.2.1 hs.2.2 l y r)
      (ulogCore sourceMark ::
        List.replicate done (ulogCore sourceMark) ++
          boundary :: pcBase)
      (ulogCore stateOne) suffix⟩
  have h₂ : Reaches
      (.running (.compareSeekState slot)
        (afterRightPath seekPath
          (ulogCore sourceMark ::
            List.replicate done (ulogCore sourceMark) ++
              boundary :: pcBase)
          (ulogCore stateOne) suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath (sourceLongRestorePath extra done corridor)
          pcBase (boundary)
          (ulogCore stateOne :: suffix))) := by
    apply reaches_step
    have hne : seekPath ≠ [] := by
      simp [seekPath, sourceLongSeekPath, sourceCompareScanPath]
    cases hr : seekPath.reverse with
    | nil =>
        have he : seekPath = [] := by
          simpa using congrArg List.reverse hr
        exact (hne he).elim
    | cons x xs =>
        have hrevEq : (sourceCompareScanPath extra corridor done).reverse =
            x :: xs := by
          simpa [seekPath, sourceLongSeekPath] using hr
        simp only [afterRightPath]
        rw [hr]
        unfold sourceLongRestorePath sourceLongSeekPath
        rw [hrevEq]
        simpa [beforeLeftPath, List.append_assoc] using
          (compareSeekState_one_mismatch slot
            (xs ++ ulogCore sourceMark ::
              List.replicate done (ulogCore sourceMark) ++
                boundary :: pcBase)
            x suffix)
  exact reaches_trans h₀ (reaches_trans h₁ h₂)

end PakFixedPolyomino.ULogBootstrapExecution
