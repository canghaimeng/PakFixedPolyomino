import PakFixedPolyomino.ULogRuleListStayCycle

/-! Exact restoration of an arbitrary successful rule-list cursor. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

@[simp] theorem restoreProgramCell_nextBoundary (b : Bool) :
    restoreProgramCell (ulogCore (nextSourceBoundary b)) = codeTape b := by
  cases b <;> decide

theorem mismatchRule_tail_next_restored (r : ULogBytecode.RuleCode) :
    (((mismatchRulePrefix r).tail.reverse ++
      [ulogCore (nextSourceBoundary (moveSecond r.action.move))]).map
        restoreProgramCell) =
      (ULogBytecode.encodeRule r).map codeTape := by
  rw [List.map_append, List.map_singleton,
    restoreProgramCell_nextBoundary]
  rcases r with ⟨source, read, slot, ⟨write, target, move⟩⟩
  cases move <;> cases slot <;>
    simp [mismatchRulePrefix, nextSourceBoundary,
      moveFirst, moveSecond,
      ULogBytecode.encodeRule, ULogBytecode.encodeAction,
      ULogBytecode.encodeNatField, List.map_append, List.reverse_append,
      List.append_assoc]

@[simp] theorem restoredBoundaryCell_nextSourceBoundary (b : Bool) :
    restoredBoundaryCell (nextSourceBoundary b) = codeTape b := by
  cases b <;> decide

@[simp] theorem restoreProgramCell_restoredBoundaryCell
    (boundary : ULogLetter) :
    restoreProgramCell (restoredBoundaryCell boundary) =
      restoredBoundaryCell boundary := by
  simp only [restoredBoundaryCell]
  split <;> decide

theorem mismatchRule_tail_restored_cons (r : ULogBytecode.RuleCode) :
    (mismatchRulePrefix r).tail.reverse.map restoreProgramCell ++
        [restoredBoundaryCell
          (nextSourceBoundary (moveSecond r.action.move))] =
      (ULogBytecode.encodeRule r).map codeTape := by
  have h := mismatchRule_tail_next_restored r
  simp only [List.map_append, List.map_singleton] at h
  rw [restoreProgramCell_nextBoundary] at h
  simpa using h

theorem restoreProgramCell_boundaryTape (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne) :
    restoreProgramCell (ulogCore boundary) = restoredBoundaryCell boundary := by
  rcases hboundary with rfl | rfl | rfl <;>
    decide

theorem mismatchHistory_complete (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode) :
    ((mismatchHistory boundary skip ++
      ulogCore (boundaryAfter boundary skip) ::
        (ULogBytecode.encodeRule r).map codeTape).map restoreProgramCell) =
      restoredBoundaryCell boundary ::
        (ULogBytecode.encodeRules (skip ++ [r])).map codeTape := by
  induction skip generalizing boundary with
  | nil =>
      simp [mismatchHistory, boundaryAfter, ULogBytecode.encodeRules,
        restoreProgramCell_boundaryTape boundary hboundary,
        restoreProgramCell_comp_codeTape]
  | cons s ss ih =>
      have hnext : nextSourceBoundary (moveSecond s.action.move) =
            sourceBoundary ∨
          nextSourceBoundary (moveSecond s.action.move) = sourceBoundaryZero ∨
          nextSourceBoundary (moveSecond s.action.move) = sourceBoundaryOne :=
        nextSourceBoundary_valid (moveSecond s.action.move)
      have hi := ih (nextSourceBoundary (moveSecond s.action.move)) hnext
      have hi' :
          (mismatchHistory
              (nextSourceBoundary (moveSecond s.action.move)) ss).map
                restoreProgramCell ++
              restoreProgramCell (ulogCore (boundaryAfter
                (nextSourceBoundary (moveSecond s.action.move)) ss)) ::
                ((ULogBytecode.encodeRule r).map codeTape).map
                  restoreProgramCell =
            restoredBoundaryCell
                (nextSourceBoundary (moveSecond s.action.move)) ::
              (ULogBytecode.encodeRules (ss ++ [r])).map codeTape := by
        simpa only [List.map_append, List.map_cons] using hi
      simp only [mismatchHistory, skippedRuleSegment, boundaryAfter,
        List.cons_append, List.map_cons, List.map_append]
      rw [restoreProgramCell_restoredBoundaryCell]
      congr 1
      calc
        (mismatchRulePrefix s).tail.reverse.map restoreProgramCell ++
              (mismatchHistory
                (nextSourceBoundary (moveSecond s.action.move)) ss).map
                  restoreProgramCell ++
            restoreProgramCell (ulogCore (boundaryAfter
              (nextSourceBoundary (moveSecond s.action.move)) ss)) ::
              ((ULogBytecode.encodeRule r).map codeTape).map
                restoreProgramCell =
            (mismatchRulePrefix s).tail.reverse.map restoreProgramCell ++
              ((mismatchHistory
                (nextSourceBoundary (moveSecond s.action.move)) ss).map
                  restoreProgramCell ++
                restoreProgramCell (ulogCore (boundaryAfter
                  (nextSourceBoundary (moveSecond s.action.move)) ss)) ::
                  ((ULogBytecode.encodeRule r).map codeTape).map
                    restoreProgramCell) := by
                  simp [List.append_assoc]
        _ =
            (mismatchRulePrefix s).tail.reverse.map restoreProgramCell ++
              (restoredBoundaryCell
                  (nextSourceBoundary (moveSecond s.action.move)) ::
                (ULogBytecode.encodeRules (ss ++ [r])).map codeTape) := by
                  rw [hi']
        _ = ((mismatchRulePrefix s).tail.reverse.map restoreProgramCell ++
              [restoredBoundaryCell
                (nextSourceBoundary (moveSecond s.action.move))]) ++
                (ULogBytecode.encodeRules (ss ++ [r])).map codeTape := by
                  simp [List.append_assoc]
        _ = (ULogBytecode.encodeRule s).map codeTape ++
                (ULogBytecode.encodeRules (ss ++ [r])).map codeTape := by
                  rw [mismatchRule_tail_restored_cons]
        _ = (ULogBytecode.encodeRules (s :: (ss ++ [r]))).map
              codeTape := by
                simp [ULogBytecode.encodeRules, List.map_append]

theorem cursorCleanupProgramPrefix_restored
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode) :
    (cursorCleanupProgramPrefix skip r).map restoreProgramCell =
      (ULogBytecode.encodeRules (skip ++ [r])).map codeTape := by
  cases skip with
  | nil =>
      simp [cursorCleanupProgramPrefix, ULogBytecode.encodeRules,
        restoreProgramCell_comp_codeTape]
  | cons s ss =>
      have hall := mismatchHistory_complete sourceBoundary
        (Or.inl rfl) (s :: ss) r
      have htail := congrArg List.tail hall
      simpa [cursorCleanupProgramPrefix, mismatchHistory, skippedRuleSegment,
        List.map_reverse,
        restoreProgramCell_comp_codeTape] using htail

theorem encodeRules_append (xs ys : List ULogBytecode.RuleCode) :
    ULogBytecode.encodeRules (xs ++ ys) =
      ULogBytecode.encodeRules xs ++ ULogBytecode.encodeRules ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [ULogBytecode.encodeRules, ih, List.append_assoc]

theorem cursorCleanupProgramPath_restored
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (programToHead : List Tape)
    (hprogramToHead : programToHead.map restoreProgramCell = programToHead) :
    ((cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs programToHead).map restoreProgramCell) =
      (ULogBytecode.encodeRules (skip ++ r :: rs)).map codeTape ++
        programToHead := by
  rw [List.map_append, cursorCleanupProgramPrefix_restored]
  simp [cursorMatchedMovePath, List.map_append,
    restoreProgramCell_comp_codeTape, hprogramToHead,
    encodeRules_append, ULogBytecode.encodeRules, List.append_assoc]

theorem cursorCleanupPcPath_map
    (skip rest : List ULogBytecode.RuleCode) :
    (cursorCleanupPcPath skip rest).reverse.map restorePcCell =
      List.replicate (skip ++ rest).length (ulogCore pcDone) := by
  simpa [cursorCleanupPcPath, restorePcPath, List.length_append] using
    restorePcPath_map skip.length rest.length

def canonicalCursorCycleLeft (rules : List ULogBytecode.RuleCode)
    (programToHead outer : List Tape) : List Tape :=
  ((ULogBytecode.encodeRules rules).map codeTape ++ programToHead).reverse ++
    ulogCore codeOne ::
      List.replicate rules.length (ulogCore pcDone) ++
        ulogCore pcMark :: outer

theorem cleanedCursorCycleLeft_eq
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (programToHead outer : List Tape)
    (hprogramToHead : programToHead.map restoreProgramCell = programToHead) :
    cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
        (cursorCleanupProgramPrefix skip r ++
          cursorMatchedMovePath rs programToHead) outer =
      canonicalCursorCycleLeft (skip ++ r :: rs) programToHead outer := by
  simp only [cleanedCycleLeft, canonicalCursorCycleLeft, List.map_reverse]
  rw [cursorCleanupProgramPath_restored skip r rs programToHead
    hprogramToHead]
  have hpc := cursorCleanupPcPath_map skip (r :: rs)
  simp only [List.map_reverse] at hpc
  rw [hpc]

end PakFixedPolyomino.ULogBootstrapExecution
