import PakFixedPolyomino.ULogRuleCursorCleanup

/-! Arbitrary lookup prefix, matching stay action, and full cleanup cycle. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem cursorCleanupPcPath_safe
    (skip rest : List ULogBytecode.RuleCode) :
    RestorePcSafe (cursorCleanupPcPath skip rest) := by
  intro x hx
  unfold cursorCleanupPcPath at hx
  rcases List.mem_append.mp hx with hz | hd
  · have heq : x = ulogCore codeZero :=
      (by simpa only [List.mem_replicate] using hz :
        skip.length ≠ 0 ∧ x = ulogCore codeZero).2
    exact Or.inr heq
  · have heq : x = ulogCore pcDone :=
      (by simpa only [List.mem_replicate] using hd :
        rest.length ≠ 0 ∧ x = ulogCore pcDone).2
    exact Or.inl heq

theorem cursorCleanupTerminal_valid (skip : List ULogBytecode.RuleCode) :
    cursorCleanupTerminal skip = ulogCore codeOne ∨
      cursorCleanupTerminal skip = ulogCore sourceBoundary := by
  cases skip <;> simp [cursorCleanupTerminal]

theorem reaches_mismatchPrefix_matchedAtMost_stay_cycle
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (extra : ℕ) (htarget : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (hmove : r.action.move = .stay)
    (hboundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead
        (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs programToHead))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: runtime))
    (hscan : MoveScanSafe (cursorMatchedMovePath rs programToHead))
    (hclock : RestoreClockSafe
      (writeHeadNat r.action.write ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead)).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs programToHead)) :
    Reaches
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        programToHead runtime outer (ulogCore stateSep :: suffix))
      (.running .cycleStart
        ⟨cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead) outer,
          writeHeadNat r.action.write,
          runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
  have haction := reaches_mismatchPrefix_matchedAtMost slot current actual
    programToHead runtime outer suffix
    (initialRuleCursor (skip ++ r :: rs)) final skip r rs trace hmatch extra
    htarget hread hwrite htargetLower hboundary hcorridor hreadPath hwritePath htargetPath
  have hdecomp := matchedCursor_cleanup_decomposition slot current actual
    programToHead runtime skip r rs trace outer
  have hhead : choiceHead (writeHeadNat r.action.write) = true := by
    interval_cases r.action.write <;> native_decide
  have hcleanup := reaches_moveStay_cleanup
    (cursorCleanupProgramPrefix skip r)
    (cursorMatchedMovePath rs programToHead)
    (cursorCleanupPcPath skip (r :: rs))
    (cursorCleanupTerminal skip) outer (writeHeadNat r.action.write)
    (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate extra MStarConcreteAlphabet.work ++ suffix)
    hscan hclock (cursorCleanupPcPath_safe skip (r :: rs))
    (cursorCleanupTerminal_valid skip) hprogram hhead
  have hcleanup' : Reaches
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (cursorMatchedMovePath rs programToHead)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read final.boundary
              ((List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: outer)))
          (writeHeadNat r.action.write)
          (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ suffix)))
      (.running .cycleStart
        ⟨cleanedCycleLeft (cursorCleanupPcPath skip (r :: rs))
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead) outer,
          writeHeadNat r.action.write,
          runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ suffix⟩) := by
    rw [hmove]
    rw [hmove] at hdecomp
    rw [hdecomp]
    exact hcleanup
  exact reaches_trans haction hcleanup'

end PakFixedPolyomino.ULogBootstrapExecution
