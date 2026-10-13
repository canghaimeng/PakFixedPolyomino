import PakFixedPolyomino.ULogRuleCursorInternalCleanup

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem reaches_cursorMatched_rightBoundary_cleanup_normalized
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hwrite : r.action.write < 3)
    (hmove : r.action.move = .right)
    (boundary : Tape) (shiftPrefix : List Tape) (last : Tape)
    (right : List Tape)
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (hscan : MoveScanSafe (cursorMatchedMovePath rs programToHead))
    (hshift : ShiftRuntimeSafe (shiftPrefix ++ [last]))
    (hreturn : ReturnMovedSafe (shiftPrefix.reverse ++ [boundary]))
    (hclock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead ++
                [unheadTape (writeHeadNat r.action.write)])).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs programToHead ++
          [unheadTape (writeHeadNat r.action.write)]))
    (hprogramToHead :
      (programToHead ++ [unheadTape (writeHeadNat r.action.write)]).map
          restoreProgramCell =
        programToHead ++ [unheadTape (writeHeadNat r.action.write)]) :
    Reaches
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (cursorMatchedMovePath rs programToHead)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read final.boundary
              ((List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: outer)))
          (writeHeadNat r.action.write)
          (boundary :: shiftPrefix ++ last ::
            MStarConcreteAlphabet.work :: right)))
      (.running .cycleStart
        ⟨canonicalCursorCycleLeft (skip ++ r :: rs)
            (programToHead ++
              [unheadTape (writeHeadNat r.action.write)]) outer,
          ulogCore payloadHeadBlank,
          boundary :: shiftPrefix ++ last :: right⟩) := by
  have hdecomp := matchedCursor_cleanup_decomposition slot current actual
    programToHead runtime skip r rs trace outer
  have hhead : choiceHead (writeHeadNat r.action.write) = true := by
    interval_cases r.action.write <;> native_decide
  have hcleanup := reaches_moveRightBoundary_cleanup
    (cursorCleanupProgramPrefix skip r)
    (cursorMatchedMovePath rs programToHead)
    (cursorCleanupPcPath skip (r :: rs))
    (cursorCleanupTerminal skip) outer (writeHeadNat r.action.write)
    boundary shiftPrefix last right hscan hboundary hshift hreturn hhead hclock
    (cursorCleanupPcPath_safe skip (r :: rs))
    (cursorCleanupTerminal_valid skip) hprogram
  rw [hmove] at hdecomp
  rw [hmove, hdecomp]
  have hpath :
      cursorCleanupProgramPrefix skip r ++
          cursorMatchedMovePath rs programToHead ++
            [unheadTape (writeHeadNat r.action.write)] =
        cursorCleanupProgramPrefix skip r ++
          cursorMatchedMovePath rs
            (programToHead ++
              [unheadTape (writeHeadNat r.action.write)]) := by
    simp [cursorMatchedMovePath, List.append_assoc]
  rw [hpath] at hcleanup
  rw [cleanedCursorCycleLeft_eq skip r rs
    (programToHead ++ [unheadTape (writeHeadNat r.action.write)]) outer
    hprogramToHead] at hcleanup
  exact hcleanup

theorem reaches_cursorMatched_leftBoundary_cleanup_normalized
    (slot : Bool) (current actual : ℕ)
    (scanPrefix runtime outer : List Tape) (boundary : Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual
      (scanPrefix ++ [boundary]) runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hwrite : r.action.write < 3)
    (hmove : r.action.move = .left)
    (right : List Tape)
    (hboundary : boundary = ulogCore payloadEnd ∨
      boundary = ulogCore payloadStartOne)
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs (scanPrefix ++ [boundary])))
    (hshift : ShiftRuntimeSafe
      ((cursorMatchedMovePath rs scanPrefix).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse ++
              [ulogCore pcMark]))
    (hreturn : ReturnMovedSafe
      (((cursorMatchedMovePath rs scanPrefix).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse).reverse ++
              [boundary]))
    (hclock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs scanPrefix ++ [boundary])).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs scanPrefix ++ [boundary]))
    (hprogramToHead :
      (scanPrefix ++ [boundary]).map restoreProgramCell =
        scanPrefix ++ [boundary]) :
    Reaches
      (.running (.moveSimHead r.action.move)
        (beforeRightPath
          (cursorMatchedMovePath rs (scanPrefix ++ [boundary]))
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read final.boundary
              ((List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)))
          (writeHeadNat r.action.write) right))
      (.running .cycleStart
        ⟨canonicalCursorCycleLeft (skip ++ r :: rs)
            (scanPrefix ++ [boundary]) outer,
          ulogCore payloadHeadBlank,
          unheadTape (writeHeadNat r.action.write) :: right⟩) := by
  have hdecomp := matchedCursor_cleanup_decomposition slot current actual
    (scanPrefix ++ [boundary]) runtime skip r rs trace
      (MStarConcreteAlphabet.work :: outer)
  have hhead : choiceHead (writeHeadNat r.action.write) = true := by
    interval_cases r.action.write <;> native_decide
  have hscan' : MoveScanSafe
      (cursorMatchedMovePath rs scanPrefix ++ [boundary]) := by
    simpa [cursorMatchedMovePath, List.append_assoc] using hscan
  have hcleanup := reaches_moveLeftBoundary_cleanup
    (cursorCleanupProgramPrefix skip r)
    (cursorMatchedMovePath rs scanPrefix)
    (cursorCleanupPcPath skip (r :: rs))
    (cursorCleanupTerminal skip) boundary outer
    (writeHeadNat r.action.write) right hscan' hboundary hshift hreturn
    hhead hclock (cursorCleanupPcPath_safe skip (r :: rs))
    (cursorCleanupTerminal_valid skip) hprogram
  rw [hmove] at hdecomp
  rw [hmove]
  have hpath : cursorMatchedMovePath rs (scanPrefix ++ [boundary]) =
      cursorMatchedMovePath rs scanPrefix ++ [boundary] := by
    simp [cursorMatchedMovePath, List.append_assoc]
  rw [hpath, hdecomp]
  have hprogramPath :
      cursorCleanupProgramPrefix skip r ++
          cursorMatchedMovePath rs scanPrefix ++ [boundary] =
        cursorCleanupProgramPrefix skip r ++
          cursorMatchedMovePath rs (scanPrefix ++ [boundary]) := by
    simp [cursorMatchedMovePath, List.append_assoc]
  rw [hprogramPath] at hcleanup
  rw [cleanedCursorCycleLeft_eq skip r rs
    (scanPrefix ++ [boundary]) outer hprogramToHead] at hcleanup
  exact hcleanup

end PakFixedPolyomino.ULogBootstrapExecution
