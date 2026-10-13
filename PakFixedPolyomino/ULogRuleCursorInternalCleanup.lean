import PakFixedPolyomino.ULogRuleListNormalizedStayCycle

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem reaches_cursorMatched_rightInternal_cleanup_normalized
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hwrite : r.action.write < 3)
    (hmove : r.action.move = .right)
    (cell : Tape) (right : List Tape)
    (hcell : cell = payloadTape false ∨
      cell = payloadTape true ∨ cell = ulogCore payloadBlank)
    (hscan : MoveScanSafe (cursorMatchedMovePath rs programToHead))
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
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
          (writeHeadNat r.action.write) (cell :: right)))
      (.running .cycleStart
        ⟨canonicalCursorCycleLeft (skip ++ r :: rs)
            (programToHead ++
              [unheadTape (writeHeadNat r.action.write)]) outer,
          headTapeOfCell cell, right⟩) := by
  have hdecomp := matchedCursor_cleanup_decomposition slot current actual
    programToHead runtime skip r rs trace outer
  have hhead : choiceHead (writeHeadNat r.action.write) = true := by
    interval_cases r.action.write <;> native_decide
  have hcleanup := reaches_moveRightInternal_cleanup
    (cursorCleanupProgramPrefix skip r)
    (cursorMatchedMovePath rs programToHead)
    (cursorCleanupPcPath skip (r :: rs))
    (cursorCleanupTerminal skip) outer (writeHeadNat r.action.write)
    cell right hscan hhead hcell hclock
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

theorem reaches_cursorMatched_leftInternal_cleanup_normalized
    (slot : Bool) (current actual : ℕ)
    (scanPrefix runtime outer : List Tape) (cell : Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual
      (scanPrefix ++ [cell]) runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hwrite : r.action.write < 3)
    (hmove : r.action.move = .left)
    (right : List Tape)
    (hcell : cell = payloadTape false ∨
      cell = payloadTape true ∨ cell = ulogCore payloadBlank)
    (hscan : MoveScanSafe
      (cursorMatchedMovePath rs (scanPrefix ++ [cell])))
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs scanPrefix)).reverse))
    (hprogram : RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs scanPrefix))
    (hprogramToHead : scanPrefix.map restoreProgramCell = scanPrefix) :
    Reaches
      (.running (.moveSimHead r.action.move)
        (beforeRightPath
          (cursorMatchedMovePath rs (scanPrefix ++ [cell]))
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read final.boundary
              ((List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: outer)))
          (writeHeadNat r.action.write) right))
      (.running .cycleStart
        ⟨canonicalCursorCycleLeft (skip ++ r :: rs) scanPrefix outer,
          headTapeOfCell cell,
          unheadTape (writeHeadNat r.action.write) :: right⟩) := by
  have hdecomp := matchedCursor_cleanup_decomposition slot current actual
    (scanPrefix ++ [cell]) runtime skip r rs trace outer
  have hhead : choiceHead (writeHeadNat r.action.write) = true := by
    interval_cases r.action.write <;> native_decide
  have hscan' : MoveScanSafe
      (cursorMatchedMovePath rs scanPrefix ++ [cell]) := by
    simpa [cursorMatchedMovePath, List.append_assoc] using hscan
  have hcleanup := reaches_moveLeftInternal_cleanup
    (cursorCleanupProgramPrefix skip r)
    (cursorMatchedMovePath rs scanPrefix)
    (cursorCleanupPcPath skip (r :: rs))
    (cursorCleanupTerminal skip) outer cell
    (writeHeadNat r.action.write) right hscan' hcell hhead hclock
    (cursorCleanupPcPath_safe skip (r :: rs))
    (cursorCleanupTerminal_valid skip) hprogram
  rw [hmove] at hdecomp
  rw [hmove]
  have hpath : cursorMatchedMovePath rs (scanPrefix ++ [cell]) =
      cursorMatchedMovePath rs scanPrefix ++ [cell] := by
    simp [cursorMatchedMovePath, List.append_assoc]
  rw [hpath, hdecomp]
  rw [cleanedCursorCycleLeft_eq skip r rs scanPrefix outer
    hprogramToHead] at hcleanup
  exact hcleanup

end PakFixedPolyomino.ULogBootstrapExecution
