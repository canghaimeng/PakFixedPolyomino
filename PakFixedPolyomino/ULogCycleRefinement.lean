import PakFixedPolyomino.ULogMatchedRuleExecution

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def cleanupLeft (pcPath : List Tape) (terminal : Tape)
    (programPath outer : List Tape) : List Tape :=
  (pcPath ++ terminal :: programPath).reverse ++ ulogCore pcMark :: outer

def cleanedCycleLeft (pcPath : List Tape) (programPath outer : List Tape) :
    List Tape :=
  programPath.reverse.map restoreProgramCell ++ ulogCore codeOne ::
    pcPath.reverse.map restorePcCell ++ ulogCore pcMark :: outer

/-- After all fields of a matching rule have been consumed, the physical
left stack is exactly the reverse bytecode rule, followed by the program-count
terminator, counter block, and program-counter marker. -/
theorem matchedRuleLeft_eq (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (base : List Tape) :
    matchedMoveLeft r.action.write r.action.target r.action.move
        (matchedReadLeft r.slot r.source r.read
          (List.replicate (r :: rs).length (ulogCore pcDone) ++
            ulogCore pcMark :: base)) =
      ((ULogBytecode.encodeRule r).map codeTape).reverse ++
        ulogCore sourceBoundary ::
          List.replicate (r :: rs).length (ulogCore pcDone) ++
            ulogCore pcMark :: base := by
  rcases r with ⟨source, read, slot, ⟨write, target, move⟩⟩
  simp [matchedMoveLeft, matchedReadLeft, ULogBytecode.encodeRule,
    ULogBytecode.encodeAction, ULogBytecode.encodeNatField, encodeMove_eq,
    codeTape, List.map_append, List.reverse_append, List.append_assoc]

theorem reaches_moveStay_cleanup
    (programPrefix scanPath pcPath : List Tape) (terminal : Tape)
    (outer : List Tape) (head : Tape) (right : List Tape)
    (hscan : MoveScanSafe scanPath)
    (hclock : RestoreClockSafe
      (head :: (pcPath ++ terminal :: (programPrefix ++ scanPath)).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe (programPrefix ++ scanPath))
    (hhead : choiceHead head = true) :
    Reaches
      (.running (.moveSimHead .stay)
        (beforeRightPath scanPath
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer)
          head right))
      (.running .cycleStart
        ⟨cleanedCycleLeft pcPath (programPrefix ++ scanPath) outer,
          head, right⟩) := by
  have h₀ := reaches_moveStay scanPath hscan
    (programPrefix.reverse ++ terminal :: pcPath.reverse ++
      ulogCore pcMark :: outer) head hhead right
  have h₁ := reaches_restoreCycle pcPath terminal (programPrefix ++ scanPath)
    outer head hclock hpc hterminal hprogram hhead right
  have h₀' : Reaches
      (.running (.moveSimHead .stay)
        (beforeRightPath scanPath
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer)
          head right))
      (.running .restoreClock
        ⟨cleanupLeft pcPath terminal (programPrefix ++ scanPath) outer,
          head, right⟩) := by
    simpa [cleanupLeft, List.reverse_append, List.append_assoc] using h₀
  simpa [cleanupLeft, cleanedCycleLeft] using reaches_trans h₀' h₁

theorem reaches_moveRightInternal_cleanup
    (programPrefix scanPath pcPath : List Tape) (terminal : Tape)
    (outer : List Tape) (head cell : Tape) (right : List Tape)
    (hscan : MoveScanSafe scanPath)
    (hhead : choiceHead head = true)
    (hcell : cell = payloadTape false ∨
      cell = payloadTape true ∨ cell = ulogCore payloadBlank)
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
        (pcPath ++ terminal ::
          (programPrefix ++ scanPath ++ [unheadTape head])).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe
      (programPrefix ++ scanPath ++ [unheadTape head])) :
    Reaches
      (.running (.moveSimHead .right)
        (beforeRightPath scanPath
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer)
          head (cell :: right)))
      (.running .cycleStart
        ⟨cleanedCycleLeft pcPath
            (programPrefix ++ scanPath ++ [unheadTape head]) outer,
          headTapeOfCell cell, right⟩) := by
  have h₀ := reaches_moveRightInternal scanPath hscan
    (programPrefix.reverse ++ terminal :: pcPath.reverse ++
      ulogCore pcMark :: outer) head hhead cell hcell right
  have hnewHead : choiceHead (headTapeOfCell cell) = true := by
    rcases hcell with rfl | rfl | rfl <;> native_decide
  have h₁ := reaches_restoreCycle pcPath terminal
    (programPrefix ++ scanPath ++ [unheadTape head]) outer
    (headTapeOfCell cell) hclock hpc hterminal hprogram hnewHead right
  have h₀' : Reaches
      (.running (.moveSimHead .right)
        (beforeRightPath scanPath
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer)
          head (cell :: right)))
      (.running .restoreClock
        ⟨cleanupLeft pcPath terminal
            (programPrefix ++ scanPath ++ [unheadTape head]) outer,
          headTapeOfCell cell, right⟩) := by
    simpa [cleanupLeft, List.reverse_append, List.append_assoc] using h₀
  simpa [cleanupLeft, cleanedCycleLeft] using reaches_trans h₀' h₁

theorem reaches_moveLeftInternal_cleanup
    (programPrefix scanPrefix pcPath : List Tape) (terminal : Tape)
    (outer : List Tape) (cell head : Tape) (right : List Tape)
    (hscan : MoveScanSafe (scanPrefix ++ [cell]))
    (hcell : cell = payloadTape false ∨
      cell = payloadTape true ∨ cell = ulogCore payloadBlank)
    (hhead : choiceHead head = true)
    (hclock : RestoreClockSafe
      (headTapeOfCell cell ::
        (pcPath ++ terminal :: (programPrefix ++ scanPrefix)).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe (programPrefix ++ scanPrefix)) :
    Reaches
      (.running (.moveSimHead .left)
        (beforeRightPath (scanPrefix ++ [cell])
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer)
          head right))
      (.running .cycleStart
        ⟨cleanedCycleLeft pcPath (programPrefix ++ scanPrefix) outer,
          headTapeOfCell cell, unheadTape head :: right⟩) := by
  have h₀ := reaches_moveLeftInternal scanPrefix cell hscan hcell
    (programPrefix.reverse ++ terminal :: pcPath.reverse ++
      ulogCore pcMark :: outer) head hhead right
  have hnewHead : choiceHead (headTapeOfCell cell) = true := by
    rcases hcell with rfl | rfl | rfl <;> native_decide
  have h₁ := reaches_restoreCycle pcPath terminal
    (programPrefix ++ scanPrefix) outer (headTapeOfCell cell) hclock hpc
    hterminal hprogram hnewHead (unheadTape head :: right)
  have h₀' : Reaches
      (.running (.moveSimHead .left)
        (beforeRightPath (scanPrefix ++ [cell])
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer)
          head right))
      (.running .restoreClock
        ⟨cleanupLeft pcPath terminal (programPrefix ++ scanPrefix) outer,
          headTapeOfCell cell, unheadTape head :: right⟩) := by
    simpa [cleanupLeft, List.reverse_append, List.append_assoc] using h₀
  simpa [cleanupLeft, cleanedCycleLeft] using reaches_trans h₀' h₁

theorem reaches_moveRightBoundary_cleanup
    (programPrefix scanPath pcPath : List Tape) (terminal : Tape)
    (outer : List Tape) (head boundary : Tape)
    (shiftPrefix : List Tape) (last : Tape) (right : List Tape)
    (hscan : MoveScanSafe scanPath)
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (hshift : ShiftRuntimeSafe (shiftPrefix ++ [last]))
    (hreturn : ReturnMovedSafe (shiftPrefix.reverse ++ [boundary]))
    (hhead : choiceHead head = true)
    (hclock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (pcPath ++ terminal ::
          (programPrefix ++ scanPath ++ [unheadTape head])).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe
      (programPrefix ++ scanPath ++ [unheadTape head])) :
    Reaches
      (.running (.moveSimHead .right)
        (beforeRightPath scanPath
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer)
          head
          (boundary :: shiftPrefix ++ last ::
            MStarConcreteAlphabet.work :: right)))
      (.running .cycleStart
        ⟨cleanedCycleLeft pcPath
            (programPrefix ++ scanPath ++ [unheadTape head]) outer,
          ulogCore payloadHeadBlank,
          boundary :: shiftPrefix ++ last :: right⟩) := by
  have h₀ := reaches_moveRightBoundary scanPath shiftPrefix hscan
    boundary last hboundary hshift hreturn
    (programPrefix.reverse ++ terminal :: pcPath.reverse ++
      ulogCore pcMark :: outer)
    head hhead right
  have hnewHead : choiceHead (ulogCore payloadHeadBlank) = true := by
    native_decide
  have h₁ := reaches_restoreCycle pcPath terminal
    (programPrefix ++ scanPath ++ [unheadTape head]) outer
    (ulogCore payloadHeadBlank) hclock hpc hterminal hprogram hnewHead
    (boundary :: shiftPrefix ++ last :: right)
  have h₀' : Reaches
      (.running (.moveSimHead .right)
        (beforeRightPath scanPath
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: outer)
          head
          (boundary :: shiftPrefix ++ last ::
            MStarConcreteAlphabet.work :: right)))
      (.running .restoreClock
        ⟨cleanupLeft pcPath terminal
            (programPrefix ++ scanPath ++ [unheadTape head]) outer,
          ulogCore payloadHeadBlank,
          boundary :: shiftPrefix ++ last :: right⟩) := by
    simpa [cleanupLeft, List.reverse_append, List.append_assoc] using h₀
  simpa [cleanupLeft, cleanedCycleLeft] using reaches_trans h₀' h₁

theorem reaches_moveLeftBoundary_cleanup
    (programPrefix scanPath pcPath : List Tape) (terminal boundary : Tape)
    (outer : List Tape) (head : Tape) (right : List Tape)
    (hscan : MoveScanSafe (scanPath ++ [boundary]))
    (hboundary : boundary = ulogCore payloadEnd ∨
      boundary = ulogCore payloadStartOne)
    (hshift : ShiftRuntimeSafe
      (scanPath.reverse ++ programPrefix.reverse ++
        terminal :: pcPath.reverse ++ [ulogCore pcMark]))
    (hreturn : ReturnMovedSafe
      ((scanPath.reverse ++ programPrefix.reverse ++
        terminal :: pcPath.reverse).reverse ++ [boundary]))
    (hhead : choiceHead head = true)
    (hclock : RestoreClockSafe
      (ulogCore payloadHeadBlank ::
        (pcPath ++ terminal ::
          (programPrefix ++ scanPath ++ [boundary])).reverse))
    (hpc : RestorePcSafe pcPath)
    (hterminal : terminal = ulogCore codeOne ∨
      terminal = ulogCore sourceBoundary)
    (hprogram : RestoreHeadSafe
      (programPrefix ++ scanPath ++ [boundary])) :
    Reaches
      (.running (.moveSimHead .left)
        (beforeRightPath (scanPath ++ [boundary])
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)
          head right))
      (.running .cycleStart
        ⟨cleanedCycleLeft pcPath
            (programPrefix ++ scanPath ++ [boundary]) outer,
          ulogCore payloadHeadBlank, unheadTape head :: right⟩) := by
  let shiftPrefix := scanPath.reverse ++ programPrefix.reverse ++
    terminal :: pcPath.reverse
  have h₀ := reaches_moveScan .left (scanPath ++ [boundary]) hscan
    (programPrefix.reverse ++ terminal :: pcPath.reverse ++
      ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)
    head right
  have h₁ : Reaches
      (.running (.moveSimHead .left)
        (afterRightPath (scanPath ++ [boundary])
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)
          head right))
      (.running (.actionPhase .movePlaceLeft)
        ⟨shiftPrefix ++ ulogCore pcMark ::
            MStarConcreteAlphabet.work :: outer,
          boundary, unheadTape head :: right⟩) := by
    apply reaches_step
    simpa [shiftPrefix, afterRightPath, List.reverse_append,
      List.append_assoc] using
      (moveSimHead_left head hhead
        (shiftPrefix ++ ulogCore pcMark ::
          MStarConcreteAlphabet.work :: outer)
        boundary right)
  have h₂ : Reaches
      (.running (.actionPhase .movePlaceLeft)
        ⟨shiftPrefix ++ ulogCore pcMark ::
            MStarConcreteAlphabet.work :: outer,
          boundary, unheadTape head :: right⟩)
      (.running (.shiftRuntime (.left boundary))
        (beforeLeftPath (shiftPrefix ++ [ulogCore pcMark]) outer
          MStarConcreteAlphabet.work
          (ulogCore payloadHeadBlank :: unheadTape head :: right))) := by
    apply reaches_step
    cases shiftPrefix with
    | nil =>
        simpa [beforeLeftPath] using
          (movePlaceLeft_boundary boundary hboundary
            (MStarConcreteAlphabet.work :: outer) (ulogCore pcMark)
            (unheadTape head :: right))
    | cons x xs =>
        simpa [beforeLeftPath, List.append_assoc] using
          (movePlaceLeft_boundary boundary hboundary
            (xs ++ ulogCore pcMark :: MStarConcreteAlphabet.work :: outer) x
            (unheadTape head :: right))
  have h₃ := reaches_shiftRuntimeLeft_restored boundary shiftPrefix
    (ulogCore pcMark) (by simpa [shiftPrefix] using hshift)
    (by simpa [shiftPrefix] using hreturn) outer
    (ulogCore payloadHeadBlank) (by native_decide) (unheadTape head :: right)
  have hmove : Reaches
      (.running (.moveSimHead .left)
        (beforeRightPath (scanPath ++ [boundary])
          (programPrefix.reverse ++ terminal :: pcPath.reverse ++
            ulogCore pcMark :: MStarConcreteAlphabet.work :: outer)
          head right))
      (.running .restoreClock
        ⟨cleanupLeft pcPath terminal
            (programPrefix ++ scanPath ++ [boundary]) outer,
          ulogCore payloadHeadBlank, unheadTape head :: right⟩) := by
    have hall := reaches_trans h₀ (reaches_trans h₁ (reaches_trans h₂ h₃))
    simpa [shiftPrefix, cleanupLeft, List.reverse_append,
      List.append_assoc] using hall
  have hcleanup := reaches_restoreCycle pcPath terminal
    (programPrefix ++ scanPath ++ [boundary]) outer
    (ulogCore payloadHeadBlank) hclock hpc hterminal hprogram
    (by native_decide) (unheadTape head :: right)
  simpa [cleanupLeft, cleanedCycleLeft] using
    reaches_trans hmove hcleanup

end PakFixedPolyomino.ULogBootstrapExecution
