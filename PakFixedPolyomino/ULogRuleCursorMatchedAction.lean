import PakFixedPolyomino.ULogCursorMatchedSource

/-! Equal-source RuleCode action execution at an arbitrary lookup cursor. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def cursorMatchedMovePath (rs : List ULogBytecode.RuleCode)
    (programToHead : List Tape) : List Tape :=
  (ULogBytecode.encodeRules rs).map codeTape ++ programToHead

def cursorRuleCorridor (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (programToHead : List Tape)
    (head : Tape) (runtime : List Tape) : List Tape :=
  ruleContinuationCorridor r rs (programToHead ++ head :: runtime)

theorem reaches_ruleCursorSourceMatch_read (slot : Bool)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead base : List Tape) (head : Tape)
    (runtime suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead head runtime)) :
    Reaches
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary :: base)
        (programToHead ++ head :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (sourceReadStartedAt slot r.source boundary
        (unaryFieldFirst r.read) base
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          codeTape r.slot :: encodedActionPath r.action.write
            r.action.target r.action.move
              (cursorMatchedMovePath rs programToHead) ++
            head :: runtime)
        suffix) := by
  rw [atBitsTail_encodeRules_cons_source]
  have hstart :
      sourceCompareStartAgainst slot r.source r.source 0
          (ruleContinuationCorridor r rs
            (programToHead ++ head :: runtime))
          (ulogCore boundary :: base) suffix =
        sourceCompareStart slot r.source 0
          (cursorRuleCorridor r rs programToHead head runtime)
          (ulogCore boundary :: base) suffix := by
    cases r.source <;>
      simp [sourceCompareStartAgainst, sourceCompareStart,
        cursorRuleCorridor, List.append_assoc]
  rw [hstart]
  have h₀ := reaches_sourceMatchRestoredAt slot r.source
    (cursorRuleCorridor r rs programToHead head runtime) hcorridor
    boundary hboundary base suffix
  have hcorridorEq :
      cursorRuleCorridor r rs programToHead head runtime =
        codeTape (unaryFieldFirst r.read) ::
          ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
            codeTape r.slot :: encodedActionPath r.action.write
              r.action.target r.action.move
                (cursorMatchedMovePath rs programToHead) ++
              head :: runtime) := by
    rcases r with ⟨source, read, ruleSlot, ⟨write, target, move⟩⟩
    cases read <;>
      simp [cursorRuleCorridor, ruleContinuationCorridor,
        cursorMatchedMovePath, encodedActionPath,
        ULogBytecode.encodeNatField, ULogBytecode.encodeAction,
        encodeMove_eq, moveBits, unaryFieldFirst, List.replicate_succ,
        List.map_append, codeTape, List.append_assoc]
  have h₁ : Reaches
      (sourceFieldRestoredAt slot r.source boundary base
        (cursorRuleCorridor r rs programToHead head runtime) suffix)
      (sourceReadStartedAt slot r.source boundary
        (unaryFieldFirst r.read) base
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          codeTape r.slot :: encodedActionPath r.action.write
            r.action.target r.action.move
              (cursorMatchedMovePath rs programToHead) ++
            head :: runtime)
        suffix) := by
    rw [hcorridorEq]
    exact reaches_sourceFieldRestoredAt_read slot r.source boundary
      (unaryFieldFirst r.read) base
      ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
        codeTape r.slot :: encodedActionPath r.action.write
          r.action.target r.action.move
            (cursorMatchedMovePath rs programToHead) ++
          head :: runtime)
      suffix
  exact reaches_trans h₀ h₁

theorem reaches_ruleCursorMatchedAtMostState
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead base runtime : List Tape) (extra : ℕ)
    (hsource : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
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
    (tail : List Tape) :
    Reaches
      (atBitsTail (.fieldCompare .source r.slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary :: base)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (cursorMatchedMovePath rs programToHead)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read boundary base))
          (writeHeadNat r.action.write)
          (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ tail))) := by
  have h₀ := reaches_ruleCursorSourceMatch_read r.slot boundary hboundary r rs
    programToHead base (readHeadNat r.read) runtime
    (ulogCore stateSep :: tail) hcorridor
  have h₁ := reaches_sourceReadAtValid_actionWrite r.slot r.source r.read
    r.action.write r.action.target boundary r.action.move hread base
    (cursorMatchedMovePath rs programToHead) runtime
    (ulogCore stateSep :: tail) hreadPath
  have hhead : choiceHead (readHeadNat r.read) = true := by
    interval_cases r.read <;> native_decide
  have h₂ := reaches_matchedActionAtMostState r.action.write
    r.action.target extra hwrite htargetLower r.action.move
    (cursorMatchedMovePath rs programToHead) runtime
    (readHeadNat r.read) hhead hwritePath htargetPath
    (matchedReadLeftAt r.slot r.source r.read boundary base) tail
  have h₁' : Reaches
      (sourceReadStartedAt r.slot r.source boundary
        (unaryFieldFirst r.read) base
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          codeTape r.slot :: encodedActionPath r.action.write
            r.action.target r.action.move
              (cursorMatchedMovePath rs programToHead) ++
            readHeadNat r.read :: runtime)
        (ulogCore stateSep :: tail))
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read boundary base)
        (List.replicate r.action.target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits r.action.move ++
            cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail)) := h₁
  have h₂' : Reaches
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read boundary base)
        (List.replicate r.action.target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits r.action.move ++
            cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (cursorMatchedMovePath rs programToHead)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read boundary base))
          (writeHeadNat r.action.write)
          (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ tail))) := by
    simpa [hsource, List.append_assoc] using h₂
  exact reaches_trans h₀ (reaches_trans h₁' h₂')

theorem reaches_ruleCursorMatchedAtLeastState
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead base runtime : List Tape) (growth : ℕ)
    (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
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
    (tail : List Tape) :
    Reaches
      (atBitsTail (.fieldCompare .source r.slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary :: base)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (cursorMatchedMovePath rs programToHead)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read boundary base))
          (writeHeadNat r.action.write)
          (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))) := by
  have h₀ := reaches_ruleCursorSourceMatch_read r.slot boundary hboundary r rs
    programToHead base (readHeadNat r.read) runtime
    (ulogCore stateSep ::
      List.replicate growth MStarConcreteAlphabet.work ++ tail) hcorridor
  have h₁ := reaches_sourceReadAtValid_actionWrite r.slot r.source r.read
    r.action.write r.action.target boundary r.action.move hread base
    (cursorMatchedMovePath rs programToHead) runtime
    (ulogCore stateSep ::
      List.replicate growth MStarConcreteAlphabet.work ++ tail) hreadPath
  have hhead : choiceHead (readHeadNat r.read) = true := by
    interval_cases r.read <;> native_decide
  have h₂ := reaches_matchedActionAtLeastState r.action.write r.source growth
    hwrite (by simpa [htarget] using htargetLower) r.action.move
    (cursorMatchedMovePath rs programToHead) runtime
    (readHeadNat r.read) hhead
    (by simpa [htarget] using hwritePath) htargetPath
    (matchedReadLeftAt r.slot r.source r.read boundary base) tail
  have h₁' : Reaches
      (sourceReadStartedAt r.slot r.source boundary
        (unaryFieldFirst r.read) base
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          codeTape r.slot :: encodedActionPath r.action.write
            r.action.target r.action.move
              (cursorMatchedMovePath rs programToHead) ++
            readHeadNat r.read :: runtime)
        (ulogCore stateSep ::
          List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read boundary base)
        (List.replicate r.action.target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits r.action.move ++
            cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ tail)) := by
    simpa [List.append_assoc] using h₁
  have h₂' : Reaches
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read boundary base)
        (List.replicate r.action.target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits r.action.move ++
            cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (cursorMatchedMovePath rs programToHead)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read boundary base))
          (writeHeadNat r.action.write)
          (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))) := by
    simpa [htarget, List.append_assoc] using h₂
  have hall := reaches_trans h₀ (reaches_trans h₁' h₂')
  simpa [List.append_assoc] using hall

end PakFixedPolyomino.ULogBootstrapExecution
