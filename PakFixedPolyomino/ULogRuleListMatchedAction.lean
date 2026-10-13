import PakFixedPolyomino.ULogRuleListMismatchFold

/-! Arbitrary mismatch-prefix fold followed by the matching RuleCode action. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem reaches_mismatchPrefix_matchedAtMost
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    (start final : RuleCursorData) (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      start skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (extra : ℕ) (htarget : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
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
        writeHeadNat r.action.write :: runtime)) :
    Reaches
      (ruleCursorResult slot current actual start (skip ++ r :: rs)
        programToHead runtime outer (ulogCore stateSep :: suffix))
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
              List.replicate extra MStarConcreteAlphabet.work ++ suffix))) := by
  have hprefix := reaches_mismatchPrefix slot current actual programToHead
    runtime outer (ulogCore stateSep :: suffix) trace
  have hmatched := reaches_ruleCursorMatchedAtMostState final.boundary
    hboundary r rs programToHead
    ((List.replicate final.done (ulogCore codeZero) ++
      ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: outer)
    runtime extra htarget hread hwrite htargetLower hcorridor hreadPath hwritePath
    htargetPath suffix
  rcases hmatch with ⟨hsource, hreadEq, hslot⟩
  have hmatched' : Reaches
      (ruleCursorResult slot current actual final (r :: rs)
        programToHead runtime outer (ulogCore stateSep :: suffix))
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
              List.replicate extra MStarConcreteAlphabet.work ++ suffix))) := by
    simpa [ruleCursorResult, ruleCursorBase, hsource, hreadEq, hslot,
      List.append_assoc] using hmatched
  exact reaches_trans hprefix hmatched'

theorem reaches_mismatchPrefix_matchedAtLeast
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    (start final : RuleCursorData) (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      start skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (growth : ℕ) (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
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
        writeHeadNat r.action.write :: runtime)) :
    Reaches
      (ruleCursorResult slot current actual start (skip ++ r :: rs)
        programToHead runtime outer
          (ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix))
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (cursorMatchedMovePath rs programToHead)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read final.boundary
              ((List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: outer)))
          (writeHeadNat r.action.write)
          (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix))) := by
  have hprefix := reaches_mismatchPrefix slot current actual programToHead
    runtime outer
      (ulogCore stateSep ::
        List.replicate growth MStarConcreteAlphabet.work ++ suffix) trace
  have hmatched := reaches_ruleCursorMatchedAtLeastState final.boundary
    hboundary r rs programToHead
    ((List.replicate final.done (ulogCore codeZero) ++
      ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: outer)
    runtime growth htarget hread hwrite htargetLower hcorridor hreadPath hwritePath
    htargetPath suffix
  rcases hmatch with ⟨hsource, hreadEq, hslot⟩
  have hmatched' : Reaches
      (ruleCursorResult slot current actual final (r :: rs)
        programToHead runtime outer
          (ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ suffix))
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (cursorMatchedMovePath rs programToHead)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeftAt r.slot r.source r.read final.boundary
              ((List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: outer)))
          (writeHeadNat r.action.write)
          (runtime ++ List.replicate r.action.target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: suffix))) := by
    simpa [ruleCursorResult, ruleCursorBase, hsource, hreadEq, hslot,
      List.append_assoc] using hmatched
  exact reaches_trans hprefix hmatched'

end PakFixedPolyomino.ULogBootstrapExecution
