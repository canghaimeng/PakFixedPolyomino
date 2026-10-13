import PakFixedPolyomino.ULogDynamicMatchedRule

/-! Full matched RuleCode action folds for evolving runtime tapes. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem reaches_dynamicMatchedRuleCodeAtMostState
    (leftTape : List Tape) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (input : List Bool) (extra : ℕ)
    (hsource : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (runtime : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (dynamicFirstRuleCorridor r rs input leftTape
        (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (dynamicMatchedRuleMovePath rs input leftTape)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          dynamicMatchedRuleMovePath rs input leftTape))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        dynamicMatchedRuleMovePath rs input leftTape ++
          writeHeadNat r.action.write :: runtime))
    (left tail : List Tape) :
    Reaches
      (dynamicRuleSourceStarted r.slot leftTape (r :: rs) input left
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (dynamicMatchedRuleMovePath rs input leftTape)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeft r.slot r.source r.read
              (List.replicate (r :: rs).length (ulogCore pcDone) ++
                ulogCore pcMark :: left)))
          (writeHeadNat r.action.write)
          (runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ tail))) := by
  have h₀ := reaches_dynamicRuleSourceMatch_read r.slot leftTape r rs input
    left (readHeadNat r.read) runtime (ulogCore stateSep :: tail) hcorridor
  have h₁ := reaches_matchedRuleAtMostState r.slot r.read r.action.write
    r.action.target extra r.action.move hread hwrite htargetLower
    (dynamicMatchedRuleMovePath rs input leftTape) runtime hreadPath
    hwritePath htargetPath
    (List.replicate (r :: rs).length (ulogCore pcDone) ++
      ulogCore pcMark :: left) tail
  have h₀' : Reaches
      (dynamicRuleSourceStarted r.slot leftTape (r :: rs) input left
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (sourceReadStarted r.slot (r.action.target + extra)
        (unaryFieldFirst r.read)
        (List.replicate (r :: rs).length (ulogCore pcDone) ++
          ulogCore pcMark :: left)
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          codeTape r.slot :: encodedActionPath r.action.write
            r.action.target r.action.move
              (dynamicMatchedRuleMovePath rs input leftTape) ++
            readHeadNat r.read :: runtime)
        (ulogCore stateSep :: tail)) := by
    simpa [hsource] using h₀
  have h₁' : Reaches
      (sourceReadStarted r.slot (r.action.target + extra)
        (unaryFieldFirst r.read)
        (List.replicate (r :: rs).length (ulogCore pcDone) ++
          ulogCore pcMark :: left)
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          codeTape r.slot :: encodedActionPath r.action.write
            r.action.target r.action.move
              (dynamicMatchedRuleMovePath rs input leftTape) ++
            readHeadNat r.read :: runtime)
        (ulogCore stateSep :: tail))
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (dynamicMatchedRuleMovePath rs input leftTape)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeft r.slot r.source r.read
              (List.replicate (r :: rs).length (ulogCore pcDone) ++
                ulogCore pcMark :: left)))
          (writeHeadNat r.action.write)
          (runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ tail))) := by
    simpa [hsource] using h₁
  exact reaches_trans h₀' h₁'

theorem reaches_dynamicMatchedRuleCodeAtLeastState
    (leftTape : List Tape) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (input : List Bool) (growth : ℕ)
    (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (runtime : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (dynamicFirstRuleCorridor r rs input leftTape
        (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (dynamicMatchedRuleMovePath rs input leftTape)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          dynamicMatchedRuleMovePath rs input leftTape))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++
        dynamicMatchedRuleMovePath rs input leftTape ++
          writeHeadNat r.action.write :: runtime))
    (left tail : List Tape) :
    Reaches
      (dynamicRuleSourceStarted r.slot leftTape (r :: rs) input left
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (dynamicMatchedRuleMovePath rs input leftTape)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeft r.slot r.source r.read
              (List.replicate (r :: rs).length (ulogCore pcDone) ++
                ulogCore pcMark :: left)))
          (writeHeadNat r.action.write)
          (runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail))) := by
  have h₀ := reaches_dynamicRuleSourceMatch_read r.slot leftTape r rs input
    left (readHeadNat r.read) runtime
    (ulogCore stateSep ::
      List.replicate growth MStarConcreteAlphabet.work ++ tail) hcorridor
  have hreadPath' : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        (r.source + growth) r.action.move
          (dynamicMatchedRuleMovePath rs input leftTape)) := by
    simpa [htarget] using hreadPath
  have hwritePath' : ActionWriteCorridorSafe
      (List.replicate (r.source + growth) (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          dynamicMatchedRuleMovePath rs input leftTape) := by
    simpa [htarget] using hwritePath
  have h₁ := reaches_matchedRuleAtLeastState r.slot r.source r.read
    r.action.write growth r.action.move hread hwrite
    (by simpa [htarget] using htargetLower)
    (dynamicMatchedRuleMovePath rs input leftTape) runtime hreadPath'
    hwritePath' htargetPath
    (List.replicate (r :: rs).length (ulogCore pcDone) ++
      ulogCore pcMark :: left) tail
  have h₀' : Reaches
      (dynamicRuleSourceStarted r.slot leftTape (r :: rs) input left
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (sourceReadStarted r.slot r.source (unaryFieldFirst r.read)
        (List.replicate (r :: rs).length (ulogCore pcDone) ++
          ulogCore pcMark :: left)
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          codeTape r.slot :: encodedActionPath r.action.write
            (r.source + growth) r.action.move
              (dynamicMatchedRuleMovePath rs input leftTape) ++
            readHeadNat r.read :: runtime)
        (ulogCore stateSep ::
          List.replicate growth MStarConcreteAlphabet.work ++ tail)) := by
    simpa [htarget] using h₀
  have h₁' : Reaches
      (sourceReadStarted r.slot r.source (unaryFieldFirst r.read)
        (List.replicate (r :: rs).length (ulogCore pcDone) ++
          ulogCore pcMark :: left)
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          codeTape r.slot :: encodedActionPath r.action.write
            (r.source + growth) r.action.move
              (dynamicMatchedRuleMovePath rs input leftTape) ++
            readHeadNat r.read :: runtime)
        (ulogCore stateSep ::
          List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (dynamicMatchedRuleMovePath rs input leftTape)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeft r.slot r.source r.read
              (List.replicate (r :: rs).length (ulogCore pcDone) ++
                ulogCore pcMark :: left)))
          (writeHeadNat r.action.write)
          (runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail))) := by
    simpa [htarget] using h₁
  exact reaches_trans h₀' h₁'

end PakFixedPolyomino.ULogBootstrapExecution
