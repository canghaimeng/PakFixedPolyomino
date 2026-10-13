import PakFixedPolyomino.ULogBootstrapExecution

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem reaches_sourceReadZero_false
    (source write target : ℕ) (m : OneTapeTableau.Move)
    (base movePath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe
      (codeTape false :: encodedActionPath write target m movePath)) :
    Reaches
      (sourceReadStarted false source (unaryFieldFirst 0) base
        ((ULogBytecode.encodeNatField 0).tail.map codeTape ++
          codeTape false :: encodedActionPath write target m movePath ++
            readHeadNat 0 :: runtime) suffix)
      (actionWriteStart write (matchedReadLeft false source 0 base)
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        (readHeadNat 0)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)) := by
  have h := reaches_sourceReadZero_slotMatch false source base
    (encodedActionPath write target m movePath) runtime suffix hsafe
  cases write <;>
    simpa [encodedActionPath, ULogBytecode.encodeNatField,
      actionWriteStart, matchedReadLeft, unaryFieldFirst, readHeadNat,
      beforeRightPath, List.map_append, List.replicate_succ,
      List.append_assoc, codeTape] using h

theorem reaches_sourceReadZero_true
    (source write target : ℕ) (m : OneTapeTableau.Move)
    (base movePath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe
      (codeTape true :: encodedActionPath write target m movePath)) :
    Reaches
      (sourceReadStarted true source (unaryFieldFirst 0) base
        ((ULogBytecode.encodeNatField 0).tail.map codeTape ++
          codeTape true :: encodedActionPath write target m movePath ++
            readHeadNat 0 :: runtime) suffix)
      (actionWriteStart write (matchedReadLeft true source 0 base)
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        (readHeadNat 0)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)) := by
  have h := reaches_sourceReadZero_slotMatch true source base
    (encodedActionPath write target m movePath) runtime suffix hsafe
  cases write <;>
    simpa [encodedActionPath, ULogBytecode.encodeNatField,
      actionWriteStart, matchedReadLeft, unaryFieldFirst, readHeadNat,
      beforeRightPath, List.map_append, List.replicate_succ,
      List.append_assoc, codeTape] using h

theorem reaches_sourceReadOne_false
    (source write target : ℕ) (m : OneTapeTableau.Move)
    (base movePath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe
      (codeTape false :: encodedActionPath write target m movePath)) :
    Reaches
      (sourceReadStarted false source (unaryFieldFirst 1) base
        ((ULogBytecode.encodeNatField 1).tail.map codeTape ++
          codeTape false :: encodedActionPath write target m movePath ++
            readHeadNat 1 :: runtime) suffix)
      (actionWriteStart write (matchedReadLeft false source 1 base)
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        (readHeadNat 1)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)) := by
  have h := reaches_sourceReadOne_slotMatch false source base
    (encodedActionPath write target m movePath) runtime suffix hsafe
  cases write <;>
    simpa [encodedActionPath, ULogBytecode.encodeNatField,
      actionWriteStart, matchedReadLeft, unaryFieldFirst, readHeadNat,
      beforeRightPath, List.map_append, List.replicate_succ,
      List.append_assoc, codeTape] using h

theorem reaches_sourceReadOne_true
    (source write target : ℕ) (m : OneTapeTableau.Move)
    (base movePath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe
      (codeTape true :: encodedActionPath write target m movePath)) :
    Reaches
      (sourceReadStarted true source (unaryFieldFirst 1) base
        ((ULogBytecode.encodeNatField 1).tail.map codeTape ++
          codeTape true :: encodedActionPath write target m movePath ++
            readHeadNat 1 :: runtime) suffix)
      (actionWriteStart write (matchedReadLeft true source 1 base)
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        (readHeadNat 1)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)) := by
  have h := reaches_sourceReadOne_slotMatch true source base
    (encodedActionPath write target m movePath) runtime suffix hsafe
  cases write <;>
    simpa [encodedActionPath, ULogBytecode.encodeNatField,
      actionWriteStart, matchedReadLeft, unaryFieldFirst, readHeadNat,
      beforeRightPath, List.map_append, List.replicate_succ,
      List.append_assoc, codeTape] using h

theorem reaches_sourceReadBlank_false
    (source write target : ℕ) (m : OneTapeTableau.Move)
    (base movePath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe
      (codeTape false :: encodedActionPath write target m movePath)) :
    Reaches
      (sourceReadStarted false source (unaryFieldFirst 2) base
        ((ULogBytecode.encodeNatField 2).tail.map codeTape ++
          codeTape false :: encodedActionPath write target m movePath ++
            readHeadNat 2 :: runtime) suffix)
      (actionWriteStart write (matchedReadLeft false source 2 base)
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        (readHeadNat 2)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)) := by
  have h := reaches_sourceReadBlank_slotMatch false source base
    (encodedActionPath write target m movePath) runtime suffix hsafe
  cases write <;>
    simpa [encodedActionPath, ULogBytecode.encodeNatField,
      actionWriteStart, matchedReadLeft, unaryFieldFirst, readHeadNat,
      beforeRightPath, List.map_append, List.replicate_succ,
      List.append_assoc, codeTape] using h

theorem reaches_sourceReadBlank_true
    (source write target : ℕ) (m : OneTapeTableau.Move)
    (base movePath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe
      (codeTape true :: encodedActionPath write target m movePath)) :
    Reaches
      (sourceReadStarted true source (unaryFieldFirst 2) base
        ((ULogBytecode.encodeNatField 2).tail.map codeTape ++
          codeTape true :: encodedActionPath write target m movePath ++
            readHeadNat 2 :: runtime) suffix)
      (actionWriteStart write (matchedReadLeft true source 2 base)
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        (readHeadNat 2)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)) := by
  have h := reaches_sourceReadBlank_slotMatch true source base
    (encodedActionPath write target m movePath) runtime suffix hsafe
  cases write <;>
    simpa [encodedActionPath, ULogBytecode.encodeNatField,
      actionWriteStart, matchedReadLeft, unaryFieldFirst, readHeadNat,
      beforeRightPath, List.map_append, List.replicate_succ,
      List.append_assoc, codeTape] using h

theorem reaches_sourceReadValid_actionWrite
    (slot : Bool) (source read write target : ℕ)
    (m : OneTapeTableau.Move) (hread : read < 3)
    (base movePath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe
      (codeTape slot :: encodedActionPath write target m movePath)) :
    Reaches
      (sourceReadStarted slot source (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape slot :: encodedActionPath write target m movePath ++
            readHeadNat read :: runtime) suffix)
      (actionWriteStart write (matchedReadLeft slot source read base)
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        (readHeadNat read)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)) := by
  cases slot <;> interval_cases read
  · exact reaches_sourceReadZero_false source write target m
      base movePath runtime suffix hsafe
  · exact reaches_sourceReadOne_false source write target m
      base movePath runtime suffix hsafe
  · exact reaches_sourceReadBlank_false source write target m
      base movePath runtime suffix hsafe
  · exact reaches_sourceReadZero_true source write target m
      base movePath runtime suffix hsafe
  · exact reaches_sourceReadOne_true source write target m
      base movePath runtime suffix hsafe
  · exact reaches_sourceReadBlank_true source write target m
      base movePath runtime suffix hsafe

theorem reaches_matchedRuleTargetZero
    (slot : Bool) (source read write : ℕ)
    (m : OneTapeTableau.Move) (hread : read < 3) (hwrite : write < 3)
    (movePath runtime : List Tape)
    (hreadPath : ReadCorridorSafe
      (codeTape slot :: encodedActionPath write 0 m movePath))
    (hwritePath : ActionWriteCorridorSafe
      (ulogCore codeOne :: moveBits m ++ movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits m ++ movePath ++ writeHeadNat write :: runtime))
    (base tail : List Tape) :
    ∃ z, Reaches
      (sourceReadStarted slot source (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape slot :: encodedActionPath write 0 m movePath ++
            readHeadNat read :: runtime)
        (ulogCore stateSep :: tail))
      (.accepted z) := by
  have h₀ := reaches_sourceReadValid_actionWrite slot source read write 0 m
    hread base movePath runtime (ulogCore stateSep :: tail) hreadPath
  have hhead : choiceHead (readHeadNat read) = true := by
    interval_cases read <;> native_decide
  obtain ⟨z, h₁⟩ := reaches_matchedActionTargetZero write source hwrite m
    movePath runtime (readHeadNat read) hhead hwritePath htargetPath
    (matchedReadLeft slot source read base) tail
  exact ⟨z, reaches_trans (by simpa using h₀) h₁⟩

theorem reaches_matchedRuleTargetOneZero
    (slot : Bool) (read write : ℕ)
    (m : OneTapeTableau.Move) (hread : read < 3) (hwrite : write < 3)
    (movePath runtime : List Tape)
    (hreadPath : ReadCorridorSafe
      (codeTape slot :: encodedActionPath write 1 m movePath))
    (hwritePath : ActionWriteCorridorSafe
      (ulogCore codeZero :: ulogCore codeOne :: moveBits m ++ movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits m ++ movePath ++ writeHeadNat write :: runtime))
    (base tail : List Tape) :
    Reaches
      (sourceReadStarted slot 0 (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape slot :: encodedActionPath write 1 m movePath ++
            readHeadNat read :: runtime)
        (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail))
      .rejected := by
  have h₀ := reaches_sourceReadValid_actionWrite slot 0 read write 1 m
    hread base movePath runtime
    (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail) hreadPath
  have hhead : choiceHead (readHeadNat read) = true := by
    interval_cases read <;> native_decide
  have h₁ := reaches_matchedActionTargetOneZero write hwrite m movePath
    runtime (readHeadNat read) hhead hwritePath htargetPath
    (matchedReadLeft slot 0 read base) tail
  exact reaches_trans (by simpa [List.append_assoc] using h₀) h₁

theorem reaches_matchedRuleTargetOnePositive
    (slot : Bool) (extra read write : ℕ)
    (m : OneTapeTableau.Move) (hread : read < 3) (hwrite : write < 3)
    (movePath runtime : List Tape)
    (hreadPath : ReadCorridorSafe
      (codeTape slot :: encodedActionPath write 1 m movePath))
    (hwritePath : ActionWriteCorridorSafe
      (ulogCore codeZero :: ulogCore codeOne :: moveBits m ++ movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits m ++ movePath ++ writeHeadNat write :: runtime))
    (base tail : List Tape) :
    Reaches
      (sourceReadStarted slot (extra + 1) (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape slot :: encodedActionPath write 1 m movePath ++
            readHeadNat read :: runtime)
        (ulogCore stateSep :: tail))
      .rejected := by
  have h₀ := reaches_sourceReadValid_actionWrite slot (extra + 1) read write
    1 m hread base movePath runtime (ulogCore stateSep :: tail) hreadPath
  have hhead : choiceHead (readHeadNat read) = true := by
    interval_cases read <;> native_decide
  have h₁ := reaches_matchedActionTargetOnePositive write extra hwrite m
    movePath runtime (readHeadNat read) hhead hwritePath htargetPath
    (matchedReadLeft slot (extra + 1) read base) tail
  exact reaches_trans (by simpa [List.append_assoc] using h₀) h₁

theorem reaches_matchedRuleAtMostState
    (slot : Bool) (read write target extra : ℕ)
    (m : OneTapeTableau.Move) (hread : read < 3) (hwrite : write < 3)
    (htarget : 2 ≤ target)
    (movePath runtime : List Tape)
    (hreadPath : ReadCorridorSafe
      (codeTape slot :: encodedActionPath write target m movePath))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits m ++ movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits m ++ movePath ++ writeHeadNat write :: runtime))
    (base tail : List Tape) :
    Reaches
      (sourceReadStarted slot (target + extra) (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape slot :: encodedActionPath write target m movePath ++
            readHeadNat read :: runtime)
        (ulogCore stateSep :: tail))
      (.running (.moveSimHead m)
        (beforeRightPath movePath
          (matchedMoveLeft write target m
            (matchedReadLeft slot (target + extra) read base))
          (writeHeadNat write)
          (runtime ++ List.replicate target (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate extra MStarConcreteAlphabet.work ++ tail))) := by
  have h₀ := reaches_sourceReadValid_actionWrite slot
    (target + extra) read write target m hread base movePath runtime
    (ulogCore stateSep :: tail) hreadPath
  have hhead : choiceHead (readHeadNat read) = true := by
    interval_cases read <;> native_decide
  have h₁ := reaches_matchedActionAtMostState write target extra hwrite
    htarget m
    movePath runtime (readHeadNat read) hhead hwritePath htargetPath
    (matchedReadLeft slot (target + extra) read base) tail
  exact reaches_trans h₀ h₁

theorem reaches_matchedRuleAtLeastState
    (slot : Bool) (current read write growth : ℕ)
    (m : OneTapeTableau.Move) (hread : read < 3) (hwrite : write < 3)
    (htargetLower : 2 ≤ current + growth)
    (movePath runtime : List Tape)
    (hreadPath : ReadCorridorSafe
      (codeTape slot :: encodedActionPath write (current + growth) m movePath))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate (current + growth) (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits m ++ movePath))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits m ++ movePath ++ writeHeadNat write :: runtime))
    (base tail : List Tape) :
    Reaches
      (sourceReadStarted slot current (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape slot ::
            encodedActionPath write (current + growth) m movePath ++
              readHeadNat read :: runtime)
        (ulogCore stateSep ::
          List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (.running (.moveSimHead m)
        (beforeRightPath movePath
          (matchedMoveLeft write (current + growth) m
            (matchedReadLeft slot current read base))
          (writeHeadNat write)
          (runtime ++
            List.replicate (current + growth) (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail))) := by
  have h₀ := reaches_sourceReadValid_actionWrite slot current read write
    (current + growth) m hread base movePath runtime
    (ulogCore stateSep ::
      List.replicate growth MStarConcreteAlphabet.work ++ tail) hreadPath
  have hhead : choiceHead (readHeadNat read) = true := by
    interval_cases read <;> native_decide
  have h₁ := reaches_matchedActionAtLeastState write current growth hwrite
    htargetLower m
    movePath runtime (readHeadNat read) hhead hwritePath htargetPath
    (matchedReadLeft slot current read base) tail
  have h₀' : Reaches
      (sourceReadStarted slot current (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape slot ::
            encodedActionPath write (current + growth) m movePath ++
              readHeadNat read :: runtime)
        (ulogCore stateSep ::
          List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (actionWriteStart write (matchedReadLeft slot current read base)
        (List.replicate (current + growth) (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        (readHeadNat read)
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ tail)) := by
    simpa [List.append_assoc] using h₀
  exact reaches_trans h₀' h₁

def matchedRuleMovePath (rs : List ULogBytecode.RuleCode)
    (input : List Bool) : List Tape :=
  (ULogBytecode.encodeRules rs).map codeTape ++
    (payloadProgramPrefix input).reverse

theorem reaches_matchedRuleCodeAtMostState
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (extra : ℕ)
    (hsource : r.source = r.action.target + extra)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (runtime : List Tape)
    (hsourcePath : SourceCompareCorridorSafe
      (readHeadNat r.read :: runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (matchedRuleMovePath rs input)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          matchedRuleMovePath rs input))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ matchedRuleMovePath rs input ++
        writeHeadNat r.action.write :: runtime))
    (left tail : List Tape) :
    Reaches
      (ruleSourceStarted r.slot (r :: rs) input left
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (matchedRuleMovePath rs input)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeft r.slot r.source r.read
              (List.replicate (r :: rs).length (ulogCore pcDone) ++
                ulogCore pcMark :: left)))
          (writeHeadNat r.action.write)
          (runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep ::
                List.replicate extra MStarConcreteAlphabet.work ++ tail))) := by
  rcases r with ⟨source, read, ruleSlot, ⟨write, target, move⟩⟩
  change source = target + extra at hsource
  subst source
  let rule : ULogBytecode.RuleCode :=
    { source := target + extra, read := read, slot := ruleSlot,
      action := { write := write, target := target, move := move } }
  have hcorridor := firstRuleCorridor_safe
    rule
    rs input (readHeadNat read) runtime hsourcePath
  have h₀ := reaches_ruleSourceMatch_read ruleSlot
    rule
    rs input left (readHeadNat read) runtime
    (ulogCore stateSep :: tail) hcorridor
  have h₁ := reaches_matchedRuleAtMostState ruleSlot read write target
    extra move hread hwrite htargetLower (matchedRuleMovePath rs input) runtime
    hreadPath hwritePath htargetPath
    (List.replicate (rs.length + 1) (ulogCore pcDone) ++
      ulogCore pcMark :: left)
    tail
  have h₀' : Reaches
      (ruleSourceStarted ruleSlot
        (rule :: rs)
        input left (readHeadNat read)
        (runtime ++ List.replicate (target + extra) (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (sourceReadStarted ruleSlot (target + extra) (unaryFieldFirst read)
        (List.replicate (rs.length + 1) (ulogCore pcDone) ++
          ulogCore pcMark :: left)
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape ruleSlot ::
            encodedActionPath write target move
              (matchedRuleMovePath rs input) ++
              readHeadNat read :: runtime)
        (ulogCore stateSep :: tail)) := by
    simpa [ULogBytecode.encodeAction, ULogBytecode.encodeRule,
      rule, matchedRuleMovePath, encodedActionPath, encodeMove_eq, moveBits,
      List.map_append, List.append_assoc] using h₀
  simpa [rule] using reaches_trans h₀' h₁

theorem reaches_matchedRuleCodeAtLeastState
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (growth : ℕ)
    (htarget : r.action.target = r.source + growth)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (htargetLower : 2 ≤ r.action.target)
    (runtime : List Tape)
    (hsourcePath : SourceCompareCorridorSafe
      (readHeadNat r.read :: runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (matchedRuleMovePath rs input)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          matchedRuleMovePath rs input))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ matchedRuleMovePath rs input ++
        writeHeadNat r.action.write :: runtime))
    (left tail : List Tape) :
    Reaches
      (ruleSourceStarted r.slot (r :: rs) input left
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (.running (.moveSimHead r.action.move)
        (beforeRightPath (matchedRuleMovePath rs input)
          (matchedMoveLeft r.action.write r.action.target r.action.move
            (matchedReadLeft r.slot r.source r.read
              (List.replicate (r :: rs).length (ulogCore pcDone) ++
                ulogCore pcMark :: left)))
          (writeHeadNat r.action.write)
          (runtime ++
            List.replicate r.action.target (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail))) := by
  rcases r with ⟨source, read, ruleSlot, ⟨write, target, move⟩⟩
  change target = source + growth at htarget
  subst target
  let rule : ULogBytecode.RuleCode :=
    { source := source, read := read, slot := ruleSlot,
      action := { write := write, target := source + growth, move := move } }
  have hcorridor := firstRuleCorridor_safe rule rs input
    (readHeadNat read) runtime hsourcePath
  have h₀ := reaches_ruleSourceMatch_read ruleSlot rule rs input left
    (readHeadNat read) runtime
    (ulogCore stateSep ::
      List.replicate growth MStarConcreteAlphabet.work ++ tail) hcorridor
  have h₁ := reaches_matchedRuleAtLeastState ruleSlot source read write
    growth move hread hwrite htargetLower
    (matchedRuleMovePath rs input) runtime
    hreadPath hwritePath htargetPath
    (List.replicate (rs.length + 1) (ulogCore pcDone) ++
      ulogCore pcMark :: left)
    tail
  have h₀' : Reaches
      (ruleSourceStarted ruleSlot (rule :: rs) input left
        (readHeadNat read)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate growth MStarConcreteAlphabet.work ++ tail))
      (sourceReadStarted ruleSlot source (unaryFieldFirst read)
        (List.replicate (rs.length + 1) (ulogCore pcDone) ++
          ulogCore pcMark :: left)
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape ruleSlot ::
            encodedActionPath write (source + growth) move
              (matchedRuleMovePath rs input) ++
              readHeadNat read :: runtime)
        (ulogCore stateSep ::
          List.replicate growth MStarConcreteAlphabet.work ++ tail)) := by
    simpa [ULogBytecode.encodeAction, ULogBytecode.encodeRule,
      rule, matchedRuleMovePath, encodedActionPath, encodeMove_eq, moveBits,
      List.map_append, List.append_assoc] using h₀
  simpa [rule] using reaches_trans h₀' h₁

theorem reaches_matchedRuleCodeTargetZero
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (htarget : r.action.target = 0)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (runtime : List Tape)
    (hsourcePath : SourceCompareCorridorSafe
      (readHeadNat r.read :: runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (matchedRuleMovePath rs input)))
    (hwritePath : ActionWriteCorridorSafe
      (ulogCore codeOne :: moveBits r.action.move ++
        matchedRuleMovePath rs input))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ matchedRuleMovePath rs input ++
        writeHeadNat r.action.write :: runtime))
    (left tail : List Tape) :
    ∃ z, Reaches
      (ruleSourceStarted r.slot (r :: rs) input left
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (.accepted z) := by
  rcases r with ⟨source, read, ruleSlot, ⟨write, target, move⟩⟩
  change target = 0 at htarget
  subst target
  let rule : ULogBytecode.RuleCode :=
    { source := source, read := read, slot := ruleSlot,
      action := { write := write, target := 0, move := move } }
  have hcorridor := firstRuleCorridor_safe rule rs input
    (readHeadNat read) runtime hsourcePath
  have h₀ := reaches_ruleSourceMatch_read ruleSlot rule rs input left
    (readHeadNat read) runtime (ulogCore stateSep :: tail) hcorridor
  obtain ⟨z, h₁⟩ := reaches_matchedRuleTargetZero ruleSlot source read write
    move hread hwrite (matchedRuleMovePath rs input) runtime hreadPath
    hwritePath htargetPath
    (List.replicate (rs.length + 1) (ulogCore pcDone) ++
      ulogCore pcMark :: left) tail
  have h₀' : Reaches
      (ruleSourceStarted ruleSlot (rule :: rs) input left
        (readHeadNat read)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (sourceReadStarted ruleSlot source (unaryFieldFirst read)
        (List.replicate (rs.length + 1) (ulogCore pcDone) ++
          ulogCore pcMark :: left)
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape ruleSlot :: encodedActionPath write 0 move
            (matchedRuleMovePath rs input) ++ readHeadNat read :: runtime)
        (ulogCore stateSep :: tail)) := by
    simpa [ULogBytecode.encodeAction, ULogBytecode.encodeRule,
      rule, matchedRuleMovePath, encodedActionPath, encodeMove_eq, moveBits,
      List.map_append, List.append_assoc] using h₀
  exact ⟨z, by simpa [rule] using reaches_trans h₀' h₁⟩

theorem reaches_matchedRuleCodeTargetOneZero
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (hsource : r.source = 0)
    (htarget : r.action.target = 1)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (runtime : List Tape)
    (hsourcePath : SourceCompareCorridorSafe
      (readHeadNat r.read :: runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (matchedRuleMovePath rs input)))
    (hwritePath : ActionWriteCorridorSafe
      (ulogCore codeZero :: ulogCore codeOne :: moveBits r.action.move ++
        matchedRuleMovePath rs input))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ matchedRuleMovePath rs input ++
        writeHeadNat r.action.write :: runtime))
    (left tail : List Tape) :
    Reaches
      (ruleSourceStarted r.slot (r :: rs) input left
        (readHeadNat r.read)
        (runtime ++ ulogCore stateOne :: ulogCore stateSep ::
          MStarConcreteAlphabet.work :: tail))
      .rejected := by
  rcases r with ⟨source, read, ruleSlot, ⟨write, target, move⟩⟩
  change source = 0 at hsource
  change target = 1 at htarget
  subst source
  subst target
  let rule : ULogBytecode.RuleCode :=
    { source := 0, read := read, slot := ruleSlot,
      action := { write := write, target := 1, move := move } }
  have hcorridor := firstRuleCorridor_safe rule rs input
    (readHeadNat read) runtime hsourcePath
  have h₀ := reaches_ruleSourceMatch_read ruleSlot rule rs input left
    (readHeadNat read) runtime
    (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail) hcorridor
  have h₁ := reaches_matchedRuleTargetOneZero ruleSlot read write move hread
    hwrite (matchedRuleMovePath rs input) runtime hreadPath hwritePath
    htargetPath
    (List.replicate (rs.length + 1) (ulogCore pcDone) ++
      ulogCore pcMark :: left) tail
  have h₀' : Reaches
      (ruleSourceStarted ruleSlot (rule :: rs) input left
        (readHeadNat read)
        (runtime ++ ulogCore stateOne :: ulogCore stateSep ::
          MStarConcreteAlphabet.work :: tail))
      (sourceReadStarted ruleSlot 0 (unaryFieldFirst read)
        (List.replicate (rs.length + 1) (ulogCore pcDone) ++
          ulogCore pcMark :: left)
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape ruleSlot :: encodedActionPath write 1 move
            (matchedRuleMovePath rs input) ++ readHeadNat read :: runtime)
        (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail)) := by
    simpa [ULogBytecode.encodeAction, ULogBytecode.encodeRule,
      rule, matchedRuleMovePath, encodedActionPath, encodeMove_eq, moveBits,
      List.map_append, List.append_assoc] using h₀
  simpa [rule] using reaches_trans h₀' h₁

theorem reaches_matchedRuleCodeTargetOnePositive
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (extra : ℕ)
    (hsource : r.source = extra + 1)
    (htarget : r.action.target = 1)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (runtime : List Tape)
    (hsourcePath : SourceCompareCorridorSafe
      (readHeadNat r.read :: runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (matchedRuleMovePath rs input)))
    (hwritePath : ActionWriteCorridorSafe
      (ulogCore codeZero :: ulogCore codeOne :: moveBits r.action.move ++
        matchedRuleMovePath rs input))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ matchedRuleMovePath rs input ++
        writeHeadNat r.action.write :: runtime))
    (left tail : List Tape) :
    Reaches
      (ruleSourceStarted r.slot (r :: rs) input left
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      .rejected := by
  rcases r with ⟨source, read, ruleSlot, ⟨write, target, move⟩⟩
  change source = extra + 1 at hsource
  change target = 1 at htarget
  subst source
  subst target
  let rule : ULogBytecode.RuleCode :=
    { source := extra + 1, read := read, slot := ruleSlot,
      action := { write := write, target := 1, move := move } }
  have hcorridor := firstRuleCorridor_safe rule rs input
    (readHeadNat read) runtime hsourcePath
  have h₀ := reaches_ruleSourceMatch_read ruleSlot rule rs input left
    (readHeadNat read) runtime (ulogCore stateSep :: tail) hcorridor
  have h₁ := reaches_matchedRuleTargetOnePositive ruleSlot extra read write
    move hread hwrite (matchedRuleMovePath rs input) runtime hreadPath
    hwritePath htargetPath
    (List.replicate (rs.length + 1) (ulogCore pcDone) ++
      ulogCore pcMark :: left) tail
  have h₀' : Reaches
      (ruleSourceStarted ruleSlot (rule :: rs) input left
        (readHeadNat read)
        (runtime ++ List.replicate (extra + 1) (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail))
      (sourceReadStarted ruleSlot (extra + 1) (unaryFieldFirst read)
        (List.replicate (rs.length + 1) (ulogCore pcDone) ++
          ulogCore pcMark :: left)
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape ruleSlot :: encodedActionPath write 1 move
            (matchedRuleMovePath rs input) ++ readHeadNat read :: runtime)
        (ulogCore stateSep :: tail)) := by
    simpa [ULogBytecode.encodeAction, ULogBytecode.encodeRule,
      rule, matchedRuleMovePath, encodedActionPath, encodeMove_eq, moveBits,
      List.map_append, List.append_assoc] using h₀
  simpa [rule] using reaches_trans h₀' h₁

end PakFixedPolyomino.ULogBootstrapExecution
