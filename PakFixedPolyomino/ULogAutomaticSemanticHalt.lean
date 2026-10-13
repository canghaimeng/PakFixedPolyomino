import PakFixedPolyomino.ULogAutomaticSemanticCycle

/-! Automatic concrete halt dispatch for semantic target states `0` and `1`. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem reaches_ruleCursorMatchedTargetZero
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead base runtime : List Tape)
    (htarget : r.action.target = 0)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
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
    ∃ z, Reaches
      (atBitsTail (.fieldCompare .source r.slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary :: base)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep :: tail))
      (.accepted z) := by
  have h₀ := reaches_ruleCursorSourceMatch_read r.slot boundary hboundary r rs
    programToHead base (readHeadNat r.read) runtime
    (ulogCore stateSep :: tail) hcorridor
  have h₁ := reaches_sourceReadAtValid_actionWrite r.slot r.source r.read
    r.action.write r.action.target boundary r.action.move hread base
    (cursorMatchedMovePath rs programToHead) runtime
    (ulogCore stateSep :: tail) hreadPath
  have hhead : choiceHead (readHeadNat r.read) = true := by
    interval_cases r.read <;> native_decide
  obtain ⟨z, h₂⟩ := reaches_matchedActionTargetZero r.action.write
    r.source hwrite r.action.move (cursorMatchedMovePath rs programToHead)
    runtime (readHeadNat r.read) hhead
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
        (ulogCore stateSep :: tail))
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read boundary base)
        (ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail)) := by
    simpa [htarget] using h₁
  exact ⟨z, reaches_trans h₀ (reaches_trans h₁' h₂)⟩

theorem reaches_ruleCursorMatchedTargetOneZero
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead base runtime : List Tape)
    (hsource : r.source = 0) (htarget : r.action.target = 1)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
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
          ulogCore stateOne :: ulogCore stateSep ::
            MStarConcreteAlphabet.work :: tail))
      .rejected := by
  have h₀ := reaches_ruleCursorSourceMatch_read r.slot boundary hboundary r rs
    programToHead base (readHeadNat r.read) runtime
    (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail) hcorridor
  have h₁ := reaches_sourceReadAtValid_actionWrite r.slot r.source r.read
    r.action.write r.action.target boundary r.action.move hread base
    (cursorMatchedMovePath rs programToHead) runtime
    (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail) hreadPath
  have hhead : choiceHead (readHeadNat r.read) = true := by
    interval_cases r.read <;> native_decide
  have h₂ := reaches_matchedActionTargetOneZero r.action.write hwrite
    r.action.move (cursorMatchedMovePath rs programToHead) runtime
    (readHeadNat r.read) hhead (by simpa [htarget] using hwritePath)
    htargetPath (matchedReadLeftAt r.slot 0 r.read boundary base) tail
  have h₁' : Reaches
      (sourceReadStartedAt r.slot r.source boundary
        (unaryFieldFirst r.read) base
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          codeTape r.slot :: encodedActionPath r.action.write
            r.action.target r.action.move
              (cursorMatchedMovePath rs programToHead) ++
            readHeadNat r.read :: runtime)
        (ulogCore stateSep :: MStarConcreteAlphabet.work :: tail))
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot 0 r.read boundary base)
        (ulogCore codeZero :: ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ ulogCore stateOne :: ulogCore stateSep ::
          MStarConcreteAlphabet.work :: tail)) := by
    simpa [hsource, htarget] using h₁
  exact reaches_trans (by simpa [hsource] using h₀)
    (reaches_trans h₁' h₂)

theorem reaches_ruleCursorMatchedTargetOnePositive
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead base runtime : List Tape) (extra : ℕ)
    (hsource : r.source = extra + 1) (htarget : r.action.target = 1)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
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
      .rejected := by
  have h₀ := reaches_ruleCursorSourceMatch_read r.slot boundary hboundary r rs
    programToHead base (readHeadNat r.read) runtime
    (ulogCore stateSep :: tail) hcorridor
  have h₁ := reaches_sourceReadAtValid_actionWrite r.slot r.source r.read
    r.action.write r.action.target boundary r.action.move hread base
    (cursorMatchedMovePath rs programToHead) runtime
    (ulogCore stateSep :: tail) hreadPath
  have hhead : choiceHead (readHeadNat r.read) = true := by
    interval_cases r.read <;> native_decide
  have h₂ := reaches_matchedActionTargetOnePositive r.action.write extra
    hwrite r.action.move (cursorMatchedMovePath rs programToHead) runtime
    (readHeadNat r.read) hhead (by simpa [htarget] using hwritePath)
    htargetPath
    (matchedReadLeftAt r.slot (extra + 1) r.read boundary base) tail
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
        (matchedReadLeftAt r.slot (extra + 1) r.read boundary base)
        (ulogCore codeZero :: ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ List.replicate (extra + 1) (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail)) := by
    simpa [hsource, htarget] using h₁
  exact reaches_trans h₀ (reaches_trans h₁' h₂)

theorem reaches_mismatchPrefix_matchedTargetZero
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (htarget : r.action.target = 0)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
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
    ∃ z, Reaches
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        programToHead runtime outer (ulogCore stateSep :: suffix))
      (.accepted z) := by
  have hprefix := reaches_mismatchPrefix slot current actual programToHead
    runtime outer (ulogCore stateSep :: suffix) trace
  obtain ⟨z, hmatched⟩ := reaches_ruleCursorMatchedTargetZero final.boundary
    hboundary r rs programToHead
    ((List.replicate final.done (ulogCore codeZero) ++
      ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: outer)
    runtime htarget hread hwrite hcorridor hreadPath hwritePath htargetPath
    suffix
  rcases hmatch with ⟨hsource, hreadEq, hslot⟩
  have hmatched' : Reaches
      (ruleCursorResult slot current actual final (r :: rs)
        programToHead runtime outer (ulogCore stateSep :: suffix))
      (.accepted z) := by
    simpa [ruleCursorResult, ruleCursorBase, hsource, hreadEq, hslot,
      List.append_assoc] using hmatched
  exact ⟨z, reaches_trans hprefix hmatched'⟩

theorem reaches_mismatchPrefix_matchedTargetOneZero
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (hcurrent : current = 0) (htarget : r.action.target = 1)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
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
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        programToHead runtime outer
        (ulogCore stateSep :: MStarConcreteAlphabet.work :: suffix))
      .rejected := by
  have hprefix := reaches_mismatchPrefix slot current actual programToHead
    runtime outer (ulogCore stateSep :: MStarConcreteAlphabet.work :: suffix)
    trace
  have hsource : r.source = 0 := hmatch.1.trans hcurrent
  have hmatched := reaches_ruleCursorMatchedTargetOneZero final.boundary
    hboundary r rs programToHead
    ((List.replicate final.done (ulogCore codeZero) ++
      ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: outer)
    runtime hsource htarget hread hwrite hcorridor hreadPath hwritePath
    htargetPath suffix
  rcases hmatch with ⟨hsourceEq, hreadEq, hslot⟩
  have hmatched' : Reaches
      (ruleCursorResult slot current actual final (r :: rs)
        programToHead runtime outer
        (ulogCore stateSep :: MStarConcreteAlphabet.work :: suffix))
      .rejected := by
    simpa [ruleCursorResult, ruleCursorBase, hcurrent, hsourceEq, hreadEq, hslot,
      List.append_assoc] using hmatched
  exact reaches_trans hprefix hmatched'

theorem reaches_mismatchPrefix_matchedTargetOnePositive
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (extra : ℕ) (hcurrent : current = extra + 1)
    (htarget : r.action.target = 1)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
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
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        programToHead runtime outer (ulogCore stateSep :: suffix))
      .rejected := by
  have hprefix := reaches_mismatchPrefix slot current actual programToHead
    runtime outer (ulogCore stateSep :: suffix) trace
  have hsource : r.source = extra + 1 := hmatch.1.trans hcurrent
  have hmatched := reaches_ruleCursorMatchedTargetOnePositive final.boundary
    hboundary r rs programToHead
    ((List.replicate final.done (ulogCore codeZero) ++
      ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: outer)
    runtime extra hsource htarget hread hwrite hcorridor hreadPath hwritePath
    htargetPath suffix
  rcases hmatch with ⟨hsourceEq, hreadEq, hslot⟩
  have hmatched' : Reaches
      (ruleCursorResult slot current actual final (r :: rs)
        programToHead runtime outer (ulogCore stateSep :: suffix))
      .rejected := by
    simpa [ruleCursorResult, ruleCursorBase, hcurrent, hsourceEq, hreadEq, hslot,
      List.append_assoc] using hmatched
  exact reaches_trans hprefix hmatched'

theorem branchedCycle_semanticTargetZero
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (htarget : action.target = 0)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (hstateCapacity : c.state ≤ capacity) :
    ∃ z, BranchedReaches slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      (.accepted z) := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hclock := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
      hp hclock c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have trace := mismatchCertificateList_initial_trace slot c.state c.focus
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
    certs (by simp)
  have hboundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  have hhead : choiceHead (readHeadNat c.focus) = true := by
    interval_cases c.focus <;> native_decide
  have hdec := reaches_clockDecrementCells (readHeadNat c.focus) hhead
    clockZeros (c.right.map payloadNat) (payloadNatList_safe c.right)
    (dynamicRuleReturnPath (c.leftRev.map payloadNat) (skip ++ r :: rs)
      input ++ ulogCore pcMark :: outer)
    (runtime ++ List.replicate c.state (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
          suffix)
  obtain ⟨branchStart, hbranch, hlookupRun⟩ :=
    chooseSlot_reaches_dynamicRuleSource slot (c.leftRev.map payloadNat)
      (payloadNatList_safe c.leftRev) (skip ++ r :: rs) (by simp) input
      outer (readHeadNat c.focus) hhead
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
        List.replicate c.state (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate (capacity - c.state)
              MStarConcreteAlphabet.work ++ suffix)
  obtain ⟨z, hterm⟩ := reaches_mismatchPrefix_matchedTargetZero
    slot c.state c.focus
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) outer
    (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++ suffix)
    skip r rs (canonicalRuleCursor skip (r :: rs)) trace hmatch htarget
    rscan.read_valid hwrite hboundary
    (by simpa [hmatch.2.1] using rscan.source_corridor)
    (matchedReadPath_safe r.slot r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (matchedWritePath_safe r rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
    (matchedTargetPath_safe r hwrite rs
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) hp hclock)
  have hterm' : Reaches
      (dynamicRuleSourceStarted slot (c.leftRev.map payloadNat)
        (skip ++ r :: rs) input outer (readHeadNat c.focus)
        (clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
          List.replicate c.state (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate (capacity - c.state)
                MStarConcreteAlphabet.work ++ suffix))
      (.accepted z) := by
    have htermDyn := hterm
    rw [← dynamicRuleSourceStarted_eq_cursorResult slot c.state c.focus
      (c.leftRev.map payloadNat) input skip r rs
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) outer
      (ulogCore stateSep ::
        (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
          suffix))] at htermDyn
    simpa [List.append_assoc] using htermDyn
  refine ⟨z, .running .chooseSlot
      ⟨dynamicRuleReturnPath (c.leftRev.map payloadNat) (skip ++ r :: rs)
          input ++ ulogCore pcMark :: outer,
        readHeadNat c.focus,
        clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
          List.replicate c.state (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate (capacity - c.state)
                MStarConcreteAlphabet.work ++ suffix⟩,
    branchStart, ?_, hbranch, reaches_trans hlookupRun hterm'⟩
  simpa [semanticCycleEncoding, stateWorkspace, clockCellsBefore,
    clockCellsAfter, heq,
    List.append_assoc] using hdec

theorem branchedCycle_semanticTargetOne
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (htarget : action.target = 1)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (hstateCapacity : c.state ≤ capacity) (honeCapacity : 1 ≤ capacity) :
    BranchedReaches slot
      (semanticCycleEncoding input
        (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
        capacity outer suffix c)
      .rejected := by
  have hp := cursorDynamicProgramToHead_passive input c.leftRev
  have hclock := clockCellsAfter_passive c.right clockZeros runtime hruntime
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, haction⟩ :=
    automatic_lookup_some slot c.state c.focus hfocus
      (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
      hp hclock c.program hreads action hlookup
  subst action
  have hwrite : r.action.write < 3 := hwrites r (by simp [heq])
  have trace := mismatchCertificateList_initial_trace slot c.state c.focus
    (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
    (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
    certs (by simp)
  have hboundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  have hhead : choiceHead (readHeadNat c.focus) = true := by
    interval_cases c.focus <;> native_decide
  have hdec := reaches_clockDecrementCells (readHeadNat c.focus) hhead
    clockZeros (c.right.map payloadNat) (payloadNatList_safe c.right)
    (dynamicRuleReturnPath (c.leftRev.map payloadNat) (skip ++ r :: rs)
      input ++ ulogCore pcMark :: outer)
    (runtime ++ List.replicate c.state (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep ::
        List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
          suffix)
  obtain ⟨branchStart, hbranch, hlookupRun⟩ :=
    chooseSlot_reaches_dynamicRuleSource slot (c.leftRev.map payloadNat)
      (payloadNatList_safe c.leftRev) (skip ++ r :: rs) (by simp) input
      outer (readHeadNat c.focus) hhead
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
        List.replicate c.state (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep ::
            List.replicate (capacity - c.state)
              MStarConcreteAlphabet.work ++ suffix)
  have hterm : Reaches
      (ruleCursorResult slot c.state c.focus
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
        (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
        outer
        (ulogCore stateSep ::
          (List.replicate (capacity - c.state)
            MStarConcreteAlphabet.work ++ suffix)))
      .rejected := by
    cases hstate : c.state with
    | zero =>
        obtain ⟨remaining, hcapacityEq⟩ : ∃ remaining, capacity = remaining + 1 :=
          ⟨capacity - 1, by omega⟩
        have h := reaches_mismatchPrefix_matchedTargetOneZero
          slot c.state c.focus
          (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
          (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
          outer
          (List.replicate remaining MStarConcreteAlphabet.work ++ suffix)
          skip r rs (canonicalRuleCursor skip (r :: rs)) trace hmatch
          hstate htarget rscan.read_valid hwrite hboundary
          (by simpa [hmatch.2.1] using rscan.source_corridor)
          (matchedReadPath_safe r.slot r rs
            (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
          (matchedWritePath_safe r rs
            (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
          (matchedTargetPath_safe r hwrite rs
            (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
            (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
            hp hclock)
        simpa [hstate, hcapacityEq, List.replicate_succ,
          List.append_assoc] using h
    | succ extra =>
        simpa [hstate] using
          (reaches_mismatchPrefix_matchedTargetOnePositive
          slot c.state c.focus
          (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
          (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
          outer
          (List.replicate (capacity - c.state)
            MStarConcreteAlphabet.work ++ suffix)
          skip r rs (canonicalRuleCursor skip (r :: rs)) trace hmatch extra
          hstate htarget rscan.read_valid hwrite hboundary
          (by simpa [hmatch.2.1] using rscan.source_corridor)
          (matchedReadPath_safe r.slot r rs
            (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
          (matchedWritePath_safe r rs
            (cursorDynamicProgramToHead input (c.leftRev.map payloadNat)) hp)
          (matchedTargetPath_safe r hwrite rs
            (cursorDynamicProgramToHead input (c.leftRev.map payloadNat))
            (clockCellsAfter (c.right.map payloadNat) clockZeros runtime)
            hp hclock))
  have hterm' : Reaches
      (dynamicRuleSourceStarted slot (c.leftRev.map payloadNat)
        (skip ++ r :: rs) input outer (readHeadNat c.focus)
        (clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
          List.replicate c.state (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate (capacity - c.state)
                MStarConcreteAlphabet.work ++ suffix))
      .rejected := by
    have htermDyn := hterm
    rw [← dynamicRuleSourceStarted_eq_cursorResult slot c.state c.focus
      (c.leftRev.map payloadNat) input skip r rs
      (clockCellsAfter (c.right.map payloadNat) clockZeros runtime) outer
      (ulogCore stateSep ::
        (List.replicate (capacity - c.state) MStarConcreteAlphabet.work ++
          suffix))] at htermDyn
    simpa [List.append_assoc] using htermDyn
  refine ⟨.running .chooseSlot
      ⟨dynamicRuleReturnPath (c.leftRev.map payloadNat) (skip ++ r :: rs)
          input ++ ulogCore pcMark :: outer,
        readHeadNat c.focus,
        clockCellsAfter (c.right.map payloadNat) clockZeros runtime ++
          List.replicate c.state (ulogCore stateZero) ++
            ulogCore stateOne :: ulogCore stateSep ::
              List.replicate (capacity - c.state)
                MStarConcreteAlphabet.work ++ suffix⟩,
    branchStart, ?_, hbranch, reaches_trans hlookupRun hterm'⟩
  simpa [semanticCycleEncoding, stateWorkspace, clockCellsBefore,
    clockCellsAfter, heq, List.append_assoc] using hdec

theorem semanticCapacityReady_target_le
    (c : ULogSemantics.Config) (action : ULogBytecode.ActionCode)
    (capacity : ℕ) (h : SemanticCapacityReady c action capacity) :
    action.target ≤ capacity := by
  cases hm : action.move with
  | stay => simpa [SemanticCapacityReady, hm] using h
  | left => simpa [SemanticCapacityReady, hm] using h
  | right =>
      cases hr : c.right with
      | nil =>
          have ht : action.target < capacity := by
            simpa [SemanticCapacityReady, hm, hr] using h
          omega
      | cons x xs => simpa [SemanticCapacityReady, hm, hr] using h

def SemanticConcreteCycleSpec
    (c : ULogSemantics.Config) (slot : Bool)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) : Prop :=
  let start := semanticCycleEncoding input
    (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
    capacity outer suffix c
  match ULogBytecode.lookupRule c.program c.state c.focus slot with
  | none => BranchedReaches slot start .rejected
  | some action =>
      match action.target with
      | 0 => ∃ z, BranchedReaches slot start (.accepted z)
      | 1 => BranchedReaches slot start .rejected
      | _ + 2 =>
          BranchedReaches slot start
            (semanticCycleEncoding input
              (clockCellsAfter
                ((ULogSemantics.applyAction c action).right.map payloadNat)
                clockZeros runtime)
              (semanticCapacityAfter c action capacity)
              (semanticOuterAfter c action outer) suffix
              (ULogSemantics.applyAction c action))

theorem branchedCycle_semanticComplete
    (c : ULogSemantics.Config) (slot : Bool)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3) (hrules : c.program ≠ [])
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (hstateCapacity : c.state ≤ capacity)
    (hcapacity : ∀ action,
      ULogBytecode.lookupRule c.program c.state c.focus slot = some action →
        SemanticCapacityReady c action capacity)
    (houter : ∀ action,
      ULogBytecode.lookupRule c.program c.state c.focus slot = some action →
        SemanticOuterReady c action outer) :
    SemanticConcreteCycleSpec c slot input clockZeros capacity runtime outer
      suffix := by
  cases hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot with
  | none =>
      have h := branchedCycle_semanticNoRule c slot input clockZeros capacity
        runtime outer suffix hruntime hfocus hrules hreads hlookup
      simpa [SemanticConcreteCycleSpec, hlookup] using h
  | some action =>
      cases htarget : action.target with
      | zero =>
          have h := branchedCycle_semanticTargetZero c slot action hlookup
            htarget input clockZeros capacity runtime outer suffix hruntime
            hfocus hreads hwrites hstateCapacity
          simpa [SemanticConcreteCycleSpec, hlookup, htarget] using h
      | succ target =>
          cases target with
          | zero =>
              have honeCapacity : 1 ≤ capacity := by
                have ht := semanticCapacityReady_target_le c action capacity
                  (hcapacity action hlookup)
                omega
              have h := branchedCycle_semanticTargetOne c slot action hlookup
                htarget input clockZeros capacity runtime outer suffix hruntime
                hfocus hreads hwrites hstateCapacity honeCapacity
              simpa [SemanticConcreteCycleSpec, hlookup, htarget] using h
          | succ target =>
              have htargetLower : 2 ≤ action.target := by omega
              have h := branchedCycle_semanticLookupSome c slot action hlookup
                input clockZeros capacity runtime outer suffix hruntime hfocus
                hreads hwrites hstateCapacity (hcapacity action hlookup)
                htargetLower (houter action hlookup)
              simpa [SemanticConcreteCycleSpec, hlookup, htarget,
                Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

@[simp] theorem applyAction_state (c : ULogSemantics.Config)
    (action : ULogBytecode.ActionCode) :
    (ULogSemantics.applyAction c action).state = action.target := by
  cases hm : action.move with
  | stay => simp [ULogSemantics.applyAction, hm]
  | right =>
      cases hr : c.right <;> simp [ULogSemantics.applyAction, hm, hr]
  | left =>
      cases hl : c.leftRev <;> simp [ULogSemantics.applyAction, hm, hl]

theorem halted_applyAction_iff_target_lt_two
    (c : ULogSemantics.Config) (action : ULogBytecode.ActionCode) :
    ULogSemantics.halted (ULogSemantics.applyAction c action) = true ↔
      action.target < 2 := by
  simp [ULogSemantics.halted]

theorem accepting_applyAction_iff_target_zero
    (c : ULogSemantics.Config) (action : ULogBytecode.ActionCode) :
    ULogSemantics.accepting (ULogSemantics.applyAction c action) = true ↔
      action.target = 0 := by
  simp [ULogSemantics.accepting, ULogSemantics.acceptCode]

theorem semanticHalted_iff_concreteTerminalDispatch
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (hstateCapacity : c.state ≤ capacity)
    (hcapacity : SemanticCapacityReady c action capacity) :
    ULogSemantics.halted (ULogSemantics.applyAction c action) = true ↔
      (action.target = 0 ∧ ∃ z, BranchedReaches slot
        (semanticCycleEncoding input
          (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
          capacity outer suffix c)
        (.accepted z)) ∨
      (action.target = 1 ∧ BranchedReaches slot
        (semanticCycleEncoding input
          (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
          capacity outer suffix c)
        .rejected) := by
  constructor
  · intro hhalt
    have ht : action.target < 2 :=
      (halted_applyAction_iff_target_lt_two c action).mp hhalt
    have hcases : action.target = 0 ∨ action.target = 1 := by omega
    rcases hcases with hzero | hone
    · left
      refine ⟨hzero, ?_⟩
      exact branchedCycle_semanticTargetZero c slot action hlookup hzero input
        clockZeros capacity runtime outer suffix hruntime hfocus hreads
        hwrites hstateCapacity
    · right
      refine ⟨hone, ?_⟩
      have honeCapacity : 1 ≤ capacity := by
        have hle := semanticCapacityReady_target_le c action capacity
          hcapacity
        omega
      exact branchedCycle_semanticTargetOne c slot action hlookup hone input
        clockZeros capacity runtime outer suffix hruntime hfocus hreads
        hwrites hstateCapacity honeCapacity
  · rintro (⟨htarget, _⟩ | ⟨htarget, _⟩)
    · apply (halted_applyAction_iff_target_lt_two c action).mpr
      omega
    · apply (halted_applyAction_iff_target_lt_two c action).mpr
      omega

theorem semanticAccepting_iff_concreteAcceptDispatch
    (c : ULogSemantics.Config) (slot : Bool)
    (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule c.program c.state c.focus slot =
      some action)
    (input : List Bool) (clockZeros capacity : ℕ)
    (runtime outer suffix : List Tape) (hruntime : PassivePath runtime)
    (hfocus : c.focus < 3)
    (hreads : ∀ r ∈ c.program, r.read < 3)
    (hwrites : ∀ r ∈ c.program, r.action.write < 3)
    (hstateCapacity : c.state ≤ capacity) :
    ULogSemantics.accepting (ULogSemantics.applyAction c action) = true ↔
      action.target = 0 ∧ ∃ z, BranchedReaches slot
        (semanticCycleEncoding input
          (clockCellsBefore (c.right.map payloadNat) clockZeros runtime)
          capacity outer suffix c)
        (.accepted z) := by
  constructor
  · intro haccept
    have htarget :=
      (accepting_applyAction_iff_target_zero c action).mp haccept
    exact ⟨htarget, branchedCycle_semanticTargetZero c slot action hlookup
      htarget input clockZeros capacity runtime outer suffix hruntime hfocus
      hreads hwrites hstateCapacity⟩
  · rintro ⟨htarget, _⟩
    exact (accepting_applyAction_iff_target_zero c action).mpr htarget

end PakFixedPolyomino.ULogBootstrapExecution
