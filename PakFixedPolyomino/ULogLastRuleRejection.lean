import PakFixedPolyomino.ULogCertifiedFirstMatchRightBoundary

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem fieldCompare_source_invalid_reject (slot : Bool)
    (left : List Tape) (after : Tape) (right : List Tape)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    oneStep (.running (.fieldCompare .source slot) ⟨left, after, right⟩) =
      .rejected := by
  have hz : after ≠ ulogCore codeZero := by
    simpa [codeTape] using hzero
  have ho : after ≠ ulogCore codeOne := by
    simpa [codeTape] using hone
  have hra : qReject ≠ qAccept := by decide
  cases slot <;>
    simp [oneStep, program, rule, deterministicStep, hz, ho, reject, go,
      applyAction, hra]

theorem reaches_mismatchSkipRule_any (lookupSlot : Bool)
    (r : ULogBytecode.RuleCode) (next : List Bool)
    (left : List Tape) (after : Tape) (right : List Tape) :
    Reaches
      (atBits (.mismatchSkipSource lookupSlot)
        (ULogBytecode.encodeRule r ++ next) left after right)
      (atBits (.fieldCompare .source lookupSlot) next
        (mismatchBoundaryTape (moveSecond r.action.move) ::
          codeTape (moveFirst r.action.move) ::
            (ULogBytecode.encodeNatField r.action.target).reverse.map
              codeTape ++
            (ULogBytecode.encodeNatField r.action.write).reverse.map
              codeTape ++
            codeTape r.slot ::
            (ULogBytecode.encodeNatField r.read).reverse.map codeTape ++
            (ULogBytecode.encodeNatField r.source).reverse.map codeTape ++
            left)
        after right) := by
  rcases r with ⟨source, read, ruleSlot, ⟨write, target, move⟩⟩
  let sBits := ULogBytecode.encodeNatField source
  let rBits := ULogBytecode.encodeNatField read
  let wBits := ULogBytecode.encodeNatField write
  let tBits := ULogBytecode.encodeNatField target
  let mBits := [moveFirst move, moveSecond move]
  let lS := sBits.reverse.map codeTape ++ left
  let lR := rBits.reverse.map codeTape ++ lS
  let lSlot := codeTape ruleSlot :: lR
  let lW := wBits.reverse.map codeTape ++ lSlot
  let lT := tBits.reverse.map codeTape ++ lW
  let lM₁ := codeTape (moveFirst move) :: lT
  let lM₂ := mismatchBoundaryTape (moveSecond move) :: lM₁
  have hS : Reaches
      (atBits (.mismatchSkipSource lookupSlot)
        (sBits ++ rBits ++ [ruleSlot] ++ wBits ++ tBits ++ mBits ++ next)
        left after right)
      (atBits (.mismatchSkipRead lookupSlot)
        (rBits ++ [ruleSlot] ++ wBits ++ tBits ++ mBits ++ next)
        lS after right) := by
    simpa only [List.append_assoc] using
      (reaches_unaryState_prefix_of
        (.mismatchSkipSource lookupSlot) (.mismatchSkipRead lookupSlot)
        source (rBits ++ [ruleSlot] ++ wBits ++ tBits ++ mBits ++ next)
        (by simp [rBits, ULogBytecode.encodeNatField])
        (fun l y rr => mismatchSkipSource_zero lookupSlot l y rr)
        (fun l y rr => mismatchSkipSource_one lookupSlot l y rr)
        left after right)
  have hR : Reaches
      (atBits (.mismatchSkipRead lookupSlot)
        (rBits ++ [ruleSlot] ++ wBits ++ tBits ++ mBits ++ next)
        lS after right)
      (atBits (.mismatchSkipSlot lookupSlot)
        ([ruleSlot] ++ wBits ++ tBits ++ mBits ++ next) lR after right) := by
    simpa only [List.append_assoc] using
      (reaches_unaryState_prefix_of
        (.mismatchSkipRead lookupSlot) (.mismatchSkipSlot lookupSlot)
        read ([ruleSlot] ++ wBits ++ tBits ++ mBits ++ next) (by simp)
        (fun l y rr => mismatchSkipRead_zero lookupSlot l y rr)
        (fun l y rr => mismatchSkipRead_one lookupSlot l y rr)
        lS after right)
  have hSlot : Reaches
      (atBits (.mismatchSkipSlot lookupSlot)
        ([ruleSlot] ++ wBits ++ tBits ++ mBits ++ next) lR after right)
      (atBits (.mismatchSkipWrite lookupSlot)
        (wBits ++ tBits ++ mBits ++ next) lSlot after right) := by
    exact reaches_step (by
      simpa [lSlot, List.append_assoc] using
        (atBits_mismatchSlot lookupSlot ruleSlot
          (wBits ++ tBits ++ mBits ++ next) lR after right))
  have hW : Reaches
      (atBits (.mismatchSkipWrite lookupSlot)
        (wBits ++ tBits ++ mBits ++ next) lSlot after right)
      (atBits (.mismatchSkipTarget lookupSlot)
        (tBits ++ mBits ++ next) lW after right) := by
    simpa only [List.append_assoc] using
      (reaches_unaryState_prefix_of
        (.mismatchSkipWrite lookupSlot) (.mismatchSkipTarget lookupSlot)
        write (tBits ++ mBits ++ next)
        (by simp [tBits, ULogBytecode.encodeNatField])
        (fun l y rr => mismatchSkipWrite_zero lookupSlot l y rr)
        (fun l y rr => mismatchSkipWrite_one lookupSlot l y rr)
        lSlot after right)
  have hT : Reaches
      (atBits (.mismatchSkipTarget lookupSlot)
        (tBits ++ mBits ++ next) lW after right)
      (atBits (.mismatchSkipMoveFirst lookupSlot)
        (mBits ++ next) lT after right) := by
    simpa only [List.append_assoc] using
      (reaches_unaryState_prefix_of
        (.mismatchSkipTarget lookupSlot) (.mismatchSkipMoveFirst lookupSlot)
        target (mBits ++ next) (by simp [mBits])
        (fun l y rr => mismatchSkipTarget_zero lookupSlot l y rr)
        (fun l y rr => mismatchSkipTarget_one lookupSlot l y rr)
        lW after right)
  have hM₁ : Reaches
      (atBits (.mismatchSkipMoveFirst lookupSlot)
        (mBits ++ next) lT after right)
      (atBits (.mismatchSkipMoveSecond lookupSlot)
        (moveSecond move :: next) lM₁ after right) := by
    exact reaches_step (by
      simpa [mBits, lM₁, List.append_assoc] using
        (atBits_mismatchMoveFirst lookupSlot (moveFirst move)
          (moveSecond move :: next) lT after right))
  have hM₂ : Reaches
      (atBits (.mismatchSkipMoveSecond lookupSlot)
        (moveSecond move :: next) lM₁ after right)
      (atBits (.fieldCompare .source lookupSlot) next lM₂ after right) := by
    exact reaches_step (by
      simpa [lM₂] using
        (atBits_mismatchMoveSecond lookupSlot (moveSecond move)
          next lM₁ after right))
  have hall := reaches_trans hS (reaches_trans hR
    (reaches_trans hSlot (reaches_trans hW
      (reaches_trans hT (reaches_trans hM₁ hM₂)))))
  simpa [sBits, rBits, wBits, tBits, mBits, lS, lR, lSlot, lW,
    lT, lM₁, lM₂, ULogBytecode.encodeRule,
    ULogBytecode.encodeAction, List.reverse_append, List.map_append,
    List.append_assoc] using hall

theorem reaches_mismatchCount_lastRule_reject
    (lookupSlot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe path)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (left : List Tape)
    (after : Tape) (right : List Tape)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    Reaches
      (.running (.mismatchCount lookupSlot)
        (beforeRightPath
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path)
          left (ulogCore boundary)
          ((ULogBytecode.encodeRule r).map codeTape ++ after :: right)))
      .rejected := by
  have h₀ := reaches_mismatchCount_prefix_fresh lookupSlot done path left
    (ulogCore boundary) ((ULogBytecode.encodeRule r).map codeTape ++
      after :: right)
  have h₁ := reaches_mismatchSeekBoundary_rule lookupSlot path hpath.1
    boundary hboundary r []
    (ulogCore codeZero :: List.replicate done (ulogCore codeZero) ++ left)
    after right
  have h₂ := reaches_mismatchSkipRule_any lookupSlot r []
    ((if boundary = sourceBoundaryZero then ulogCore codeZero
      else ulogCore codeOne) :: path.reverse ++
        ulogCore codeZero :: List.replicate done (ulogCore codeZero) ++ left)
    after right
  have h₃ : Reaches
      (atBits (.fieldCompare .source lookupSlot) []
        (mismatchBoundaryTape (moveSecond r.action.move) ::
          codeTape (moveFirst r.action.move) ::
            (ULogBytecode.encodeNatField r.action.target).reverse.map
              codeTape ++
            (ULogBytecode.encodeNatField r.action.write).reverse.map
              codeTape ++
            codeTape r.slot ::
            (ULogBytecode.encodeNatField r.read).reverse.map codeTape ++
            (ULogBytecode.encodeNatField r.source).reverse.map codeTape ++
            (if boundary = sourceBoundaryZero then ulogCore codeZero
              else ulogCore codeOne) :: path.reverse ++
              ulogCore codeZero ::
                List.replicate done (ulogCore codeZero) ++ left)
        after right)
      .rejected := by
    exact reaches_step (by
      simpa [atBits] using fieldCompare_source_invalid_reject
        lookupSlot
        (mismatchBoundaryTape (moveSecond r.action.move) ::
          codeTape (moveFirst r.action.move) ::
            (ULogBytecode.encodeNatField r.action.target).reverse.map
              codeTape ++
            (ULogBytecode.encodeNatField r.action.write).reverse.map
              codeTape ++
            codeTape r.slot ::
            (ULogBytecode.encodeNatField r.read).reverse.map codeTape ++
            (ULogBytecode.encodeNatField r.source).reverse.map codeTape ++
            (if boundary = sourceBoundaryZero then ulogCore codeZero
              else ulogCore codeOne) :: path.reverse ++
              ulogCore codeZero ::
                List.replicate done (ulogCore codeZero) ++ left)
        after right hzero hone)
  exact reaches_trans h₀
    (reaches_trans (by simpa [List.append_assoc] using h₁)
      (reaches_trans h₂ (by simpa [List.append_assoc] using h₃)))

theorem reaches_mismatchReturn_lastRule_reject
    (lookupSlot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe path)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (outer : List Tape)
    (after : Tape) (right : List Tape)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    Reaches
      (.running (.mismatchReturnToPc lookupSlot)
        (beforeLeftPath
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path).reverse
          outer (ulogCore pcMark)
          (ulogCore boundary ::
            (ULogBytecode.encodeRule r).map codeTape ++ after :: right)))
      .rejected := by
  let returnPath :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: path).reverse
  have hreturnSafe : ∀ x ∈ returnPath, x ≠ ulogCore pcMark := by
    intro x hx
    have hx' : x ∈ path ∨ x = ulogCore pcDone ∨
        (done ≠ 0 ∧ x = ulogCore codeZero) := by
      simpa [returnPath] using hx
    rcases hx' with hp | hd | hz
    · exact hpath.2 x hp
    · rw [hd]
      native_decide
    · rw [hz.2]
      native_decide
  have h₀ := reaches_mismatchReturnToPc lookupSlot returnPath hreturnSafe
    outer (ulogCore boundary)
    ((ULogBytecode.encodeRule r).map codeTape ++ after :: right)
  have h₁ := reaches_mismatchCount_lastRule_reject lookupSlot done
    path hpath boundary hboundary r (ulogCore pcMark :: outer) after right
    hzero hone
  exact reaches_trans (by simpa [returnPath] using h₀) h₁

theorem reaches_restoreMismatchLastRule_reject
    (lookupSlot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe path)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (restorePath : List Tape)
    (hrestoreSafe : MismatchRestorePathSafe restorePath)
    (mismatchRight : List Tape) (r : ULogBytecode.RuleCode)
    (outer : List Tape) (after : Tape) (right : List Tape)
    (hrestored : restorePath.reverse.map restoreMismatchCell ++ mismatchRight =
      (ULogBytecode.encodeRule r).map codeTape ++ after :: right)
    (hzero : after ≠ codeTape false) (hone : after ≠ codeTape true) :
    Reaches
      (restoreAdvanceStarted lookupSlot restorePath
        (List.replicate done (ulogCore codeZero) ++
          ulogCore pcDone :: path).reverse
        outer boundary mismatchRight)
      .rejected := by
  let returnPath :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: path).reverse
  have hreturn : returnPath ≠ [] := by simp [returnPath]
  cases he : returnPath with
  | nil => exact (hreturn he).elim
  | cons x xs =>
      have h₀ := reaches_restoreRule_boundary lookupSlot restorePath
        hrestoreSafe boundary hboundary
        (xs ++ ulogCore pcMark :: outer) x mismatchRight
      have hrestored' :
          (restorePath.map restoreMismatchCell).reverse ++ mismatchRight =
            (ULogBytecode.encodeRule r).map codeTape ++ after :: right := by
        simpa only [List.map_reverse] using hrestored
      have h₀' : Reaches
          (restoreAdvanceStarted lookupSlot restorePath returnPath
            outer boundary mismatchRight)
          (.running (.mismatchReturnToPc lookupSlot)
            (beforeLeftPath returnPath outer (ulogCore pcMark)
              (ulogCore boundary ::
                (ULogBytecode.encodeRule r).map codeTape ++
                  after :: right))) := by
        simpa [restoreAdvanceStarted, he, beforeLeftPath,
          hrestored', List.append_assoc] using h₀
      have h₁ := reaches_mismatchReturn_lastRule_reject lookupSlot
        done path hpath boundary hboundary r outer after right hzero hone
      exact reaches_trans h₀' (by simpa [returnPath] using h₁)

end PakFixedPolyomino.ULogBootstrapExecution
