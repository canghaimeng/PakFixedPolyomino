import PakFixedPolyomino.ULogConcreteNoSpurious

namespace PakFixedPolyomino.PakULogCursorFuelExact

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution
open ULogBootstrapExecution

def unaryState_prefix_exact
    (q qnext : State) (hq : q ≠ .cycleStart) (n : ℕ)
    (tail : List Bool) (htail : tail ≠ [])
    (hzero : ∀ left y right,
      ULogBootstrapExecution.oneStep
          (ULogBootstrapExecution.Result.running q
            ⟨left, ulogCore codeZero, y :: right⟩) =
        ULogBootstrapExecution.Result.running q
          ⟨ulogCore codeZero :: left, y, right⟩)
    (hone : ∀ left y right,
      ULogBootstrapExecution.oneStep
          (ULogBootstrapExecution.Result.running q
            ⟨left, ulogCore codeOne, y :: right⟩) =
        ULogBootstrapExecution.Result.running qnext
          ⟨ulogCore codeOne :: left, y, right⟩)
    (left : List Tape) (after : Tape) (right : List Tape) :
    StopFreeValidZeroRun (n + 1)
      (atBits q (ULogBytecode.encodeNatField n ++ tail) left after right)
      (atBits qnext tail
        ((ULogBytecode.encodeNatField n).reverse.map codeTape ++ left)
        after right) := by
  cases tail with
  | nil => exact (htail rfl).elim
  | cons b bs =>
      cases n with
      | zero =>
          simpa [atBits, beforeUnaryState, ULogBytecode.encodeNatField,
            codeTape, List.map_append, List.reverse_append,
            List.append_assoc] using
            (stopFree_unaryState_of q qnext hq 0 hzero hone left
              (codeTape b) (bs.map codeTape ++ after :: right))
      | succ n =>
          simpa [atBits, beforeUnaryState, ULogBytecode.encodeNatField,
            codeTape, List.map_append, List.reverse_append, List.replicate_succ,
            List.append_assoc] using
            (stopFree_unaryState_of q qnext hq (n + 1) hzero hone left
              (codeTape b) (bs.map codeTape ++ after :: right))

def mismatchCount_prefix_fresh_exact
    (slot : Bool) (done : ℕ) (path left : List Tape)
    (boundary : Tape) (right : List Tape) :
    StopFreeValidZeroRun (done + 1)
      (.running (.mismatchCount slot)
        (beforeRightPath
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path) left boundary right))
      (.running (.mismatchSeekBoundary slot)
        (beforeRightPath path
          (ulogCore codeZero ::
            List.replicate done (ulogCore codeZero) ++ left)
          boundary right)) := by
  have hscan := stopFree_rightPath_of (.mismatchCount slot)
    (by intro h; cases h) (List.replicate done (ulogCore codeZero)) (by
      intro x hx l z rr
      have hm : done ≠ 0 ∧ x = ulogCore codeZero := by
        simpa only [List.mem_replicate] using hx
      rw [hm.2]
      exact mismatchCount_consumed slot l z rr)
    left (ulogCore pcDone) (path ++ boundary :: right)
  have hend : StopFreeValidZeroRun 1
      (.running (.mismatchCount slot)
        (afterRightPath (List.replicate done (ulogCore codeZero)) left
          (ulogCore pcDone) (path ++ boundary :: right)))
      (.running (.mismatchSeekBoundary slot)
        (beforeRightPath path
          (ulogCore codeZero :: List.replicate done (ulogCore codeZero) ++ left)
          boundary right)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases path with
      | nil => simpa [afterRightPath, beforeRightPath] using
          (mismatchCount_fresh slot
            (List.replicate done (ulogCore codeZero) ++ left) boundary right)
      | cons x xs => simpa [afterRightPath, beforeRightPath,
          List.append_assoc] using
          (mismatchCount_fresh slot
            (List.replicate done (ulogCore codeZero) ++ left) x
            (xs ++ boundary :: right))
    · cases path <;> cases slot <;>
        simp [afterRightPath, IsConcreteCycleStop,
          IsConcreteCycleBoundary, concreteHalted]
  cases done <;>
    simpa [beforeRightPath, List.replicate_succ,
      List.append_assoc] using hscan.append hend

def mismatchSeekBoundary_rule_exact
    (slot : Bool) (path : List Tape) (hpath : MismatchBoundaryFree path)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (next : List Bool)
    (left : List Tape) (after : Tape) (right : List Tape) :
    StopFreeValidZeroRun (path.length + 1)
      (.running (.mismatchSeekBoundary slot)
        (beforeRightPath path left (ulogCore boundary)
          ((ULogBytecode.encodeRule r ++ next).map codeTape ++
            after :: right)))
      (atBits (.mismatchSkipSource slot)
        (ULogBytecode.encodeRule r ++ next)
        ((if boundary = sourceBoundaryZero then ulogCore codeZero
          else ulogCore codeOne) :: path.reverse ++ left) after right) := by
  have henc : ULogBytecode.encodeRule r ≠ [] := by
    rcases r with ⟨source, read, ruleSlot, action⟩
    cases source <;> simp [ULogBytecode.encodeRule,
      ULogBytecode.encodeNatField, List.replicate_succ]
  cases he : ULogBytecode.encodeRule r ++ next with
  | nil =>
      have : False := by simpa [henc] using he
      exact this.elim
  | cons b bs =>
      have hscan := stopFree_rightPath_of (.mismatchSeekBoundary slot)
        (by intro h; cases h) path (by
          intro x hx l z rr
          have h := hpath x hx
          exact mismatchSeekBoundary_pass slot x h.1 h.2.1 h.2.2 l z rr)
        left (ulogCore boundary)
        (codeTape b :: bs.map codeTape ++ after :: right)
      have hend : StopFreeValidZeroRun 1
          (.running (.mismatchSeekBoundary slot)
            (afterRightPath path left (ulogCore boundary)
              (codeTape b :: bs.map codeTape ++ after :: right)))
          (atBits (.mismatchSkipSource slot) (b :: bs)
            ((if boundary = sourceBoundaryZero then ulogCore codeZero
              else ulogCore codeOne) :: path.reverse ++ left) after right) := by
        apply StopFreeValidZeroRun.one
        · apply validStepAt_zero_of_oneStep_running
          simpa [atBits, afterRightPath, List.append_assoc] using
            mismatchSeekBoundary_boundary slot boundary hboundary
              (path.reverse ++ left) (codeTape b)
              (bs.map codeTape ++ after :: right)
        · cases slot <;>
            simp [atBits, afterRightPath, IsConcreteCycleStop,
              IsConcreteCycleBoundary, concreteHalted]
      simpa [he, List.map_append, List.append_assoc] using hscan.append hend

def mismatchSkipRule_exact
    (lookupSlot : Bool) (r : ULogBytecode.RuleCode)
    (next : List Bool) (hnext : next ≠ [])
    (left : List Tape) (after : Tape) (right : List Tape) :
    StopFreeValidZeroRun (ULogBytecode.encodeRule r).length
      (atBits (.mismatchSkipSource lookupSlot)
        (ULogBytecode.encodeRule r ++ next) left after right)
      (atBits (.fieldCompare .source lookupSlot) next
        (mismatchRulePrefix r ++ left) after right) := by
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
  have hS := unaryState_prefix_exact
    (.mismatchSkipSource lookupSlot) (.mismatchSkipRead lookupSlot)
    (by intro h; cases h) source
    (rBits ++ [ruleSlot] ++ wBits ++ tBits ++ mBits ++ next)
    (by simp [rBits, ULogBytecode.encodeNatField])
    (mismatchSkipSource_zero lookupSlot) (mismatchSkipSource_one lookupSlot)
    left after right
  have hR := unaryState_prefix_exact
    (.mismatchSkipRead lookupSlot) (.mismatchSkipSlot lookupSlot)
    (by intro h; cases h) read
    ([ruleSlot] ++ wBits ++ tBits ++ mBits ++ next) (by simp)
    (mismatchSkipRead_zero lookupSlot) (mismatchSkipRead_one lookupSlot)
    lS after right
  have hSlotEq := atBits_mismatchSlot lookupSlot ruleSlot
    (wBits ++ tBits ++ mBits ++ next) lR after right
  have hSlot : StopFreeValidZeroRun 1
      (atBits (.mismatchSkipSlot lookupSlot)
        ([ruleSlot] ++ wBits ++ tBits ++ mBits ++ next) lR after right)
      (atBits (.mismatchSkipWrite lookupSlot)
        (wBits ++ tBits ++ mBits ++ next) lSlot after right) := by
    apply StopFreeValidZeroRun.oneOfStep
    · simpa [lSlot, List.append_assoc] using hSlotEq
    · cases lookupSlot <;> cases ruleSlot <;> rfl
    · cases write <;>
        simp [atBits, wBits, ULogBytecode.encodeNatField,
          List.replicate_succ]
    · cases lookupSlot <;> cases ruleSlot <;>
        simp [atBits, IsConcreteCycleStop, IsConcreteCycleBoundary,
          concreteHalted]
  have hW := unaryState_prefix_exact
    (.mismatchSkipWrite lookupSlot) (.mismatchSkipTarget lookupSlot)
    (by intro h; cases h) write (tBits ++ mBits ++ next)
    (by simp [tBits, ULogBytecode.encodeNatField])
    (mismatchSkipWrite_zero lookupSlot) (mismatchSkipWrite_one lookupSlot)
    lSlot after right
  have hT := unaryState_prefix_exact
    (.mismatchSkipTarget lookupSlot) (.mismatchSkipMoveFirst lookupSlot)
    (by intro h; cases h) target (mBits ++ next) (by simp [mBits])
    (mismatchSkipTarget_zero lookupSlot) (mismatchSkipTarget_one lookupSlot)
    lW after right
  have hM₁Eq := atBits_mismatchMoveFirst lookupSlot (moveFirst move)
    (moveSecond move :: next) lT after right
  have hM₁ : StopFreeValidZeroRun 1
      (atBits (.mismatchSkipMoveFirst lookupSlot) (mBits ++ next)
        lT after right)
      (atBits (.mismatchSkipMoveSecond lookupSlot)
        (moveSecond move :: next) lM₁ after right) := by
    apply StopFreeValidZeroRun.oneOfStep
    · simpa [mBits, lM₁, List.append_assoc] using hM₁Eq
    · cases lookupSlot <;> cases move <;> rfl
    · cases lookupSlot <;> cases move <;> simp [atBits]
    · cases lookupSlot <;> cases move <;>
        simp [atBits, mBits, IsConcreteCycleStop, IsConcreteCycleBoundary,
          concreteHalted]
  have hM₂ : StopFreeValidZeroRun 1
      (atBits (.mismatchSkipMoveSecond lookupSlot)
        (moveSecond move :: next) lM₁ after right)
      (atBits (.fieldCompare .source lookupSlot) next lM₂ after right) := by
    cases next with
    | nil => exact (hnext rfl).elim
    | cons b bs =>
        apply StopFreeValidZeroRun.oneOfStep
        · simpa [lM₂] using atBits_mismatchMoveSecond lookupSlot
            (moveSecond move) (b :: bs) lM₁ after right
        · cases lookupSlot <;> cases move <;> rfl
        · cases lookupSlot <;> cases move <;> simp [atBits]
        · cases lookupSlot <;> cases move <;>
            simp [atBits, IsConcreteCycleStop, IsConcreteCycleBoundary,
              concreteHalted]
  dsimp [sBits, rBits, wBits, tBits, mBits, lS, lR, lSlot, lW,
    lT, lM₁, lM₂] at hS hR hSlot hW hT hM₁ hM₂
  simp only [List.append_assoc] at hS hR hSlot hW hT hM₁ hM₂
  have hall := (((((hS.append hR).append hSlot).append hW).append hT).append
    hM₁).append hM₂
  cases move <;> simpa [ULogBytecode.encodeRule, ULogBytecode.encodeAction,
    ULogBytecode.encodeMove, moveFirst, moveSecond, mismatchRulePrefix,
    ULogBytecode.encodeNatField, List.reverse_append, List.map_append,
    List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

def mismatchCount_skipRule_exact
    (lookupSlot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchBoundaryFree path) (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (next : List Bool) (hnext : next ≠ [])
    (left : List Tape) (after : Tape) (right : List Tape) :
    StopFreeValidZeroRun
      (done + path.length + (ULogBytecode.encodeRule r).length + 2)
      (.running (.mismatchCount lookupSlot)
        (beforeRightPath
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: path) left (ulogCore boundary)
          ((ULogBytecode.encodeRule r ++ next).map codeTape ++
            after :: right)))
      (atBits (.fieldCompare .source lookupSlot) next
        (mismatchRulePrefix r ++
          (if boundary = sourceBoundaryZero then ulogCore codeZero
            else ulogCore codeOne) :: path.reverse ++ ulogCore codeZero ::
              List.replicate done (ulogCore codeZero) ++ left)
        after right) := by
  let countLeft := ulogCore codeZero ::
    List.replicate done (ulogCore codeZero) ++ left
  let restoredLeft :=
    (if boundary = sourceBoundaryZero then ulogCore codeZero
      else ulogCore codeOne) :: path.reverse ++ countLeft
  have hcount := mismatchCount_prefix_fresh_exact lookupSlot done path left
    (ulogCore boundary)
    ((ULogBytecode.encodeRule r ++ next).map codeTape ++ after :: right)
  have hseek := mismatchSeekBoundary_rule_exact lookupSlot path hpath boundary
    hboundary r next countLeft after right
  have hskip := mismatchSkipRule_exact lookupSlot r next hnext restoredLeft
    after right
  have hall := (hcount.append hseek).append hskip
  convert hall using 1 <;>
    simp [countLeft, restoredLeft, mismatchRulePrefix,
      List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;>
    omega

end PakFixedPolyomino.PakULogCursorFuelExact
