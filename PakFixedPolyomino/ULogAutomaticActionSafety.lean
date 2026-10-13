import PakFixedPolyomino.ULogAutomaticSemanticLookup

/-! Automatic successful-action and cleanup safety on encoded passive paths. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem mismatchHistory_code (boundary : ULogLetter)
    (skip : List ULogBytecode.RuleCode) (x : Tape)
    (hx : x ∈ mismatchHistory boundary skip) :
    ∃ b, x = codeTape b := by
  induction skip generalizing boundary with
  | nil => simp [mismatchHistory] at hx
  | cons r rs ih =>
      simp only [mismatchHistory, skippedRuleSegment, List.mem_append,
        List.mem_cons, List.mem_reverse] at hx
      rcases hx with (hb | hr) | hs
      · by_cases hz : boundary = sourceBoundaryZero
        · subst x
          exact ⟨false, by simp [restoredBoundaryCell, hz, codeTape]⟩
        · subst x
          exact ⟨true, by simp [restoredBoundaryCell, hz, codeTape]⟩
      · exact mismatchRulePrefix_tail_code r x hr
      · exact ih (nextSourceBoundary (moveSecond r.action.move)) hs

theorem cursorCleanupProgramPrefix_cell
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (x : Tape) (hx : x ∈ cursorCleanupProgramPrefix skip r) :
    (∃ b, x = codeTape b) ∨ x = ulogCore sourceBoundary ∨
      x = ulogCore sourceBoundaryZero ∨ x = ulogCore sourceBoundaryOne := by
  cases skip with
  | nil =>
      left
      rcases List.mem_map.mp hx with ⟨b, -, rfl⟩
      exact ⟨b, rfl⟩
  | cons s ss =>
      unfold cursorCleanupProgramPrefix at hx
      simp only [List.mem_reverse, List.mem_append, List.mem_cons] at hx
      rcases hx with hr | hb | hh
      · left
        have hr' : x ∈ (ULogBytecode.encodeRule r).map codeTape := by
          simpa only [List.mem_reverse] using hr
        rcases List.mem_map.mp hr' with ⟨b, -, hxb⟩
        exact ⟨b, hxb.symm⟩
      · right
        have hv := boundaryAfter_valid sourceBoundary (Or.inl rfl) (s :: ss)
        rcases hv with h | h | h
        · exact Or.inl (hb.trans (congrArg ulogCore h))
        · exact Or.inr (Or.inl (hb.trans (congrArg ulogCore h)))
        · exact Or.inr (Or.inr (hb.trans (congrArg ulogCore h)))
      · left
        have hfull : x ∈ mismatchHistory sourceBoundary (s :: ss) := by
          cases he : mismatchHistory sourceBoundary (s :: ss) with
          | nil => simp [he] at hh
          | cons y ys =>
              have : x ∈ ys := by simpa [he] using hh
              simp [he, this]
        exact mismatchHistory_code sourceBoundary (s :: ss) x hfull

theorem cursorCleanupProgramPrefix_restoreHeadSafe
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode) :
    RestoreHeadSafe (cursorCleanupProgramPrefix skip r) := by
  intro x hx
  rcases cursorCleanupProgramPrefix_cell skip r x hx with
    ⟨b, rfl⟩ | rfl | rfl | rfl
  · exact (passiveCell_codeTape b).move
  all_goals decide

theorem cursorCleanupProgramPrefix_clockSafe
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode) :
    RestoreClockSafe (cursorCleanupProgramPrefix skip r) := by
  intro x hx
  rcases cursorCleanupProgramPrefix_cell skip r x hx with
    ⟨b, rfl⟩ | rfl | rfl | rfl
  · exact (passiveCell_codeTape b).restoreClock
  all_goals decide

theorem cursorCleanupProgramPath_restoreHeadSafe
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (programToHead : List Tape)
    (hp : PassivePath programToHead) :
    RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs programToHead) := by
  intro x hx
  rcases List.mem_append.mp hx with hcleanup | hmove
  · exact cursorCleanupProgramPrefix_restoreHeadSafe skip r x hcleanup
  · exact passivePath_restoreHead
      (cursorMatchedMovePath_passive rs programToHead hp) x hmove

theorem cursorCleanupProgramPath_clockSafe
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (programToHead : List Tape)
    (hp : PassivePath programToHead) :
    RestoreClockSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs programToHead) := by
  intro x hx
  rcases List.mem_append.mp hx with hcleanup | hmove
  · exact cursorCleanupProgramPrefix_clockSafe skip r x hcleanup
  · exact passivePath_restoreClock
      (cursorMatchedMovePath_passive rs programToHead hp) x hmove

theorem writeHeadNat_targetSafe (n : ℕ) (hn : n < 3) :
    TargetRewriteCorridorSafe [writeHeadNat n] := by
  interval_cases n <;> constructor <;> intro x hx <;>
    simp only [List.mem_singleton] at hx <;> subst x <;> decide

theorem writeHeadNat_restoreClockSafe (n : ℕ) (hn : n < 3) :
    RestoreClockSafe [writeHeadNat n] := by
  interval_cases n <;> intro x hx <;>
    simp only [List.mem_singleton] at hx <;> subst x <;> decide

theorem matchedReadPath_safe
    (slot : Bool) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (programToHead : List Tape)
    (hp : PassivePath programToHead) :
    ReadCorridorSafe
      (codeTape slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs programToHead)) := by
  apply passivePath_read
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact passiveCell_codeTape slot
  · exact encodedActionPath_passive _ _ _ _
      (cursorMatchedMovePath_passive rs programToHead hp) x hx

theorem matchedWritePath_safe
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead : List Tape) (hp : PassivePath programToHead) :
    ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs programToHead) := by
  apply passivePath_action
  intro x hx
  rcases List.mem_append.mp hx with hprefix | hp'
  · rcases List.mem_append.mp hprefix with hz | hrest
    · have heq : x = ulogCore codeZero :=
        (by simpa only [List.mem_replicate] using hz :
          r.action.target ≠ 0 ∧ x = ulogCore codeZero).2
      rw [heq]; exact passiveCell_codeTape false
    · rcases List.mem_cons.mp hrest with ho | hm
      · rw [ho]; exact passiveCell_codeTape true
      · unfold moveBits at hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl
        · exact passiveCell_codeTape _
        · exact passiveCell_codeTape _
  · exact cursorMatchedMovePath_passive rs programToHead hp x hp'

theorem matchedTargetPath_safe
    (r : ULogBytecode.RuleCode) (hwrite : r.action.write < 3)
    (rs : List ULogBytecode.RuleCode) (programToHead runtime : List Tape)
    (hp : PassivePath programToHead) (hruntime : PassivePath runtime) :
    TargetRewriteCorridorSafe
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: runtime) := by
  have hmoveBits : PassivePath (moveBits r.action.move) := by
    intro x hx
    unfold moveBits at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact passiveCell_codeTape _
    · exact passiveCell_codeTape _
  have hpre : PassivePath
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead) :=
    passivePath_append hmoveBits
      (cursorMatchedMovePath_passive rs programToHead hp)
  constructor <;> intro x hx
  · rcases List.mem_append.mp hx with hpre' | hheadRuntime
    · exact (hpre x hpre').targetRound
    · rcases List.mem_cons.mp hheadRuntime with hw | hr
      · have hs := (writeHeadNat_targetSafe r.action.write hwrite).1
        exact hs x (by simpa [hw])
      · exact (hruntime x hr).targetRound
  · rcases List.mem_append.mp hx with hpre' | hheadRuntime
    · exact (hpre x hpre').targetFinish
    · rcases List.mem_cons.mp hheadRuntime with hw | hr
      · have hs := (writeHeadNat_targetSafe r.action.write hwrite).2
        exact hs x (by simpa [hw])
      · exact (hruntime x hr).targetFinish

theorem cursorCleanupPcPath_clockSafe
    (skip rest : List ULogBytecode.RuleCode) :
    RestoreClockSafe (cursorCleanupPcPath skip rest) := by
  intro x hx
  unfold cursorCleanupPcPath at hx
  rcases List.mem_append.mp hx with hz | hd
  · have heq : x = ulogCore codeZero :=
      (by simpa only [List.mem_replicate] using hz :
        skip.length ≠ 0 ∧ x = ulogCore codeZero).2
    rw [heq]; decide
  · have heq : x = ulogCore pcDone :=
      (by simpa only [List.mem_replicate] using hd :
        rest.length ≠ 0 ∧ x = ulogCore pcDone).2
    rw [heq]; decide

theorem cursorCleanupTerminal_clockSafe (skip : List ULogBytecode.RuleCode) :
    RestoreClockSafe [cursorCleanupTerminal skip] := by
  intro x hx
  simp only [List.mem_singleton] at hx
  subst x
  rcases cursorCleanupTerminal_valid skip with h | h <;> rw [h] <;>
    decide

theorem matchedCleanupClock_safe
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (programToHead : List Tape)
    (hp : PassivePath programToHead) (hwrite : r.action.write < 3) :
    RestoreClockSafe
      (writeHeadNat r.action.write ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead)).reverse) := by
  intro x hx
  rcases List.mem_cons.mp hx with hw | hrest
  · have hs := writeHeadNat_restoreClockSafe r.action.write hwrite
    exact hs x (by simpa [hw])
  · simp only [List.mem_reverse, List.mem_append, List.mem_cons] at hrest
    rcases hrest with hmove | htail
    · exact cursorCleanupPcPath_clockSafe skip (r :: rs) x hmove
    · rcases htail with hcleanup | htail
      · have hs := cursorCleanupTerminal_clockSafe skip
        exact hs x (by simpa [hcleanup])
      · rcases htail with ht | hpc
        · exact cursorCleanupProgramPrefix_clockSafe skip r x ht
        · exact passivePath_restoreClock
            (cursorMatchedMovePath_passive rs programToHead hp) x hpc

theorem matchedCleanupProgram_appendUnhead_safe
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (programToHead : List Tape)
    (hp : PassivePath programToHead) :
    RestoreHeadSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs programToHead ++
          [unheadTape (writeHeadNat r.action.write)]) := by
  intro x hx
  rcases List.mem_append.mp hx with hbase | hu
  · exact cursorCleanupProgramPath_restoreHeadSafe skip r rs
      programToHead hp x hbase
  · have heq : x = payloadNat r.action.write := by
      simpa [payloadNat] using hu
    rw [heq]
    exact (passiveCell_payloadNat r.action.write).move

theorem matchedCleanupProgram_appendUnhead_clockSafe
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (programToHead : List Tape)
    (hp : PassivePath programToHead) :
    RestoreClockSafe
      (cursorCleanupProgramPrefix skip r ++
        cursorMatchedMovePath rs programToHead ++
          [unheadTape (writeHeadNat r.action.write)]) := by
  intro x hx
  rcases List.mem_append.mp hx with hbase | hu
  · exact cursorCleanupProgramPath_clockSafe skip r rs
      programToHead hp x hbase
  · have heq : x = payloadNat r.action.write := by
      simpa [payloadNat] using hu
    rw [heq]
    exact (passiveCell_payloadNat r.action.write).restoreClock

theorem headTapeOfCell_payloadNat_restoreClockSafe (n : ℕ) :
    (headTapeOfCell (payloadNat n) ≠ ulogCore pcMark ∧
      headTapeOfCell (payloadNat n) ≠ MStarConcreteAlphabet.work) := by
  rw [headTapeOfCell_payloadNat]
  cases n with
  | zero => decide
  | succ n =>
      cases n with
      | zero => decide
      | succ n => simp [readHeadNat]; decide

theorem matchedCleanupClock_rightInternal_safe
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (programToHead : List Tape)
    (hp : PassivePath programToHead) (next : ℕ) :
    RestoreClockSafe
      (headTapeOfCell (payloadNat next) ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead ++
                [unheadTape (writeHeadNat r.action.write)])).reverse) := by
  intro x hx
  rcases List.mem_cons.mp hx with hhead | hrest
  · rw [hhead]
    exact headTapeOfCell_payloadNat_restoreClockSafe next
  · have hagg : x ∈ cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead ++
                [unheadTape (writeHeadNat r.action.write)]) := by
      simpa only [List.mem_reverse] using hrest
    rcases List.mem_append.mp hagg with hpc | htail
    · exact cursorCleanupPcPath_clockSafe skip (r :: rs) x hpc
    · rcases List.mem_cons.mp htail with ht | hprogram
      · have hs := cursorCleanupTerminal_clockSafe skip
        exact hs x (by simpa [ht])
      · exact matchedCleanupProgram_appendUnhead_clockSafe skip r rs
          programToHead hp x hprogram

theorem matchedCleanupClock_leftInternal_safe
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (programToHead : List Tape)
    (hp : PassivePath programToHead) (next : ℕ) :
    RestoreClockSafe
      (headTapeOfCell (payloadNat next) ::
        (cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead)).reverse) := by
  intro x hx
  rcases List.mem_cons.mp hx with hhead | hrest
  · rw [hhead]
    exact headTapeOfCell_payloadNat_restoreClockSafe next
  · have hagg : x ∈ cursorCleanupPcPath skip (r :: rs) ++
          cursorCleanupTerminal skip ::
            (cursorCleanupProgramPrefix skip r ++
              cursorMatchedMovePath rs programToHead) := by
      simpa only [List.mem_reverse] using hrest
    rcases List.mem_append.mp hagg with hpc | htail
    · exact cursorCleanupPcPath_clockSafe skip (r :: rs) x hpc
    · rcases List.mem_cons.mp htail with ht | hprogram
      · have hs := cursorCleanupTerminal_clockSafe skip
        exact hs x (by simpa [ht])
      · exact cursorCleanupProgramPath_clockSafe skip r rs
          programToHead hp x hprogram

theorem cursorCleanupPcPath_restoreHeadSafe
    (skip rest : List ULogBytecode.RuleCode) :
    RestoreHeadSafe (cursorCleanupPcPath skip rest) := by
  intro x hx
  unfold cursorCleanupPcPath at hx
  rcases List.mem_append.mp hx with hz | hd
  · have heq : x = ulogCore codeZero :=
      (by simpa only [List.mem_replicate] using hz :
        skip.length ≠ 0 ∧ x = ulogCore codeZero).2
    rw [heq]; decide
  · have heq : x = ulogCore pcDone :=
      (by simpa only [List.mem_replicate] using hd :
        rest.length ≠ 0 ∧ x = ulogCore pcDone).2
    rw [heq]; decide

theorem cursorCleanupTerminal_restoreHeadSafe
    (skip : List ULogBytecode.RuleCode) :
    RestoreHeadSafe [cursorCleanupTerminal skip] := by
  intro x hx
  simp only [List.mem_singleton] at hx
  subst x
  rcases cursorCleanupTerminal_valid skip with h | h <;> rw [h] <;>
    decide

theorem leftBoundaryShiftBase_restoreHeadSafe
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) :
    RestoreHeadSafe
      (cursorCleanupPcPath skip (r :: rs) ++
        cursorCleanupTerminal skip ::
          (cursorCleanupProgramPrefix skip r ++ cursorMatchedMovePath rs [])) := by
  intro x hx
  rcases List.mem_append.mp hx with hpc | htail
  · exact cursorCleanupPcPath_restoreHeadSafe skip (r :: rs) x hpc
  · rcases List.mem_cons.mp htail with ht | hprogram
    · have hs := cursorCleanupTerminal_restoreHeadSafe skip
      exact hs x (by simpa [ht])
    · exact cursorCleanupProgramPath_restoreHeadSafe skip r rs []
        (by simp [PassivePath]) x hprogram

theorem matchedLeftBoundary_shift_safe
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) :
    ShiftRuntimeSafe
      ((cursorMatchedMovePath rs []).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse ++
              [ulogCore pcMark]) := by
  have hbase := leftBoundaryShiftBase_restoreHeadSafe skip r rs
  intro x hx
  have heq : (cursorMatchedMovePath rs []).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse =
      (cursorCleanupPcPath skip (r :: rs) ++
        cursorCleanupTerminal skip ::
          (cursorCleanupProgramPrefix skip r ++
            cursorMatchedMovePath rs [])).reverse := by
    simp [List.reverse_append, List.append_assoc]
  rw [heq] at hx
  rcases List.mem_append.mp hx with hb | hmark
  · exact (hbase x (by simpa only [List.mem_reverse] using hb)).2
  · have heq : x = ulogCore pcMark := by simpa using hmark
    rw [heq]; native_decide

theorem matchedLeftBoundary_return_safe
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) :
    ReturnMovedSafe
      (((cursorMatchedMovePath rs []).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse).reverse ++
              [ulogCore payloadStartOne]) := by
  have hbase := leftBoundaryShiftBase_restoreHeadSafe skip r rs
  intro x hx
  have heq : ((cursorMatchedMovePath rs []).reverse ++
        (cursorCleanupProgramPrefix skip r).reverse ++
          cursorCleanupTerminal skip ::
            (cursorCleanupPcPath skip (r :: rs)).reverse).reverse =
      cursorCleanupPcPath skip (r :: rs) ++
        cursorCleanupTerminal skip ::
          (cursorCleanupProgramPrefix skip r ++
            cursorMatchedMovePath rs []) := by
    simp [List.reverse_append, List.append_assoc]
  rw [heq] at hx
  rcases List.mem_append.mp hx with hb | hboundary
  · exact (hbase x hb).1
  · have heq : x = ulogCore payloadStartOne := by simpa using hboundary
    rw [heq]; native_decide

theorem matchedRightBoundary_shift_safe
    (runtime : List Tape) (hruntime : PassivePath runtime) (target : ℕ) :
    ShiftRuntimeSafe
      (runtime ++ List.replicate target (ulogCore stateZero) ++
        [ulogCore stateOne, ulogCore stateSep]) := by
  intro x hx
  rcases List.mem_append.mp hx with hprefix | hlast
  · rcases List.mem_append.mp hprefix with hr | hz
    · exact (hruntime x hr).move.2
    · have heq : x = ulogCore stateZero :=
        (by simpa only [List.mem_replicate] using hz :
          target ≠ 0 ∧ x = ulogCore stateZero).2
      rw [heq]; decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hlast
    rcases hlast with ho | hs
    · rw [ho]; decide
    · rw [hs]; decide

theorem matchedRightBoundary_return_safe
    (boundary : Tape)
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (runtime : List Tape) (hruntime : PassivePath runtime) (target : ℕ) :
    ReturnMovedSafe
      ((runtime ++ List.replicate target (ulogCore stateZero) ++
        [ulogCore stateOne]).reverse ++ [boundary]) := by
  intro x hx
  rcases List.mem_append.mp hx with hbase | hb
  · have hbase' : x ∈ runtime ++
        List.replicate target (ulogCore stateZero) ++
          [ulogCore stateOne] := by
      simpa only [List.mem_reverse] using hbase
    rcases List.mem_append.mp hbase' with hprefix | ho
    · rcases List.mem_append.mp hprefix with hr | hz
      · exact (hruntime x hr).move.1
      · have heq : x = ulogCore stateZero :=
          (by simpa only [List.mem_replicate] using hz :
            target ≠ 0 ∧ x = ulogCore stateZero).2
        rw [heq]; decide
    · have heq : x = ulogCore stateOne := by simpa using ho
      rw [heq]; decide
  · have heq : x = boundary := by simpa using hb
    rw [heq]
    rcases hboundary with rfl | rfl <;> decide

end PakFixedPolyomino.ULogBootstrapExecution
