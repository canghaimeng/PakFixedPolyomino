import PakFixedPolyomino.ULogSemanticStayCycleAtLeast

/-! Automatically safe passive code, payload, and clock paths. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

structure PassiveCell (x : Tape) : Prop where
  source : x ≠ ulogCore stateZero ∧ x ≠ ulogCore stateOne ∧
    x ≠ MStarConcreteAlphabet.work ∧ x ≠ ulogCore sourceMark ∧
    x ≠ ulogCore pcMark ∧ x ≠ ulogCore stateMark ∧
    x ≠ ulogCore sourceBoundary ∧
    x ≠ ulogCore sourceBoundaryZero ∧
    x ≠ ulogCore sourceBoundaryOne
  read : x ≠ ulogCore payloadHeadZero ∧
    x ≠ ulogCore payloadHeadOne ∧
    x ≠ ulogCore payloadHeadBlank ∧
    x ≠ MStarConcreteAlphabet.work ∧
    x ≠ ulogCore readBoundary ∧ x ≠ ulogCore pcMark
  action : choiceHead x = false ∧ x ≠ MStarConcreteAlphabet.work ∧
    x ≠ ulogCore actionBoundary ∧ x ≠ ulogCore pcMark
  targetRound : x ≠ ulogCore stateMark ∧
    x ≠ ulogCore stateZero ∧ x ≠ ulogCore stateOne ∧
    x ≠ MStarConcreteAlphabet.work ∧ x ≠ ulogCore targetMark ∧
    x ≠ ulogCore pcMark
  targetFinish : x ≠ ulogCore stateMark ∧
    x ≠ ulogCore stateZero ∧ x ≠ ulogCore stateOne ∧
    x ≠ MStarConcreteAlphabet.work ∧
    x ≠ ulogCore targetBoundary ∧ x ≠ ulogCore pcMark
  move : choiceHead x = false ∧ x ≠ MStarConcreteAlphabet.work
  restoreClock : x ≠ ulogCore pcMark ∧ x ≠ MStarConcreteAlphabet.work
  mismatch : x ≠ ulogCore sourceBoundary ∧
    x ≠ ulogCore sourceBoundaryZero ∧
    x ≠ ulogCore sourceBoundaryOne ∧ x ≠ ulogCore pcMark
  restoreMismatch : restoreMismatchCell x = x

def PassivePath (path : List Tape) : Prop := ∀ x ∈ path, PassiveCell x

theorem passiveCell_codeTape (b : Bool) : PassiveCell (codeTape b) := by
  cases b <;> constructor <;> decide

theorem passiveCell_payloadTape (b : Bool) : PassiveCell (payloadTape b) := by
  cases b <;> constructor <;> decide

theorem passiveCell_payloadBlank : PassiveCell (ulogCore payloadBlank) := by
  constructor <;> decide

theorem passiveCell_payloadEnd : PassiveCell (ulogCore payloadEnd) := by
  constructor <;> decide

theorem passiveCell_payloadDone : PassiveCell (ulogCore payloadDone) := by
  constructor <;> decide

theorem passiveCell_payloadStartDone :
    PassiveCell (ulogCore payloadStartDone) := by
  constructor <;> decide

theorem passiveCell_payloadStartOne :
    PassiveCell (ulogCore payloadStartOne) := by
  constructor <;> decide

theorem passiveCell_clockZero : PassiveCell (ulogCore clockZero) := by
  constructor <;> decide

theorem passiveCell_clockOne : PassiveCell (ulogCore clockOne) := by
  constructor <;> decide

theorem passiveCell_payloadNat (n : ℕ) : PassiveCell (payloadNat n) := by
  cases n with
  | zero =>
      have h : payloadNat 0 = payloadTape false := by decide
      rw [h]; exact passiveCell_payloadTape false
  | succ n =>
      cases n with
      | zero =>
          have h : payloadNat 1 = payloadTape true := by decide
          rw [h]; exact passiveCell_payloadTape true
      | succ n =>
          have h : payloadNat (n + 2) = ulogCore payloadBlank := by
            simp [payloadNat, readHeadNat]; decide
          rw [show n + 1 + 1 = n + 2 by omega, h]
          exact passiveCell_payloadBlank

theorem passivePath_source {path : List Tape} (h : PassivePath path) :
    SourceCompareCorridorSafe path := fun x hx => (h x hx).source

theorem passivePath_read {path : List Tape} (h : PassivePath path) :
    ReadCorridorSafe path := fun x hx => (h x hx).read

theorem passivePath_action {path : List Tape} (h : PassivePath path) :
    ActionWriteCorridorSafe path := fun x hx => (h x hx).action

theorem passivePath_target {path : List Tape} (h : PassivePath path) :
    TargetRewriteCorridorSafe path :=
  ⟨fun x hx => (h x hx).targetRound, fun x hx => (h x hx).targetFinish⟩

theorem passivePath_move {path : List Tape} (h : PassivePath path) :
    MoveScanSafe path := fun x hx => (h x hx).move

theorem passivePath_restoreHead {path : List Tape} (h : PassivePath path) :
    RestoreHeadSafe path := fun x hx => ⟨(h x hx).action.1, (h x hx).move.2⟩

theorem passivePath_restoreClock {path : List Tape} (h : PassivePath path) :
    RestoreClockSafe path := fun x hx => (h x hx).restoreClock

theorem passivePath_mismatch {path : List Tape} (h : PassivePath path) :
    MismatchRestorePathSafe path := fun x hx => (h x hx).mismatch

theorem passivePath_restoreMismatch {path : List Tape}
    (h : PassivePath path) : RestoreMismatchIdentity path := by
  change path.map restoreMismatchCell = path
  induction path with
  | nil => rfl
  | cons x xs ih =>
      rw [List.map_cons, (h x (by simp)).restoreMismatch]
      rw [ih (fun y hy => h y (by simp [hy]))]

theorem passivePath_append {xs ys : List Tape}
    (hx : PassivePath xs) (hy : PassivePath ys) : PassivePath (xs ++ ys) := by
  intro x hxy
  rcases List.mem_append.mp hxy with h | h
  · exact hx x h
  · exact hy x h

theorem passivePath_reverse {xs : List Tape} (h : PassivePath xs) :
    PassivePath xs.reverse := fun x hx => h x (by simpa using hx)

theorem passivePath_map_codeTape (bits : List Bool) :
    PassivePath (bits.map codeTape) := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨b, -, rfl⟩
  exact passiveCell_codeTape b

theorem passivePath_map_payloadNat (xs : List ℕ) :
    PassivePath (xs.map payloadNat) := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨n, -, rfl⟩
  exact passiveCell_payloadNat n

theorem passivePath_payloadProgramPrefix (input : List Bool) :
    PassivePath (payloadProgramPrefix input) := by
  intro x hx
  rcases payloadProgramPrefix_mem hx with rfl | rfl | rfl | rfl
  · exact passiveCell_payloadEnd
  · exact passiveCell_payloadDone
  · exact passiveCell_payloadStartDone
  · exact passiveCell_payloadStartOne

theorem cursorDynamicProgramToHead_passive
    (input : List Bool) (left : List ℕ) :
    PassivePath (cursorDynamicProgramToHead input (left.map payloadNat)) := by
  apply passivePath_append
  · exact passivePath_reverse (passivePath_payloadProgramPrefix input)
  · exact passivePath_reverse (passivePath_map_payloadNat left)

theorem clockCellsAfter_passive (right : List ℕ) (k : ℕ)
    (runtime : List Tape) (hruntimeSafe : PassivePath runtime) :
    PassivePath (clockCellsAfter (right.map payloadNat) k runtime) := by
  intro x hx
  unfold clockCellsAfter at hx
  rcases List.mem_append.mp hx with hpre | htail
  · rcases List.mem_append.mp hpre with hpayload | hclock
    · exact passivePath_map_payloadNat right x hpayload
    · have heq : x = ulogCore clockOne :=
        (by simpa only [List.mem_replicate] using hclock :
          k ≠ 0 ∧ x = ulogCore clockOne).2
      rw [heq]; exact passiveCell_clockOne
  · rcases List.mem_cons.mp htail with hzero | hruntime
    · rw [hzero]; exact passiveCell_clockZero
    · exact hruntimeSafe x hruntime

end PakFixedPolyomino.ULogBootstrapExecution
