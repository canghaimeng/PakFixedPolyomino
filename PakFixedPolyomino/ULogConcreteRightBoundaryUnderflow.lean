import PakFixedPolyomino.ULogBootstrapMicroPrefix

/-! Genuine right-boundary movement shortage: the finite suffix after `last`
is empty, so the next shiftRuntime RIGHT is stuck with no allocated WORK. -/

namespace PakFixedPolyomino.ULogConcreteRightBoundaryUnderflow

open ULogAlphabet ULogControl ULogProgram ULogBootstrapExecution
open ULogConcreteChoiceBarrier ULogConcreteMicroPathSplitting
open MStarParserExecution (Zipper applyAction)

def start (path pre : List Tape) (boundary last head : Tape)
    (left : List Tape) : Result :=
  .running (.moveSimHead .right)
    (beforeRightPath path left head (boundary :: pre ++ [last]))

def shiftLeft (path : List Tape) (head : Tape) (left : List Tape) : List Tape :=
  ulogCore payloadHeadBlank :: unheadTape head :: path.reverse ++ left

/-- Recursive walk tracking the actual shifted carry and written left. -/
def walk (last carry : Tape) : List Tape → List Tape → Result
  | [], left => .running (.shiftRuntime (.right carry)) ⟨left, last, []⟩
  | x :: xs, left => walk last x xs (carry :: left)

def walkCarry (carry : Tape) : List Tape → Tape
  | [] => carry
  | x :: xs => walkCarry x xs

def walkWritten (carry : Tape) : List Tape → List Tape → List Tape
  | [], left => left
  | x :: xs, left => walkWritten x xs (carry :: left)

theorem walk_eq (last carry : Tape) (pre left : List Tape) :
    walk last carry pre left =
      .running (.shiftRuntime (.right (walkCarry carry pre)))
        ⟨walkWritten carry pre left, last, []⟩ := by
  induction pre generalizing carry left with
  | nil => rfl
  | cons x xs ih => exact ih x (carry :: left)

def penultimate (path pre : List Tape) (boundary last head : Tape)
    (left : List Tape) : Result :=
  walk last boundary pre (shiftLeft path head left)

def shiftStart (path pre : List Tape) (boundary last head : Tape)
    (left : List Tape) : Result :=
  .running (.shiftRuntime (.right boundary))
    (beforeRightPath pre (shiftLeft path head left) last [])

theorem start_outside (path pre : List Tape) (boundary last head : Tape)
    (left : List Tape) :
    preChoiceResult (start path pre boundary last head left) = false :=
  rfl

theorem last_ne_work {pre : List Tape} {last : Tape}
    (hshift : ShiftRuntimeSafe (pre ++ [last])) :
    last ≠ MStarConcreteAlphabet.work :=
  hshift last (by simp)

theorem shiftRuntimeRight_empty_stuck (carry last : Tape)
    (hlast : last ≠ MStarConcreteAlphabet.work) (left : List Tape) :
    oneStep (.running (.shiftRuntime (.right carry)) ⟨left, last, []⟩) =
      .stuck := by
  simp [oneStep, program, rule, deterministicStep, go, hlast, applyAction]

theorem validStepAt_shiftRuntimeRight_empty (carry last : Tape)
    (hlast : last ≠ MStarConcreteAlphabet.work) (left : List Tape) :
    validStepAt 0 (.running (.shiftRuntime (.right carry)) ⟨left, last, []⟩) =
      some .stuck := by
  simp [validStepAt, oneStepAt, program, rule, deterministicStep, go, hlast,
    applyAction]

def stopFree_walk (last carry : Tape) (pre : List Tape)
    (hsafe : ShiftRuntimeSafe (pre ++ [last]))
    (left : List Tape) :
    StopFreeValidZeroRun pre.length
      (.running (.shiftRuntime (.right carry))
        (beforeRightPath pre left last []))
      (walk last carry pre left) := by
  induction pre generalizing carry left with
  | nil =>
      exact
        { valid := ValidZeroRun.nil _
          stop_free := fun m hm => (Nat.not_lt_zero m hm).elim }
  | cons x xs ih =>
      have hx : x ≠ MStarConcreteAlphabet.work := hsafe x (by simp)
      have hxs : ShiftRuntimeSafe (xs ++ [last]) := by
        intro y hy
        exact hsafe y (by simp [hy])
      have hfirst : StopFreeValidZeroRun 1
          (.running (.shiftRuntime (.right carry))
            (beforeRightPath (x :: xs) left last []))
          (.running (.shiftRuntime (.right x))
            (beforeRightPath xs (carry :: left) last [])) := by
        apply StopFreeValidZeroRun.one
        · apply validStepAt_zero_of_oneStep_running
          cases xs with
          | nil =>
              simpa [beforeRightPath] using
                shiftRuntimeRight_step carry x hx left last []
          | cons z zs =>
              simpa [beforeRightPath, List.append_assoc] using
                shiftRuntimeRight_step carry x hx left z (zs ++ [last])
        · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
      have hrest := ih x hxs (carry :: left)
      simpa [walk, Nat.add_comm] using hfirst.append hrest

def stopFree_to_penultimate
    (path pre : List Tape) (hscan : MoveScanSafe path)
    (boundary last head : Tape)
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (hshift : ShiftRuntimeSafe (pre ++ [last]))
    (left : List Tape) (hhead : choiceHead head = true) :
    StopFreeValidZeroRun (path.length + pre.length + 2)
      (start path pre boundary last head left)
      (penultimate path pre boundary last head left) := by
  have hscanRun :=
    stopFree_moveScan .right path hscan left head (boundary :: pre ++ [last])
  have hmove : StopFreeValidZeroRun 1
      (.running (.moveSimHead .right)
        (afterRightPath path left head (boundary :: pre ++ [last])))
      (.running (.actionPhase .movePlaceRight)
        ⟨unheadTape head :: path.reverse ++ left, boundary,
          pre ++ [last]⟩) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [afterRightPath, List.append_assoc] using
        moveSimHead_right head hhead (path.reverse ++ left) boundary
          (pre ++ [last])
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hplace : StopFreeValidZeroRun 1
      (.running (.actionPhase .movePlaceRight)
        ⟨unheadTape head :: path.reverse ++ left, boundary, pre ++ [last]⟩)
      (shiftStart path pre boundary last head left) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases pre with
      | nil =>
          simpa [shiftStart, shiftLeft, beforeRightPath] using
            movePlaceRight_boundary boundary hboundary
              (unheadTape head :: path.reverse ++ left) last []
      | cons x xs =>
          simpa [shiftStart, shiftLeft, beforeRightPath, List.append_assoc] using
            movePlaceRight_boundary boundary hboundary
              (unheadTape head :: path.reverse ++ left) x (xs ++ [last])
    · simp [IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hwalk :=
    stopFree_walk last boundary pre hshift (shiftLeft path head left)
  have hall := ((hscanRun.append hmove).append hplace).append hwalk
  have hn : ((path.length + 1) + 1) + pre.length =
      path.length + pre.length + 2 := by omega
  simpa [start, penultimate, shiftStart, hn] using hall

theorem penultimate_oneStep
    (path pre : List Tape) (boundary last head : Tape)
    (hshift : ShiftRuntimeSafe (pre ++ [last]))
    (left : List Tape) :
    oneStep (penultimate path pre boundary last head left) = .stuck := by
  simpa [penultimate, walk_eq] using
    shiftRuntimeRight_empty_stuck (walkCarry boundary pre) last
      (last_ne_work hshift) (walkWritten boundary pre (shiftLeft path head left))

def stopFree_to_stuck
    (path pre : List Tape) (hscan : MoveScanSafe path)
    (boundary last head : Tape)
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (hshift : ShiftRuntimeSafe (pre ++ [last]))
    (left : List Tape) (hhead : choiceHead head = true) :
    StopFreeValidZeroRun (path.length + pre.length + 3)
      (start path pre boundary last head left) .stuck := by
  have hpre :=
    stopFree_to_penultimate path pre hscan boundary last head hboundary
      hshift left hhead
  have hstuck : StopFreeValidZeroRun 1
      (penultimate path pre boundary last head left) .stuck := by
    apply StopFreeValidZeroRun.one
    · simpa [penultimate, walk_eq] using
        validStepAt_shiftRuntimeRight_empty (walkCarry boundary pre) last
          (last_ne_work hshift)
          (walkWritten boundary pre (shiftLeft path head left))
    · simp [penultimate, walk_eq, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hall := hpre.append hstuck
  have hn : path.length + pre.length + 2 + 1 =
      path.length + pre.length + 3 := by omega
  simpa [hn] using hall

theorem no_choice_before {n : Nat} {start finish : Result}
    (valid : ValidZeroRun n start finish)
    (noStop : ∀ m, m < n → ¬ IsConcreteCycleStop (run m start))
    (outside : preChoiceResult start = false) :
    ∀ m, m < n → ¬ IsConcreteChoice (run m start) := by
  have allOutside := outside_before_boundary valid noStop outside
  intro m hm choice
  have current := allOutside m (Nat.le_of_lt hm)
  cases h : run m start with
  | accepted z => simp [h, IsConcreteChoice] at choice
  | rejected => simp [h, IsConcreteChoice] at choice
  | stuck => simp [h, IsConcreteChoice] at choice
  | running q z =>
      have hq : q = .chooseSlot := by cases q <;> simp_all [IsConcreteChoice]
      simp [h, hq, preChoiceResult, preChoice] at current

theorem no_accepting_path
    (path pre : List Tape) (hscan : MoveScanSafe path)
    (boundary last head : Tape)
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (hshift : ShiftRuntimeSafe (pre ++ [last]))
    (left : List Tape) (hhead : choiceHead head = true)
    (labels : List (Fin 2)) (tape : Zipper Tape) :
    ConcreteMicroPath (start path pre boundary last head left) labels
      (.accepted tape) → False := by
  intro raw
  have hsf :=
    stopFree_to_stuck path pre hscan boundary last head hboundary
      hshift left hhead
  have noChoice :=
    no_choice_before hsf.valid hsf.stop_free
      (start_outside path pre boundary last head left)
  obtain ⟨rest, _, fromPen⟩ :=
    zero_prefix_of_micro_accepting hsf.valid noChoice raw
  have halted := microPath_halted_start fromPen (by rfl)
  cases halted.2

/-- FOUR-joint constructive packaging of the exact-count shortage. -/
def right_boundary_underflow_spec
    (path pre : List Tape) (hscan : MoveScanSafe path)
    (boundary last head : Tape)
    (hboundary : boundary = ulogCore clockZero ∨
      boundary = ulogCore clockOne)
    (hshift : ShiftRuntimeSafe (pre ++ [last]))
    (left : List Tape) (hhead : choiceHead head = true) :
    PProd
      (StopFreeValidZeroRun (path.length + pre.length + 2)
        (start path pre boundary last head left)
        (penultimate path pre boundary last head left))
      (PProd (oneStep (penultimate path pre boundary last head left) = .stuck)
        (PProd
          (StopFreeValidZeroRun (path.length + pre.length + 3)
            (start path pre boundary last head left) .stuck)
          (∀ (labels : List (Fin 2)) (tape : Zipper Tape),
            ConcreteMicroPath (start path pre boundary last head left) labels
              (.accepted tape) → False))) :=
  ⟨stopFree_to_penultimate path pre hscan boundary last head hboundary
      hshift left hhead,
    ⟨penultimate_oneStep path pre boundary last head hshift left,
      ⟨stopFree_to_stuck path pre hscan boundary last head hboundary
          hshift left hhead,
        no_accepting_path path pre hscan boundary last head hboundary
          hshift left hhead⟩⟩⟩

end PakFixedPolyomino.ULogConcreteRightBoundaryUnderflow
