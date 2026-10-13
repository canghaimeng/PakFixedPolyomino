import PakFixedPolyomino.ULogClockCycleExecution

/-! Dynamic zero/one/blank runtime paths for repeated universal cycles. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def PayloadCell (x : Tape) : Prop :=
  x = payloadTape false ∨ x = payloadTape true ∨
    x = ulogCore payloadBlank

def PayloadPathSafe (path : List Tape) : Prop :=
  ∀ x ∈ path, PayloadCell x

theorem clockSeek_payloadCell_step (x : Tape) (hx : PayloadCell x)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running .clockSeek ⟨left, x, y :: right⟩) =
      .running .clockSeek ⟨x :: left, y, right⟩ := by
  rcases hx with rfl | rfl | rfl
  · exact clockSeek_payload_step false left y right
  · exact clockSeek_payload_step true left y right
  · exact clockSeek_blank_step left y right

theorem clockReturn_payloadCell_step (x : Tape) (hx : PayloadCell x)
    (left : List Tape) (y : Tape) (right : List Tape) :
    oneStep (.running .clockReturn ⟨y :: left, x, right⟩) =
      .running .clockReturn ⟨left, y, x :: right⟩ := by
  rcases hx with rfl | rfl | rfl
  · exact clockReturn_payload_step false left y right
  · exact clockReturn_payload_step true left y right
  · exact clockReturn_blank_step left y right

def runtimeClockReturnPath (k : ℕ) (payloadPath : List Tape) : List Tape :=
  List.replicate k (ulogCore clockOne) ++ payloadPath.reverse

theorem runtimeClockReturnPath_pass (k : ℕ) (payloadPath : List Tape)
    (hsafe : PayloadPathSafe payloadPath) (x : Tape)
    (hx : x ∈ runtimeClockReturnPath k payloadPath) (left : List Tape)
    (y : Tape) (right : List Tape) :
    oneStep (.running .clockReturn ⟨y :: left, x, right⟩) =
      .running .clockReturn ⟨left, y, x :: right⟩ := by
  simp only [runtimeClockReturnPath, List.mem_append,
    List.mem_replicate, List.mem_reverse] at hx
  rcases hx with hclock | hpayload
  · rw [hclock.2]
    exact clockReturn_clock_step true left y right
  · exact clockReturn_payloadCell_step x (hsafe x hpayload) left y right

theorem runtimeClockReturnPath_reverse (k : ℕ)
    (payloadPath : List Tape) :
    (runtimeClockReturnPath k payloadPath).reverse =
      payloadPath ++ List.replicate k (ulogCore clockOne) := by
  simp [runtimeClockReturnPath, List.reverse_append, List.append_assoc]

theorem reaches_clockDecrementCells (head : Tape)
    (hhead : choiceHead head = true) (k : ℕ) (payloadPath : List Tape)
    (hsafe : PayloadPathSafe payloadPath) (left suffix : List Tape) :
    Reaches
      (.running .cycleStart
        ⟨left, head,
          payloadPath ++ List.replicate k (ulogCore clockZero) ++
            ulogCore clockOne :: suffix⟩)
      (.running .chooseSlot
        ⟨left, head,
          payloadPath ++ List.replicate k (ulogCore clockOne) ++
            ulogCore clockZero :: suffix⟩) := by
  let firstClock := if k = 0 then ulogCore clockOne else ulogCore clockZero
  let clockTail := match k with
    | 0 => suffix
    | n + 1 => List.replicate n (ulogCore clockZero) ++
        ulogCore clockOne :: suffix
  have hcycle : Reaches
      (.running .cycleStart
        ⟨left, head, payloadPath ++ firstClock :: clockTail⟩)
      (.running .clockSeek
        (beforeRightPath payloadPath (head :: left) firstClock clockTail)) := by
    apply reaches_step
    cases payloadPath <;> cases k <;>
      simp [firstClock, clockTail, beforeRightPath,
        cycleStart_head_step head hhead, List.replicate_succ,
        List.append_assoc]
  have hscan : Reaches
      (.running .clockSeek
        (beforeRightPath payloadPath (head :: left) firstClock clockTail))
      (.running .clockSeek
        (afterRightPath payloadPath (head :: left) firstClock clockTail)) := by
    exact ⟨payloadPath.length,
      run_right_path_of .clockSeek payloadPath (by
        intro x hx l y r
        exact clockSeek_payloadCell_step x (hsafe x hx) l y r)
      (head :: left) firstClock clockTail⟩
  have hdec : Reaches
      (.running .clockSeek
        (afterRightPath payloadPath (head :: left) firstClock clockTail))
      (.running .clockReturn
        (beforeLeftPath (runtimeClockReturnPath k payloadPath) left head
          (ulogCore clockZero :: suffix))) := by
    cases k with
    | zero =>
        apply reaches_step
        simpa [firstClock, clockTail, afterRightPath,
          runtimeClockReturnPath, List.append_assoc] using
          (clockSeek_one_over_path payloadPath.reverse left head suffix)
    | succ k =>
        have h₀ : Reaches
            (.running .clockSeek
              (afterRightPath payloadPath (head :: left) firstClock clockTail))
            (.running .clockConsume
              (beforeConsumeZeros k
                (ulogCore clockOne :: payloadPath.reverse ++ head :: left)
                suffix)) := by
          apply reaches_step
          cases k <;>
            simp [firstClock, clockTail, afterRightPath,
              beforeConsumeZeros, clockSeek_zero_step,
              List.replicate_succ, List.append_assoc]
        have h₁ : Reaches
            (.running .clockConsume
              (beforeConsumeZeros k
                (ulogCore clockOne :: payloadPath.reverse ++ head :: left)
                suffix))
            (.running .clockConsume
              (afterConsumeZeros k
                (ulogCore clockOne :: payloadPath.reverse ++ head :: left)
                suffix)) :=
          ⟨k, run_clockConsume_zeros k _ _⟩
        have h₂ : Reaches
            (.running .clockConsume
              (afterConsumeZeros k
                (ulogCore clockOne :: payloadPath.reverse ++ head :: left)
                suffix))
            (.running .clockReturn
              (beforeLeftPath (runtimeClockReturnPath (k + 1) payloadPath)
                left head (ulogCore clockZero :: suffix))) := by
          apply reaches_step
          simpa [afterConsumeZeros, runtimeClockReturnPath,
            List.replicate_succ', List.append_assoc] using
            (clockConsume_one_over_path
              (runtimeClockReturnPath (k + 1) payloadPath) left head suffix)
        exact reaches_trans h₀ (reaches_trans h₁ h₂)
  have hreturn : Reaches
      (.running .clockReturn
        (beforeLeftPath (runtimeClockReturnPath k payloadPath) left head
          (ulogCore clockZero :: suffix)))
      (.running .clockReturn
        (afterLeftPath (runtimeClockReturnPath k payloadPath) left head
          (ulogCore clockZero :: suffix))) :=
    ⟨(runtimeClockReturnPath k payloadPath).length,
      run_left_path_of .clockReturn (runtimeClockReturnPath k payloadPath)
        (runtimeClockReturnPath_pass k payloadPath hsafe) left head
        (ulogCore clockZero :: suffix)⟩
  have hheadReturn : Reaches
      (.running .clockReturn
        (afterLeftPath (runtimeClockReturnPath k payloadPath) left head
          (ulogCore clockZero :: suffix)))
      (.running .chooseSlot
        ⟨left, head,
          payloadPath ++ List.replicate k (ulogCore clockOne) ++
            ulogCore clockZero :: suffix⟩) := by
    apply reaches_step
    simpa [afterLeftPath, runtimeClockReturnPath_reverse,
      List.append_assoc] using
      clockReturn_head_step head hhead left
        (payloadPath ++ List.replicate k (ulogCore clockOne) ++
          ulogCore clockZero :: suffix)
  have hall := reaches_trans hcycle (reaches_trans hscan
    (reaches_trans hdec (reaches_trans hreturn hheadReturn)))
  cases k <;>
    simpa [firstClock, clockTail, List.replicate_succ,
      List.append_assoc] using hall

end PakFixedPolyomino.ULogBootstrapExecution
