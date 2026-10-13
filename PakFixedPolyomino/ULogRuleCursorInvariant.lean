import PakFixedPolyomino.ULogRuleCursorAdvance

/-! Cursor normalization and safety under one skipped RuleCode. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def nextSourceBoundary (b : Bool) : ULogLetter :=
  if b then sourceBoundaryOne else sourceBoundaryZero

@[simp] theorem mismatchBoundaryTape_eq_next (b : Bool) :
    mismatchBoundaryTape b = ulogCore (nextSourceBoundary b) := by
  cases b <;> rfl

theorem nextSourceBoundary_valid (b : Bool) :
    nextSourceBoundary b = sourceBoundary ∨
      nextSourceBoundary b = sourceBoundaryZero ∨
        nextSourceBoundary b = sourceBoundaryOne := by
  cases b <;> simp [nextSourceBoundary]

def advanceMismatchPath (r : ULogBytecode.RuleCode)
    (boundary : ULogLetter) (path : List Tape) : List Tape :=
  path ++
    (if boundary = sourceBoundaryZero then ulogCore codeZero
      else ulogCore codeOne) :: (mismatchRulePrefix r).tail.reverse

theorem mismatchRulePrefix_tail_code (r : ULogBytecode.RuleCode)
    (x : Tape) (hx : x ∈ (mismatchRulePrefix r).tail) :
    ∃ b, x = codeTape b := by
  rcases r with ⟨source, read, slot, ⟨write, target, move⟩⟩
  simp only [mismatchRulePrefix, List.tail_cons] at hx
  rcases List.mem_cons.mp hx with hmove | hx
  · exact ⟨moveFirst move, hmove⟩
  rcases List.mem_append.mp hx with hbefore | hsource
  · rcases List.mem_append.mp hbefore with htw | hslotRead
    · rcases List.mem_append.mp htw with htarget | hwrite
      · rcases List.mem_map.mp htarget with ⟨b, -, rfl⟩
        exact ⟨b, rfl⟩
      · rcases List.mem_map.mp hwrite with ⟨b, -, rfl⟩
        exact ⟨b, rfl⟩
    · rcases List.mem_cons.mp hslotRead with hslot | hread
      · exact ⟨slot, hslot⟩
      · rcases List.mem_map.mp hread with ⟨b, -, rfl⟩
        exact ⟨b, rfl⟩
  · rcases List.mem_map.mp hsource with ⟨b, -, rfl⟩
    exact ⟨b, rfl⟩

theorem mismatchRulePrefix_tail_safe (r : ULogBytecode.RuleCode) :
    MismatchAdvancePathSafe (mismatchRulePrefix r).tail := by
  constructor <;> intro x hx
  · rcases mismatchRulePrefix_tail_code r x hx with ⟨b, rfl⟩
    cases b <;> decide
  · rcases mismatchRulePrefix_tail_code r x hx with ⟨b, rfl⟩
    cases b <;> decide

theorem advanceMismatchPath_safe (r : ULogBytecode.RuleCode)
    (boundary : ULogLetter) (path : List Tape)
    (hpath : MismatchAdvancePathSafe path) :
    MismatchAdvancePathSafe (advanceMismatchPath r boundary path) := by
  constructor <;> intro x hx
  · unfold advanceMismatchPath at hx
    rcases List.mem_append.mp hx with hp | ht
    · exact hpath.1 x hp
    · rcases List.mem_cons.mp ht with hrestored | hrule
      · rw [hrestored]
        split <;> native_decide
      · have hrule' : x ∈ (mismatchRulePrefix r).tail := by
          simpa using hrule
        exact (mismatchRulePrefix_tail_safe r).1 x hrule'
  · unfold advanceMismatchPath at hx
    rcases List.mem_append.mp hx with hp | ht
    · exact hpath.2 x hp
    · rcases List.mem_cons.mp ht with hrestored | hrule
      · rw [hrestored]
        split <;> native_decide
      · have hrule' : x ∈ (mismatchRulePrefix r).tail := by
          simpa using hrule
        exact (mismatchRulePrefix_tail_safe r).2 x hrule'

theorem ruleCursor_advance_left_eq (done : ℕ)
    (path : List Tape) (r : ULogBytecode.RuleCode)
    (boundary : ULogLetter) (outer : List Tape) :
    mismatchRulePrefix r ++
          (if boundary = sourceBoundaryZero then ulogCore codeZero
            else ulogCore codeOne) :: (ulogCore pcDone :: path).reverse ++
          ulogCore codeZero ::
            List.replicate done (ulogCore codeZero) ++
              ulogCore pcMark :: outer =
      ulogCore (nextSourceBoundary (moveSecond r.action.move)) ::
        (List.replicate (done + 1) (ulogCore codeZero) ++
          ulogCore pcDone ::
            advanceMismatchPath r boundary path).reverse ++
          ulogCore pcMark :: outer := by
  rcases r with ⟨source, read, slot, ⟨write, target, move⟩⟩
  simp [mismatchRulePrefix, mismatchBoundaryTape_eq_next,
    advanceMismatchPath, List.reverse_append, List.replicate_succ',
    List.append_assoc]

end PakFixedPolyomino.ULogBootstrapExecution
