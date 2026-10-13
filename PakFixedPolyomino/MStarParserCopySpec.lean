import PakFixedPolyomino.MStarOuterProgram
import PakFixedPolyomino.ConcretePakSideEncoding
import Mathlib.Tactic

/-!
# Executable word-level parser/copy specification for `M_star`

This is the functional specification that the future deterministic one-tape
`parserStep` must refine.  It fixes the exact parse language and the exact
two-sided copied workspace, so the remaining low-level implementation cannot
silently choose a different delimiter order or buffer length.
-/

namespace PakFixedPolyomino.MStarParserCopySpec

open ConcretePakSide MStarOuterProgram

inductive MacroPhase where
  | countPadding
  | expectPaddingSeparator
  | countPayloadLength
  | expectLengthSeparator
  | readPayload
  | expectLeadingOne
  | checkHighZero
  | placeLeftMark
  | writeLeftBuffer
  | copyPayload
  | writeRightBuffer
  | placeRightMark
  | restoreScratch
  | enterSimulation
  deriving DecidableEq, Repr

instance : Fintype MacroPhase := Fintype.ofList
  [.countPadding, .expectPaddingSeparator, .countPayloadLength,
    .expectLengthSeparator, .readPayload, .expectLeadingOne, .checkHighZero,
    .placeLeftMark, .writeLeftBuffer, .copyPayload, .writeRightBuffer,
    .placeRightMark, .restoreScratch, .enterSimulation] (by
      intro p
      cases p <;> simp)

/-- `p_U(m)=8(m+1)`. -/
def timeExponent (m : ℕ) : ℕ := 8 * (m + 1)

/-- `W_sp=2^{p_U(m)}+1`. -/
def workspaceRadius (m : ℕ) : ℕ := 2 ^ timeExponent m + 1

def bitLetter {UTape : Type*} (zero one : UTape) : Bool → UTape
  | false => zero
  | true => one

/-- The exact marked tape segment produced by a successful copy. -/
def copiedWorkspace {UTape : Type*}
    (zero one work : UTape) (x : ConcretePakSide.Word) :
    List (MStarOuterProgram.Tape UTape) :=
  .markL ::
    List.replicate (workspaceRadius x.length) (.core work) ++
    x.map (fun b => .core (bitLetter zero one b)) ++
    List.replicate (workspaceRadius x.length) (.core work) ++
    [.markR]

@[simp] theorem copiedWorkspace_length {UTape : Type*}
    (zero one work : UTape) (x : ConcretePakSide.Word) :
    (copiedWorkspace zero one work x).length =
      2 * workspaceRadius x.length + x.length + 2 := by
  simp [copiedWorkspace]
  omega

@[simp] theorem copiedWorkspace_head {UTape : Type*}
    (zero one work : UTape) (x : ConcretePakSide.Word) :
    (copiedWorkspace zero one work x).head? = some .markL := by
  simp [copiedWorkspace]

theorem copiedWorkspace_payload {UTape : Type*}
    (zero one work : UTape) (x : ConcretePakSide.Word) :
    ((copiedWorkspace zero one work x).drop (workspaceRadius x.length + 1)).take x.length =
      x.map (fun b => .core (bitLetter zero one b)) := by
  simp [copiedWorkspace]

theorem copiedWorkspace_left_buffer {UTape : Type*}
    (zero one work : UTape) (x : ConcretePakSide.Word) :
    ((copiedWorkspace zero one work x).drop 1).take (workspaceRadius x.length) =
      List.replicate (workspaceRadius x.length) (.core work) := by
  simp [copiedWorkspace]

theorem copiedWorkspace_right_buffer {UTape : Type*}
    (zero one work : UTape) (x : ConcretePakSide.Word) :
    ((copiedWorkspace zero one work x).drop
      (workspaceRadius x.length + 1 + x.length)).take (workspaceRadius x.length) =
      List.replicate (workspaceRadius x.length) (.core work) := by
  let pre : List (MStarOuterProgram.Tape UTape) :=
    .markL :: List.replicate (workspaceRadius x.length) (.core work) ++
      x.map (fun b => .core (bitLetter zero one b))
  have hform : copiedWorkspace zero one work x =
      pre ++ (List.replicate (workspaceRadius x.length) (.core work) ++ [.markR]) := by
    simp [copiedWorkspace, pre, List.append_assoc]
  have hlen : pre.length = workspaceRadius x.length + 1 + x.length := by
    simp [pre]
    omega
  rw [hform, List.drop_left' hlen]
  simp

theorem copiedWorkspace_last {UTape : Type*}
    (zero one work : UTape) (x : ConcretePakSide.Word) :
    (copiedWorkspace zero one work x).getLast? = some .markR := by
  let pre : List (MStarOuterProgram.Tape UTape) :=
    .markL :: List.replicate (workspaceRadius x.length) (.core work) ++
      x.map (fun b => .core (bitLetter zero one b)) ++
      List.replicate (workspaceRadius x.length) (.core work)
  have hform : copiedWorkspace zero one work x = pre ++ [.markR] := by
    simp [copiedWorkspace, pre, List.append_assoc]
  rw [hform, List.getLast?_append_of_ne_nil pre (by simp)]
  simp

/-- Successful word-level parsing followed by copying. -/
def parseAndCopy {UTape : Type*}
    (zero one work : UTape) (w : ConcretePakSide.Word) :
    Option (List (MStarOuterProgram.Tape UTape)) :=
  (ConcretePakSide.decodeWord w).map (copiedWorkspace zero one work)

@[simp] theorem parseAndCopy_encoded {UTape : Type*}
    (zero one work : UTape) (x : ConcretePakSide.Word) :
    parseAndCopy zero one work (ConcretePakSide.encodedWord x) =
      some (copiedWorkspace zero one work x) := by
  simp [parseAndCopy]

theorem parseAndCopy_sound {UTape : Type*}
    {zero one work : UTape} {w : ConcretePakSide.Word}
    {out : List (MStarOuterProgram.Tape UTape)}
    (h : parseAndCopy zero one work w = some out) :
    ∃ x, ConcretePakSide.encodedWord x = w ∧
      out = copiedWorkspace zero one work x := by
  unfold parseAndCopy at h
  cases hd : ConcretePakSide.decodeWord w with
  | none => simp [hd] at h
  | some x =>
      have hw := ConcretePakSide.decodeWord_sound hd
      simp [hd] at h
      exact ⟨x, hw, h.symm⟩

theorem parseAndCopy_output_unique {UTape : Type*}
    (zero one work : UTape) (w : ConcretePakSide.Word)
    {a b : List (MStarOuterProgram.Tape UTape)}
    (ha : parseAndCopy zero one work w = some a)
    (hb : parseAndCopy zero one work w = some b) : a = b := by
  rw [ha] at hb
  exact Option.some.inj hb

end PakFixedPolyomino.MStarParserCopySpec
