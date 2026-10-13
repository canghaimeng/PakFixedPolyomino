import PakFixedPolyomino.ULogFiniteTapeNondeterministicMicroCounts

/-! Literal physical micro-label counts at a time cutoff. A proved bound
on ALL actual raw paths removes the cutoff; the raw subtype has no chosen
trace or semantic-image certificate. Concrete bounds are supplied by the
separate whole-program inverse and physical-fuel proof. -/
namespace PakFixedPolyomino.ULogConcreteMicroTimeCounts
open ULogBootstrapExecution ULogProgram
open ULogFiniteTapeNondeterministicMicroCounts (RawAcceptingMicroWords)

def RawAcceptingMicroWordsAtMost (T : Nat) (start : Result) : Type :=
  {labels : List (Fin 2) // labels.length ≤ T ∧
    ∃ tape : MStarParserExecution.Zipper Tape, ConcreteMicroPath start labels (.accepted tape)}

noncomputable def acceptingMicroPaths (T : Nat) (start : Result) : Nat :=
  Nat.card (RawAcceptingMicroWordsAtMost T start)

theorem common_time_count {start : Result} (B T : Nat)
    (bounded : ∀ labels tape, ConcreteMicroPath start labels (.accepted tape) → labels.length ≤ B)
    (time : B ≤ T) : acceptingMicroPaths T start = Nat.card (RawAcceptingMicroWords start) := by
  let e : RawAcceptingMicroWordsAtMost T start ≃ RawAcceptingMicroWords start :=
    { toFun := fun raw => ⟨raw.val, raw.property.2⟩
      invFun := fun raw => ⟨raw.val, by
        obtain ⟨tape, path⟩ := raw.property
        exact ⟨(bounded raw.val tape path).trans time, tape, path⟩⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  exact Nat.card_congr e

end PakFixedPolyomino.ULogConcreteMicroTimeCounts
