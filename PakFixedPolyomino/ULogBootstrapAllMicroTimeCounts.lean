import PakFixedPolyomino.ULogBootstrapAllMicroCounts
import PakFixedPolyomino.ULogConcreteMicroTimeCounts

/-! Genuine bootstrap first hits shift ALL physical word cutoffs exactly.
No chosen expansion or semantic-image predicate occurs in the counted domain. -/
namespace PakFixedPolyomino.ULogBootstrapAllMicroTimeCounts
open ULogBootstrapExecution ULogConcreteChoiceBarrier ULogBootstrapMicroPrefix
open ULogBootstrapAllMicroCounts ULogConcreteMicroTimeCounts

theorem cutoff_count_shift {start finish : Result}
    (hit : FirstValidZeroHit IsConcreteCycleBoundary start finish)
    (outside : preChoiceResult start = false) (T : Nat) :
    acceptingMicroPaths (hit.steps + T) start = acceptingMicroPaths T finish := by
  classical
  let zeroPrefix := List.replicate hit.steps (0 : Fin 2)
  let f : RawAcceptingMicroWordsAtMost T finish →
      RawAcceptingMicroWordsAtMost (hit.steps + T) start := fun raw =>
    ⟨zeroPrefix ++ raw.val, by
      constructor
      · simpa only [zeroPrefix, List.length_append, List.length_replicate] using
          Nat.add_le_add_left raw.property.1 hit.steps
      · exact (raw_split_iff hit outside _).2 ⟨raw.val, rfl, raw.property.2⟩⟩
  have injective : Function.Injective f := by
    intro first last same
    exact Subtype.ext (List.append_cancel_left (congrArg Subtype.val same))
  have surjective : Function.Surjective f := by
    intro raw
    obtain ⟨rest, word, accepts⟩ := (raw_split_iff hit outside raw.val).1 raw.property.2
    have length : rest.length ≤ T := by
      have bounded := raw.property.1
      rw [word] at bounded
      simp only [List.length_append, List.length_replicate] at bounded
      omega
    exact ⟨⟨rest, length, accepts⟩, Subtype.ext word.symm⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨injective, surjective⟩)).symm

theorem cutoff_count_zero_before_hit {start finish : Result}
    (hit : FirstValidZeroHit IsConcreteCycleBoundary start finish)
    (outside : preChoiceResult start = false) (T : Nat) (early : T < hit.steps) :
    acceptingMicroPaths T start = 0 := by
  let : IsEmpty (RawAcceptingMicroWordsAtMost T start) := ⟨by
    intro raw
    obtain ⟨rest, word, _⟩ := (raw_split_iff hit outside raw.val).1 raw.property.2
    have bounded := raw.property.1
    rw [word] at bounded
    simp only [List.length_append, List.length_replicate] at bounded
    omega⟩
  exact Nat.card_of_isEmpty

theorem all_path_length_transfer {start finish : Result}
    (hit : FirstValidZeroHit IsConcreteCycleBoundary start finish)
    (outside : preChoiceResult start = false) (P Q : Nat) (prefixBound : hit.steps ≤ P)
    (suffixBound : ∀ labels tape, ConcreteMicroPath finish labels (.accepted tape) →
      labels.length ≤ Q) (labels : List (Fin 2)) (tape : MStarParserExecution.Zipper ULogProgram.Tape)
    (path : ConcreteMicroPath start labels (.accepted tape)) : labels.length ≤ P + Q := by
  obtain ⟨rest, word, tail⟩ := (accepting_path_split_iff hit outside labels tape).1 path
  rw [word]
  simpa only [List.length_append, List.length_replicate] using
    Nat.add_le_add prefixBound (suffixBound rest tape tail)

end PakFixedPolyomino.ULogBootstrapAllMicroTimeCounts
