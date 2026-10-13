import PakFixedPolyomino.ULogBootstrapMicroPrefix
import PakFixedPolyomino.ULogFiniteTapeNondeterministicMicroCounts

/-! A genuine first bootstrap hit preserves the count of ALL accepting
physical label words. The raw domain contains only actual physical paths;
no semantic expansion or selected-image certificate occurs in it. -/
namespace PakFixedPolyomino.ULogBootstrapAllMicroCounts
open ULogBootstrapExecution ULogConcreteChoiceBarrier ULogBootstrapMicroPrefix
open ULogFiniteTapeNondeterministicMicroCounts (RawAcceptingMicroWords)

theorem raw_split_iff {start finish : Result}
    (hit : FirstValidZeroHit IsConcreteCycleBoundary start finish)
    (outside : preChoiceResult start = false) (labels : List (Fin 2)) :
    (∃ tape, ConcreteMicroPath start labels (.accepted tape)) ↔
      ∃ rest, labels = List.replicate hit.steps (0 : Fin 2) ++ rest ∧
        ∃ tape, ConcreteMicroPath finish rest (.accepted tape) := by
  constructor
  · rintro ⟨tape, path⟩
    obtain ⟨rest, word, tail⟩ := (accepting_path_split_iff hit outside labels tape).1 path
    exact ⟨rest, word, tape, tail⟩
  · rintro ⟨rest, word, tape, tail⟩
    exact ⟨tape, (accepting_path_split_iff hit outside labels tape).2 ⟨rest, word, tail⟩⟩

theorem raw_card_eq {start finish : Result}
    (hit : FirstValidZeroHit IsConcreteCycleBoundary start finish)
    (outside : preChoiceResult start = false) :
    Nat.card (RawAcceptingMicroWords start) = Nat.card (RawAcceptingMicroWords finish) := by
  classical
  let zeroPrefix := List.replicate hit.steps (0 : Fin 2)
  let f : RawAcceptingMicroWords finish → RawAcceptingMicroWords start := fun raw =>
    ⟨zeroPrefix ++ raw.val, (raw_split_iff hit outside _).2 ⟨raw.val, rfl, raw.property⟩⟩
  have injective : Function.Injective f := by
    intro first last same
    have labels : zeroPrefix ++ first.val = zeroPrefix ++ last.val := congrArg Subtype.val same
    exact Subtype.ext (List.append_cancel_left labels)
  have surjective : Function.Surjective f := by
    intro raw
    obtain ⟨rest, word, accepts⟩ := (raw_split_iff hit outside raw.val).1 raw.property
    exact ⟨⟨rest, accepts⟩, Subtype.ext word.symm⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨injective, surjective⟩)).symm

end PakFixedPolyomino.ULogBootstrapAllMicroCounts
