import PakFixedPolyomino.PakFixedShapeFeedbackDecoding

/-! Every raw accepting leaf of the actual finite feedback machine bijects
an original placement word and hence an exact tiling of the plain square. -/
namespace PakFixedPolyomino.PakFixedShapeFeedbackLeafEquivalence
noncomputable section
open StandardNondeterministicMachine
open PakFixedShapeNondeterministicPhases PakFixedShapeFeedbackEncoding PakFixedShapeFeedbackDecoding
open PakFixedShapeFiniteLabelRound (L)
open PakFixedShapeFlaggedPreparation (prepare state)

theorem encode_injective_on_terminating (raw : List Bool) (is js : List (Fin L))
    (hi : terminates raw is) (hj : terminates raw js) (he : encode raw is=encode raw js) : is=js := by
  induction is generalizing raw js with
  | nil =>
    cases js with
    | nil => rfl
    | cons j js =>
      have hp := (terminates_nil raw).mp hi
      have hq := (terminates_cons raw j js).mp hj
      rw [hp] at hq
      cases hq.1
  | cons i is ih =>
    cases js with
    | nil =>
      have hp := (terminates_nil raw).mp hj
      have hq := (terminates_cons raw i is).mp hi
      rw [hp] at hq
      cases hq.1
    | cons j js =>
      have hpath :
          PakFixedShapeNondeterministicRound.path (prepare raw).tail i++
            ([zero]++hword (checked raw i)++[zero]++encode (next raw i) is)=
          PakFixedShapeNondeterministicRound.path (prepare raw).tail j++
            ([zero]++hword (checked raw j)++[zero]++encode (next raw j) js) := by
        have he' := he
        simp only [encode,cycleWord,List.append_assoc] at he'
        have e1 := List.append_cancel_left he'
        have e2 := List.append_cancel_left e1
        have e3 := List.append_cancel_left e2
        have e4 := List.append_cancel_left e3
        simpa only [List.append_assoc] using e4
      have hu := (StandardMachineAcceptingPrefixUniqueness.accepting_prefix_unique
        roundMachine (initial roundMachine (prepare raw).tail) (mfinal raw i) (mfinal raw j)
        _ _ _ _ (round_path_run _ i) rfl (round_path_run _ j) rfl hpath).1
      have hij := PakFixedShapeNondeterministicRound.path_injective (prepare raw).tail hu
      subst j
      have hrest : encode (next raw i) is=encode (next raw i) js := List.append_cancel_left he
      exact congrArg (List.cons i) (ih _ _ (terminates_cons raw i is |>.mp hi).2.2
        (terminates_cons raw i js |>.mp hj).2.2 hrest)

def SemanticWord (raw : List Bool) := {is : List (Fin L) // terminates raw is}

def leafEquiv (raw : List Bool) : SemanticWord raw ≃ AcceptingLeaf machine raw where
  toFun w := ⟨encode raw w.val,encoded_accepted raw w.val w.property⟩
  invFun w := ⟨Classical.choose ((accepted_iff_encoding raw w.val).mp w.property),
    (Classical.choose_spec ((accepted_iff_encoding raw w.val).mp w.property)).1⟩
  left_inv w := by
    apply Subtype.ext
    have hs := Classical.choose_spec ((accepted_iff_encoding raw (encode raw w.val)).mp
      (encoded_accepted raw w.val w.property))
    exact encode_injective_on_terminating raw _ w.val hs.1 w.property hs.2.symm
  right_inv w := by
    apply Subtype.ext
    exact (Classical.choose_spec ((accepted_iff_encoding raw w.val).mp w.property)).2.symm

def originalLeafEquiv (side : List Bool) :
    PakFixedShapeFlaggedChoiceWords.AcceptedWord side ≃ AcceptingLeaf machine (state side ∅) :=
  leafEquiv (state side ∅)

def tilingLeafEquiv (side : List Bool) :
    Tiling PakFixedWeightedShapeFamily.shapeSupport
      (square (PakFixedWeightedStandardBinaryCount.value side)) ≃
        AcceptingLeaf machine (state side ∅) := by
  let e := Equiv.cast (congrArg
    (fun d : DecidableEq PakFixedWeightedShapeFamily.Shape =>
      @Tiling PakFixedWeightedShapeFamily.Shape d PakFixedWeightedShapeFamily.shapeSupport
        (square (PakFixedWeightedStandardBinaryCount.value side)))
    (Subsingleton.elim (fun a b => Subtype.instDecidableEq a b) (Classical.decEq _)))
  exact e.trans ((PakFixedShapeFlaggedChoiceWords.tilingWordEquiv side).trans (originalLeafEquiv side))

theorem squareCount_eq_leafCard (side : List Bool) :
    PakFixedWeightedShapeFamily.squareCount (PakFixedWeightedStandardBinaryCount.value side)=
      Nat.card (AcceptingLeaf machine (state side ∅)) := by
  calc
    _ = Fintype.card (PakFixedShapeFlaggedChoiceWords.AcceptedWord side) :=
      PakFixedShapeFlaggedChoiceWords.squareCount_eq_acceptedWordCount side
    _ = Nat.card (PakFixedShapeFlaggedChoiceWords.AcceptedWord side) := Nat.card_eq_fintype_card.symm
    _ = Nat.card (AcceptingLeaf machine (state side ∅)) := Nat.card_congr (originalLeafEquiv side)

theorem squareCount_eq_acceptingCount (side : List Bool) (bound : Nat)
    (ht : RunsAtMost machine (state side ∅) bound) :
    PakFixedWeightedShapeFamily.squareCount (PakFixedWeightedStandardBinaryCount.value side)=
      acceptingCount machine (state side ∅) bound := by
  rw [squareCount_eq_leafCard]
  exact (Nat.card_congr (acceptingLeavesEquiv machine (state side ∅) bound ht).symm).trans
    Nat.card_eq_fintype_card

end
end PakFixedPolyomino.PakFixedShapeFeedbackLeafEquivalence
