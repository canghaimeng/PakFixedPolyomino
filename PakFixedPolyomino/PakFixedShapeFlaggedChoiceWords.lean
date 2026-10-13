import PakFixedPolyomino.PakFixedShapeFlaggedPreparation

/-! The actual flagged helper maps implement the ORIGINAL literal-label
choice algorithm, on every side word including zero and redundant zero bits.
This establishes the reference loop's full accepted-word count. A finite
nondeterministic feedback machine and its raw-slot inverse remain separate. -/
set_option maxHeartbeats 1000000
namespace PakFixedPolyomino.PakFixedShapeFlaggedChoiceWords
noncomputable section
open Computability StandardBitTime StandardBitMetric PakFixedWeightedShapeFamily TilingAnchoredChoices
open PakFixedShapeChoiceWords
open PakFixedWeightedStandardBinaryCount (value)
open PakFixedShapeFiniteLabelRound (L labelAt)
open PakFixedShapeFlaggedPreparation (state prepare)
local instance shapeDecidableEq : DecidableEq Shape := Classical.decEq _

def step (i : Fin L) (raw : List Bool) : Option (List Bool) :=
  if (prepare raw).headD false then
    let out := PakFixedShapeFiniteLabelRound.round
      (pairBits (StandardBitFiniteChoicePrefix.labelCode L i) (prepare raw).tail)
    if out.headD false then some out.tail else none
  else none

def run : List (Fin L) → List Bool → Option (List Bool)
  | [], raw => some raw
  | i::is, raw => (step i raw).bind (run is)

def accepts (side : List Bool) (is : List (Fin L)) : Prop :=
  (run is (state side ∅)).map (fun raw => (prepare raw).headD false)=some false

theorem step_original (side : List Bool) (done : Done) (i : Fin L) :
    step i (state side done)=
      match PakFixedShapeFirstUncovered.firstUncovered (value side) done with
      | none => none
      | some c => if Fits (value side) done (placeAt c (labelAt i)) then
          some (state side (insert (placeAt c (labelAt i)) done)) else none := by
  cases hc : PakFixedShapeFirstUncovered.firstUncovered (value side) done with
  | none =>
    have hb := (PakFixedShapeFlaggedPreparation.stops_iff side done).mpr hc
    simp only [step,hb,Bool.false_eq_true,if_false]
  | some c =>
    have hb : (prepare (state side done)).headD false=true := by
      by_contra h
      have hn := (PakFixedShapeFlaggedPreparation.stops_iff side done).mp (Bool.eq_false_iff.mpr h)
      rw [hc] at hn
      contradiction
    have he := PakFixedShapeFlaggedPreparation.original_coordinate side done hb
    rw [hc] at he
    have hcoord := Option.some.inj he
    subst c
    rw [step,hb,if_pos rfl,PakFixedShapeFlaggedPreparation.prepare_original,
      List.tail_cons,PakFixedShapeFiniteLabelRound.round_code]
    by_cases hf : Fits (value side) done
        (placeAt (((StandardBitFirstZero.index (PakFixedShapeOccupancyScan.mask (value side) done)%value side : Nat) : Int),
          ((StandardBitFirstZero.index (PakFixedShapeOccupancyScan.mask (value side) done)/value side : Nat) : Int)) (labelAt i))
    · rw [PakFixedShapeFiniteLabelRound.checked_frame_valid side done _ _ (labelAt i) hf]
      simp only [List.headD_cons,List.tail_cons,if_pos hf,if_true,state]
    · rw [PakFixedShapeFiniteLabelRound.checked_frame_invalid side done _ _ (labelAt i) hf]
      simp only [List.headD_cons,Bool.false_eq_true,if_false,if_neg hf]

theorem run_original (side : List Bool) (done : Done) (is : List (Fin L)) :
    run is (state side done)=
      (PakFixedShapeChoiceWords.run (value side) (is.map labelAt) done).map (state side) := by
  induction is generalizing done with
  | nil => rfl
  | cons i is ih =>
    rw [run,step_original,List.map_cons,PakFixedShapeChoiceWords.run]
    cases hc : PakFixedShapeFirstUncovered.firstUncovered (value side) done with
    | none => rfl
    | some c =>
      by_cases hf : Fits (value side) done (placeAt c (labelAt i))
      · simp only [if_pos hf,Option.bind_some]
        exact ih _
      · simp only [if_neg hf,Option.bind_none,Option.map_none]

theorem accepts_original (side : List Bool) (is : List (Fin L)) :
    accepts side is ↔ PakFixedShapeChoiceWords.accepts (value side) (is.map labelAt) := by
  unfold accepts PakFixedShapeChoiceWords.accepts
  rw [run_original]
  cases hr : PakFixedShapeChoiceWords.run (value side) (is.map labelAt) ∅ with
  | none => simp
  | some done =>
    simpa only [Option.map_some,Option.some.injEq] using
      PakFixedShapeFlaggedPreparation.stops_iff side done

def labelEquiv : Fin L ≃ Label := (Fintype.equivFin Label).symm
def wordEquiv : List (Fin L) ≃ List Label where
  toFun := List.map labelEquiv
  invFun := List.map labelEquiv.symm
  left_inv is := by simp only [List.map_map,Function.comp_def,Equiv.symm_apply_apply,List.map_id']
  right_inv as := by simp only [List.map_map,Function.comp_def,Equiv.apply_symm_apply,List.map_id']

theorem wordEquiv_apply (is : List (Fin L)) : wordEquiv is=is.map labelAt := rfl

def AcceptedWord (side : List Bool) := {is : List (Fin L) // accepts side is}

def acceptedWordEquiv (side : List Bool) : AcceptedWord side ≃ RawAcceptedWord (value side) where
  toFun w := ⟨wordEquiv w.val,(accepts_original side w.val).mp w.property⟩
  invFun w := ⟨wordEquiv.symm w.val,(accepts_original side _).mpr (by
    simpa only [← wordEquiv_apply,Equiv.apply_symm_apply] using w.property)⟩
  left_inv w := Subtype.ext (wordEquiv.symm_apply_apply w.val)
  right_inv w := Subtype.ext (wordEquiv.apply_symm_apply w.val)

def tilingWordEquiv (side : List Bool) :
    Tiling shapeSupport (square (value side)) ≃ AcceptedWord side :=
  (PakFixedShapeChoiceWords.rawTilingWordEquiv (value side)).trans (acceptedWordEquiv side).symm

instance acceptedWordFintype (side : List Bool) : Fintype (AcceptedWord side) :=
  Fintype.ofEquiv (RawAcceptedWord (value side)) (acceptedWordEquiv side).symm

theorem squareCount_eq_acceptedWordCount (side : List Bool) :
    squareCount (value side)=Fintype.card (AcceptedWord side) :=
  (squareCount_eq_rawWordCount (value side)).trans (Fintype.card_congr (acceptedWordEquiv side).symm)

theorem accepted_length_le (side : List Bool) (is : List (Fin L))
    (h : accepts side is) : is.length≤(value side)^2 := by
  have hb := (choice_word_spec (value side)).2.2 (is.map labelAt)
    ((accepts_original side is).mp h)
  simpa only [List.length_map] using hb

theorem successful_prefix_length_le (side : List Bool) (done : Done)
    (is : List (Fin L)) (out : List Bool) (h : run is (state side done)=some out) :
    is.length≤(value side)^2 := by
  rw [run_original] at h
  cases hr : PakFixedShapeChoiceWords.run (value side) (is.map labelAt) done with
  | none => simp only [hr,Option.map_none] at h; contradiction
  | some next =>
    simpa only [List.length_map] using run_square_bound (value side) (is.map labelAt) done next hr

theorem flagged_choice_word_spec (side : List Bool) :
    (∀ is,accepts side is ↔ PakFixedShapeChoiceWords.accepts (value side) (is.map labelAt)) ∧
    squareCount (value side)=Fintype.card (AcceptedWord side) ∧
    (∀ is,accepts side is → is.length≤(value side)^2) ∧
    (∀ done is out,run is (state side done)=some out → is.length≤(value side)^2) :=
  ⟨accepts_original side,squareCount_eq_acceptedWordCount side,
    accepted_length_le side,successful_prefix_length_le side⟩

end
end PakFixedPolyomino.PakFixedShapeFlaggedChoiceWords
