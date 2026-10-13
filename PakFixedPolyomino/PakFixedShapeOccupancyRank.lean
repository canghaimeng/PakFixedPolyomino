import PakFixedPolyomino.PakFixedShapeFlaggedReachability

/-! A rank determined by the literal state word, not a chosen placement
history. Every valid original helper step decreases it, and it is at most
the ORIGINAL square area on all original states. -/
namespace PakFixedPolyomino.PakFixedShapeOccupancyRank
noncomputable section
open TilingAnchoredChoices PakFixedWeightedShapeFamily PakFixedShapeChoiceWords
open PakFixedShapeFirstUncovered (scanCells firstUncovered first_some_mem)
open PakFixedShapeOccupancyScan (mask)
open PakFixedShapeFlaggedPreparation (state)
open PakFixedShapeFiniteLabelRound (L labelAt)
open PakFixedWeightedStandardBinaryCount (value)
local instance shapeDecidableEq : DecidableEq Shape := Classical.decEq _

def falseCount (w : List Bool) : Nat := w.countP (fun b => !b)
def rank (raw : List Bool) : Nat := falseCount (StandardBitWordVector.field 1 raw)

theorem scan_nodup (n : Nat) : (scanCells n).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro y hy
    apply (List.nodup_range (n:=n)).map
    intro x z he
    have h := congrArg Prod.fst he
    dsimp at h
    exact_mod_cast h
  · apply (List.nodup_range (n:=n)).imp
    intro y z hne c hc hd
    obtain ⟨x,_,he⟩ := List.mem_map.mp hc
    obtain ⟨w,_,hf⟩ := List.mem_map.mp hd
    have h := congrArg Prod.snd (he.trans hf.symm)
    dsimp at h
    apply hne
    exact_mod_cast h

theorem scan_toFinset (n : Nat) : (scanCells n).toFinset=square n := by
  ext c
  simp only [List.mem_toFinset,PakFixedShapeFirstUncovered.mem_scanCells]

theorem falseCount_mask (n : Nat) (done : Done) :
    falseCount (mask n done)=(uncovered shapeSupport (square n) done).card := by
  have hf : (square n).filter (fun c => c ∈ uncovered shapeSupport (square n) done)=
      uncovered shapeSupport (square n) done := by
    ext c
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨(Finset.mem_sdiff.mp h).1,h⟩⟩
  have h := (scan_nodup n).card_eq_countP (P:=fun c => c ∈ uncovered shapeSupport (square n) done)
  rw [scan_toFinset,hf] at h
  simpa only [falseCount,mask,List.countP_map,Function.comp_def,Bool.not_not] using h.symm

theorem rank_state (side : List Bool) (done : Done) :
    rank (state side done)=(uncovered shapeSupport (square (value side)) done).card := by
  simp only [rank,state,StandardBitWordVector.field_encode,List.getElem?_cons_succ,
    List.getElem?_cons_zero,Option.getD_some,falseCount_mask]

theorem rank_state_bound (side : List Bool) (done : Done) : rank (state side done)≤(value side)^2 := by
  rw [rank_state]
  exact PakFixedShapeAnchoredChoices.uncovered_card_bound (value side) done

theorem step_decreases (side : List Bool) (done : Done) (i : Fin L) (out : List Bool)
    (hr : PakFixedShapeFlaggedChoiceWords.step i (state side done)=some out) :
    rank out < rank (state side done) := by
  rw [PakFixedShapeFlaggedChoiceWords.step_original] at hr
  cases hc : firstUncovered (value side) done with
  | none => simp only [hc] at hr;contradiction
  | some c =>
    rw [hc] at hr
    change (if Fits (value side) done (placeAt c (labelAt i)) then
      some (state side (insert (placeAt c (labelAt i)) done)) else none)=some out at hr
    by_cases hf : Fits (value side) done (placeAt c (labelAt i))
    · rw [if_pos hf] at hr
      have he := Option.some.inj hr
      subst out
      rw [rank_state,rank_state]
      exact uncovered_strictly_decreases shapeSupport c (first_some_mem _ _ _ hc) (labelAt i)
    · simp only [if_neg hf] at hr
      contradiction

theorem rank_reachable_bound (side : List Bool) (done : Done) (is : List (Fin L)) (out : List Bool)
    (hr : PakFixedShapeFlaggedChoiceWords.run is (state side done)=some out) : rank out≤(value side)^2 := by
  obtain ⟨next,_,he⟩ := PakFixedShapeFlaggedReachability.original_output side done is out hr
  rw [he]
  exact rank_state_bound side next

theorem occupancy_rank_spec :
    (∀ side done,rank (state side done)≤(value side)^2) ∧
    (∀ side done i out,PakFixedShapeFlaggedChoiceWords.step i (state side done)=some out →
      rank out<rank (state side done)) ∧
    ∀ side done is out,PakFixedShapeFlaggedChoiceWords.run is (state side done)=some out → rank out≤(value side)^2 :=
  ⟨rank_state_bound,step_decreases,rank_reachable_bound⟩
end
end PakFixedPolyomino.PakFixedShapeOccupancyRank
