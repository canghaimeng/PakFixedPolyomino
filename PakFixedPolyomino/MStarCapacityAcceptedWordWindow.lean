import PakFixedPolyomino.MStarHashWindowPersistence
import PakFixedPolyomino.PakOuterULogTraceBridge

/-! Every actual accepted word from the literal capacity input supplies its
own complete padded uniform spatial run. Configurations are the real history,
and arrows are the entire original chronological word, without a caller
provided spatial certificate. The time dimension is the actual word length. -/
namespace PakFixedPolyomino.MStarCapacityAcceptedWordWindow
open PakMStarCouplingCorrectness PakGeneralCapacityInitialWindow
open PakSlotOneScannerMultiplicity MStarHashWindowPersistence
open PakOuterULogTraceBridge FiniteOneTapeSemantics

theorem history_configs_hash_interval (left right : Int)
    {start finish : Config} {labels : List Arrow}
    (H : OuterArrowHistory start labels finish) (hs : InHashInterval left right start) :
    ∀ t : Fin (labels.length + 1), InHashInterval left right (H.configAt t) := by
  have hall : ∀ i (hi : i < labels.length + 1),
      InHashInterval left right (H.configAt ⟨i, hi⟩) := by
    intro i
    induction i with
    | zero =>
      intro hi
      rw [OuterArrowHistory.configAt_zero]
      exact hs
    | succ i ih =>
      intro hi
      have ht : i < labels.length := by omega
      exact step_preserves_hash_interval left right _ _ _ (ih (by omega))
        (H.step_configAt ⟨i, ht⟩)
  intro t
  exact hall t.1 t.2

noncomputable def capacityAcceptedWordWindow (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x) (labels : List Arrow) (d : Config)
    (hr : run MStarULogAssembly.program MStarOuterProgram.movable labels
      (capacityEncodedStartConfig x cap) = some d)
    (hd : d.state = .accept) :
    PaddedUniformWindowedMStarRun (ConcretePakSide.sideValue x) labels.length := by
  let H := OuterArrowHistory.of_run_eq labels (capacityEncodedStartConfig x cap) d hr
  have hall := history_configs_hash_interval 0 (ConcretePakSide.sideValue x - 1 : Int)
    H (capacity_initial_hash_interval x cap)
  have side := PakSideScanner.sideValue_ge_five x
  let R : UniformWindowedMStarRun (ConcretePakSide.sideValue x) labels.length := {
    config := H.configAt
    arrow := H.arrowAt
    step := H.step_configAt
    origin := 0
    width_ge_three := by omega
    head_index := fun t => ⟨(H.configAt t).head.toNat, by
      obtain ⟨hl, hh, hz⟩ := hall t
      omega⟩
    head_eq := fun t => by
      obtain ⟨hl, hh, hz⟩ := hall t
      change (H.configAt t).head = 0 + ((H.configAt t).head.toNat : Int)
      omega
    head_interior_left := fun t => by
      obtain ⟨hl, hh, hz⟩ := hall t
      change 0 < (H.configAt t).head.toNat
      omega
    head_interior_right := fun t => by
      obtain ⟨hl, hh, hz⟩ := hall t
      change (H.configAt t).head.toNat + 1 < ConcretePakSide.sideValue x
      omega
    hash_outside := fun t z hz => (hall t).2.2 z (by
      rcases hz with hz | hz
      · exact Or.inl (by omega)
      · exact Or.inr (by omega))
    final_accept := by simpa using hd }
  refine ⟨R, ?_, ?_⟩
  · intro t
    exact (hall t).2.2 0 (Or.inl (by omega))
  · intro t
    apply (hall t).2.2
    right
    simp only [R, Int.zero_add]
    omega

theorem capacity_accepted_word_window_spec (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x) (labels : List Arrow) (d : Config)
    (hr : run MStarULogAssembly.program MStarOuterProgram.movable labels
      (capacityEncodedStartConfig x cap) = some d)
    (hd : d.state = .accept) :
    let W := capacityAcceptedWordWindow x cap labels d hr hd
    W.run.origin = 0 ∧
    W.run.config ⟨0, Nat.zero_lt_succ _⟩ = capacityEncodedStartConfig x cap ∧
    W.run.config ⟨labels.length, Nat.lt_succ_self _⟩ = d ∧
    (∀ t, W.run.arrow t = labels.get t) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact OuterArrowHistory.configAt_zero _
  · exact OuterArrowHistory.configAt_finish _
  · intro t
    rfl

def capacity_word_window_spec : Prop :=
  ∀ (x : ConcretePakSide.Word) (cap : ScannerCapacity x) (labels : List Arrow) (d : Config),
    run MStarULogAssembly.program MStarOuterProgram.movable labels
      (capacityEncodedStartConfig x cap) = some d → d.state = .accept →
    ∃ W : PaddedUniformWindowedMStarRun (ConcretePakSide.sideValue x) labels.length,
      W.run.origin = 0 ∧
      W.run.config ⟨0, Nat.zero_lt_succ _⟩ = capacityEncodedStartConfig x cap ∧
      W.run.config ⟨labels.length, Nat.lt_succ_self _⟩ = d ∧
      (∀ t, W.run.arrow t = labels.get t)

theorem capacity_word_window_spec_holds : capacity_word_window_spec := by
  intro x cap labels d hr hd
  exact ⟨capacityAcceptedWordWindow x cap labels d hr hd,
    capacity_accepted_word_window_spec x cap labels d hr hd⟩

end PakFixedPolyomino.MStarCapacityAcceptedWordWindow
