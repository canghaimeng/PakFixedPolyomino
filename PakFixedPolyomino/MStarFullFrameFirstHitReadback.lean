import PakFixedPolyomino.MStarFixedWidthFirstHitEquiv

/-! The full frame supplies exactly its chronological number of occupied
arrows. Its first-hit boundary and acceptance padding are extracted from every
actual frame, without assuming that an earlier fuel bound is its exact length.
-/
namespace PakFixedPolyomino.MStarFullFrameFirstHitReadback
open PakMStarCouplingCorrectness PakFullFrameTableauReadback
open FiniteOneTapeSemantics MStarFirstHitPadding MStarAcceptPaddingWords
open MStarFixedWidthFirstHitEquiv

theorem chronological_word_run {n : Nat}
    (config : Fin (n + 1) → MStarConfig) (arrow : Fin n → MStarULogAssembly.Arrow)
    (hs : ∀ j : Fin n,
      step MStarULogAssembly.program MStarOuterProgram.movable
        (config ⟨j.1, Nat.lt_succ_of_lt j.2⟩) (arrow j) =
        some (config ⟨j.1 + 1, by omega⟩)) :
    run MStarULogAssembly.program MStarOuterProgram.movable (List.ofFn arrow)
      (config ⟨0, Nat.zero_lt_succ n⟩) =
        some (config ⟨n, Nat.lt_succ_self n⟩) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hzero : step MStarULogAssembly.program MStarOuterProgram.movable
          (config ⟨0, by omega⟩) (arrow 0) = some (config ⟨1, by omega⟩) := by
        simpa using hs (0 : Fin (n + 1))
      rw [List.ofFn_succ, run_cons, hzero, Option.bind_some]
      exact ih (fun j => config j.succ) (fun j => arrow j.succ)
        (fun j => by simpa using hs j.succ)

noncomputable def frameWord {w h : Nat} (F : FullFrame w h) :
    List MStarULogAssembly.Arrow := List.ofFn (FullFrame.toUniformWindowedRun F).arrow

theorem frame_word_length {w h : Nat} (F : FullFrame w h) :
    (frameWord F).length = w := by simp [frameWord]

theorem frame_word_run {w h : Nat} (F : FullFrame w h) :
    run MStarULogAssembly.program MStarOuterProgram.movable (frameWord F)
      ((FullFrame.toUniformWindowedRun F).config ⟨0, Nat.zero_lt_succ w⟩) =
        some ((FullFrame.toUniformWindowedRun F).config ⟨w, Nat.lt_succ_self w⟩) :=
  chronological_word_run _ _ (FullFrame.toUniformWindowedRun F).step

noncomputable def frameAcceptedWord {w h : Nat} (F : FullFrame w h) :
    AcceptedWordsAtLength
      ((FullFrame.toUniformWindowedRun F).config ⟨0, Nat.zero_lt_succ w⟩) w :=
  ⟨frameWord F, frame_word_length F,
    (FullFrame.toUniformWindowedRun F).config ⟨w, Nat.lt_succ_self w⟩,
    frame_word_run F, (FullFrame.toUniformWindowedRun F).final_accept⟩

theorem every_frame_first_hit_padding {w h : Nat} (F : FullFrame w h) :
    let c := (FullFrame.toUniformWindowedRun F).config ⟨0, Nat.zero_lt_succ w⟩
    let d := (FullFrame.toUniformWindowedRun F).config ⟨w, Nat.lt_succ_self w⟩
    ∃ hm : MStarOuterProgram.movable (d.tape d.head) = true,
      ∃ k, 0 < k ∧ k ≤ w ∧ FirstHit c ((frameWord F).take k) d ∧
        frameWord F = (frameWord F).take k ++
          List.replicate (w - k) (paddingArrow d hm) := by
  dsimp only
  have hc : ((FullFrame.toUniformWindowedRun F).config
      ⟨0, Nat.zero_lt_succ w⟩).state ≠ .accept := by
    rw [FullFrame.uniform_initial_state_start F]
    intro he
    cases he
  simpa only [frame_word_length F] using
    every_accepted_word_first_hit_padding _ _ (frameWord F) hc (frame_word_run F)
      (FullFrame.toUniformWindowedRun F).final_accept

theorem every_frame_unique_first_hit {w h : Nat} (F : FullFrame w h) :
    let c := (FullFrame.toUniformWindowedRun F).config ⟨0, Nat.zero_lt_succ w⟩
    let d := (FullFrame.toUniformWindowedRun F).config ⟨w, Nat.lt_succ_self w⟩
    ∃! k, k ≤ w ∧ FirstHit c ((frameWord F).take k) d := by
  dsimp only
  have hc : ((FullFrame.toUniformWindowedRun F).config
      ⟨0, Nat.zero_lt_succ w⟩).state ≠ .accept := by
    rw [FullFrame.uniform_initial_state_start F]
    intro he
    cases he
  simpa only [frame_word_length F] using
    every_accepted_word_has_unique_first_hit _ _ (frameWord F) hc (frame_word_run F)
      (FullFrame.toUniformWindowedRun F).final_accept

end PakFixedPolyomino.MStarFullFrameFirstHitReadback
