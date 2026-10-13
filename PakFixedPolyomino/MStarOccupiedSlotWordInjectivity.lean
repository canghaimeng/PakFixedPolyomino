import PakFixedPolyomino.PakFullFrameFirstBranch
import PakFixedPolyomino.MStarFixedWidthFirstHitEquiv

/-! Successful complete occupied-arrow words from a fixed configuration are
internally determined by their chronological slots. Equal actions do not
collapse distinct slots. This is an ALL-run inverse ingredient. -/
namespace PakFixedPolyomino.MStarOccupiedSlotWordInjectivity
open FiniteOneTapeSemantics PakFullFrameTableauReadback

abbrev Config := PakMStarCouplingCorrectness.MStarConfig
abbrev Arrow := MStarULogAssembly.Arrow

def slotWord (labels : List Arrow) : List (Fin 2) := labels.map (fun a => a.val.2)

theorem slotWord_length (labels : List Arrow) : (slotWord labels).length = labels.length := by
  simp [slotWord]

theorem successful_words_eq_of_slots (c d e : Config) (first second : List Arrow)
    (hf : run MStarULogAssembly.program MStarOuterProgram.movable first c = some d)
    (hs : run MStarULogAssembly.program MStarOuterProgram.movable second c = some e)
    (same : slotWord first = slotWord second) : first = second := by
  induction first generalizing c second with
  | nil =>
      have hempty : second = [] := List.map_eq_nil_iff.mp same.symm
      exact hempty.symm
  | cons a first ih =>
      cases second with
      | nil => simp [slotWord] at same
      | cons b second =>
          have he : a.val.2 = b.val.2 ∧ slotWord first = slotWord second := by
            simpa only [slotWord, List.map_cons, List.cons.injEq] using same
          cases ha : step MStarULogAssembly.program MStarOuterProgram.movable c a with
          | none => simp [run_cons, ha] at hf
          | some nextA =>
              cases hb : step MStarULogAssembly.program MStarOuterProgram.movable c b with
              | none => simp [run_cons, hb] at hs
              | some nextB =>
                  have hab := arrow_eq_of_successful_steps_same_slot c nextA nextB a b ha hb he.1
                  subst b
                  have hn : nextA = nextB := Option.some.inj (ha.symm.trans hb)
                  subst nextB
                  have hft : run MStarULogAssembly.program MStarOuterProgram.movable
                      first nextA = some d := by simpa [run_cons, ha] using hf
                  have hst : run MStarULogAssembly.program MStarOuterProgram.movable
                      second nextA = some e := by simpa [run_cons, ha] using hs
                  exact congrArg (List.cons a) (ih nextA second hft hst he.2)

theorem first_hit_slot_map_injective (c : Config) (T : Nat) :
    Function.Injective (fun w : MStarFixedWidthFirstHitEquiv.FirstHitWordsAtMost c T =>
      slotWord w.val) := by
  intro first second same
  obtain ⟨d, hd⟩ := first.property.2
  obtain ⟨e, he⟩ := second.property.2
  apply Subtype.ext
  exact successful_words_eq_of_slots c d e first.val second.val hd.1 he.1 same

def occupied_slot_word_injectivity_spec : Prop :=
  (∀ (c d e : Config) (first second : List Arrow),
    run MStarULogAssembly.program MStarOuterProgram.movable first c = some d →
    run MStarULogAssembly.program MStarOuterProgram.movable second c = some e →
    slotWord first = slotWord second → first = second) ∧
  (∀ (c : Config) (T : Nat),
    Function.Injective (fun w : MStarFixedWidthFirstHitEquiv.FirstHitWordsAtMost c T =>
      slotWord w.val))

theorem occupied_slot_word_injectivity_spec_holds : occupied_slot_word_injectivity_spec :=
  ⟨successful_words_eq_of_slots, first_hit_slot_map_injective⟩

end PakFixedPolyomino.MStarOccupiedSlotWordInjectivity
