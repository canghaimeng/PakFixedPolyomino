import PakFixedPolyomino.MStarFirstHitPadding
import Mathlib.Data.Fintype.Vector

/-! The literal fixed-width accepting-word domain is equivalent to the full
bounded first-hit domain. Stationary acceptance padding is supplied internally.
Neither domain is a selected image of source computations. -/
namespace PakFixedPolyomino.MStarFixedWidthFirstHitEquiv
open PakMStarCouplingCorrectness FiniteOneTapeSemantics
open MStarAcceptPaddingWords MStarFirstHitPadding

def AcceptedWordsAtLength (c : MStarConfig) (N : Nat) :=
  {labels : List MStarULogAssembly.Arrow // labels.length = N ∧
    ∃ d, run MStarULogAssembly.program MStarOuterProgram.movable labels c = some d ∧
      d.state = .accept}

def FirstHitWordsAtMost (c : MStarConfig) (N : Nat) :=
  {labels : List MStarULogAssembly.Arrow // labels.length ≤ N ∧
    ∃ d, FirstHit c labels d}

theorem accepted_words_finite (c : MStarConfig) (N : Nat) :
    Finite (AcceptedWordsAtLength c N) := by
  let code : AcceptedWordsAtLength c N → List.Vector MStarULogAssembly.Arrow N :=
    fun w => ⟨w.1, w.2.1⟩
  apply Finite.of_injective code
  intro a b h
  apply Subtype.ext
  exact congrArg List.Vector.toList h

theorem first_hit_words_finite (c : MStarConfig) (N : Nat) :
    Finite (FirstHitWordsAtMost c N) := by
  let code : FirstHitWordsAtMost c N →
      (Σ k : Fin (N + 1), List.Vector MStarULogAssembly.Arrow k.1) :=
    fun w => ⟨⟨w.1.length, by have := w.2.1; omega⟩, ⟨w.1, rfl⟩⟩
  apply Finite.of_injective code
  intro a b h
  apply Subtype.ext
  exact congrArg (fun v : Σ k : Fin (N + 1), List.Vector MStarULogAssembly.Arrow k.1 =>
    v.2.toList) h

theorem actual_run_append (pre tail : List MStarULogAssembly.Arrow) (c : MStarConfig) :
    run MStarULogAssembly.program MStarOuterProgram.movable (pre ++ tail) c =
      (run MStarULogAssembly.program MStarOuterProgram.movable pre c).bind
        (run MStarULogAssembly.program MStarOuterProgram.movable tail) := by
  induction pre generalizing c with
  | nil => rfl
  | cons a pre ih =>
      simp only [List.cons_append, run_cons]
      cases step MStarULogAssembly.program MStarOuterProgram.movable c a <;>
        simp only [Option.bind_none, Option.bind_some, ih]

noncomputable def padWord (c : MStarConfig) (hc : c.state ≠ .accept) (N : Nat)
    (w : FirstHitWordsAtMost c N) : AcceptedWordsAtLength c N := by
  classical
  let d := Classical.choose w.2.2
  have hf : FirstHit c w.1 d := Classical.choose_spec w.2.2
  have hm := nonempty_run_finish_movable c d w.1 (first_hit_nonempty c d w.1 hc hf) hf.1
  refine ⟨w.1 ++ List.replicate (N - w.1.length) (paddingArrow d hm), ?_, d, ?_, hf.2.1⟩
  · simp only [List.length_append, List.length_replicate]
    have := w.2.1
    omega
  · rw [actual_run_append, hf.1, Option.bind_some]
    exact padding_word_run d hf.2.1 hm _

theorem pad_word_spec (c : MStarConfig) (hc : c.state ≠ .accept) (N : Nat)
    (w : FirstHitWordsAtMost c N) :
    ∃ d, ∃ hm : MStarOuterProgram.movable (d.tape d.head) = true,
      FirstHit c w.1 d ∧ (padWord c hc N w).1 =
        w.1 ++ List.replicate (N - w.1.length) (paddingArrow d hm) := by
  classical
  let d := Classical.choose w.2.2
  have hf : FirstHit c w.1 d := Classical.choose_spec w.2.2
  refine ⟨d, nonempty_run_finish_movable c d w.1
    (first_hit_nonempty c d w.1 hc hf) hf.1, hf, rfl⟩

noncomputable def trimWord (c : MStarConfig) (hc : c.state ≠ .accept) (N : Nat)
    (w : AcceptedWordsAtLength c N) : FirstHitWordsAtMost c N := by
  classical
  let d := Classical.choose w.2.2
  have hd := Classical.choose_spec w.2.2
  have hex := every_accepted_word_has_unique_first_hit c d w.1 hc hd.1 hd.2
  let k := Classical.choose hex
  have hk := (Classical.choose_spec hex).1
  refine ⟨w.1.take k, ?_, d, hk.2⟩
  simp only [List.length_take]
  have hn := w.2.1
  omega

theorem trim_word_spec (c : MStarConfig) (hc : c.state ≠ .accept) (N : Nat)
    (w : AcceptedWordsAtLength c N) :
    ∃ k, k ≤ w.1.length ∧ ∃ d,
      FirstHit c (w.1.take k) d ∧ (trimWord c hc N w).1 = w.1.take k := by
  classical
  let d := Classical.choose w.2.2
  have hd := Classical.choose_spec w.2.2
  have hex := every_accepted_word_has_unique_first_hit c d w.1 hc hd.1 hd.2
  let k := Classical.choose hex
  have hk := (Classical.choose_spec hex).1
  exact ⟨k, hk.1, d, hk.2, rfl⟩

theorem pad_trim_word (c : MStarConfig) (hc : c.state ≠ .accept) (N : Nat)
    (w : AcceptedWordsAtLength c N) : padWord c hc N (trimWord c hc N w) = w := by
  apply Subtype.ext
  obtain ⟨d, hr, hd⟩ := w.2.2
  obtain ⟨hm, k, hkpos, hk, hf, hpad⟩ :=
    every_accepted_word_first_hit_padding c d w.1 hc hr hd
  obtain ⟨l, hl, e, hg, htrim⟩ := trim_word_spec c hc N w
  have hkl := first_hit_take_index_unique c d e w.1 k l hk hl hf hg
  subst l
  obtain ⟨f, hmf, hh, hvalue⟩ := pad_word_spec c hc N (trimWord c hc N w)
  have hfd : f = d := by
    rw [htrim] at hh
    exact Option.some.inj (hh.1.symm.trans hf.1)
  subst f
  rw [hvalue, htrim]
  have hlen : (w.1.take k).length = k := by simp [List.length_take, hk]
  rw [hlen]
  simpa only [w.2.1] using hpad.symm

theorem trim_pad_word (c : MStarConfig) (hc : c.state ≠ .accept) (N : Nat)
    (w : FirstHitWordsAtMost c N) : trimWord c hc N (padWord c hc N w) = w := by
  apply Subtype.ext
  obtain ⟨d, hm, hf, hvalue⟩ := pad_word_spec c hc N w
  obtain ⟨k, hk, e, hg, htrim⟩ := trim_word_spec c hc N (padWord c hc N w)
  have htake : (padWord c hc N w).1.take w.1.length = w.1 := by simp [hvalue]
  have hbound : w.1.length ≤ (padWord c hc N w).1.length := by
    rw [(padWord c hc N w).2.1]
    exact w.2.1
  have hf' : FirstHit c ((padWord c hc N w).1.take w.1.length) d := by
    simpa [htake] using hf
  have hindex := first_hit_take_index_unique c e d (padWord c hc N w).1
    k w.1.length hk hbound hg hf'
  exact htrim.trans (hindex ▸ htake)

noncomputable def fixedWidthFirstHitEquiv (c : MStarConfig)
    (hc : c.state ≠ .accept) (N : Nat) :
    AcceptedWordsAtLength c N ≃ FirstHitWordsAtMost c N where
  toFun := trimWord c hc N
  invFun := padWord c hc N
  left_inv := pad_trim_word c hc N
  right_inv := trim_pad_word c hc N

theorem fixed_width_count_eq_first_hit_count (c : MStarConfig)
    (hc : c.state ≠ .accept) (N : Nat) :
    Nat.card (AcceptedWordsAtLength c N) = Nat.card (FirstHitWordsAtMost c N) :=
  Nat.card_congr (fixedWidthFirstHitEquiv c hc N)

end PakFixedPolyomino.MStarFixedWidthFirstHitEquiv
