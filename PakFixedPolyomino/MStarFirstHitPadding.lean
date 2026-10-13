import PakFixedPolyomino.MStarAcceptPaddingWords

/-! Every literal successful outer history from a nonaccepting start has a
unique first accepting prefix. The remainder consists of the actual occupied
stationary padding arrow. This is an execution theorem, not a frame census. -/
namespace PakFixedPolyomino.MStarFirstHitPadding
open PakMStarCouplingCorrectness FiniteOneTapeSemantics
open MStarAcceptPaddingWords

def FirstHit (c : MStarConfig) (labels : List MStarULogAssembly.Arrow)
    (d : MStarConfig) : Prop :=
  run MStarULogAssembly.program MStarOuterProgram.movable labels c = some d ∧
  d.state = .accept ∧
  ∀ k < labels.length, ∀ mid,
    run MStarULogAssembly.program MStarOuterProgram.movable (labels.take k) c =
      some mid → mid.state ≠ .accept

theorem first_hit_nonempty (c d : MStarConfig)
    (labels : List MStarULogAssembly.Arrow) (hc : c.state ≠ .accept)
    (h : FirstHit c labels d) : labels ≠ [] := by
  intro he
  subst labels
  have hd : c = d := Option.some.inj h.1
  subst d
  exact hc h.2.1

theorem first_hit_cons (c next d : MStarConfig) (a : MStarULogAssembly.Arrow)
    (labels : List MStarULogAssembly.Arrow) (hc : c.state ≠ .accept)
    (hs : step MStarULogAssembly.program MStarOuterProgram.movable c a = some next)
    (h : FirstHit next labels d) : FirstHit c (a :: labels) d := by
  refine ⟨by simpa [run_cons, hs] using h.1, h.2.1, ?_⟩
  intro k hk mid hm
  cases k with
  | zero =>
      have he : c = mid := Option.some.inj hm
      exact he ▸ hc
  | succ k =>
      have hk' : k < labels.length := by simpa using hk
      apply h.2.2 k hk' mid
      simpa [List.take_succ_cons, run_cons, hs] using hm

theorem first_hit_split (c d : MStarConfig)
    (labels : List MStarULogAssembly.Arrow) (hc : c.state ≠ .accept)
    (hr : run MStarULogAssembly.program MStarOuterProgram.movable labels c = some d)
    (hd : d.state = .accept) :
    ∃ pre tail mid, labels = pre ++ tail ∧ FirstHit c pre mid ∧
      run MStarULogAssembly.program MStarOuterProgram.movable tail mid = some d := by
  induction labels generalizing c with
  | nil =>
      have he : c = d := Option.some.inj hr
      subst c
      exact (hc hd).elim
  | cons a labels ih =>
      cases hs : step MStarULogAssembly.program MStarOuterProgram.movable c a with
      | none => simp [run_cons, hs] at hr
      | some next =>
          have ht : run MStarULogAssembly.program MStarOuterProgram.movable labels next =
              some d := by simpa [run_cons, hs] using hr
          by_cases hn : next.state = .accept
          · refine ⟨[a], labels, next, rfl, ?_, ht⟩
            apply first_hit_cons c next next a [] hc hs
            exact ⟨rfl, hn, by simp⟩
          · obtain ⟨pre, tail, mid, he, hf, hsuf⟩ := ih next hn ht
            exact ⟨a :: pre, tail, mid, by simp [he],
              first_hit_cons c next mid a pre hc hs hf, hsuf⟩

theorem first_hit_take_index_unique (c d e : MStarConfig)
    (labels : List MStarULogAssembly.Arrow) (k l : Nat)
    (hk : k ≤ labels.length) (hl : l ≤ labels.length)
    (hf : FirstHit c (labels.take k) d)
    (hg : FirstHit c (labels.take l) e) : k = l := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hkl | hlk
  · have hlt : k < (labels.take l).length := by simp [List.length_take, hl]; omega
    have hn := hg.2.2 k hlt d
    have hr : run MStarULogAssembly.program MStarOuterProgram.movable
        ((labels.take l).take k) c = some d := by
      simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hkl)] using hf.1
    exact hn hr hf.2.1
  · have hlt : l < (labels.take k).length := by simp [List.length_take, hk]; omega
    have hn := hf.2.2 l hlt e
    have hr : run MStarULogAssembly.program MStarOuterProgram.movable
        ((labels.take k).take l) c = some e := by
      simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hlk)] using hg.1
    exact hn hr hg.2.1

theorem every_accepted_word_first_hit_padding (c d : MStarConfig)
    (labels : List MStarULogAssembly.Arrow) (hc : c.state ≠ .accept)
    (hr : run MStarULogAssembly.program MStarOuterProgram.movable labels c = some d)
    (hd : d.state = .accept) :
    ∃ hm : MStarOuterProgram.movable (d.tape d.head) = true,
      ∃ k, 0 < k ∧ k ≤ labels.length ∧ FirstHit c (labels.take k) d ∧
        labels = labels.take k ++
          List.replicate (labels.length - k) (paddingArrow d hm) := by
  obtain ⟨pre, tail, mid, he, hf, hsuf⟩ := first_hit_split c d labels hc hr hd
  have hp := first_hit_nonempty c mid pre hc hf
  have hm := nonempty_run_finish_movable c mid pre hp hf.1
  obtain ⟨hfinal, htail⟩ := every_accept_word_is_padding mid d hf.2.1 hm tail hsuf
  subst mid
  have hlen : labels.length = pre.length + tail.length := by simp [he]
  have htake : labels.take pre.length = pre := by simp [he]
  refine ⟨hm, pre.length, List.length_pos_iff.mpr hp, by omega, ?_, ?_⟩
  · simpa [htake] using hf
  · rw [htake, hlen, Nat.add_sub_cancel_left]
    exact he.trans (congrArg (pre ++ ·) htail)

theorem every_accepted_word_has_unique_first_hit (c d : MStarConfig)
    (labels : List MStarULogAssembly.Arrow) (hc : c.state ≠ .accept)
    (hr : run MStarULogAssembly.program MStarOuterProgram.movable labels c = some d)
    (hd : d.state = .accept) :
    ∃! k, k ≤ labels.length ∧ FirstHit c (labels.take k) d := by
  obtain ⟨hm, k, hkpos, hk, hf, hpad⟩ :=
    every_accepted_word_first_hit_padding c d labels hc hr hd
  refine ⟨k, ⟨hk, hf⟩, ?_⟩
  intro l hl
  exact first_hit_take_index_unique c d d labels l k hl.1 hk hl.2 hf

end PakFixedPolyomino.MStarFirstHitPadding
