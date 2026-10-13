import PakFixedPolyomino.MStarFixedWidthFirstHitEquiv
import Mathlib.Data.Fintype.Vector

/-! Generic ALL first-hit words and deterministic-prefix cancellation. -/

namespace PakFixedPolyomino.PakOuterFirstHitPrefix

set_option linter.unusedSectionVars false
open FiniteOneTapeProgram FiniteOneTapeSemantics MStarFixedWidthFirstHitEquiv

variable {State Tape : Type*} [Fintype State] [Fintype Tape]
  [DecidableEq State] [DecidableEq Tape]

def FirstAcceptingWordsAtMost (P : Program State Tape) (movable : Tape → Bool)
    (accept : State) (B : ℕ) (start : Config State Tape) :=
  {labels : List (Arrow P) //
    labels.length ≤ B ∧
      ∃ finish, run P movable labels start = some finish ∧
        finish.state = accept ∧
          ∀ k < labels.length, ∀ mid,
            run P movable (labels.take k) start = some mid →
              mid.state ≠ accept}

instance firstAcceptingWords_finite (P : Program State Tape)
    (movable : Tape → Bool) (accept : State) (B : ℕ)
    (start : Config State Tape) :
    Finite (FirstAcceptingWordsAtMost P movable accept B start) := by
  let code : FirstAcceptingWordsAtMost P movable accept B start →
      (Σ k : Fin (B + 1), List.Vector (Arrow P) k.1) :=
    fun w => ⟨⟨w.1.length, Nat.lt_succ_of_le w.2.1⟩, ⟨w.1, rfl⟩⟩
  refine Finite.of_injective code ?_
  intro a b h
  apply Subtype.ext
  exact congrArg (fun v : Σ k : Fin (B + 1), List.Vector (Arrow P) k.1 =>
    v.2.toList) h

noncomputable def firstAcceptingCount (P : Program State Tape)
    (movable : Tape → Bool) (accept : State) (B : ℕ)
    (start : Config State Tape) : ℕ :=
  Nat.card (FirstAcceptingWordsAtMost P movable accept B start)

theorem run_append (P : Program State Tape) (movable : Tape → Bool)
    (pre tail : List (Arrow P)) (c : Config State Tape) :
    run P movable (pre ++ tail) c =
      (run P movable pre c).bind (run P movable tail) := by
  induction pre generalizing c with
  | nil => rfl
  | cons a pre ih =>
      simp only [List.cons_append, run_cons]
      cases step P movable c a <;> simp [ih]

inductive DeterministicPrefix (P : Program State Tape) (movable : Tape → Bool)
    (accept : State) :
    List (Arrow P) → Config State Tape → Config State Tape → Prop
  | nil (c : Config State Tape) :
      DeterministicPrefix P movable accept [] c c
  | cons {a : Arrow P} {as : List (Arrow P)}
      {start mid finish : Config State Tape}
      (hstep : step P movable start a = some mid)
      (hna : start.state ≠ accept)
      (huniq : ∀ b next, step P movable start b = some next → b = a)
      (htail : DeterministicPrefix P movable accept as mid finish) :
      DeterministicPrefix P movable accept (a :: as) start finish

theorem deterministicPrefix_run {P : Program State Tape}
    {movable : Tape → Bool} {accept : State}
    {labels : List (Arrow P)} {start finish : Config State Tape}
    (h : DeterministicPrefix P movable accept labels start finish) :
    run P movable labels start = some finish := by
  induction h with
  | nil c => rfl
  | cons hstep _hna _huniq _htail ih =>
      simp [run_cons, hstep, ih]

theorem deterministicPrefix_append {P : Program State Tape}
    {movable : Tape → Bool} {accept : State}
    {pre suf : List (Arrow P)}
    {start middle finish : Config State Tape}
    (hpre : DeterministicPrefix P movable accept pre start middle)
    (hsuf : DeterministicPrefix P movable accept suf middle finish) :
    DeterministicPrefix P movable accept (pre ++ suf) start finish := by
  induction hpre with
  | nil c => simpa using hsuf
  | cons hstep hna huniq _htail ih =>
      exact DeterministicPrefix.cons hstep hna huniq (ih hsuf)

theorem deterministicPrefix_take_ne_accept {P : Program State Tape}
    {movable : Tape → Bool} {accept : State}
    {pre : List (Arrow P)} {start middle : Config State Tape}
    (h : DeterministicPrefix P movable accept pre start middle)
    (k : ℕ) (hk : k < pre.length) :
    ∃ ck, run P movable (pre.take k) start = some ck ∧ ck.state ≠ accept := by
  induction h generalizing k with
  | nil c =>
      cases hk
  | @cons a as start mid finish hstep hna _huniq _htail ih =>
      cases k with
      | zero =>
          exact ⟨start, rfl, hna⟩
      | succ k =>
          have hk' : k < as.length := by simpa using hk
          obtain ⟨ck, hr, hne⟩ := ih k hk'
          refine ⟨ck, ?_, hne⟩
          simpa [List.take_succ_cons, run_cons, hstep] using hr

theorem firstHit_cancel {P : Program State Tape} {movable : Tape → Bool}
    {accept : State} {pre labels : List (Arrow P)}
    {start middle finish : Config State Tape}
    (hpre : DeterministicPrefix P movable accept pre start middle)
    (hrun : run P movable labels start = some finish)
    (hacc : finish.state = accept)
    (hfirst : ∀ k < labels.length, ∀ mid,
      run P movable (labels.take k) start = some mid → mid.state ≠ accept) :
    labels = pre ++ labels.drop pre.length ∧
      run P movable (labels.drop pre.length) middle = some finish ∧
        ∀ k < (labels.drop pre.length).length, ∀ m,
          run P movable ((labels.drop pre.length).take k) middle = some m →
            m.state ≠ accept := by
  induction hpre generalizing labels finish with
  | nil c =>
      exact ⟨by simp, hrun, hfirst⟩
  | @cons a as start mid finish0 hstep hna huniq _htail ih =>
      cases labels with
      | nil =>
          have hst : start = finish := Option.some.inj hrun
          exact (hna (hst ▸ hacc)).elim
      | cons b rest =>
          cases hs : step P movable start b with
          | none =>
              simp [run_cons, hs] at hrun
          | some next =>
              have hb : b = a := huniq b next hs
              subst b
              have hnext : next = mid := by
                have := hs
                rw [hstep] at this
                exact Option.some.inj this.symm
              subst next
              have hrest :
                  run P movable rest mid = some finish := by
                simpa [run_cons, hstep] using hrun
              have hfirst' : ∀ k < rest.length, ∀ m,
                  run P movable (rest.take k) mid = some m →
                    m.state ≠ accept := by
                intro k hk m hm
                have hk' : k + 1 < (a :: rest).length := by simpa using hk
                apply hfirst (k + 1) hk' m
                simpa [List.take_succ_cons, run_cons, hstep] using hm
              obtain ⟨heq, hsuf, hfh⟩ := ih hrest hacc hfirst'
              refine ⟨?_, ?_, ?_⟩
              · simpa [List.drop_succ_cons] using congrArg (List.cons a) heq
              · simpa [List.drop_succ_cons] using hsuf
              · simpa [List.drop_succ_cons] using hfh

theorem firstHit_prepend {P : Program State Tape} {movable : Tape → Bool}
    {accept : State} {pre suf : List (Arrow P)}
    {start middle finish : Config State Tape}
    (hpre : DeterministicPrefix P movable accept pre start middle)
    (hrun : run P movable suf middle = some finish)
    (hacc : finish.state = accept)
    (hfirst : ∀ k < suf.length, ∀ m,
      run P movable (suf.take k) middle = some m → m.state ≠ accept) :
    run P movable (pre ++ suf) start = some finish ∧
      ∀ k < (pre ++ suf).length, ∀ ck,
        run P movable ((pre ++ suf).take k) start = some ck →
          ck.state ≠ accept := by
  refine ⟨?_, ?_⟩
  · rw [run_append, deterministicPrefix_run hpre, Option.bind_some, hrun]
  · intro k hk ck hr
    by_cases hlt : k < pre.length
    · obtain ⟨ck0, hr0, hne⟩ :=
        deterministicPrefix_take_ne_accept hpre k hlt
      have heq : (pre ++ suf).take k = pre.take k :=
        List.take_append_of_le_length (Nat.le_of_lt hlt)
      rw [heq] at hr
      exact (Option.some.inj (hr.symm.trans hr0)) ▸ hne
    · have hkpre : pre.length ≤ k := Nat.le_of_not_gt hlt
      have hj : k - pre.length < suf.length := by
        have := hk
        simp only [List.length_append] at this
        omega
      have htake :
          (pre ++ suf).take k = pre ++ suf.take (k - pre.length) := by
        rw [List.take_append, List.take_of_length_le hkpre]
      rw [htake] at hr
      have hm :
          run P movable (suf.take (k - pre.length)) middle = some ck := by
        simpa [run_append, deterministicPrefix_run hpre] using hr
      exact hfirst _ hj _ hm

noncomputable def appendFirstHit {P : Program State Tape}
    {movable : Tape → Bool} {accept : State} {pre : List (Arrow P)}
    {start middle : Config State Tape} {T : ℕ}
    (hpre : DeterministicPrefix P movable accept pre start middle)
    (w : FirstAcceptingWordsAtMost P movable accept T middle) :
    FirstAcceptingWordsAtMost P movable accept (pre.length + T) start :=
  let hf := Classical.choose_spec w.2.2
  let hp := firstHit_prepend hpre hf.1 hf.2.1 hf.2.2
  ⟨pre ++ w.1,
    by simpa [List.length_append] using Nat.add_le_add_left w.2.1 pre.length,
    Classical.choose w.2.2, hp.1, hf.2.1, hp.2⟩

noncomputable def dropFirstHit {P : Program State Tape}
    {movable : Tape → Bool} {accept : State} {pre : List (Arrow P)}
    {start middle : Config State Tape} {T : ℕ}
    (hpre : DeterministicPrefix P movable accept pre start middle)
    (w : FirstAcceptingWordsAtMost P movable accept (pre.length + T) start) :
    FirstAcceptingWordsAtMost P movable accept T middle :=
  let hf := Classical.choose_spec w.2.2
  let hc := firstHit_cancel hpre hf.1 hf.2.1 hf.2.2
  ⟨w.1.drop pre.length, by
      have := w.2.1
      simp only [List.length_drop]
      omega,
    Classical.choose w.2.2, hc.2.1, hf.2.1, hc.2.2⟩

theorem appendFirstHit_dropFirstHit {P : Program State Tape}
    {movable : Tape → Bool} {accept : State} {pre : List (Arrow P)}
    {start middle : Config State Tape} {T : ℕ}
    (hpre : DeterministicPrefix P movable accept pre start middle)
    (w : FirstAcceptingWordsAtMost P movable accept (pre.length + T) start) :
    appendFirstHit hpre (dropFirstHit hpre w) = w := by
  apply Subtype.ext
  obtain ⟨finish, hrun, hacc, hfirst⟩ := w.2.2
  exact (firstHit_cancel (labels := w.1) hpre hrun hacc hfirst).1.symm

theorem dropFirstHit_appendFirstHit {P : Program State Tape}
    {movable : Tape → Bool} {accept : State} {pre : List (Arrow P)}
    {start middle : Config State Tape} {T : ℕ}
    (hpre : DeterministicPrefix P movable accept pre start middle)
    (w : FirstAcceptingWordsAtMost P movable accept T middle) :
    dropFirstHit hpre (appendFirstHit hpre w) = w :=
  Subtype.ext (List.drop_left (l₁ := pre) (l₂ := w.1))

noncomputable def firstHit_prefix_equiv {P : Program State Tape}
    {movable : Tape → Bool} {accept : State} {pre : List (Arrow P)}
    {start middle : Config State Tape} {T : ℕ}
    (hpre : DeterministicPrefix P movable accept pre start middle) :
    FirstAcceptingWordsAtMost P movable accept (pre.length + T) start ≃
      FirstAcceptingWordsAtMost P movable accept T middle where
  toFun := dropFirstHit hpre
  invFun := appendFirstHit hpre
  left_inv := appendFirstHit_dropFirstHit hpre
  right_inv := dropFirstHit_appendFirstHit hpre

theorem firstHit_prefix_count_eq {P : Program State Tape}
    {movable : Tape → Bool} {accept : State} {pre : List (Arrow P)}
    {start middle : Config State Tape} {T : ℕ}
    (hpre : DeterministicPrefix P movable accept pre start middle) :
    firstAcceptingCount P movable accept (pre.length + T) start =
      firstAcceptingCount P movable accept T middle :=
  Nat.card_congr (firstHit_prefix_equiv hpre)

theorem firstHit_short_zero {P : Program State Tape}
    {movable : Tape → Bool} {accept : State} {pre : List (Arrow P)}
    {start middle : Config State Tape} {B : ℕ}
    (hpre : DeterministicPrefix P movable accept pre start middle)
    (hB : B < pre.length) :
    firstAcceptingCount P movable accept B start = 0 := by
  have : IsEmpty (FirstAcceptingWordsAtMost P movable accept B start) :=
    ⟨fun w => by
      obtain ⟨finish, hrun, hacc, hfirst⟩ := w.2.2
      have hc := firstHit_cancel hpre hrun hacc hfirst
      have hlen : pre.length ≤ w.1.length := by
        have := congrArg List.length hc.1
        simp at this
        omega
      exact (not_lt_of_ge (le_trans hlen w.2.1) hB).elim⟩
  exact @Nat.card_of_isEmpty _ this

lemma parser_arrow_slot_zero
    (q : MStarULogAssembly.ParserControl)
    (x : MStarULogAssembly.Tape) (a : MStarULogAssembly.Arrow)
    (hs : a.1.1.1 = .parser q) (hr : a.1.1.2 = x) : a.1.2 = 0 := by
  have hne : MStarULogAssembly.program.rule a.1.1.1 a.1.1.2 a.1.2 ≠ none := a.2
  have h01 : a.1.2.val = 0 ∨ a.1.2.val = 1 := by
    have := a.1.2.isLt
    omega
  cases h01 with
  | inl h0 => exact Fin.ext h0
  | inr h1 =>
      have hi : a.1.2 = 1 := Fin.ext h1
      have : MStarULogAssembly.program.rule (.parser q) x 1 ≠ none := by
        simpa [hs, hr, hi] using hne
      exact (this (MStarOuterProgram.parser_deterministic_slot_one
        MStarULogAssembly.data q x)).elim

theorem parser_state_ne_accept {q : MStarULogAssembly.ParserControl} :
    (MStarOuterProgram.State.parser q : MStarULogAssembly.State) ≠ .accept := by
  intro h
  cases h

theorem parser_occupied_arrow_unique
    (c : Config MStarULogAssembly.State MStarULogAssembly.Tape)
    (q : MStarULogAssembly.ParserControl)
    (a b : MStarULogAssembly.Arrow)
    (d e : Config MStarULogAssembly.State MStarULogAssembly.Tape)
    (hs : c.state = .parser q)
    (ha : step MStarULogAssembly.program MStarOuterProgram.movable c a = some d)
    (hb : step MStarULogAssembly.program MStarOuterProgram.movable c b = some e) :
    a = b ∧ d = e := by
  have hsa := step_some_forces_source MStarULogAssembly.program
    MStarOuterProgram.movable c d a ha
  have hsb := step_some_forces_source MStarULogAssembly.program
    MStarOuterProgram.movable c e b hb
  have hsrca : a.1.1.1 = .parser q := hsa.1.symm.trans hs
  have hsrcb : b.1.1.1 = .parser q := hsb.1.symm.trans hs
  have hreada : a.1.1.2 = c.tape c.head := hsa.2.symm
  have hreadb : b.1.1.2 = c.tape c.head := hsb.2.symm
  have hia := parser_arrow_slot_zero q (c.tape c.head) a hsrca hreada
  have hib := parser_arrow_slot_zero q (c.tape c.head) b hsrcb hreadb
  have hval : a.1 = b.1 := by
    apply Prod.ext
    · apply Prod.ext
      · exact hsrca.trans hsrcb.symm
      · exact hreada.trans hreadb.symm
    · exact hia.trans hib.symm
  have hab : a = b := Subtype.ext hval
  refine ⟨hab, ?_⟩
  subst hab
  exact step_label_deterministic MStarULogAssembly.program
    MStarOuterProgram.movable c d e a ha hb

noncomputable def toFirstHitWords
    (c : PakMStarCouplingCorrectness.MStarConfig) (N : ℕ)
    (w : FirstAcceptingWordsAtMost MStarULogAssembly.program
      MStarOuterProgram.movable .accept N c) :
    FirstHitWordsAtMost c N :=
  ⟨w.1, w.2.1, by
    obtain ⟨finish, hrun, hacc, hfirst⟩ := w.2.2
    exact ⟨finish, hrun, hacc, hfirst⟩⟩

noncomputable def ofFirstHitWords
    (c : PakMStarCouplingCorrectness.MStarConfig) (N : ℕ)
    (w : FirstHitWordsAtMost c N) :
    FirstAcceptingWordsAtMost MStarULogAssembly.program
      MStarOuterProgram.movable .accept N c :=
  ⟨w.1, w.2.1, by
    obtain ⟨d, hd⟩ := w.2.2
    exact ⟨d, hd.1, hd.2.1, hd.2.2⟩⟩

noncomputable def firstAcceptingWords_equiv_firstHit
    (c : PakMStarCouplingCorrectness.MStarConfig) (N : ℕ) :
    FirstAcceptingWordsAtMost MStarULogAssembly.program
      MStarOuterProgram.movable .accept N c ≃ FirstHitWordsAtMost c N where
  toFun := toFirstHitWords c N
  invFun := ofFirstHitWords c N
  left_inv := by intro w; apply Subtype.ext; rfl
  right_inv := by intro w; apply Subtype.ext; rfl

theorem deterministicPrefix_of_parser_run
    (labels : List MStarULogAssembly.Arrow)
    (start finish : Config MStarULogAssembly.State MStarULogAssembly.Tape)
    (hrun : run MStarULogAssembly.program MStarOuterProgram.movable
      labels start = some finish)
    (hparser : ∀ k < labels.length, ∀ mid,
      run MStarULogAssembly.program MStarOuterProgram.movable
        (labels.take k) start = some mid →
          ∃ q, mid.state = .parser q) :
    DeterministicPrefix MStarULogAssembly.program MStarOuterProgram.movable
      .accept labels start finish := by
  induction labels generalizing start with
  | nil =>
      have hst : start = finish := Option.some.inj hrun
      subst finish
      exact DeterministicPrefix.nil _
  | cons a rest ih =>
      cases hs : step MStarULogAssembly.program MStarOuterProgram.movable
          start a with
      | none =>
          simp [run_cons, hs] at hrun
      | some mid =>
          have hrest :
              run MStarULogAssembly.program MStarOuterProgram.movable rest mid =
                some finish := by
            simpa [run_cons, hs] using hrun
          have ⟨q, hq⟩ := hparser 0 (Nat.succ_pos _) start rfl
          have hna : start.state ≠ .accept := by
            intro ha
            exact parser_state_ne_accept (hq.symm.trans ha)
          have huniq : ∀ b next,
              step MStarULogAssembly.program MStarOuterProgram.movable start b =
                some next → b = a := by
            intro b next hb
            exact (parser_occupied_arrow_unique start q a b mid next hq hs hb).1.symm
          have hparser' : ∀ k < rest.length, ∀ m,
              run MStarULogAssembly.program MStarOuterProgram.movable
                (rest.take k) mid = some m →
                  ∃ q, m.state = .parser q := by
            intro k hk m hm
            have hk' : k + 1 < (a :: rest).length := by simpa using hk
            apply hparser (k + 1) hk' m
            simpa [List.take_succ_cons, run_cons, hs] using hm
          exact DeterministicPrefix.cons hs hna huniq (ih mid hrest hparser')

def outer_first_hit_prefix_spec : Prop :=
  (∀ {State Tape : Type*} [Fintype State] [Fintype Tape]
      [DecidableEq State] [DecidableEq Tape]
      (P : Program State Tape) (movable : Tape → Bool) (accept : State)
      (B : ℕ) (start : Config State Tape),
    Finite (FirstAcceptingWordsAtMost P movable accept B start)) ∧
  (∀ {State Tape : Type*} [Fintype State] [Fintype Tape]
      [DecidableEq State] [DecidableEq Tape]
      (P : Program State Tape) (movable : Tape → Bool) (accept : State)
      {labels : List (Arrow P)} {start finish : Config State Tape},
    DeterministicPrefix P movable accept labels start finish →
      run P movable labels start = some finish) ∧
  (∀ {State Tape : Type*} [Fintype State] [Fintype Tape]
      [DecidableEq State] [DecidableEq Tape]
      (P : Program State Tape) (movable : Tape → Bool) (accept : State)
      {pre : List (Arrow P)} {start middle : Config State Tape} {T : ℕ},
    DeterministicPrefix P movable accept pre start middle →
      Nonempty
        (FirstAcceptingWordsAtMost P movable accept (pre.length + T) start ≃
          FirstAcceptingWordsAtMost P movable accept T middle)) ∧
  (∀ {State Tape : Type*} [Fintype State] [Fintype Tape]
      [DecidableEq State] [DecidableEq Tape]
      (P : Program State Tape) (movable : Tape → Bool) (accept : State)
      {pre : List (Arrow P)} {start middle : Config State Tape} {B : ℕ},
    DeterministicPrefix P movable accept pre start middle →
      B < pre.length → firstAcceptingCount P movable accept B start = 0) ∧
  (∀ (c : Config MStarULogAssembly.State MStarULogAssembly.Tape)
      (q : MStarULogAssembly.ParserControl)
      (a b : MStarULogAssembly.Arrow)
      (d e : Config MStarULogAssembly.State MStarULogAssembly.Tape),
    c.state = .parser q →
      step MStarULogAssembly.program MStarOuterProgram.movable c a = some d →
        step MStarULogAssembly.program MStarOuterProgram.movable c b = some e →
          a = b ∧ d = e) ∧
  (∀ (c : PakMStarCouplingCorrectness.MStarConfig) (N : ℕ),
    Nonempty
      (FirstAcceptingWordsAtMost MStarULogAssembly.program
        MStarOuterProgram.movable .accept N c ≃ FirstHitWordsAtMost c N))

theorem outer_first_hit_prefix_spec_holds :
    outer_first_hit_prefix_spec := by
  refine ⟨?fin, ?run, ?equiv, ?zero, ?uniq, ?bridge⟩
  · intro State Tape _ _ _ _ P movable accept B start
    exact firstAcceptingWords_finite P movable accept B start
  · intro State Tape _ _ _ _ P movable accept labels start finish h
    exact deterministicPrefix_run h
  · intro State Tape _ _ _ _ P movable accept pre start middle T hpre
    exact ⟨firstHit_prefix_equiv hpre⟩
  · intro State Tape _ _ _ _ P movable accept pre start middle B hpre hB
    exact firstHit_short_zero hpre hB
  · exact parser_occupied_arrow_unique
  · exact fun c N => ⟨firstAcceptingWords_equiv_firstHit c N⟩

end PakFixedPolyomino.PakOuterFirstHitPrefix
