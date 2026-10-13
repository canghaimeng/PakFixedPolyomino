import PakFixedPolyomino.ULogFiniteTapeStageComposition

/-! Inversion of every raw word of literal finite bytecode sequencing.
No determinism is assumed: the original labels and their multiplicities
remain in the first and second words. The handoff has one false label.
These are structural lemmas, not a closed physical loader theorem. -/

namespace PakFixedPolyomino.ULogFiniteTapeStageCompositionRuns

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeStageComposition
open FiniteOneTapeSemantics (moveHead)

variable {ns ms nt : Nat}

theorem right_halted (z : BoundedConfig ms nt) :
    boundedHalted (rightConfig (ns := ns) z) = boundedHalted z := by
  by_cases h : z.state.val < 2
  · simp [boundedHalted, rightConfig, rightState, h]
  · simp [boundedHalted, rightConfig, rightState, h]
    omega

theorem run_right_map (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (handoff : OneTapeTableau.Move)
    (blank : Fin nt) (w : List Bool) (head : Int) (z : BoundedConfig ms nt) :
    run (program p q hns hms handoff) blank w head (rightConfig z) =
      (run q blank w head z).map (fun hz => (hz.1, rightConfig hz.2)) := by
  induction w generalizing head z with
  | nil => rfl
  | cons slot rest ih =>
      cases hh : boundedHalted z with
      | true => simp [run, right_halted, hh]
      | false =>
          cases hr : q.rule z.state z.focus slot with
          | none =>
              simp only [run, right_halted, hh, Bool.false_eq_true, ↓reduceIte]
              rw [show (rightConfig z).state = rightState z.state by rfl,
                show (rightConfig z).focus = z.focus by rfl,
                rule_right p q hns hms handoff z slot hh, hr]
              rfl
          | some a =>
              simp only [run, right_halted, hh, Bool.false_eq_true, ↓reduceIte]
              rw [show (rightConfig z).state = rightState z.state by rfl,
                show (rightConfig z).focus = z.focus by rfl,
                rule_right p q hns hms handoff z slot hh, hr]
              change run (program p q hns hms handoff) blank rest
                (moveHead a.move head) (applyBounded blank (rightConfig z) (rightAction a)) = _
              rw [apply_right]
              exact ih _ _

theorem left_reject_halted (z : BoundedConfig ns nt) (hz : z.state.val = 1) :
    boundedHalted (leftConfig (ms := ms) z) = true := by
  simp [boundedHalted, leftConfig, leftState, hz]

theorem left_accept_live (hns : 3 ≤ ns) (z : BoundedConfig ns nt)
    (hz : z.state.val = 0) :
    boundedHalted (leftConfig (ms := ms) z) = false := by
  simp [boundedHalted, leftConfig, leftState, hz, show ¬ ns < 2 by omega]

theorem left_accept_rule (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (handoff : OneTapeTableau.Move)
    (z : BoundedConfig ns nt) (hz : z.state.val = 0) (slot : Bool) :
    (program p q hns hms handoff).rule (leftConfig z).state (leftConfig (ms := ms) z).focus slot =
      if slot then none else some ⟨z.focus, rightState (⟨2, by omega⟩ : Fin ms), handoff⟩ := by
  simp [program, leftConfig, leftState, hz]

theorem handoff_apply (hms : 3 ≤ ms) (blank : Fin nt)
    (handoff : OneTapeTableau.Move) (z : BoundedConfig ns nt) :
    applyBounded blank (leftConfig z)
        ⟨z.focus, rightState (⟨2, by omega⟩ : Fin ms), handoff⟩ =
      rightConfig (secondStart hms blank handoff z) := by
  cases hm : handoff <;> cases hl : z.leftRev <;> cases hr : z.right <;>
    simp [applyBounded, leftConfig, rightConfig, secondStart, hl, hr]

theorem every_raw_run_splits (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (handoff : OneTapeTableau.Move)
    (blank : Fin nt) (w : List Bool) (head hf : Int)
    (z : BoundedConfig ns nt) (zf : BoundedConfig (stateCount ns ms) nt)
    (hw : run (program p q hns hms handoff) blank w head (leftConfig z) = some (hf, zf)) :
    (∃ zp, run p blank w head z = some (hf, zp) ∧ zf = leftConfig zp) ∨
      ∃ u v mid zp zq,
        w = u ++ false :: v ∧ run p blank u head z = some (mid, zp) ∧
        zp.state.val = 0 ∧
        run q blank v (moveHead handoff mid) (secondStart hms blank handoff zp) =
          some (hf, zq) ∧ zf = rightConfig zq := by
  induction w generalizing head z with
  | nil =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at hw
      rcases hw with ⟨rfl, rfl⟩
      exact Or.inl ⟨z, rfl, rfl⟩
  | cons slot rest ih =>
      by_cases hzero : z.state.val = 0
      · cases slot with
        | true =>
            simp [run, left_accept_live hns z hzero,
              left_accept_rule p q hns hms handoff z hzero] at hw
        | false =>
            have htail : run (program p q hns hms handoff) blank rest
                (moveHead handoff head) (rightConfig (secondStart hms blank handoff z)) =
                  some (hf, zf) := by
              simp only [run, left_accept_live hns z hzero, Bool.false_eq_true,
                ↓reduceIte] at hw
              rw [left_accept_rule p q hns hms handoff z hzero] at hw
              change run (program p q hns hms handoff) blank rest
                (moveHead handoff head) (applyBounded blank (leftConfig z)
                  ⟨z.focus, rightState (⟨2, by omega⟩ : Fin ms), handoff⟩) = _ at hw
              rw [handoff_apply] at hw
              exact hw
            rw [run_right_map] at htail
            obtain ⟨hz, hq, heq⟩ := Option.map_eq_some_iff.mp htail
            have he := Prod.mk.inj heq
            rcases hz with ⟨headq, zq⟩
            dsimp at he
            rcases he with ⟨rfl, hzq⟩
            exact Or.inr ⟨[], rest, head, z, zq, rfl, rfl, hzero, hq, hzq.symm⟩
      · by_cases hone : z.state.val = 1
        · simp [run, left_reject_halted z hone] at hw
        · have hlive : boundedHalted z = false := by
            simp [boundedHalted]
            omega
          cases hr : p.rule z.state z.focus slot with
          | none =>
              simp only [run, left_live z hlive, Bool.false_eq_true, ↓reduceIte] at hw
              rw [show (leftConfig z).state = leftState z.state by rfl,
                show (leftConfig z).focus = z.focus by rfl,
                rule_left p q hns hms handoff z slot hlive, hr] at hw
              cases hw
          | some a =>
              have htail : run (program p q hns hms handoff) blank rest
                  (moveHead a.move head) (leftConfig (applyBounded blank z a)) =
                    some (hf, zf) := by
                simp only [run, left_live z hlive, Bool.false_eq_true, ↓reduceIte] at hw
                rw [show (leftConfig z).state = leftState z.state by rfl,
                  show (leftConfig z).focus = z.focus by rfl,
                  rule_left p q hns hms handoff z slot hlive, hr] at hw
                change run (program p q hns hms handoff) blank rest
                  (moveHead a.move head) (applyBounded blank (leftConfig z) (leftAction a)) = _ at hw
                rw [apply_left] at hw
                exact hw
              rcases ih _ _ htail with hfirst | hsecond
              · obtain ⟨zp, hp, hfz⟩ := hfirst
                refine Or.inl ⟨zp, ?_, hfz⟩
                simpa [run, hlive, hr] using hp
              · obtain ⟨u, v, mid, zp, zq, he, hp, ha, hq, hfz⟩ := hsecond
                refine Or.inr ⟨slot :: u, v, mid, zp, zq, ?_, ?_, ha, hq, hfz⟩
                · simpa using congrArg (List.cons slot) he
                · simpa [run, hlive, hr] using hp

theorem left_not_accepts (hns : 3 ≤ ns) (z : BoundedConfig ns nt) :
    (leftConfig (ms := ms) z).state.val ≠ 0 := by
  by_cases h : z.state.val = 0 <;> simp [leftConfig, leftState, h]
  omega

theorem right_accepts_iff (z : BoundedConfig ms nt) :
    (rightConfig (ns := ns) z).state.val = 0 ↔ z.state.val = 0 := by
  by_cases h : z.state.val < 2
  · simp [rightConfig, rightState, h]
  · simp [rightConfig, rightState, h]
    omega

theorem every_accepting_run_splits (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (handoff : OneTapeTableau.Move)
    (blank : Fin nt) (w : List Bool) (head hf : Int)
    (z : BoundedConfig ns nt) (zf : BoundedConfig (stateCount ns ms) nt)
    (hw : run (program p q hns hms handoff) blank w head (leftConfig z) = some (hf, zf))
    (ha : zf.state.val = 0) :
    ∃ u v mid zp zq,
      w = u ++ false :: v ∧ run p blank u head z = some (mid, zp) ∧
      zp.state.val = 0 ∧
      run q blank v (moveHead handoff mid) (secondStart hms blank handoff zp) =
        some (hf, zq) ∧ zq.state.val = 0 ∧ zf = rightConfig zq := by
  rcases every_raw_run_splits p q hns hms handoff blank w head hf z zf hw with hp | hq
  · obtain ⟨zp, _, rfl⟩ := hp
    exact (left_not_accepts hns zp ha).elim
  · obtain ⟨u, v, mid, zp, zq, he, hp, hap, hq, hfz⟩ := hq
    refine ⟨u, v, mid, zp, zq, he, hp, hap, hq, ?_, hfz⟩
    exact (right_accepts_iff zq).mp (hfz ▸ ha)

theorem deterministic_first_stage_split (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (handoff : OneTapeTableau.Move)
    (blank : Fin nt) (falseOnly : ULogFiniteAlphabetDeterministicRuns.FalseOnly p)
    (L : Nat) (head mid : Int) (z zp : BoundedConfig ns nt)
    (hp : run p blank (List.replicate L false) head z = some (mid, zp))
    (ha : zp.state.val = 0) (w : List Bool) (hf : Int)
    (zf : BoundedConfig (stateCount ns ms) nt)
    (hw : run (program p q hns hms handoff) blank w head (leftConfig z) = some (hf, zf)) :
    (w.length ≤ L ∧ ∃ z', run p blank w head z = some (hf, z') ∧ zf = leftConfig z') ∨
      ∃ v zq, w = List.replicate L false ++ false :: v ∧
        run q blank v (moveHead handoff mid) (secondStart hms blank handoff zp) =
          some (hf, zq) ∧ zf = rightConfig zq := by
  rcases every_raw_run_splits p q hns hms handoff blank w head hf z zf hw with hfirst | hsecond
  · obtain ⟨z', hp', hfz⟩ := hfirst
    refine Or.inl ⟨?_, z', hp', hfz⟩
    exact ULogFiniteAlphabetDeterministicRuns.successful_zipper_length_le
      blank p falseOnly L head z zp mid hp ha hp'
  · obtain ⟨u, v, mid', zp', zq, he, hp', ha', hq, hfz⟩ := hsecond
    obtain ⟨hu, hm, hz⟩ := ULogFiniteAlphabetDeterministicRuns.accepting_zipper_word_eq
      blank p falseOnly L head z zp mid hp ha hp' ha'
    subst u
    subst mid'
    subst zp'
    exact Or.inr ⟨v, zq, he, hq, hfz⟩

theorem program_falseOnly (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (handoff : OneTapeTableau.Move)
    (hp : ULogFiniteAlphabetDeterministicRuns.FalseOnly p)
    (hq : ULogFiniteAlphabetDeterministicRuns.FalseOnly q) :
    ULogFiniteAlphabetDeterministicRuns.FalseOnly (program p q hns hms handoff) := by
  dsimp [ULogFiniteAlphabetDeterministicRuns.FalseOnly] at hp hq ⊢
  intro state read
  simp [program, hp, hq]

end PakFixedPolyomino.ULogFiniteTapeStageCompositionRuns
