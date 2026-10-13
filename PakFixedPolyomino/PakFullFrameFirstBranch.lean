import PakFixedPolyomino.PakFullFrameUniformReadback
import PakFixedPolyomino.PakScannerBaselineAutomaton

/-! # The first outer branch read from a literal FullFrame -/

namespace PakFixedPolyomino.PakFullFrameTableauReadback

open PakMStarCouplingCorrectness

/-- The unique head in the east old tableau column is emitted by a scanner
head buffer, hence carries the literal outer start state. -/
theorem FullFrame.east_before_state_start {w h : ℕ} (F : FullFrame w h) :
    (tableau_column_readback F (eastIndex F.width_pos)).before.state =
      MStarOuterProgram.State.start := by
  let east := tableau_column_readback F (eastIndex F.width_pos)
  rcases F.east_emits_tableau_window east.head with
    ⟨s, t, hscan, hold⟩
  have hold' : east.oldStrip east.head =
      PakCouplingGenerated.emittedWindow MStarULogAssembly.boundaryData s t := by
    simpa [east] using hold
  have hcenter := congrArg CellTriple.center hold'
  change ((east.oldStrip east.head).center.headSourceOf east.head_is_head).1 =
    MStarOuterProgram.State.start
  have hhead := east.head_is_head
  rcases s with ⟨phase, left, centre, lookahead, mode⟩
  cases centre with
  | hash | zero | one | work | rightEnd =>
      rw [hcenter] at hhead
      simp [PakCouplingGenerated.emittedWindow,
        PakCouplingGenerated.bufferCell, TableauCell.isHead,
        MStarULogAssembly.boundaryData, MStarOuterProgram.boundaryData,
        MStarULogAssembly.data, MStarCopierMicrocode.attach] at hhead
  | headZero =>
      have hsource := WindowedMStarStep.headSourceOf_eq_of_eq hcenter
        east.head_is_head
      rw [hsource]
      rfl
  | headOne =>
      have hsource := WindowedMStarStep.headSourceOf_eq_of_eq hcenter
        east.head_is_head
      rw [hsource]
      rfl

theorem FullFrame.uniform_initial_state_start {w h : ℕ} (F : FullFrame w h) :
    ((toUniformWindowedRun F).config ⟨0, Nat.zero_lt_succ _⟩).state =
      MStarOuterProgram.State.start := by
  change (reverse_tableau_config F ⟨0, Nat.zero_lt_succ _⟩).state = _
  rw [reverse_tableau_config_of_lt F _ F.width_pos]
  simpa [reverseColumn, eastIndex] using east_before_state_start F

/-- The fixed outer program has exactly the two labelled start slots. -/
theorem FullFrame.firstArrow_slot_zero_or_one {w h : ℕ}
    (F : FullFrame w h) :
    ((toUniformWindowedRun F).arrow ⟨0, F.width_pos⟩).1.2 = 0 ∨
      ((toUniformWindowedRun F).arrow ⟨0, F.width_pos⟩).1.2 = 1 := by
  let slot := ((toUniformWindowedRun F).arrow ⟨0, F.width_pos⟩).1.2
  change slot = 0 ∨ slot = 1
  have hv : slot.1 = 0 ∨ slot.1 = 1 := by
    have hlt := slot.2
    omega
  rcases hv with hv | hv
  · exact Or.inl (Fin.eq_of_val_eq hv)
  · exact Or.inr (Fin.eq_of_val_eq hv)

private theorem actionOf_eq_of_rule_eq
    {State Tape : Type*} [Fintype State] [Fintype Tape]
    [DecidableEq State] [DecidableEq Tape]
    (P : FiniteOneTapeProgram.Program State Tape)
    (a : FiniteOneTapeProgram.Arrow P)
    (act : FiniteOneTapeProgram.Action State Tape)
    (h : P.rule a.1.1.1 a.1.1.2 a.1.2 = some act) :
    FiniteOneTapeProgram.actionOf P a = act := by
  unfold FiniteOneTapeProgram.actionOf
  split
  · rename_i found hfound
    exact Option.some.inj (hfound.symm.trans h)
  · rename_i hnone
    exact (a.2 hnone).elim

theorem firstArrow_target_accept_of_slot_zero
    (a : MStarULogAssembly.Arrow)
    (hsource : (FiniteOneTapeProgram.transition MStarULogAssembly.program a).sourceState =
      MStarOuterProgram.State.start)
    (hslot : a.1.2 = 0) :
    (FiniteOneTapeProgram.transition MStarULogAssembly.program a).targetState =
      MStarOuterProgram.State.accept := by
  rcases a with ⟨⟨⟨q, x⟩, slot⟩, ha⟩
  change q = MStarOuterProgram.State.start at hsource
  subst q
  change slot = 0 at hslot
  have ha0 : MStarULogAssembly.program.rule (.start : MStarULogAssembly.State)
      x 0 ≠ none := by simpa [hslot] using ha
  let a0 : MStarULogAssembly.Arrow := ⟨((.start, x), (0 : Fin 2)), ha0⟩
  have heq : (⟨((.start, x), slot), ha⟩ : MStarULogAssembly.Arrow) = a0 := by
    apply Subtype.ext
    simp [a0, hslot]
  rw [heq]
  dsimp only [a0]
  cases x with
  | core core =>
      by_cases hinit : MStarOuterProgram.isInitialLetter MStarULogAssembly.data core = true
      · have hrule := MStarOuterProgram.start_slot_zero
          MStarULogAssembly.data hinit
        have haction := actionOf_eq_of_rule_eq MStarULogAssembly.program
          ⟨((.start, .core core), (0 : Fin 2)), ha0⟩
          { write := .core core, target := .accept, move := .stay } hrule
        simpa [FiniteOneTapeProgram.transition, haction]
      · have hinitFalse :
            MStarOuterProgram.isInitialLetter MStarULogAssembly.data core = false :=
          Bool.eq_false_of_not_eq_true hinit
        have hnone := MStarOuterProgram.start_no_other_letter
          MStarULogAssembly.data hinitFalse (0 : Fin 2)
        exact (ha0 hnone).elim
  | hash => simp [MStarULogAssembly.program, MStarOuterProgram.program] at ha0
  | markL => simp [MStarULogAssembly.program, MStarOuterProgram.program] at ha0
  | markR => simp [MStarULogAssembly.program, MStarOuterProgram.program] at ha0
  | scratch i => simp [MStarULogAssembly.program, MStarOuterProgram.program] at ha0

theorem FullFrame.slotZero_first_target_accept {w h : ℕ}
    (F : FullFrame w h)
    (hslot : ((toUniformWindowedRun F).arrow ⟨0, F.width_pos⟩).1.2 = 0) :
    ((toUniformWindowedRun F).config ⟨1, by have := F.width_pos; omega⟩).state =
      MStarOuterProgram.State.accept := by
  let R := toUniformWindowedRun F
  let t : Fin w := ⟨0, F.width_pos⟩
  have hstep := R.step t
  have hsrc := FiniteOneTapeSemantics.step_some_forces_source
    MStarULogAssembly.program MStarOuterProgram.movable
    (R.config ⟨0, Nat.lt_succ_of_lt F.width_pos⟩)
    (R.config ⟨1, by have := F.width_pos; omega⟩) (R.arrow t) hstep
  have hsource :
      (FiniteOneTapeProgram.transition MStarULogAssembly.program
        (R.arrow t)).sourceState = MStarOuterProgram.State.start := by
    rw [← hsrc.1]
    exact uniform_initial_state_start F
  have htarget := firstArrow_target_accept_of_slot_zero (R.arrow t)
    hsource hslot
  have hstate := FiniteOneTapeSemantics.step_some_state
    MStarULogAssembly.program MStarOuterProgram.movable
    (R.config ⟨0, Nat.lt_succ_of_lt F.width_pos⟩)
    (R.config ⟨1, by have := F.width_pos; omega⟩) (R.arrow t) hstep
  exact hstate.trans htarget

/-- Every successful outer step from the literal accept state is its unique
slot-zero stay loop and leaves the complete configuration unchanged. -/
theorem accept_successor_eq_self
    (c d : MStarConfig) (a : MStarULogAssembly.Arrow)
    (haccept : c.state = MStarOuterProgram.State.accept)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some d) : d = c := by
  have hsrc := FiniteOneTapeSemantics.step_some_forces_source
    MStarULogAssembly.program MStarOuterProgram.movable c d a hstep
  have hsource : a.1.1.1 = MStarOuterProgram.State.accept := by
    change (FiniteOneTapeProgram.transition MStarULogAssembly.program a).sourceState = _
    exact hsrc.1.symm.trans haccept
  let read : MStarULogAssembly.Tape := a.1.1.2
  have hread : c.tape c.head = read := hsrc.2
  have hread_ne_hash : read ≠ MStarOuterProgram.Tape.hash := by
    intro hhash
    have hnone := MStarOuterProgram.sentinel_has_no_rule MStarULogAssembly.data
      (.accept : MStarULogAssembly.State) a.1.2 (by
        intro p hp
        cases hp)
    apply a.2
    simpa [read, hsource, hhash] using hnone
  have hslot : a.1.2 = 0 := by
    have hv : a.1.2.1 = 0 ∨ a.1.2.1 = 1 := by
      have := a.1.2.2
      omega
    rcases hv with hv | hv
    · exact Fin.eq_of_val_eq hv
    · have hone : a.1.2 = 1 := Fin.eq_of_val_eq hv
      have hnone := (MStarOuterProgram.accept_unique_stay
        MStarULogAssembly.data hread_ne_hash).2
      exfalso
      exact a.2 (by simpa [read, hsource, hone] using hnone)
  let act : FiniteOneTapeProgram.Action MStarULogAssembly.State
      MStarULogAssembly.Tape :=
    { write := read, target := .accept, move := .stay }
  have hrule : MStarULogAssembly.program.rule a.1.1.1 a.1.1.2 a.1.2 =
      some act := by
    have hzero := (MStarOuterProgram.accept_unique_stay
      MStarULogAssembly.data hread_ne_hash).1
    simpa [act, read, hsource, hslot] using hzero
  have haction : FiniteOneTapeProgram.actionOf MStarULogAssembly.program a = act :=
    actionOf_eq_of_rule_eq MStarULogAssembly.program a act hrule
  have htape : FiniteOneTapeSemantics.writtenTape c read = c.tape := by
    funext z
    by_cases hz : z = c.head
    · subst z
      simp [FiniteOneTapeSemantics.writtenTape, Function.update, hread]
    · simp [FiniteOneTapeSemantics.writtenTape, Function.update, hz]
  have hmovable : MStarOuterProgram.movable read = true := by
    cases hreadcase : read with
    | core x => simp [hreadcase, MStarOuterProgram.movable]
    | hash => exact (hread_ne_hash hreadcase).elim
    | markL => simp [hreadcase, MStarOuterProgram.movable]
    | markR => simp [hreadcase, MStarOuterProgram.movable]
    | scratch k => simp [hreadcase, MStarOuterProgram.movable]
  have hc : (⟨MStarOuterProgram.State.accept, c.head, c.tape⟩ : MStarConfig) = c := by
    cases c with
    | mk state head tape =>
        simp only at haccept ⊢
        subst state
        rfl
  have hself : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some c := by
    simp [FiniteOneTapeSemantics.step, FiniteOneTapeProgram.transition,
      haction, hsource, hread, act, FiniteOneTapeSemantics.moveHead,
      htape, hmovable, haccept, hc, read]
  rw [hself] at hstep
  exact (Option.some.inj hstep).symm

/-- Two occupied arrows that both execute from the same configuration and
carry the same slot label are definitionally the same labelled arrow. -/
theorem arrow_eq_of_successful_steps_same_slot
    (c d e : MStarConfig) (a b : MStarULogAssembly.Arrow)
    (ha : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some d)
    (hb : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c b = some e)
    (hslot : a.1.2 = b.1.2) : a = b := by
  have hsa := FiniteOneTapeSemantics.step_some_forces_source
    MStarULogAssembly.program MStarOuterProgram.movable c d a ha
  have hsb := FiniteOneTapeSemantics.step_some_forces_source
    MStarULogAssembly.program MStarOuterProgram.movable c e b hb
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · exact hsa.1.symm.trans hsb.1
    · exact hsa.2.symm.trans hsb.2
  · exact hslot

/-- Every successful arrow out of accept uses the unique occupied slot zero. -/
theorem accept_successful_arrow_slot_zero
    (c d : MStarConfig) (a : MStarULogAssembly.Arrow)
    (haccept : c.state = MStarOuterProgram.State.accept)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some d) : a.1.2 = 0 := by
  have hsrc := FiniteOneTapeSemantics.step_some_forces_source
    MStarULogAssembly.program MStarOuterProgram.movable c d a hstep
  have hsource : a.1.1.1 = MStarOuterProgram.State.accept := hsrc.1.symm.trans haccept
  let read : MStarULogAssembly.Tape := a.1.1.2
  have hread_ne_hash : read ≠ MStarOuterProgram.Tape.hash := by
    intro hhash
    have hnone := MStarOuterProgram.sentinel_has_no_rule MStarULogAssembly.data
      (.accept : MStarULogAssembly.State) a.1.2 (by intro p hp; cases hp)
    exact a.2 (by simpa [read, hsource, hhash] using hnone)
  have hv : a.1.2.1 = 0 ∨ a.1.2.1 = 1 := by omega
  rcases hv with hv | hv
  · exact Fin.eq_of_val_eq hv
  · have hone : a.1.2 = 1 := Fin.eq_of_val_eq hv
    have hnone := (MStarOuterProgram.accept_unique_stay
      MStarULogAssembly.data hread_ne_hash).2
    exfalso
    exact a.2 (by simpa [read, hsource, hone] using hnone)

/-- On the slot-zero branch, every later tableau column is the same literal
accepting configuration as column one.  Thus no hidden machine choice remains
after the first labelled arrow. -/
theorem FullFrame.slotZero_config_succ_eq_first_accept {w h : ℕ}
    (F : FullFrame w h)
    (hslot : ((toUniformWindowedRun F).arrow ⟨0, F.width_pos⟩).1.2 = 0)
    (m : ℕ) (hm : m + 1 < w + 1) :
    (toUniformWindowedRun F).config ⟨m + 1, hm⟩ =
      (toUniformWindowedRun F).config ⟨1, by omega⟩ := by
  let R := toUniformWindowedRun F
  have hacceptOne : (R.config ⟨1, by omega⟩).state =
      MStarOuterProgram.State.accept := slotZero_first_target_accept F hslot
  induction m with
  | zero => rfl
  | succ m ih =>
      have hmPrev : m + 1 < w + 1 := by omega
      have ht : m + 1 < w := by omega
      let t : Fin w := ⟨m + 1, ht⟩
      have hstep := R.step t
      have haccept : (R.config ⟨m + 1, by omega⟩).state =
          MStarOuterProgram.State.accept := by
        rw [ih hmPrev hacceptOne]
        exact hacceptOne
      have heq := accept_successor_eq_self
        (R.config ⟨m + 1, by omega⟩)
        (R.config ⟨m + 1 + 1, by omega⟩) (R.arrow t) haccept (by
          simpa [t] using hstep)
      exact heq.trans (ih hmPrev hacceptOne)

end PakFixedPolyomino.PakFullFrameTableauReadback
