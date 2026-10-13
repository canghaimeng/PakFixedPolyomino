import PakFixedPolyomino.PakOuterParserReflection
import PakFixedPolyomino.PakSlotOneFullFrameReflection

/-! # Prefix reflection for literal outer parser runs

This module keeps the long-run argument separate from the local zipper
reflection.  Its basic induction atom is deliberately stated against a
literal successful outer arrow, so a parser acceptance proof never acquires
an abstract action or a reachability witness as an extra premise.
-/

namespace PakFixedPolyomino.PakOuterParserPrefixReflection

open PakMStarCouplingCorrectness
open PakParserOuterBridge
open PakOuterParserReflection
open PakFullFrameTableauReadback

/-- A successful outer transition out of the literal reject state again has
reject as target.  Only the state claim is needed for suffix exclusion; it
does not assume that the labelled arrow is a chosen reject loop. -/
theorem outerStep_from_reject_target_reject
    (c d : OuterConfig) (a : OuterArrow)
    (hreject : c.state = MStarOuterProgram.State.reject)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some d) :
    d.state = MStarOuterProgram.State.reject := by
  have hsource := FiniteOneTapeSemantics.step_some_forces_source
    MStarULogAssembly.program MStarOuterProgram.movable c d a hstep
  have hq : a.1.1.1 = MStarOuterProgram.State.reject :=
    hsource.1.symm.trans hreject
  have htarget := FiniteOneTapeSemantics.step_some_state
    MStarULogAssembly.program MStarOuterProgram.movable c d a hstep
  rcases a with ⟨⟨⟨q, x⟩, slot⟩, hoccupied⟩
  change q = MStarOuterProgram.State.reject at hq
  subst q
  change d.state =
    (FiniteOneTapeProgram.actionOf MStarULogAssembly.program
      ⟨((MStarOuterProgram.State.reject, x), slot), hoccupied⟩).target at htarget
  cases x <;> fin_cases slot <;>
    simp [MStarULogAssembly.program, MStarULogAssembly.data,
      MStarOuterProgram.program, FiniteOneTapeProgram.actionOf] at hoccupied htarget ⊢ <;>
    exact htarget

/-- Reject is absorbing along every suffix of a literal indexed outer run. -/
theorem uniformRun_reject_suffix
    {width n : ℕ} (R : UniformWindowedMStarRun width n)
    (t : Fin (n + 1))
    (hreject : (R.config t).state = MStarOuterProgram.State.reject) :
    ∀ k : ℕ, ∀ hk : t.1 + k ≤ n,
      (R.config ⟨t.1 + k, Nat.lt_succ_of_le hk⟩).state =
        MStarOuterProgram.State.reject := by
  intro k hk
  induction k with
  | zero => simpa using hreject
  | succ k ih =>
      have hk' : t.1 + k < n := by
        apply lt_of_lt_of_le (show t.1 + k < t.1 + (k + 1) by omega)
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hk
      let i : Fin n := ⟨t.1 + k, hk'⟩
      have hstep := R.step i
      have hprev : (R.config ⟨i.1, Nat.lt_succ_of_lt i.2⟩).state =
          MStarOuterProgram.State.reject := by
        simpa [i] using ih (by omega)
      have hnext := outerStep_from_reject_target_reject
        (R.config ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
        (R.config ⟨i.1 + 1, by omega⟩) (R.arrow i) hprev hstep
      simpa [i, Nat.add_assoc] using hnext

/-- The local backward-induction atom: once the literal successor window is
known to have a successful finite parser continuation, the preceding
non-copy outer parser state has one as well. -/
theorem canAcceptResult_of_noncopy_outer_parser_step
    (n : ℕ) (p p' : MStarParserMicrocode.ParserState)
    (c d : OuterConfig) (a : OuterArrow) (h h' : Fin n)
    (hstate : c.state = .parser (.inl p))
    (hstate' : d.state = .parser (.inl p'))
    (hp : p ≠ MStarParserMicrocode.copyStart)
    (hhead : c.head = h.1) (hhead' : d.head = h'.1)
    (hhash : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → c.tape z = .hash)
    (hhash' : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → d.tape z = .hash)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some d)
    (haccept : MStarParserSoundness.CanAcceptResult
      (.running p' (windowZipper n d h'))) :
    MStarParserSoundness.CanAcceptResult
      (.running p (windowZipper n c h)) := by
  have hreflect := noncopy_parser_oneStep_reflection n p p' c d a h h'
    hstate hstate' hp hhead hhead' hhash hhash' hstep
  apply (MStarParserSoundness.canAcceptResult_oneStep_iff
    (.running p (windowZipper n c h))).mp
  simpa [hreflect] using haccept

/-- The terminal atom for the backward induction.  It is intentionally
zero-arrow at the parser level; the later copier-entry arrow belongs to the
outer continuation, not to `MStarParserExecution`. -/
theorem copyStart_window_canAccept
    (n : ℕ) (c : OuterConfig) (h : Fin n) :
    MStarParserSoundness.CanAcceptResult
      (.running MStarParserMicrocode.copyStart (windowZipper n c h)) := by
  apply (MStarParserSoundness.canAcceptResult_oneStep_iff
    (.running MStarParserMicrocode.copyStart (windowZipper n c h))).mp
  rw [copyStart_oneStep_windowZipper]
  exact MStarParserSoundness.canAcceptResult_copyReady _

/-- A finite literal parser prefix, read backwards from its `copyStart`
endpoint.  Every extension stores the actual labelled outer step and the two
window boundary facts needed by the local reflection theorem.  In particular
there is no abstract parser-action field. -/
inductive OuterParserPrefix (n : ℕ) :
    OuterConfig → Fin n → MStarParserMicrocode.ParserState → Prop
  | copyStart (c : OuterConfig) (h : Fin n) :
      OuterParserPrefix n c h MStarParserMicrocode.copyStart
  | step {c d : OuterConfig} {h h' : Fin n}
      {p p' : MStarParserMicrocode.ParserState} (a : OuterArrow)
      (hstate : c.state = .parser (.inl p))
      (hstate' : d.state = .parser (.inl p'))
      (hp : p ≠ MStarParserMicrocode.copyStart)
      (hhead : c.head = h.1) (hhead' : d.head = h'.1)
      (hhash : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → c.tape z = .hash)
      (hhash' : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → d.tape z = .hash)
      (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
        MStarOuterProgram.movable c a = some d)
      (tail : OuterParserPrefix n d h' p') :
      OuterParserPrefix n c h p

/-- Strong backward induction over a concrete parser prefix. -/
theorem OuterParserPrefix.canAccept {n : ℕ}
    {c : OuterConfig} {h : Fin n} {p : MStarParserMicrocode.ParserState}
    (P : OuterParserPrefix n c h p) :
    MStarParserSoundness.CanAcceptResult (.running p (windowZipper n c h)) := by
  induction P with
  | copyStart c h => exact copyStart_window_canAccept n c h
  | @step c d h h' p p' a hstate hstate' hp hhead hhead'
      hhash hhash' hstep tail ih =>
      exact canAcceptResult_of_noncopy_outer_parser_step n p p' c d a h h'
        hstate hstate' hp hhead hhead' hhash hhash' hstep ih

/-- On the slot-one full-frame branch, the first literal outer step enters
the concrete parser's fixed-zero control. -/
theorem slotOne_first_target_parserStart {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    ((FullFrame.toUniformWindowedRun F.1).config
      ⟨1, Nat.succ_lt_succ F.1.width_pos⟩).state =
        .parser (.inl (MStarParserMicrocode.fixed ⟨0, by decide⟩)) := by
  let R := FullFrame.toUniformWindowedRun F.1
  let t : Fin n := ⟨0, F.1.width_pos⟩
  have hstep := PakSlotOneFullFrameReflection.slotOne_first_step F
  have hsource := FiniteOneTapeSemantics.step_some_forces_source
    MStarULogAssembly.program MStarOuterProgram.movable
    (R.config ⟨0, Nat.zero_lt_succ n⟩)
    (R.config ⟨1, Nat.succ_lt_succ F.1.width_pos⟩) (R.arrow t) (by
      simpa [R, t] using hstep)
  have htarget := FiniteOneTapeSemantics.step_some_state
    MStarULogAssembly.program MStarOuterProgram.movable
    (R.config ⟨0, Nat.zero_lt_succ n⟩)
    (R.config ⟨1, Nat.succ_lt_succ F.1.width_pos⟩) (R.arrow t) (by
      simpa [R, t] using hstep)
  have hq : (R.arrow t).1.1.1 = MStarOuterProgram.State.start := by
    exact hsource.1.symm.trans (by
      simpa [R] using FullFrame.uniform_initial_state_start F.1)
  have hslot : (R.arrow t).1.2 = 1 := by simpa [R, t] using F.2
  generalize harrow : R.arrow t = A at hq hslot htarget
  rcases A with ⟨⟨⟨q, x⟩, slot⟩, hoccupied⟩
  change q = MStarOuterProgram.State.start at hq
  subst q
  change slot = 1 at hslot
  subst slot
  cases x with
  | core a =>
      by_cases hinitial : MStarOuterProgram.isInitialLetter MStarULogAssembly.data a = true
      · let act : FiniteOneTapeProgram.Action MStarULogAssembly.State
            MStarULogAssembly.Tape :=
          { write := .core a, target := .parser MStarULogAssembly.data.parserStart,
            move := .stay }
        have hrule : MStarULogAssembly.program.rule .start (.core a) 1 =
            some act := by
          simpa [act] using MStarOuterProgram.start_slot_one
            MStarULogAssembly.data hinitial
        have haction : FiniteOneTapeProgram.actionOf MStarULogAssembly.program
            ⟨((MStarOuterProgram.State.start, .core a), (1 : Fin 2)), hoccupied⟩ = act := by
          unfold FiniteOneTapeProgram.actionOf
          split
          · rename_i found hfound
            exact Option.some.inj (hfound.symm.trans hrule)
          · rename_i hnone
            exact (hoccupied hnone).elim
        change (R.config ⟨1, Nat.succ_lt_succ F.1.width_pos⟩).state =
          (FiniteOneTapeProgram.actionOf MStarULogAssembly.program
            ⟨((MStarOuterProgram.State.start, .core a), (1 : Fin 2)),
              hoccupied⟩).target at htarget
        rw [haction] at htarget
        simpa [act, MStarULogAssembly.data, MStarCopierMicrocode.attach] using htarget
      · simp [MStarULogAssembly.program, MStarOuterProgram.program,
          hinitial] at hoccupied
  | hash => simp [MStarULogAssembly.program, MStarOuterProgram.program] at hoccupied
  | markL => simp [MStarULogAssembly.program, MStarOuterProgram.program] at hoccupied
  | markR => simp [MStarULogAssembly.program, MStarOuterProgram.program] at hoccupied
  | scratch i => simp [MStarULogAssembly.program, MStarOuterProgram.program] at hoccupied

/-- Slot-one specialization of the generic prefix theorem.  The prefix is
anchored at chronological time one, whose parser control is proved above
directly from the occupied first arrow. -/
theorem slotOne_parserPrefix_canAccept {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n)
    (P : OuterParserPrefix n
      ((FullFrame.toUniformWindowedRun F.1).config
        ⟨1, Nat.succ_lt_succ F.1.width_pos⟩)
      ((FullFrame.toUniformWindowedRun F.1).head_index
        ⟨1, Nat.succ_lt_succ F.1.width_pos⟩)
      (MStarParserMicrocode.fixed ⟨0, by decide⟩)) :
    MStarParserSoundness.CanAcceptResult (.running
      (MStarParserMicrocode.fixed ⟨0, by decide⟩)
      (windowZipper n
        ((FullFrame.toUniformWindowedRun F.1).config
          ⟨1, Nat.succ_lt_succ F.1.width_pos⟩)
        ((FullFrame.toUniformWindowedRun F.1).head_index
          ⟨1, Nat.succ_lt_succ F.1.width_pos⟩))) :=
  P.canAccept

end PakFixedPolyomino.PakOuterParserPrefixReflection
