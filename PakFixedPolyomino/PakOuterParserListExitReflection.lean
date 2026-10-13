import PakFixedPolyomino.PakParserOuterBridge
import PakFixedPolyomino.PakSlotOneFullFrameReflection
import PakFixedPolyomino.PakOuterParserPrefixReflection

/-! # Ordinary list trace of a slot-one full frame

This module removes dependent chronological indexing from the literal outer
run before any first-exit argument is attempted.  It contains no exit search
or parser-prefix recursion.
-/

namespace PakFixedPolyomino.PakOuterParserListExitReflection

open PakParserOuterBridge
open PakOuterParserReflection
open PakFullFrameTableauReadback
open PakMStarCouplingCorrectness

abbrev OuterConfig := PakMStarCouplingCorrectness.MStarConfig

noncomputable def traceConfigs {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) : List OuterConfig :=
  List.ofFn (FullFrame.toUniformWindowedRun F.1).config

noncomputable def traceHeads {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) : List (Fin n) :=
  List.ofFn (FullFrame.toUniformWindowedRun F.1).head_index

noncomputable def traceArrows {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) : List OuterArrow :=
  List.ofFn (FullFrame.toUniformWindowedRun F.1).arrow

/-- A list presentation of the same fixed-window outer computation. -/
structure WindowedOuterListTrace (n : ℕ) where
  configs : List OuterConfig
  heads : List (Fin n)
  arrows : List OuterArrow
  configs_length : configs.length = n + 1
  heads_length : heads.length = n + 1
  arrows_length : arrows.length = n
  size_ge_two : 2 ≤ n
  step : ∀ t : Fin n,
    FiniteOneTapeSemantics.step MStarULogAssembly.program MStarOuterProgram.movable
      (configs.get ⟨t.1, by simpa [configs_length] using t.2⟩)
      (arrows.get ⟨t.1, by simpa [arrows_length] using t.2⟩) =
        some (configs.get ⟨t.1 + 1, by
          simpa [configs_length] using Nat.succ_lt_succ t.2⟩)
  head_eq : ∀ t : Fin (n + 1),
    (configs.get ⟨t.1, by simpa [configs_length] using t.2⟩).head =
      (heads.get ⟨t.1, by simpa [heads_length] using t.2⟩).1
  head_interior : ∀ t : Fin (n + 1),
    0 < (heads.get ⟨t.1, by simpa [heads_length] using t.2⟩).1 ∧
      (heads.get ⟨t.1, by simpa [heads_length] using t.2⟩).1 + 1 < n
  hash_outside : ∀ (t : Fin (n + 1)) (z : Int),
    z < 0 ∨ (n : Int) ≤ z →
      (configs.get ⟨t.1, by simpa [configs_length] using t.2⟩).tape z = .hash
  time_one_parserStart :
    (configs.get ⟨1, by rw [configs_length]; omega⟩).state =
        .parser (.inl (MStarParserMicrocode.fixed ⟨0, by decide⟩))
  final_accept :
    (configs.get ⟨n, by simpa [configs_length] using Nat.lt_succ_self n⟩).state =
      MStarOuterProgram.State.accept

theorem traceConfigs_length {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    (traceConfigs F).length = n + 1 := by
  simp [traceConfigs]

theorem traceHeads_length {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    (traceHeads F).length = n + 1 := by
  simp [traceHeads]

theorem traceArrows_length {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    (traceArrows F).length = n := by
  simp [traceArrows]

theorem traceConfigs_get {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) (t : Fin (n + 1)) :
    (traceConfigs F).get ⟨t.1, by simpa [traceConfigs] using t.2⟩ =
      (FullFrame.toUniformWindowedRun F.1).config t := by
  rw [List.get_eq_getElem]
  change (List.ofFn (FullFrame.toUniformWindowedRun F.1).config)[t.1] = _
  rw [List.getElem_ofFn]

theorem traceHeads_get {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) (t : Fin (n + 1)) :
    (traceHeads F).get ⟨t.1, by simpa [traceHeads] using t.2⟩ =
      (FullFrame.toUniformWindowedRun F.1).head_index t := by
  rw [List.get_eq_getElem]
  change (List.ofFn (FullFrame.toUniformWindowedRun F.1).head_index)[t.1] = _
  rw [List.getElem_ofFn]

theorem traceArrows_get {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) (t : Fin n) :
    (traceArrows F).get ⟨t.1, by simpa [traceArrows] using t.2⟩ =
      (FullFrame.toUniformWindowedRun F.1).arrow t := by
  rw [List.get_eq_getElem]
  change (List.ofFn (FullFrame.toUniformWindowedRun F.1).arrow)[t.1] = _
  rw [List.getElem_ofFn]

/-- The literal slot-one frame produces the promised ordinary list trace. -/
noncomputable def slotOneListTrace {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    WindowedOuterListTrace n where
  configs := traceConfigs F
  heads := traceHeads F
  arrows := traceArrows F
  configs_length := traceConfigs_length F
  heads_length := traceHeads_length F
  arrows_length := traceArrows_length F
  size_ge_two := FullFrame.height_ge_two F.1
  step := by
    intro t
    let U := FullFrame.toUniformWindowedRun F.1
    have h0 : (traceConfigs F).get
        ⟨t.1, by simpa [traceConfigs_length F] using Nat.lt_succ_of_lt t.2⟩ =
        U.config ⟨t.1, Nat.lt_succ_of_lt t.2⟩ := by
      simpa [U] using traceConfigs_get F ⟨t.1, Nat.lt_succ_of_lt t.2⟩
    have ha : (traceArrows F).get
        ⟨t.1, by simpa [traceArrows_length F] using t.2⟩ = U.arrow t := by
      simpa [U] using traceArrows_get F t
    have h1 : (traceConfigs F).get
        ⟨t.1 + 1, by simpa [traceConfigs_length F] using Nat.succ_lt_succ t.2⟩ =
        U.config ⟨t.1 + 1, by omega⟩ := by
      simpa [U] using traceConfigs_get F ⟨t.1 + 1, by omega⟩
    rw [h0, ha, h1]
    exact U.step t
  head_eq := by
    intro t
    let U := FullFrame.toUniformWindowedRun F.1
    have hc := traceConfigs_get F t
    have hh := traceHeads_get F t
    calc
      ((traceConfigs F).get ⟨t.1, by simpa [traceConfigs_length F] using t.2⟩).head =
          (U.config t).head := congrArg (fun q : OuterConfig => q.head)
            (by simpa [U] using hc)
      _ = U.origin + (U.head_index t).1 := U.head_eq t
      _ = (U.head_index t).1 := by
        have horigin : U.origin = 0 := by
          change (FullFrame.toUniformWindowedRun F.1).origin = 0
          simp only [FullFrame.toUniformWindowedRun]
        rw [horigin, zero_add]
      _ = ((traceHeads F).get
          ⟨t.1, by simpa [traceHeads_length F] using t.2⟩).1 := by
            rw [show (traceHeads F).get
              ⟨t.1, by simpa [traceHeads_length F] using t.2⟩ = U.head_index t by
                simpa [U] using hh]
  head_interior := by
    intro t
    let U := FullFrame.toUniformWindowedRun F.1
    have hh := traceHeads_get F t
    have hh' : (traceHeads F).get
        ⟨t.1, by simpa [traceHeads_length F] using t.2⟩ = U.head_index t := by
      simpa [U] using hh
    rw [hh']
    exact ⟨U.head_interior_left t, U.head_interior_right t⟩
  hash_outside := by
    intro t z hz
    let U := FullFrame.toUniformWindowedRun F.1
    have horigin : U.origin = 0 := by rfl
    have hu := U.hash_outside t z (by simpa [horigin] using hz)
    have hc := traceConfigs_get F t
    calc
      ((traceConfigs F).get ⟨t.1, by simpa [traceConfigs_length F] using t.2⟩).tape z =
          (U.config t).tape z := congrArg (fun q : OuterConfig => q.tape z)
            (by simpa [U] using hc)
      _ = .hash := hu
  time_one_parserStart := by
    let U := FullFrame.toUniformWindowedRun F.1
    have hc := traceConfigs_get F ⟨1, by
      have := F.1.width_pos
      omega⟩
    calc
      ((traceConfigs F).get ⟨1, by
        simpa [traceConfigs_length F] using Nat.succ_lt_succ
          (show 0 < n by have := F.1.width_pos; omega)⟩).state =
          (U.config ⟨1, by have := F.1.width_pos; omega⟩).state :=
        congrArg (fun q : OuterConfig => q.state) (by simpa [U] using hc)
      _ = .parser (.inl (MStarParserMicrocode.fixed ⟨0, by decide⟩)) := by
        simpa [U] using
          PakOuterParserPrefixReflection.slotOne_first_target_parserStart F
  final_accept := by
    let U := FullFrame.toUniformWindowedRun F.1
    have hc := traceConfigs_get F ⟨n, Nat.lt_succ_self n⟩
    calc
      ((traceConfigs F).get ⟨n, by simpa [traceConfigs_length F] using Nat.lt_succ_self n⟩).state =
          (U.config ⟨n, Nat.lt_succ_self n⟩).state :=
        congrArg (fun q : OuterConfig => q.state) (by simpa [U] using hc)
      _ = MStarOuterProgram.State.accept := by simpa [U] using U.final_accept

/-! ## Structural histories -/

/-- A finite outer computation with window data stored directly at each
structural cons.  This is the ordinary recursive object used below instead of
any first-exit minimisation. -/
inductive WindowedOuterHistory (n : ℕ) :
    OuterConfig → Fin n → List OuterArrow → OuterConfig → Fin n → Type
  | nil (c : OuterConfig) (h : Fin n) :
      WindowedOuterHistory n c h [] c h
  | cons {c d e : OuterConfig} {h h' h'' : Fin n} {as : List OuterArrow}
      (a : OuterArrow)
      (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
        MStarOuterProgram.movable c a = some d)
      (hhead : c.head = h.1) (hhead' : d.head = h'.1)
      (hhash : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → c.tape z = .hash)
      (hhash' : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → d.tape z = .hash)
      (tail : WindowedOuterHistory n d h' as e h'') :
      WindowedOuterHistory n c h (a :: as) e h''

/-- Reject propagates through every structural history. -/
theorem WindowedOuterHistory.reject_suffix {n : ℕ}
    {c d : OuterConfig} {h h' : Fin n} {as : List OuterArrow}
    (H : WindowedOuterHistory n c h as d h')
    (hreject : c.state = MStarOuterProgram.State.reject) :
    d.state = MStarOuterProgram.State.reject := by
  induction H with
  | nil c h => exact hreject
  | @cons c d e h h' h'' as a hstep hhead hhead' hhash hhash' tail ih =>
      apply ih
      exact PakOuterParserPrefixReflection.outerStep_from_reject_target_reject
        c d a hreject hstep

private def unitParserTargetGood
    (q : MStarOuterProgram.State MStarParserMicrocode.ParserState Unit) : Bool :=
  match q with
  | .parser _ | .reject => true
  | _ => false

private def unitParserOutcomeGood
    (o : Option (FiniteOneTapeProgram.Action
      (MStarOuterProgram.State MStarParserMicrocode.ParserState Unit) OuterTape)) : Bool :=
  match o with
  | none => true
  | some a => unitParserTargetGood a.target

private theorem noncopy_unit_outcome_good :
    ∀ (p : MStarParserMicrocode.ParserState) (x : OuterTape),
      p ≠ MStarParserMicrocode.copyStart →
      unitParserOutcomeGood (MStarParserMicrocode.step (UState := Unit)
        MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
        MStarConcreteAlphabet.work p x) = true := by
  native_decide

set_option maxRecDepth 10000 in
/-- The first actual transition of a history from a non-copy parser state
either remains in original parser control or reaches literal outer reject. -/
theorem history_noncopy_target_parser_or_reject {c d : OuterConfig}
    (p : MStarParserMicrocode.ParserState)
    (a : OuterArrow)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some d)
    (hstate : c.state = .parser (.inl p))
    (hp : p ≠ MStarParserMicrocode.copyStart) :
    (∃ p', d.state = (.parser (.inl p') : OuterState)) ∨
      d.state = MStarOuterProgram.State.reject := by
  rcases PakOuterParserReflection.parserUnitAction_of_outerStep
      p c d a hstate hp hstep with
    ⟨ua, hua, _slot, haction, hafter⟩
  have hkind := noncopy_unit_outcome_good p (c.tape c.head) hp
  rw [hua] at hkind
  simp only [unitParserOutcomeGood] at hkind
  change unitParserTargetGood ua.target = true at hkind
  generalize htarget : ua.target = target at hkind
  cases target with
  | parser p' =>
      left
      refine ⟨p', ?_⟩
      have hs := congrArg (fun q : OuterConfig => q.state) hafter
      simpa [afterAction, liftUnitParserAction, liftUnitParserState, htarget] using hs
  | reject =>
      right
      have hs := congrArg (fun q : OuterConfig => q.state) hafter
      simpa [afterAction, liftUnitParserAction, liftUnitParserState, htarget] using hs
  | start => contradiction
  | accept => contradiction
  | sim q => contradiction

/-- Structural backward reflection needs no first-exit index: a parser state
at the head of any literal history ending in accept has a concrete parser
prefix terminating at `copyStart`. -/
theorem WindowedOuterHistory.parserPrefix_to_accept {n : ℕ}
    {c e : OuterConfig} {h h' : Fin n} {as : List OuterArrow}
    (H : WindowedOuterHistory n c h as e h')
    (hfinal : e.state = MStarOuterProgram.State.accept)
    (p : MStarParserMicrocode.ParserState)
    (hstate : c.state = (.parser (.inl p) : OuterState)) :
    PakOuterParserPrefixReflection.OuterParserPrefix n c h p := by
  induction H generalizing p with
  | nil c h =>
      rw [hstate] at hfinal
      cases hfinal
  | @cons c d e h h' h'' as a hstep hhead hhead' hhash hhash' tail ih =>
      by_cases hp : p = MStarParserMicrocode.copyStart
      · subst p
        exact .copyStart c h
      · rcases history_noncopy_target_parser_or_reject p a hstep
            hstate hp with
          ⟨p', hstate'⟩ | hreject
        · exact .step a hstate hstate' hp hhead hhead' hhash hhash' hstep
            (ih hfinal p' hstate')
        · have hend := tail.reject_suffix hreject
          rw [hfinal] at hend
          cases hend

/-! ## Constructing structural histories from the ordinary trace -/

noncomputable def historyOfTraceFrom {n : ℕ}
    (T : WindowedOuterListTrace n) (k : ℕ) (hk : k ≤ n) :
    ∃ as : List OuterArrow,
      Nonempty (WindowedOuterHistory n
        (T.configs.get ⟨k, by simpa [T.configs_length] using Nat.lt_succ_of_le hk⟩)
        (T.heads.get ⟨k, by simpa [T.heads_length] using Nat.lt_succ_of_le hk⟩)
        as
        (T.configs.get ⟨n, by simpa [T.configs_length] using Nat.lt_succ_self n⟩)
        (T.heads.get ⟨n, by simpa [T.heads_length] using Nat.lt_succ_self n⟩)) := by
  by_cases hlast : k = n
  · subst k
    exact ⟨[], ⟨WindowedOuterHistory.nil _ _⟩⟩
  · have hklt : k < n := lt_of_le_of_ne hk hlast
    rcases historyOfTraceFrom T (k + 1) (by omega) with ⟨as, ⟨tail⟩⟩
    let i : Fin n := ⟨k, hklt⟩
    refine ⟨T.arrows.get ⟨k, by simpa [T.arrows_length] using hklt⟩ :: as, ⟨
      WindowedOuterHistory.cons
        (T.arrows.get ⟨k, by simpa [T.arrows_length] using hklt⟩)
        ?_ ?_ ?_ ?_ ?_ tail⟩⟩
    · simpa [i] using T.step i
    · simpa [i] using T.head_eq ⟨k, by omega⟩
    · simpa [i] using T.head_eq ⟨k + 1, by omega⟩
    · simpa [i] using T.hash_outside ⟨k, by omega⟩
    · simpa [i] using T.hash_outside ⟨k + 1, by omega⟩
termination_by n - k
decreasing_by omega

theorem slotOneWindowedHistory {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    ∃ as : List OuterArrow,
      Nonempty (WindowedOuterHistory n
        ((slotOneListTrace F).configs.get ⟨1, by
          rw [(slotOneListTrace F).configs_length]
          have := F.1.width_pos
          omega⟩)
        ((slotOneListTrace F).heads.get ⟨1, by
          rw [(slotOneListTrace F).heads_length]
          have := F.1.width_pos
          omega⟩)
        as
        ((slotOneListTrace F).configs.get ⟨n, by
          rw [(slotOneListTrace F).configs_length]
          omega⟩)
        ((slotOneListTrace F).heads.get ⟨n, by
          rw [(slotOneListTrace F).heads_length]
          omega⟩)) ∧
      ((slotOneListTrace F).configs.get ⟨n, by
        rw [(slotOneListTrace F).configs_length]
        omega⟩).state = MStarOuterProgram.State.accept := by
  rcases historyOfTraceFrom (slotOneListTrace F) 1 (by
      have := F.1.width_pos
      omega) with ⟨as, ⟨has⟩⟩
  refine ⟨as, ?_, ?_⟩
  · exact ⟨by simpa using has⟩
  · simpa using (slotOneListTrace F).final_accept

/-- No parser-prefix certificate is supplied: the literal slot-one frame
itself structurally yields an accepting parser computation from time one. -/
theorem slotOneListTrace_parser_canAccept {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    MStarParserSoundness.CanAcceptResult (.running
      (MStarParserMicrocode.fixed ⟨0, by decide⟩)
      (windowZipper n
        ((slotOneListTrace F).configs.get ⟨1, by
          rw [(slotOneListTrace F).configs_length]
          have := F.1.width_pos
          omega⟩)
        ((slotOneListTrace F).heads.get ⟨1, by
          rw [(slotOneListTrace F).heads_length]
          have := F.1.width_pos
          omega⟩))) := by
  rcases slotOneWindowedHistory F with ⟨as, ⟨H⟩, hfinal⟩
  exact (H.parserPrefix_to_accept hfinal
    (MStarParserMicrocode.fixed ⟨0, by decide⟩)
    (slotOneListTrace F).time_one_parserStart).canAccept

/-- Parameter-free slot-one parser soundness at the actual FullFrame time-one
window. -/
theorem slotOneFrame_parser_canAccept {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    MStarParserSoundness.CanAcceptResult (.running
      (MStarParserMicrocode.fixed ⟨0, by decide⟩)
      (windowZipper n
        ((FullFrame.toUniformWindowedRun F.1).config
          ⟨1, Nat.succ_lt_succ F.1.width_pos⟩)
        ((FullFrame.toUniformWindowedRun F.1).head_index
          ⟨1, Nat.succ_lt_succ F.1.width_pos⟩))) := by
  have h := slotOneListTrace_parser_canAccept F
  have hc := traceConfigs_get F ⟨1, Nat.succ_lt_succ F.1.width_pos⟩
  have hh := traceHeads_get F ⟨1, Nat.succ_lt_succ F.1.width_pos⟩
  have hc' : (slotOneListTrace F).configs.get ⟨1, by
        rw [(slotOneListTrace F).configs_length]
        have := F.1.width_pos
        omega⟩ =
      (FullFrame.toUniformWindowedRun F.1).config
        ⟨1, Nat.succ_lt_succ F.1.width_pos⟩ := by
    simpa only [slotOneListTrace] using hc
  have hh' : (slotOneListTrace F).heads.get ⟨1, by
        rw [(slotOneListTrace F).heads_length]
        have := F.1.width_pos
        omega⟩ =
      (FullFrame.toUniformWindowedRun F.1).head_index
        ⟨1, Nat.succ_lt_succ F.1.width_pos⟩ := by
    simpa only [slotOneListTrace] using hh
  rw [hc', hh'] at h
  exact h

end PakFixedPolyomino.PakOuterParserListExitReflection
