import PakFixedPolyomino.PakOuterParserListExitReflection
import PakFixedPolyomino.MStarParserSoundness
import Mathlib.Data.Fin.Tuple.Take

/-! # Decoding the parser window of a slot-one full frame

The literal slot-one history supplies `CanAcceptResult` at the original fixed
parser state.  This module records the first canonical, non-scanner-specific
decoding consequences of that fact. -/

namespace PakFixedPolyomino.PakSlotOneParserDecode

open PakOuterParserListExitReflection
open PakFullFrameTableauReadback
open MStarParserSoundness
open MStarParserExecution
open MStarParserMicrocode
open MStarConcreteAlphabet
open MStarOuterProgram
open PakScannerBaselineAutomaton
open PakMStarCouplingCorrectness

theorem canAccept_fixed_zero_prefix
    (z : Zipper (MStarOuterProgram.Tape CoreTape))
    (hacc : CanAcceptResult (.running (fixed ⟨0, by decide⟩) z)) :
    (z.focus :: z.right).take 72 = List.replicate 72 (.core zero) := by
  exact fixed_canAccept_forces_zero_prefix (⟨0, by decide⟩ : Fin 73) 72
    (by decide) z hacc

theorem canAccept_fixed_zero_focus_and_room
    (z : Zipper (MStarOuterProgram.Tape CoreTape))
    (hacc : CanAcceptResult (.running (fixed ⟨0, by decide⟩) z)) :
    z.focus = .core zero ∧ z.right ≠ [] :=
  fixed_canAccept_forces_zero_and_right (⟨0, by decide⟩ : Fin 73)
    (by decide) z hacc

private theorem parserStep_control_hash_rejected_all :
    ∀ q : Fin 18, q ≠ (⟨5, by decide⟩ : Fin 18) →
      q ≠ (⟨17, by decide⟩ : Fin 18) →
      MStarParserMicrocode.step (UState := Unit) zero one work
        (control q) .hash = some (MStarParserMicrocode.reject .hash) := by
  native_decide

/-- Every nonterminal parser state on an accepting finite zipper reads a
non-hash letter.  This is independent of scanner canonicity and of the
unconstrained exterior list segments. -/
theorem canAccept_noncopy_focus_ne_hash
    (p : ParserState) (z : Zipper (Tape CoreTape))
    (hp : p ≠ copyStart)
    (hacc : CanAcceptResult (.running p z)) : z.focus ≠ .hash := by
  intro hhash
  cases p with
  | inl counters =>
      cases counters with
      | inl k =>
          by_cases hk : k.1 < 72
          · have hzero := fixed_canAccept_forces_zero_and_right k hk z hacc
            exact (by simpa [hhash] using hzero.1)
          · have hk72 : k = (⟨72, by decide⟩ : Fin 73) := by
              apply Fin.ext
              change k.1 = 72
              omega
            subst k
            have hnext := (canAcceptResult_oneStep_iff
              (.running (fixed ⟨72, by decide⟩) z)).2 hacc
            rw [show z = ⟨z.leftRev, .hash, z.right⟩ by
              apply Zipper.ext <;> simp [hhash],
              MStarConcreteAlphabet.oneStep_fixed_72] at hnext
            have hafter := (canAcceptResult_oneStep_iff
              (.running scanPad ⟨z.leftRev, .hash, z.right⟩)).2 hnext
            rw [oneStep_scanPad_noncore _ _ .hash (by simp)] at hafter
            exact not_canAcceptResult_rejected hafter
      | inr k =>
          by_cases hk : k.1 < 72
          · have hzero := cross_canAccept_forces_zero_and_left k hk z hacc
            exact (by simpa [hhash] using hzero.1)
          · have hk72 : k = (⟨72, by decide⟩ : Fin 73) := by
              apply Fin.ext
              change k.1 = 72
              omega
            subst k
            have hnext := (canAcceptResult_oneStep_iff
              (.running (cross ⟨72, by decide⟩) z)).2 hacc
            rw [show z = ⟨z.leftRev, .hash, z.right⟩ by
              apply Zipper.ext <;> simp [hhash]] at hnext
            change CanAcceptResult
              (.running returnSepPad ⟨z.leftRev, .hash, z.right⟩) at hnext
            have hafter := (canAcceptResult_oneStep_iff
              (.running returnSepPad ⟨z.leftRev, .hash, z.right⟩)).2 hnext
            have hreject : oneStep zero one work
                (.running returnSepPad ⟨z.leftRev, .hash, z.right⟩) = .rejected := by
              rfl
            rw [hreject] at hafter
            exact not_canAcceptResult_rejected hafter
  | inr phase =>
      have hnext := (canAcceptResult_oneStep_iff
        (.running (control phase) z)).2 hacc
      rw [show z = ⟨z.leftRev, .hash, z.right⟩ by
        apply Zipper.ext <;> simp [hhash]] at hnext
      have hphase : phase ≠ (⟨17, by decide⟩ : Fin 18) := by
        intro h17
        apply hp
        change Sum.inr phase = Sum.inr (⟨17, by decide⟩ : Fin 18)
        rw [h17]
      by_cases h5 : phase = (⟨5, by decide⟩ : Fin 18)
      · subst phase
        change CanAcceptResult (.running scanLen ⟨z.leftRev, .hash, z.right⟩) at hnext
        have hafter := (canAcceptResult_oneStep_iff
          (.running scanLen ⟨z.leftRev, .hash, z.right⟩)).2 hnext
        rw [oneStep_scanLen_noncore _ _ .hash (by simp)] at hafter
        exact not_canAcceptResult_rejected hafter
      · have hstep : oneStep zero one work
            (.running (control phase) ⟨z.leftRev, .hash, z.right⟩) = .rejected := by
            unfold oneStep
            change (if control phase = copyStart then _ else _) = _
            rw [if_neg (by
              intro h
              apply hphase
              change Sum.inr phase = Sum.inr (⟨17, by decide⟩ : Fin 18) at h
              exact Sum.inr.inj h)]
            rw [parserStep_control_hash_rejected_all phase h5 hphase]
            rfl
        rw [hstep] at hnext
        exact not_canAcceptResult_rejected hnext

/-- The actual slot-one frame window begins with the required fixed padding;
this conclusion uses only its parameter-free parser acceptance theorem and
does not assume a canonical scanner input or a canonical exterior tail. -/
theorem slotOne_window_fixed_padding {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    let c := (FullFrame.toUniformWindowedRun F.1).config
      ⟨1, Nat.succ_lt_succ F.1.width_pos⟩
    let h := (FullFrame.toUniformWindowedRun F.1).head_index
      ⟨1, Nat.succ_lt_succ F.1.width_pos⟩
    ((PakOuterParserReflection.windowZipper n c h).focus ::
      (PakOuterParserReflection.windowZipper n c h).right).take 72 =
        List.replicate 72 (.core zero) := by
  dsimp
  apply canAccept_fixed_zero_prefix
  exact slotOneFrame_parser_canAccept F

private theorem legalScan_from_bottom_target_isHead :
    ∀ (t : ConcretePakScanner.State) (b : Bool),
      ConcretePakScanner.LegalScan PakCouplingGenerated.scannerBottom t b →
        PakScannerBaselineAutomaton.isHeadBuffer t.centre = true := by
  native_decide

/-- The scanner bottom clause puts its unique emitted head in physical row
one.  Hence the time-zero tableau readback head is exactly index one. -/
theorem slotOne_timeZero_headIndex_eq_one {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    (FullFrame.toUniformWindowedRun F.1).head_index
      ⟨0, Nat.zero_lt_succ n⟩ = ⟨1, by
        have := FullFrame.height_ge_two F.1
        omega⟩ := by
  let P := FullFrame.toScannerPath F.1
  let j₀ : Fin n := ⟨0, F.1.height_pos⟩
  let j₁ : Fin n := ⟨1, by have := FullFrame.height_ge_two F.1; omega⟩
  have hlegal : ConcretePakScanner.LegalScan
      PakCouplingGenerated.scannerBottom
      (P.states ⟨1, by have := FullFrame.height_ge_two F.1; omega⟩)
      (n.testBit 0) := by
    rw [← P.bottom]
    simpa [j₀] using P.legal j₀
  have hstateHead : PakScannerBaselineAutomaton.isHeadBuffer
      (P.states ⟨1, by have := FullFrame.height_ge_two F.1; omega⟩).centre =
        true := legalScan_from_bottom_target_isHead _ _ hlegal
  have htableau :
      ((tableauAt F.1.tiling (eastIndex F.1.width_pos) j₁).1.old.center.isHead =
        true) := by
    apply (FullFrame.toScannerPath_state_head_iff F.1 j₁).mp
    simpa [P, j₁] using hstateHead
  let R := FullFrame.tableau_column_readback F.1 (eastIndex F.1.width_pos)
  have hj : j₁ = R.head := R.head_unique j₁ (by simpa [R] using htableau)
  apply Fin.ext
  change (FullFrame.reverse_tableau_headIndex F.1 ⟨0, Nat.zero_lt_succ n⟩).1 = 1
  have hread : FullFrame.reverse_tableau_headIndex F.1
      ⟨0, Nat.zero_lt_succ n⟩ = R.head := by
    simp [FullFrame.reverse_tableau_headIndex, F.1.width_pos,
      reverseColumn, eastIndex, R]
  rw [hread, ← hj]

theorem slotOne_firstArrow_move_stay {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    (FiniteOneTapeProgram.transition MStarULogAssembly.program
      ((FullFrame.toUniformWindowedRun F.1).arrow
        ⟨0, F.1.width_pos⟩)).move = .stay := by
  let A := (FullFrame.toUniformWindowedRun F.1).arrow ⟨0, F.1.width_pos⟩
  change (FiniteOneTapeProgram.transition MStarULogAssembly.program A).move = .stay
  have hsource : A.1.1.1 = MStarOuterProgram.State.start := by
    change (FiniteOneTapeProgram.transition MStarULogAssembly.program A).sourceState = _
    exact PakSlotOneFullFrameReflection.slotOne_first_source_start F
  have hslot : A.1.2 = 1 := F.2
  generalize harrow : A = a at hsource hslot
  rcases a with ⟨⟨⟨q, x⟩, slot⟩, hoccupied⟩
  change q = MStarOuterProgram.State.start at hsource
  subst q
  change slot = 1 at hslot
  subst slot
  cases x with
  | core x =>
      by_cases hinitial : MStarOuterProgram.isInitialLetter MStarULogAssembly.data x = true
      · let act : FiniteOneTapeProgram.Action MStarULogAssembly.State
            MStarULogAssembly.Tape :=
          { write := .core x
            target := .parser MStarULogAssembly.data.parserStart
            move := .stay }
        have hrule : MStarULogAssembly.program.rule .start (.core x) 1 =
            some act := by
          simpa [act] using MStarOuterProgram.start_slot_one
            MStarULogAssembly.data hinitial
        have haction : FiniteOneTapeProgram.actionOf MStarULogAssembly.program
            ⟨((MStarOuterProgram.State.start, .core x), (1 : Fin 2)), hoccupied⟩ =
              act :=
          PakCanonicalFullTrack.actionOf_eq_of_rule_eq _ _ _ hrule
        change (FiniteOneTapeProgram.actionOf MStarULogAssembly.program
          ⟨((MStarOuterProgram.State.start, .core x), (1 : Fin 2)), hoccupied⟩).move = .stay
        rw [haction]
      · exact (hoccupied (by
          simp [MStarULogAssembly.program, MStarOuterProgram.program,
            hinitial])).elim
  | hash => exact (hoccupied (by
      simp [MStarULogAssembly.program, MStarOuterProgram.program])).elim
  | markL => exact (hoccupied (by
      simp [MStarULogAssembly.program, MStarOuterProgram.program])).elim
  | markR => exact (hoccupied (by
      simp [MStarULogAssembly.program, MStarOuterProgram.program])).elim
  | scratch i => exact (hoccupied (by
      simp [MStarULogAssembly.program, MStarOuterProgram.program])).elim

theorem slotOne_timeOne_headIndex_eq_one {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    (FullFrame.toUniformWindowedRun F.1).head_index
      ⟨1, Nat.succ_lt_succ F.1.width_pos⟩ = ⟨1, by
        have := FullFrame.height_ge_two F.1
        omega⟩ := by
  let U := FullFrame.toUniformWindowedRun F.1
  let t : Fin n := ⟨0, F.1.width_pos⟩
  have hstep := PakSlotOneFullFrameReflection.slotOne_first_step F
  have hmove := slotOne_firstArrow_move_stay F
  have hhead : (U.config ⟨1, Nat.succ_lt_succ F.1.width_pos⟩).head =
      (U.config ⟨0, Nat.zero_lt_succ n⟩).head := by
    unfold FiniteOneTapeSemantics.step at hstep
    dsimp only at hstep
    split at hstep
    · simp at hstep
    · split at hstep
      · have hc := Option.some.inj hstep
        rw [← hc]
        simpa [U, FiniteOneTapeSemantics.moveHead, hmove]
      · simp at hstep
  apply Fin.ext
  have hzero := slotOne_timeZero_headIndex_eq_one F
  have hhead₀ := U.head_eq ⟨0, Nat.zero_lt_succ n⟩
  have hhead₁ := U.head_eq ⟨1, Nat.succ_lt_succ F.1.width_pos⟩
  have horigin : U.origin = 0 := rfl
  rw [horigin, zero_add] at hhead₀ hhead₁
  have hval : ((U.head_index
      ⟨1, Nat.succ_lt_succ F.1.width_pos⟩).1 : Int) = 1 := by
    calc
    ((U.head_index ⟨1, Nat.succ_lt_succ F.1.width_pos⟩).1 : Int) =
        (U.config ⟨1, Nat.succ_lt_succ F.1.width_pos⟩).head := hhead₁.symm
    _ = (U.config ⟨0, Nat.zero_lt_succ n⟩).head := hhead
    _ = (U.head_index ⟨0, Nat.zero_lt_succ n⟩).1 := hhead₀
    _ = 1 := by rw [hzero]; rfl
  exact_mod_cast hval

theorem slotOne_timeOne_tape_zero_hash {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    ((FullFrame.toUniformWindowedRun F.1).config
      ⟨1, Nat.succ_lt_succ F.1.width_pos⟩).tape 0 = .hash := by
  let U := FullFrame.toUniformWindowedRun F.1
  let R := FullFrame.tableau_column_readback F.1 (eastIndex F.1.width_pos)
  have hconfig₀ : U.config ⟨0, Nat.zero_lt_succ n⟩ = R.before := by
    change FullFrame.reverse_tableau_config F.1 ⟨0, Nat.zero_lt_succ n⟩ = R.before
    simp [FullFrame.reverse_tableau_config, F.1.width_pos,
      reverseColumn, eastIndex, R]
  have htape₀ : (U.config ⟨0, Nat.zero_lt_succ n⟩).tape 0 = .hash := by
    rw [hconfig₀]
    change R.oldTape 0 = .hash
    let j₀ : Fin n := ⟨0, F.1.height_pos⟩
    calc
      R.oldTape 0 = OneTapeTableau.cellLetter (R.oldStrip j₀).center := by
        simpa [j₀] using R.oldTape_at j₀
      _ = .hash := by rw [R.south_old_hash.2]; rfl
  have hstep := PakSlotOneFullFrameReflection.slotOne_first_step F
  have hhead₀ : (U.config ⟨0, Nat.zero_lt_succ n⟩).head = 1 := by
    have hhead := U.head_eq ⟨0, Nat.zero_lt_succ n⟩
    have horigin : U.origin = 0 := rfl
    rw [horigin, zero_add, slotOne_timeZero_headIndex_eq_one F] at hhead
    exact hhead
  unfold FiniteOneTapeSemantics.step at hstep
  dsimp only at hstep
  split at hstep
  · simp at hstep
  · split at hstep
    · have hc := Option.some.inj hstep
      have ht := congrArg (fun c : PakMStarCouplingCorrectness.MStarConfig =>
        c.tape 0) hc
      change FiniteOneTapeSemantics.writtenTape
        (U.config ⟨0, Nat.zero_lt_succ n⟩)
        (FiniteOneTapeProgram.transition MStarULogAssembly.program
          (U.arrow ⟨0, F.1.width_pos⟩)).write 0 =
          (U.config ⟨1, Nat.succ_lt_succ F.1.width_pos⟩).tape 0 at ht
      rw [← ht]
      have hne : (0 : Int) ≠ (U.config ⟨0, Nat.zero_lt_succ n⟩).head := by
        rw [hhead₀]
        decide
      unfold FiniteOneTapeSemantics.writtenTape
      rw [Function.update_apply, if_neg hne]
      exact htape₀
    · simp at hstep

noncomputable def slotOneTimeOneZipper {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    Zipper (Tape CoreTape) :=
  PakOuterParserReflection.windowZipper n
    ((FullFrame.toUniformWindowedRun F.1).config
      ⟨1, Nat.succ_lt_succ F.1.width_pos⟩)
    ((FullFrame.toUniformWindowedRun F.1).head_index
      ⟨1, Nat.succ_lt_succ F.1.width_pos⟩)

noncomputable def slotOneTrimmedZipper {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    Zipper (Tape CoreTape) :=
  { leftRev := []
    focus := (slotOneTimeOneZipper F).focus
    right := (slotOneTimeOneZipper F).right }

theorem slotOneTimeOneZipper_leftRev {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    (slotOneTimeOneZipper F).leftRev = [.hash] := by
  unfold slotOneTimeOneZipper PakOuterParserReflection.windowZipper
  rw [slotOne_timeOne_headIndex_eq_one F]
  unfold PakOuterParserReflection.windowCells
  rw [← Fin.ofFn_take_eq_take_ofFn (show 1 ≤ n by
    have := FullFrame.height_ge_two F.1
    omega)]
  simp [Fin.take,
    slotOne_timeOne_tape_zero_hash F]

set_option maxRecDepth 100000 in
/-- The concrete 72-step fixed-counter run is stable under an arbitrary
already-present left zipper segment. -/
theorem run_fixed_72_with_left
    (left : List (Tape CoreTape)) (y : Tape CoreTape)
    (right : List (Tape CoreTape)) :
    run zero one work 72
      (.running (fixed ⟨0, by decide⟩)
        ⟨left, .core zero,
          List.replicate 71 (.core zero) ++ y :: right⟩) =
      .running (fixed ⟨72, by decide⟩)
        ⟨fixedPaddingTail ++ left, y, right⟩ := by
  rfl

/-- An accepting arbitrary-left fixed-zero parser configuration can be moved
through the mandatory 72-cell prefix without imposing any condition on its
left boundary or on the tail after the next cell. -/
theorem canAccept_fixed0_after_prefix
    (z : Zipper (Tape CoreTape))
    (hacc : CanAcceptResult (.running (fixed ⟨0, by decide⟩) z)) :
    ∃ y ys,
      z.focus :: z.right = List.replicate 72 (.core zero) ++ y :: ys ∧
      CanAcceptResult (.running scanPad
        ⟨fixedPaddingTail ++ z.leftRev, y, ys⟩) := by
  have hprefix := canAccept_fixed_zero_prefix z hacc
  have hroom := fixed_canAccept_forces_room (⟨0, by decide⟩ : Fin 73) 72
    (by decide) z hacc
  have hdrop : (z.focus :: z.right).drop 72 ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    have hzero : (z.focus :: z.right).length - 72 = 0 := by
      simpa only [List.length_drop, List.length_nil] using hlen
    omega
  cases htail : (z.focus :: z.right).drop 72 with
  | nil => exact (hdrop htail).elim
  | cons y ys =>
      have hshape : z.focus :: z.right =
          List.replicate 72 (.core zero) ++ y :: ys := by
        calc
          z.focus :: z.right = (z.focus :: z.right).take 72 ++
              (z.focus :: z.right).drop 72 := (List.take_append_drop 72 _).symm
          _ = List.replicate 72 (.core zero) ++ y :: ys := by rw [hprefix, htail]
      have hstart : z = ⟨z.leftRev, .core zero,
          List.replicate 71 (.core zero) ++ y :: ys⟩ := by
        apply Zipper.ext
        · rfl
        · have := congrArg List.head? hshape
          simpa using this
        · have := congrArg List.tail hshape
          simpa [List.replicate_succ, List.append_assoc] using this
      have hfixed : CanAcceptResult (.running (fixed ⟨72, by decide⟩)
          ⟨fixedPaddingTail ++ z.leftRev, y, ys⟩) := by
        have hrun := (canAcceptResult_run_iff 72
          (.running (fixed ⟨0, by decide⟩) z)).2 hacc
        rw [hstart, run_fixed_72_with_left] at hrun
        exact hrun
      have hscan := (canAcceptResult_oneStep_iff
        (.running (fixed ⟨72, by decide⟩)
          ⟨fixedPaddingTail ++ z.leftRev, y, ys⟩)).2 hfixed
      rw [oneStep_fixed_72] at hscan
      exact ⟨y, ys, hshape, hscan⟩

/-- The usual length-scanning state with an arbitrary zipper segment retained
strictly beyond the parser's fixed padding. -/
def lengthStateWithLeft (extraLeft : List (Tape CoreTape))
    (paid padding : ℕ) (focus : Tape CoreTape)
    (right : List (Tape CoreTape)) : Result CoreTape :=
  .running scanLen
    ⟨List.replicate paid lenDone ++ sepPad ::
      (List.replicate (72 * paid) padDone ++
        List.replicate padding (.core zero) ++ fixedPaddingTail ++ extraLeft),
      focus, right⟩

theorem lengthStateWithLeft_zero_eq
    (extraLeft : List (Tape CoreTape)) (padding : ℕ)
    (focus : Tape CoreTape) (right : List (Tape CoreTape)) :
    lengthStateWithLeft extraLeft 0 padding focus right =
      .running scanLen
        ⟨sepPad :: List.replicate padding (.core zero) ++
          fixedPaddingTail ++ extraLeft, focus, right⟩ := by
  rfl

/-- The generic scan-pad split composes with the arbitrary-left fixed-prefix
run.  Thus the actual cells expose the padding separator and an accepting
scan-length state while preserving the untouched left segment. -/
theorem canAccept_fixed0_after_scanPad_split
    (z : Zipper (Tape CoreTape))
    (hacc : CanAcceptResult (.running (fixed ⟨0, by decide⟩) z)) :
    ∃ padding y ys,
      z.focus :: z.right =
        List.replicate 72 (.core zero) ++
          List.replicate padding (.core zero) ++ .core one :: y :: ys ∧
      CanAcceptResult (lengthStateWithLeft z.leftRev 0 padding y ys) := by
  rcases canAccept_fixed0_after_prefix z hacc with
    ⟨focus, right, hprefix, hscan⟩
  rcases scanPad_canAccept_split (fixedPaddingTail ++ z.leftRev) focus right hscan with
    ⟨padding, y, ys, hscanShape, hlength⟩
  refine ⟨padding, y, ys, ?_, ?_⟩
  · rw [hprefix, hscanShape]
    simp [List.append_assoc]
  · rw [lengthStateWithLeft_zero_eq]
    simpa only [List.append_assoc] using hlength

/-! ## Far-left hash extension -/

def appendLeftHash (z : Zipper (Tape CoreTape)) : Zipper (Tape CoreTape) :=
  { leftRev := z.leftRev ++ [.hash], focus := z.focus, right := z.right }

def appendLeftHashResult : Result CoreTape → Result CoreTape
  | .running p z => .running p (appendLeftHash z)
  | .copyReady z => .copyReady (appendLeftHash z)
  | .rejected => .rejected
  | .stuck => .stuck

private def leftTargetsCopyStart
    (o : Option (FiniteOneTapeProgram.Action
      (MStarOuterProgram.State ParserState Unit) (Tape CoreTape))) : Bool :=
  match o with
  | none => false
  | some a => decide (a.move = .left ∧ a.target = .parser copyStart)

private theorem parserStep_leftTargetsCopyStart_false :
    ∀ (p : ParserState) (x : Tape CoreTape),
      leftTargetsCopyStart (MStarParserMicrocode.step (UState := Unit)
        zero one work p x) = false := by
  native_decide

/-- A parser row which moves left can never make `copyStart` its next parser
control.  This finite fact is what makes the artificial far-left hash safe. -/
private theorem parserStep_left_target_ne_copyStart
    (p : ParserState) (x : Tape CoreTape)
    (a : FiniteOneTapeProgram.Action
      (MStarOuterProgram.State ParserState Unit) (Tape CoreTape))
    (hstep : MStarParserMicrocode.step (UState := Unit) zero one work p x = some a)
    (hleft : a.move = .left) : a.target ≠ .parser copyStart := by
  intro htarget
  have hfalse := parserStep_leftTargetsCopyStart_false p x
  simp [leftTargetsCopyStart, hstep, hleft, htarget] at hfalse

theorem applyAction_appendLeftHash_of_some {State : Type*}
    (z z' : Zipper (Tape CoreTape))
    (a : FiniteOneTapeProgram.Action State (Tape CoreTape))
    (happly : applyAction z a = some z') :
    applyAction (appendLeftHash z) a = some (appendLeftHash z') := by
  rcases z with ⟨left, focus, right⟩
  rcases a with ⟨write, target, move⟩
  cases move with
  | stay =>
      simp only [applyAction] at happly ⊢
      cases happly
      rfl
  | right =>
      cases right with
      | nil => simp [applyAction] at happly
      | cons y ys =>
          simp only [applyAction] at happly ⊢
          cases happly
          rfl
  | left =>
      cases left with
      | nil => simp [applyAction] at happly
      | cons y ys =>
          simp only [applyAction] at happly ⊢
          cases happly
          rfl

set_option maxRecDepth 100000 in
/-- Appending a single far-left hash commutes with one parser step whenever
the extended running state still has an accepting continuation. -/
theorem oneStep_appendLeftHash_of_canAccept
    (r : Result CoreTape)
    (hacc : CanAcceptResult (appendLeftHashResult r)) :
    oneStep zero one work (appendLeftHashResult r) =
      appendLeftHashResult (oneStep zero one work r) := by
  cases r with
  | rejected | stuck | copyReady z => rfl
  | running p z =>
      by_cases hp : p = copyStart
      · subst p
        rfl
      · have hnext := (canAcceptResult_oneStep_iff
          (appendLeftHashResult (.running p z))).2 hacc
        simp only [appendLeftHashResult] at hnext ⊢
        change oneStep zero one work (.running p (appendLeftHash z)) =
          appendLeftHashResult (oneStep zero one work (.running p z))
        rw [oneStep, oneStep, if_neg hp, if_neg hp]
        rw [show (appendLeftHash z).focus = z.focus by rfl]
        cases hstep : MStarParserMicrocode.step (UState := Unit)
            zero one work p z.focus with
        | none => rfl
        | some a =>
            dsimp only
            rw [oneStep, if_neg hp,
              show (appendLeftHash z).focus = z.focus by rfl, hstep] at hnext
            dsimp only at hnext
            cases happly : applyAction z a with
            | some z' =>
                have hext := applyAction_appendLeftHash_of_some z z' a happly
                rw [hext]
                cases a.target <;> rfl
            | none =>
                cases hmove : a.move with
                | stay => simp [applyAction, hmove] at happly
                | right =>
                    cases hright : z.right with
                    | nil =>
                        simp [appendLeftHash, applyAction, hmove, hright]
                        rfl
                    | cons y ys => simp [applyAction, hmove, hright] at happly
                | left =>
                    cases hleft : z.leftRev with
                    | cons y ys => simp [applyAction, hmove, hleft] at happly
                    | nil =>
                        have htarget := parserStep_left_target_ne_copyStart
                          p z.focus a hstep hmove
                        have hextApply : applyAction (appendLeftHash z) a =
                            some ⟨[], .hash, a.write :: z.right⟩ := by
                          simp [appendLeftHash, applyAction, hmove, hleft]
                        rw [hextApply]
                        cases htar : a.target with
                        | parser q =>
                            have hq : q ≠ copyStart := by
                              intro hqcopy
                              apply htarget
                              simpa [htar, hqcopy]
                            have hnext' : CanAcceptResult
                                (.running q ⟨[], .hash, a.write :: z.right⟩) := by
                              rw [hextApply, htar] at hnext
                              exact hnext
                            exact False.elim ((canAccept_noncopy_focus_ne_hash q
                              ⟨[], .hash, a.write :: z.right⟩ hq hnext') rfl)
                        | reject =>
                            have hnext' : CanAcceptResult (.rejected : Result CoreTape) := by
                              rw [hextApply, htar] at hnext
                              exact hnext
                            exact False.elim (not_canAcceptResult_rejected hnext')
                        | start | accept | sim _ =>
                            have hnext' : CanAcceptResult (.stuck : Result CoreTape) := by
                              rw [hextApply, htar] at hnext
                              exact hnext
                            exact False.elim (not_canAcceptResult_stuck hnext')

/-- Erasing one artificial far-left hash preserves existence of a finite
parser acceptance witness.  The proof follows the witness fuel and uses the
accepted one-step commutation theorem at each successor stage. -/
theorem canAccept_appendLeftHash_reflect
    (r : Result CoreTape)
    (hacc : CanAcceptResult (appendLeftHashResult r)) :
    CanAcceptResult r := by
  rcases hacc with ⟨fuel, out, hrun⟩
  induction fuel generalizing r out with
  | zero =>
      simp only [run_zero] at hrun
      cases r with
      | running p z => simp [appendLeftHashResult] at hrun
      | copyReady z => exact canAcceptResult_copyReady z
      | rejected => simp [appendLeftHashResult] at hrun
      | stuck => simp [appendLeftHashResult] at hrun
  | succ fuel ih =>
      change run zero one work fuel
        (oneStep zero one work (appendLeftHashResult r)) = .copyReady out at hrun
      have hfull : CanAcceptResult (appendLeftHashResult r) :=
        ⟨fuel + 1, out, by simpa [run] using hrun⟩
      have hcomm := oneStep_appendLeftHash_of_canAccept r hfull
      rw [hcomm] at hrun
      exact (canAcceptResult_oneStep_iff r).mp
        (ih (oneStep zero one work r) out hrun)

theorem canAccept_running_appendLeftHash_reflect
    (p : ParserState) (z : Zipper (Tape CoreTape))
    (hacc : CanAcceptResult (.running p (appendLeftHash z))) :
    CanAcceptResult (.running p z) := by
  exact canAccept_appendLeftHash_reflect (.running p z) hacc

theorem slotOneTimeOneZipper_eq_appendLeftHash {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    slotOneTimeOneZipper F = appendLeftHash (slotOneTrimmedZipper F) := by
  apply Zipper.ext
  · simp [slotOneTrimmedZipper, appendLeftHash,
      slotOneTimeOneZipper_leftRev F]
  · rfl
  · rfl

theorem slotOneTrimmedZipper_canAccept {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    CanAcceptResult (.running (fixed ⟨0, by decide⟩)
      (slotOneTrimmedZipper F)) := by
  apply canAccept_running_appendLeftHash_reflect
  rw [← slotOneTimeOneZipper_eq_appendLeftHash F]
  exact slotOneFrame_parser_canAccept F

end PakFixedPolyomino.PakSlotOneParserDecode
