import PakFixedPolyomino.PakSlotOneCopierMarkRBarrier

/-! # State-indexed provenance for the tail beyond the installed `markR`

The copier uses `scratch 2` both for the parser's `lenDone` bookkeeping and
for its terminal `rightEnd`.  Consequently a bare alphabet-membership
invariant cannot identify the terminal read.  The useful spatial statement is
instead indexed by the *terminal control*: once `rightBufferScan` has crossed
the particular `markR` installed at copy entry, the focused suffix is a suffix
of the external tail supplied at that installation.

This file deliberately keeps that occurrence-sensitive assertion separate
from the temporal `CrossesMarkR` statement in `PakSlotOneCopierMarkRBarrier`.
The latter supplies the control-flow entrance; `ExternalResidue` below is the
spatial certificate that has to be transported through mark-R relocation.
-/

namespace PakFixedPolyomino.PakSlotOneMarkRTailProvenance

open MStarCopierMicrocode
open MStarCopierExecution
open MStarOuterProgram

/-- At a terminal right-buffer configuration, the part of tape at and to the
right of the head is the unconsumed suffix of the external tail that was on
the right of the installed `markR`. -/
def ExternalResidue (external : List ConcreteTape)
    (z : MStarParserExecution.Zipper ConcreteTape) : Prop :=
  ∃ consumed, external = consumed ++ z.focus :: z.right

/-- A terminal `rightEnd` certified by an `ExternalResidue` is an occurrence
of `rightEnd` in the original external tail, not a parser-created `lenDone`.
-/
theorem ExternalResidue.rightEnd_mem
    {external : List ConcreteTape} {left right : List ConcreteTape}
    (hresidue : ExternalResidue external ⟨left, rightEnd, right⟩) :
    rightEnd ∈ external := by
  rcases hresidue with ⟨consumed, hconsumed⟩
  rw [hconsumed]
  simp

/-- The self-loop of `rightBufferScan` consumes one work cell without losing
the external-tail provenance.  This is the local, state-indexed step needed
to transport a provenance certificate across an arbitrarily long terminal
buffer. -/
theorem externalResidue_rightBuffer_work
    (external left right : List ConcreteTape) :
    ExternalResidue external
      ⟨left, .core MStarConcreteAlphabet.work,
        .core MStarConcreteAlphabet.work :: right⟩ →
    ExternalResidue external
      ⟨.core MStarConcreteAlphabet.work :: left,
        .core MStarConcreteAlphabet.work, right⟩ := by
  intro hresidue
  rcases hresidue with ⟨consumed, hconsumed⟩
  refine ⟨consumed ++ [.core MStarConcreteAlphabet.work], ?_⟩
  simpa [List.append_assoc] using hconsumed

/-- A right move inside the external suffix consumes its old focused cell;
the value written behind the head is irrelevant to the remaining suffix. -/
theorem externalResidue_move_right
    {external left right : List ConcreteTape} {x y written : ConcreteTape}
    (hresidue : ExternalResidue external ⟨left, x, y :: right⟩) :
    ExternalResidue external ⟨written :: left, y, right⟩ := by
  rcases hresidue with ⟨consumed, hconsumed⟩
  refine ⟨consumed ++ [x], ?_⟩
  simpa [List.append_assoc] using hconsumed

/-- Before the terminal crossing, the distinguished relocating `markR` still
occurs in the current forward zipper, and the tape after it is a suffix of the
*original* external tail.  `consumed` records the old external cells over
which the barrier has already been relocated; their current values need not
equal their original values. -/
def MarkRResidue (external : List ConcreteTape)
    (z : MStarParserExecution.Zipper ConcreteTape) : Prop :=
  ∃ before after consumed,
    (∀ x ∈ before, x ≠ .markR) ∧
    z.focus :: z.right = before ++ .markR :: after ∧
    external = consumed ++ after

/-- The literal post-installation state has the distinguished `markR` and
the complete external tail immediately to its right. -/
theorem markRResidue_installed
    (source external : List ConcreteTape) :
    MarkRResidue external
      ⟨.markL :: source, cellA, .markR :: external⟩ := by
  refine ⟨[cellA], external, [], ?_, by simp, by simp⟩
  intro x hx
  simp only [List.mem_singleton] at hx
  subst x
  native_decide

/-- The focused form of `MarkRResidue` used by the three transitions which
overwrite the current barrier and move right. -/
def MarkRFocusResidue (external : List ConcreteTape)
    (z : MStarParserExecution.Zipper ConcreteTape) : Prop :=
  z.focus = .markR ∧ ∃ consumed, external = consumed ++ z.right

/-- The no-earlier-`markR` clause makes the selected marker occurrence
unambiguous: when the focus itself is `markR`, it is the distinguished
relocating marker, rather than an unrelated marker deeper in `external`. -/
theorem MarkRResidue.at_focus
    {external left right : List ConcreteTape}
    (hresidue : MarkRResidue external ⟨left, .markR, right⟩) :
    MarkRFocusResidue external ⟨left, .markR, right⟩ := by
  rcases hresidue with ⟨before, after, consumed, hbefore, heq, htail⟩
  cases before with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at heq
      have hafter := heq.2
      subst after
      exact ⟨rfl, consumed, htail⟩
  | cons x xs =>
      have hne : x ≠ .markR := hbefore x (by simp)
      simp only [List.cons_append, List.cons.injEq] at heq
      exact (hne heq.1.symm).elim

/-- Crossing a focused distinguished marker to the right turns its suffix
certificate into the terminal external-residue certificate.  This lemma is
purely spatial; the copier-state table decides which crossing is the terminal
`finalSeekBoundary` crossing. -/
theorem markRFocusResidue_cross_right
    {external left : List ConcreteTape} {y : ConcreteTape}
    {right : List ConcreteTape}
    (hresidue : MarkRFocusResidue external ⟨left, .markR, y :: right⟩) :
    ExternalResidue external ⟨.core MStarConcreteAlphabet.work :: left, y, right⟩ := by
  rcases hresidue with ⟨_, consumed, hconsumed⟩
  exact ⟨consumed, hconsumed⟩

/-- The write value is irrelevant when the selected marker is crossed to the
right: it is placed in `leftRev`, while the new forward suffix is unchanged.
This common form serves `seekBoundary`, `counterToWork`, and `payloadCarry`. -/
theorem markRFocusResidue_cross_right_written
    {external left : List ConcreteTape} {y written : ConcreteTape}
    {right : List ConcreteTape}
    (hresidue : MarkRFocusResidue external ⟨left, .markR, y :: right⟩) :
    ExternalResidue external ⟨written :: left, y, right⟩ := by
  rcases hresidue with ⟨_, consumed, hconsumed⟩
  exact ⟨consumed, hconsumed⟩

/-- `findOld` crosses the selected marker to the left but writes the marker
back.  A successful normalize continuation excludes a second marker at the
new focus, so the same selected occurrence remains available. -/
theorem markRFocusResidue_cross_left_write_markR
    {external left right : List ConcreteTape} {y : ConcreteTape}
    (hy : y ≠ .markR)
    (hresidue : MarkRFocusResidue external ⟨y :: left, .markR, right⟩) :
    MarkRResidue external ⟨left, y, .markR :: right⟩ := by
  rcases hresidue with ⟨_, consumed, hconsumed⟩
  refine ⟨[y], right, consumed, ?_, ?_, hconsumed⟩
  · intro x hx
    simp only [List.mem_singleton] at hx
    simpa [hx] using hy
  · simp

/-- The actual terminal table edge preserves the original-tail provenance.
The `finalSeekBoundary` edge overwrites the selected marker by work and moves
right; `MarkRResidue.at_focus` is what prevents this from accidentally using
a later, unrelated `markR` that happened to occur in `external`. -/
theorem finalSeekBoundary_markR_enters_external_residue
    (external left right : List ConcreteTape) (y : ConcreteTape)
    (hresidue : MarkRResidue external ⟨left, .markR, y :: right⟩) :
    ExternalResidue external
      ⟨.core MStarConcreteAlphabet.work :: left, y, right⟩ := by
  exact markRFocusResidue_cross_right (MarkRResidue.at_focus hresidue)

/-- The three transient controls (`placeBoundary`, `payloadBoundary`, and
`payloadPlace`) write a fresh `markR` and move left.  If their new focus is
live (hence not an unrelated marker), an external residue is converted back
into a selected relocating-barrier residue. -/
theorem externalResidue_install_markR_left
    (external left right : List ConcreteTape) (y : ConcreteTape)
    (hy : y ≠ .markR)
    (hresidue : ExternalResidue external
      ⟨y :: left, .core MStarConcreteAlphabet.work, right⟩) :
    MarkRResidue external ⟨left, y, .markR :: right⟩ := by
  rcases hresidue with ⟨consumed, hconsumed⟩
  refine ⟨[y], right,
    consumed ++ [.core MStarConcreteAlphabet.work], ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_singleton] at hx
    simpa [hx] using hy
  · simp
  · simpa [List.append_assoc] using hconsumed

/-- Moving right while the current cell is not the selected marker leaves the
marker occurrence and its external suffix intact.  The written cell is moved
to `leftRev`, hence does not occur in the forward word of the conclusion. -/
theorem markRResidue_move_right
    {external left right : List ConcreteTape} {x y written : ConcreteTape}
    (hx : x ≠ .markR)
    (hresidue : MarkRResidue external ⟨left, x, y :: right⟩) :
    MarkRResidue external ⟨written :: left, y, right⟩ := by
  rcases hresidue with ⟨before, after, consumed, hbefore, heq, htail⟩
  cases before with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at heq
      exact (hx heq.1).elim
  | cons b bs =>
      simp only [List.cons_append, List.cons.injEq] at heq
      have hb : b = x := heq.1.symm
      subst b
      refine ⟨bs, after, consumed, ?_, heq.2, htail⟩
      intro a ha
      exact hbefore a (by simp [ha])

/-- Ordinary left moves preserve the selected marker whenever both newly
placed forward cells are not markers.  This is the list-level engine for the
return and search loops; special write-`markR` moves use
`externalResidue_install_markR_left` instead. -/
theorem markRResidue_move_left
    {external left right : List ConcreteTape} {x y written : ConcreteTape}
    (hx : x ≠ .markR) (hy : y ≠ .markR) (hwritten : written ≠ .markR)
    (hresidue : MarkRResidue external ⟨y :: left, x, right⟩) :
    MarkRResidue external ⟨left, y, written :: right⟩ := by
  rcases hresidue with ⟨before, after, consumed, hbefore, heq, htail⟩
  cases before with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at heq
      exact (hx heq.1).elim
  | cons b bs =>
      simp only [List.cons_append, List.cons.injEq] at heq
      have hb : b = x := heq.1.symm
      subst b
      refine ⟨y :: written :: bs, after, consumed, ?_, ?_, htail⟩
      · intro a ha
        simp only [List.mem_cons] at ha
        rcases ha with rfl | rfl | ha
        · exact hy
        · exact hwritten
        · exact hbefore a (by simp [ha])
      · simpa [List.cons_append] using heq.2

/-- The control-indexed shape required for the relocation induction.  The
three transient controls have just overwritten the old marker and therefore
carry an `ExternalResidue` directly.  All other preterminal controls retain a
literal marker in their forward zipper.  `finalReturn` is deliberately
unconstrained: by then the terminal `rightEnd` occurrence has already been
read, so no further tail-origin argument is needed. -/
def MarkRRelocationState (external : List ConcreteTape)
    (q : CopierState) (z : MStarParserExecution.Zipper ConcreteTape) : Prop :=
  match q with
  | .placeBoundary _ | .payloadBoundary | .payloadPlace | .rightBufferScan =>
      ExternalResidue external z
  | .finalReturn => True
  | _ => MarkRResidue external z

/-- Initial state of the state-indexed relocation invariant. -/
theorem markRRelocationState_installed
    (source external : List ConcreteTape) :
    MarkRRelocationState external (.findOld 0)
      ⟨.markL :: source, cellA, .markR :: external⟩ :=
  markRResidue_installed source external

/-- The state invariant has to be paired with the remaining successful
continuation.  This rules out syntactically possible but dead visits to a
second `markR` occurring inside the arbitrary parser-side `source` list.
It is the induction carrier for the copier-control relocation proof. -/
def SuccessfulCopierSuffix (fuel : ℕ) (q : CopierState)
    (z out : MStarParserExecution.Zipper ConcreteTape) : Prop :=
  run fuel (.running q z) = .groupReady out

/-- Liveness-indexed version of the relocation invariant.  The `out` is kept
explicit because every recursive run step transports the same deterministic
group-ready endpoint. -/
def LiveMarkRRelocationState (external : List ConcreteTape) (fuel : ℕ)
    (q : CopierState) (z out : MStarParserExecution.Zipper ConcreteTape) : Prop :=
  SuccessfulCopierSuffix fuel q z out →
    MarkRRelocationState external q z

/-- The installed `findOld` configuration satisfies the liveness-indexed
carrier for every remaining successful continuation; the spatial part is
independent of that continuation. -/
theorem liveMarkRRelocationState_installed
    (source external : List ConcreteTape) (fuel : ℕ)
    (out : MStarParserExecution.Zipper ConcreteTape) :
    LiveMarkRRelocationState external fuel (.findOld 0)
      ⟨.markL :: source, cellA, .markR :: external⟩ out := by
  intro _
  exact markRRelocationState_installed source external

/-- An arbitrary parser-side `source` is allowed to contain a second literal
`markR`, but `groupSeekLen` cannot successfully traverse one.  This is the
first liveness inversion used when the selected relocating barrier is carried
past the source-side grouping phase. -/
theorem groupSeekLen_markR_has_no_successful_suffix
    (fuel : ℕ) (left right : List ConcreteTape)
    (out : MStarParserExecution.Zipper ConcreteTape)
    (hrun : run fuel (.running .groupSeekLen ⟨left, .markR, right⟩) =
      .groupReady out) : False := by
  exact PakSlotOneCopierMarkRBarrier.running_run_to_groupReady_not_oneStep_rejected
    .groupSeekLen ⟨left, .markR, right⟩ fuel out (by rfl) hrun

/-- Convenient focused form of the preceding liveness exclusion. -/
theorem groupSeekLen_success_focus_ne_markR
    (fuel : ℕ) (z out : MStarParserExecution.Zipper ConcreteTape)
    (hrun : SuccessfulCopierSuffix fuel .groupSeekLen z out) :
    z.focus ≠ .markR := by
  intro hfocus
  rcases z with ⟨left, focus, right⟩
  change focus = .markR at hfocus
  subst focus
  exact groupSeekLen_markR_has_no_successful_suffix fuel left right out hrun

/-- The source-return pass likewise cannot turn an unrelated `markR` into a
successful continuation. -/
theorem groupReturn_markR_has_no_successful_suffix
    (fuel : ℕ) (left right : List ConcreteTape)
    (out : MStarParserExecution.Zipper ConcreteTape)
    (hrun : run fuel (.running .groupReturn ⟨left, .markR, right⟩) =
      .groupReady out) : False := by
  exact PakSlotOneCopierMarkRBarrier.running_run_to_groupReady_not_oneStep_rejected
    .groupReturn ⟨left, .markR, right⟩ fuel out (by rfl) hrun

/-- The final source-return pass has the same dead-branch exclusion. -/
theorem finishReturn_markR_has_no_successful_suffix
    (fuel : ℕ) (left right : List ConcreteTape)
    (out : MStarParserExecution.Zipper ConcreteTape)
    (hrun : run fuel (.running .finishReturn ⟨left, .markR, right⟩) =
      .groupReady out) : False := by
  exact PakSlotOneCopierMarkRBarrier.running_run_to_groupReady_not_oneStep_rejected
    .finishReturn ⟨left, .markR, right⟩ fuel out (by rfl) hrun

/-- In payload search, only the selected barrier may be crossed by the
separate `payloadCarry` control; a bare `payloadSeek` read of `markR` is
dead. -/
theorem payloadSeek_markR_has_no_successful_suffix
    (fuel : ℕ) (left right : List ConcreteTape)
    (out : MStarParserExecution.Zipper ConcreteTape)
    (hrun : run fuel (.running .payloadSeek ⟨left, .markR, right⟩) =
      .groupReady out) : False := by
  exact PakSlotOneCopierMarkRBarrier.running_run_to_groupReady_not_oneStep_rejected
    .payloadSeek ⟨left, .markR, right⟩ fuel out (by rfl) hrun

/-- After payload completion the only legal return delimiter is `markL`; an
extra right marker cannot be a live state. -/
theorem payloadDoneReturn_markR_has_no_successful_suffix
    (fuel : ℕ) (left right : List ConcreteTape)
    (out : MStarParserExecution.Zipper ConcreteTape)
    (hrun : run fuel (.running .payloadDoneReturn ⟨left, .markR, right⟩) =
      .groupReady out) : False := by
  exact PakSlotOneCopierMarkRBarrier.running_run_to_groupReady_not_oneStep_rejected
    .payloadDoneReturn ⟨left, .markR, right⟩ fuel out (by rfl) hrun

/-- Precisely the controls whose literal table has a marker-crossing arm.
This finite classification is kept separate from the spatial provenance:
crossing is permitted here, but only `finalSeekBoundary` turns it into the
terminal external-tail residue. -/
def MayCrossMarkR : CopierState → Prop
  | .findOld _ | .seekBoundary _ | .counterToWork | .payloadCarry _ |
      .finalSeekBoundary | .finalReturn => True
  | _ => False

/-- Exhaustive control-table inversion for all non-crossing controls.  It is
the compact form of the individual liveness exclusions above and covers the
transient boundary states as well as final return. -/
theorem nonCrossing_markR_has_no_successful_suffix
    (q : CopierState) (hq : ¬ MayCrossMarkR q)
    (fuel : ℕ) (left right : List ConcreteTape)
    (out : MStarParserExecution.Zipper ConcreteTape)
    (hrun : run fuel (.running q ⟨left, .markR, right⟩) = .groupReady out) :
    False := by
  apply PakSlotOneCopierMarkRBarrier.running_run_to_groupReady_not_oneStep_rejected
    q ⟨left, .markR, right⟩ fuel out ?_ hrun
  cases q <;>
    simp [MayCrossMarkR, oneStep, copierStep, copyGo, copyReject,
      MStarParserExecution.applyAction, cellA, cellB, rightEnd,
      MStarParserMicrocode.lenDone, MStarParserMicrocode.endpointMark,
      MStarParserMicrocode.payloadZero, MStarParserMicrocode.payloadOne,
      MStarParserMicrocode.sepLen, MStarParserMicrocode.sepPad,
      MStarParserMicrocode.pairedLen, MStarParserMicrocode.padDone] at hq ⊢

private theorem markRResidue_move_right_clean
    {external left right : List ConcreteTape} {x y written : ConcreteTape}
    (hx : x ≠ .markR) (hw : written ≠ .markR)
    (hleft : .markR ∉ left)
    (hresidue : MarkRResidue external ⟨left, x, y :: right⟩) :
    MarkRResidue external ⟨written :: left, y, right⟩ ∧
      .markR ∉ written :: left := by
  refine ⟨markRResidue_move_right hx hresidue, ?_⟩
  intro hmem
  simp only [List.mem_cons] at hmem
  rcases hmem with h | h
  · exact hw h.symm
  · exact hleft h

private theorem markRResidue_move_left_clean
    {external left right : List ConcreteTape} {x y written : ConcreteTape}
    (hx : x ≠ .markR) (hw : written ≠ .markR)
    (hleft : .markR ∉ y :: left)
    (hresidue : MarkRResidue external ⟨y :: left, x, right⟩) :
    MarkRResidue external ⟨left, y, written :: right⟩ ∧ .markR ∉ left := by
  have hy : y ≠ .markR := by
    intro h
    apply hleft
    simp [h]
  have htail : .markR ∉ left := by
    intro h
    apply hleft
    simp [h]
  exact ⟨markRResidue_move_left hx hy hw hresidue, htail⟩

private theorem markRResidue_cross_right_clean
    {external left right : List ConcreteTape} {y written : ConcreteTape}
    (hw : written ≠ .markR) (hleft : .markR ∉ left)
    (hresidue : MarkRResidue external ⟨left, .markR, y :: right⟩) :
    ExternalResidue external ⟨written :: left, y, right⟩ ∧
      .markR ∉ written :: left := by
  refine ⟨markRFocusResidue_cross_right_written
    (MarkRResidue.at_focus hresidue), ?_⟩
  intro hmem
  simp only [List.mem_cons] at hmem
  rcases hmem with h | h
  · exact hw h.symm
  · exact hleft h

private theorem markRResidue_cross_left_clean
    {external left right : List ConcreteTape} {y : ConcreteTape}
    (hleft : .markR ∉ y :: left)
    (hresidue : MarkRResidue external ⟨y :: left, .markR, right⟩) :
    MarkRResidue external ⟨left, y, .markR :: right⟩ ∧ .markR ∉ left := by
  have hy : y ≠ .markR := by
    intro h
    apply hleft
    simp [h]
  have htail : .markR ∉ left := by
    intro h
    apply hleft
    simp [h]
  exact ⟨markRFocusResidue_cross_left_write_markR hy
    (MarkRResidue.at_focus hresidue), htail⟩

private theorem externalResidue_install_left_clean
    {external left right : List ConcreteTape} {y : ConcreteTape}
    (hleft : .markR ∉ y :: left)
    (hresidue : ExternalResidue external
      ⟨y :: left, .core MStarConcreteAlphabet.work, right⟩) :
    MarkRResidue external ⟨left, y, .markR :: right⟩ ∧ .markR ∉ left := by
  have hy : y ≠ .markR := by
    intro h
    apply hleft
    simp [h]
  have htail : .markR ∉ left := by
    intro h
    apply hleft
    simp [h]
  exact ⟨externalResidue_install_markR_left external left right y hy hresidue,
    htail⟩

private theorem externalResidue_move_right_clean
    {external left right : List ConcreteTape} {x y written : ConcreteTape}
    (hw : written ≠ .markR) (hleft : .markR ∉ left)
    (hresidue : ExternalResidue external ⟨left, x, y :: right⟩) :
    ExternalResidue external ⟨written :: left, y, right⟩ ∧
      .markR ∉ written :: left := by
  refine ⟨externalResidue_move_right hresidue, ?_⟩
  intro hmem
  simp only [List.mem_cons] at hmem
  rcases hmem with h | h
  · exact hw h.symm
  · exact hleft h

attribute [aesop safe apply]
  markRResidue_move_right_clean markRResidue_move_left_clean
  markRResidue_cross_right_clean markRResidue_cross_left_clean
  externalResidue_install_left_clean externalResidue_move_right_clean
  markRResidue_move_right markRResidue_move_left
  markRFocusResidue_cross_right_written markRFocusResidue_cross_left_write_markR
  externalResidue_install_markR_left externalResidue_move_right

/-- The relocation certificate is preserved by every live copier step.  The
successful suffix hypothesis is essential: it excludes branches which read
an unrelated `markR` on the parser side and immediately reject later. -/
theorem markRRelocationState_oneStep_live
    (external : List ConcreteTape) (fuel : ℕ)
    (q q' : CopierState)
    (z z' out : MStarParserExecution.Zipper ConcreteTape)
    (hpast : q ≠ .seedCell ∧ q ≠ .seedBoundary)
    (hstate : MarkRRelocationState external q z)
    (hleft : .markR ∉ z.leftRev)
    (hstep : oneStep (.running q z) = .running q' z')
    (hrun : run fuel (.running q' z') = .groupReady out) :
    MarkRRelocationState external q' z' ∧ .markR ∉ z'.leftRev ∧
      q' ≠ .seedCell ∧ q' ≠ .seedBoundary := by
  rcases z with ⟨left, focus, right⟩
  rcases z' with ⟨left', focus', right'⟩
  cases q <;> cases focus <;>
    simp [oneStep, copierStep, copyGo, copyReject, copySim,
      MStarParserExecution.applyAction, MarkRRelocationState,
      cellA, cellB, rightEnd,
      MStarParserMicrocode.lenDone, MStarParserMicrocode.endpointMark,
      MStarParserMicrocode.payloadZero, MStarParserMicrocode.payloadOne,
      MStarParserMicrocode.sepLen, MStarParserMicrocode.sepPad,
      MStarParserMicrocode.pairedLen, MStarParserMicrocode.padDone] at hstep
  all_goals
    cases left <;> cases right
  all_goals
    try split_ifs at hstep
  all_goals
      simp_all [MarkRRelocationState, oneStep, copierStep, copyGo, copyReject,
        copySim, MStarParserExecution.applyAction, cellA, cellB, rightEnd,
        MStarParserMicrocode.lenDone, MStarParserMicrocode.endpointMark,
        MStarParserMicrocode.payloadZero, MStarParserMicrocode.payloadOne,
        MStarParserMicrocode.sepLen, MStarParserMicrocode.sepPad,
        MStarParserMicrocode.pairedLen, MStarParserMicrocode.padDone]
  all_goals
    rcases hstep with ⟨hq, hleft, hfocus, hright⟩
    subst q'
    subst left'
    subst focus'
    subst right'
  all_goals
    simp only [MarkRRelocationState]
  all_goals
    try apply And.intro
  all_goals
    solve
    | simp_all
    | exact markRFocusResidue_cross_left_write_markR (by intro h; simp_all)
        (MarkRResidue.at_focus hstate)
    | exact markRFocusResidue_cross_right_written
        (MarkRResidue.at_focus hstate)
    | exact externalResidue_install_markR_left external _ _ _
        (by intro h; simp_all)
        hstate
    | exact markRResidue_move_left (by simp_all) (by intro h; simp_all)
        (by simp_all)
        hstate
    | exact markRResidue_move_right (by simp_all) hstate
    | exact externalResidue_move_right hstate

/-- Iteration of the live one-step relocation theorem along a successful
prefix.  The explicit `rest` ledger avoids dependent subtraction during the
induction. -/
theorem markRRelocationState_at_run
    (external : List ConcreteTape) :
    ∀ (steps rest : ℕ) (q : CopierState)
      (z out : MStarParserExecution.Zipper ConcreteTape)
      (q' : CopierState) (z' : MStarParserExecution.Zipper ConcreteTape),
      q ≠ .seedCell ∧ q ≠ .seedBoundary →
      MarkRRelocationState external q z →
      .markR ∉ z.leftRev →
      run (steps + rest) (.running q z) = .groupReady out →
      run steps (.running q z) = .running q' z' →
      MarkRRelocationState external q' z' ∧ .markR ∉ z'.leftRev ∧
        q' ≠ .seedCell ∧ q' ≠ .seedBoundary := by
  intro steps
  induction steps with
  | zero =>
      intro rest q z out q' z' hpast hstate hleft _ hat
      simp only [run_zero] at hat
      cases hat
      exact ⟨hstate, hleft, hpast⟩
  | succ steps ih =>
      intro rest q z out q' z' hpast hstate hleft htotal hat
      cases hnext : oneStep (.running q z) with
      | rejected =>
          rw [Nat.succ_add, run_succ, hnext, rejected_absorbing] at htotal
          cases htotal
      | stuck =>
          rw [Nat.succ_add, run_succ, hnext, stuck_absorbing] at htotal
          cases htotal
      | groupReady w =>
          rw [run_succ, hnext, groupReady_absorbing] at hat
          cases hat
      | running q₁ z₁ =>
          have htail : run (steps + rest) (.running q₁ z₁) =
              .groupReady out := by
            simpa only [Nat.succ_add, run_succ, hnext] using htotal
          have hprefix : run steps (.running q₁ z₁) = .running q' z' := by
            simpa only [run_succ, hnext] using hat
          rcases markRRelocationState_oneStep_live external (steps + rest)
              q q₁ z z₁ out hpast hstate hleft hnext htail with
            ⟨hstate₁, hleft₁, hpast₁⟩
          exact ih rest q₁ z₁ out q' z' hpast₁ hstate₁ hleft₁ htail hprefix

/-- A state-indexed trace invariant for the copier run started immediately
after the four-step `markR` installation.  Its `barrier` component records the
literal installation/crossing occurrence; its `rightBuffer_residue` component
is deliberately stronger than the old time-only `CrossesMarkR` fact: it
identifies the actual suffix at every later terminal-scan state.

The parser-to-copier bridge should construct this record by induction on the
concrete copier controls while relocating `markR`; it must not be replaced by
a global claim that the copier never writes `scratch 2` (which is false in the
payload phase). -/
structure InstalledMarkRTrace
    (source external : List ConcreteTape) (fuel : ℕ) : Prop where
  barrier :
    PakSlotOneCopierMarkRBarrier.CrossesMarkR fuel
      (.running (.findOld 0) ⟨.markL :: source, cellA, .markR :: external⟩)
  rightBuffer_residue :
    ∀ (j : ℕ) (z : MStarParserExecution.Zipper ConcreteTape),
      j < fuel →
      run j (.running (.findOld 0)
        ⟨.markL :: source, cellA, .markR :: external⟩) =
          .running .rightBufferScan z →
      ExternalResidue external z

/-- Once the state-indexed relocation invariant has been established, the
desired tail-origin conclusion is immediate from the existing successful-run
right-end read certificate.  Notice that the proof uses the *specific*
`rightBufferScan` state supplied by the certificate, rather than merely a
time index at which some `markR` was crossed. -/
theorem run_from_installedMarkR_readsRightEnd_mem_tail_of_trace
    (source external : List ConcreteTape) (fuel : ℕ)
    (out : MStarParserExecution.Zipper ConcreteTape)
    (htrace : InstalledMarkRTrace source external fuel)
    (hrun : run fuel
      (.running (.findOld 0) ⟨.markL :: source, cellA, .markR :: external⟩) =
        .groupReady out) :
    rightEnd ∈ external := by
  let initial : Result :=
    .running (.findOld 0) ⟨.markL :: source, cellA, .markR :: external⟩
  have hreads : PakSlotOneCopierMarkRBarrier.ReadsRightEnd fuel initial := by
    rcases PakSlotOneCopierMarkRBarrier.run_to_groupReady_reads_or_starts_finalReturn
        fuel (.findOld 0)
          ⟨.markL :: source, cellA, .markR :: external⟩ out hrun with
      hbad | hreads
    · cases hbad
    · exact hreads
  rcases (PakSlotOneCopierMarkRBarrier.readsRightEnd_iff_exists fuel initial).mp
      hreads with ⟨j, hj, hread⟩
  cases hres : run j initial with
  | running q z =>
      rw [hres] at hread
      cases q <;>
        simp [PakSlotOneCopierMarkRBarrier.CopierReadsRightEnd] at hread
      rcases z with ⟨left, focus, right⟩
      change focus = rightEnd at hread
      subst focus
      apply ExternalResidue.rightEnd_mem
      apply htrace.rightBuffer_residue j
        ⟨left, rightEnd, right⟩ hj
      simpa [initial] using hres
  | groupReady z | rejected | stuck =>
      rw [hres] at hread
      simp [PakSlotOneCopierMarkRBarrier.CopierReadsRightEnd, hres] at hread

/-- A successful installed-marker run reads its terminal symbol from the
supplied external tail whenever the parser-side source contains no marker.
This is the form needed by the slot-one frame: its source consists only of
core letters, scratch bookkeeping, and the left delimiter. -/
theorem run_from_installedMarkR_readsRightEnd_mem_tail
    (source external : List ConcreteTape) (fuel : ℕ)
    (out : MStarParserExecution.Zipper ConcreteTape)
    (hsource : .markR ∉ source)
    (hrun : run fuel
      (.running (.findOld 0) ⟨.markL :: source, cellA, .markR :: external⟩) =
        .groupReady out) :
    rightEnd ∈ external := by
  let initial : Result :=
    .running (.findOld 0) ⟨.markL :: source, cellA, .markR :: external⟩
  apply run_from_installedMarkR_readsRightEnd_mem_tail_of_trace
    source external fuel out ?_ hrun
  refine
    { barrier := ?_
      rightBuffer_residue := ?_ }
  · rcases PakSlotOneCopierMarkRBarrier.run_to_groupReady_post_or_crossesMarkR
      fuel (.findOld 0) ⟨.markL :: source, cellA, .markR :: external⟩ out
      hrun with hpost | hcross
    · simp [PakSlotOneCopierMarkRBarrier.PostRightBuffer] at hpost
    · exact hcross
  · intro j z hj hat
    have htotal : run (j + (fuel - j))
        (.running (.findOld 0)
          ⟨.markL :: source, cellA, .markR :: external⟩) =
        .groupReady out := by
      rw [Nat.add_sub_of_le (Nat.le_of_lt hj)]
      exact hrun
    have hinv := markRRelocationState_at_run external j (fuel - j)
      (.findOld 0) ⟨.markL :: source, cellA, .markR :: external⟩ out
      .rightBufferScan z (by simp) (markRRelocationState_installed source external)
      (by simpa using hsource) htotal hat
    simpa only [MarkRRelocationState] using hinv.1

end PakFixedPolyomino.PakSlotOneMarkRTailProvenance
