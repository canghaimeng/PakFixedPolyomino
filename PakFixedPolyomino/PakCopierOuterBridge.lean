import PakFixedPolyomino.PakParserOuterBridge

/-!
# Canonical copier zipper realization in the outer program

The parser bridge stops at the concrete `copyReady` configuration and supplies
the physical copier-entry arrow.  This module records the corresponding
anchored configurations for the copier proper.  Canonicality includes a real
future `groupReady` execution, so arbitrary hash-entering zippers are not
silently admitted into the ambient simulation.
-/

namespace PakFixedPolyomino.PakParserOuterBridge

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics

def anchoredCopierConfig (q : MStarCopierMicrocode.CopierState)
    (origin : Int) (z : MStarParserExecution.Zipper OuterTape) : OuterConfig :=
  { state := .parser (.inr q)
    head := origin + z.leftRev.length
    tape := anchoredZipperTape origin z }

def anchoredGroupReadyConfig (origin : Int)
    (z : MStarParserExecution.Zipper OuterTape) : OuterConfig :=
  { state := .sim MStarULogAssembly.data.uStart
    head := origin + z.leftRev.length
    tape := anchoredZipperTape origin z }

/-- A copier result is canonical only when it genuinely reaches the abstract
`groupReady` endpoint of the finite copier execution. -/
def SideCopierCanFinish (r : MStarCopierExecution.Result) : Prop :=
  ∃ z, MStarCopierExecution.Reaches r (.groupReady z)

def sideCopierRealize (r : MStarCopierExecution.Result)
    (c : OuterConfig) : Prop :=
  match r with
  | .running q z => ∃ origin, c = anchoredCopierConfig q origin z
  | .groupReady z => ∃ origin, c = anchoredGroupReadyConfig origin z
  | .rejected => False
  | .stuck => False

def SideCopierCanonical (x : ConcretePakSide.Word)
    (r : MStarCopierExecution.Result) : Prop :=
  MStarCopierExecution.Reaches
      (.running .seedCell (PakSideScanner.sideCopierSeedZipper x)) r ∧
    SideCopierCanFinish r

def CanonicalSideCopierRealize (x : ConcretePakSide.Word)
    (r : MStarCopierExecution.Result) (c : OuterConfig) : Prop :=
  SideCopierCanonical x r ∧ sideCopierRealize r c

theorem sideCopierCanFinish_groupReady
    (z : MStarParserExecution.Zipper OuterTape) :
    SideCopierCanFinish (.groupReady z) := by
  exact ⟨z, MStarCopierExecution.reaches_refl _⟩

theorem sideCopierCanFinish_ne_rejected
    (h : SideCopierCanFinish .rejected) : False := by
  rcases h with ⟨z, fuel, hrun⟩
  have habsorb : MStarCopierExecution.run fuel .rejected = .rejected := by
    induction fuel with
    | zero => rfl
    | succ fuel ih => simpa [MStarCopierExecution.run,
        MStarCopierExecution.oneStep] using ih
  rw [habsorb] at hrun
  cases hrun

theorem sideCopierCanFinish_ne_stuck
    (h : SideCopierCanFinish .stuck) : False := by
  rcases h with ⟨z, fuel, hrun⟩
  have habsorb : MStarCopierExecution.run fuel .stuck = .stuck := by
    induction fuel with
    | zero => rfl
    | succ fuel ih => simpa [MStarCopierExecution.run,
        MStarCopierExecution.oneStep] using ih
  rw [habsorb] at hrun
  cases hrun

/-- Canonical future reachability advances by one finite copier step. -/
theorem SideCopierCanFinish.oneStep {r : MStarCopierExecution.Result}
    (h : SideCopierCanFinish r) :
    SideCopierCanFinish (MStarCopierExecution.oneStep r) := by
  cases r with
  | groupReady z => simpa [MStarCopierExecution.oneStep] using h
  | rejected => exact (sideCopierCanFinish_ne_rejected h).elim
  | stuck => exact (sideCopierCanFinish_ne_stuck h).elim
  | running q tape =>
      rcases h with ⟨finish, fuel, hrun⟩
      cases fuel with
      | zero => simp [MStarCopierExecution.run] at hrun
      | succ fuel => exact ⟨finish, fuel, hrun⟩

theorem SideCopierCanonical.oneStep (x : ConcretePakSide.Word)
    {r : MStarCopierExecution.Result} (h : SideCopierCanonical x r) :
    SideCopierCanonical x (MStarCopierExecution.oneStep r) := by
  constructor
  · exact MStarCopierExecution.reaches_trans h.1
      (MStarCopierExecution.reaches_of_oneStep rfl)
  · exact h.2.oneStep

theorem sideCopierCanonical_seed (x : ConcretePakSide.Word) :
    SideCopierCanonical x
      (.running .seedCell (PakSideScanner.sideCopierSeedZipper x)) := by
  rcases (PakSideScanner.side_parser_then_copier x).2.2 with
    ⟨finish, hreach, _⟩
  exact ⟨MStarCopierExecution.reaches_refl _, ⟨finish, hreach⟩⟩

def changeUnitCopierState (uStart : MStarULogAssembly.UniversalState) :
    MStarCopierMicrocode.CopierOuterState Unit → OuterState
  | .start => .start
  | .accept => .accept
  | .reject => .reject
  | .parser q => .parser q
  | .sim () => .sim uStart

def changeUnitCopierAction (uStart : MStarULogAssembly.UniversalState)
    (a : FiniteOneTapeProgram.Action
      (MStarCopierMicrocode.CopierOuterState Unit) OuterTape) : OuterAction :=
  { write := a.write
    target := changeUnitCopierState uStart a.target
    move := a.move }

/-- The concrete copier table is parametric only in its final universal start
state; this closed finite check transports every literal rule. -/
theorem copierStep_changeUState_all :
    ∀ q : MStarCopierMicrocode.CopierState, ∀ x : OuterTape,
      MStarCopierMicrocode.copierStep MStarULogAssembly.data.uStart q x =
        (MStarCopierMicrocode.copierStep (UState := Unit) () q x).map
          (changeUnitCopierAction MStarULogAssembly.data.uStart) := by
  intro q x
  cases q <;> cases x <;>
    simp [MStarCopierMicrocode.copierStep, MStarCopierMicrocode.copyGo,
      MStarCopierMicrocode.copyReject, MStarCopierMicrocode.copySim,
      changeUnitCopierAction, changeUnitCopierState]
  all_goals
    repeat' first | split
    all_goals simp_all [MStarCopierMicrocode.copyGo,
      MStarCopierMicrocode.copyReject, MStarCopierMicrocode.copySim,
      changeUnitCopierAction, changeUnitCopierState]

theorem applyAction_changeUnitCopierAction
    (z : MStarParserExecution.Zipper OuterTape)
    (a : FiniteOneTapeProgram.Action
      (MStarCopierMicrocode.CopierOuterState Unit) OuterTape) :
    MStarParserExecution.applyAction z
        (changeUnitCopierAction MStarULogAssembly.data.uStart a) =
      MStarParserExecution.applyAction z a := by
  rcases a with ⟨write, target, move⟩
  cases move <;> rfl

theorem copierUnitAction_to_outerAction
    (q : MStarCopierMicrocode.CopierState) (x : OuterTape)
    (a : FiniteOneTapeProgram.Action
      (MStarCopierMicrocode.CopierOuterState Unit) OuterTape)
    (hstep : MStarCopierMicrocode.copierStep (UState := Unit) () q x =
      some a) :
    MStarCopierMicrocode.copierStep MStarULogAssembly.data.uStart q x =
      some (changeUnitCopierAction MStarULogAssembly.data.uStart a) := by
  rw [copierStep_changeUState_all q x, hstep]
  rfl

theorem sideCopierRealize_outerRunningStep_atMostOne
    (q q' : MStarCopierMicrocode.CopierState) (origin : Int)
    (z z' : MStarParserExecution.Zipper OuterTape)
    (a : FiniteOneTapeProgram.Action
      (MStarCopierMicrocode.CopierOuterState Unit) OuterTape)
    (hstep : MStarCopierMicrocode.copierStep (UState := Unit) () q z.focus =
      some a)
    (happly : MStarParserExecution.applyAction z a = some z')
    (htarget : a.target = .parser (.inr q'))
    (hmovable : MStarOuterProgram.movable
      (anchoredZipperTape origin z' (origin + z'.leftRev.length)) = true) :
    ∃ d, sideCopierRealize (.running q' z') d ∧
      ∃ arrows : List OuterArrow, arrows.length ≤ 1 ∧
        FiniteOneTapeSemantics.run MStarULogAssembly.program
          MStarOuterProgram.movable arrows (anchoredCopierConfig q origin z) =
            some d := by
  let a' := changeUnitCopierAction MStarULogAssembly.data.uStart a
  let c := anchoredCopierConfig q origin z
  let d := anchoredCopierConfig q' origin z'
  have hstep' := copierUnitAction_to_outerAction q z.focus a hstep
  have happly' : MStarParserExecution.applyAction z a' = some z' := by
    rw [applyAction_changeUnitCopierAction]
    exact happly
  have htarget' : a'.target = (.parser (.inr q') : OuterState) := by
    simp [a', changeUnitCopierAction, changeUnitCopierState, htarget]
  have hafter : afterAction c a' = d := by
    simp only [c, d, afterAction, anchoredCopierConfig, writtenTape]
    rw [htarget', anchoredZipperHead_applyAction origin z z' a' happly',
      anchoredZipperTape_applyAction origin z z' a' happly']
  have htape : writtenTape c a'.write = anchoredZipperTape origin z' := by
    simpa only [c, anchoredCopierConfig, writtenTape] using
      (anchoredZipperTape_applyAction origin z z' a' happly').symm
  have hmove : MStarOuterProgram.movable
      ((writtenTape c a'.write) (moveHead a'.move c.head)) = true := by
    change MStarOuterProgram.movable
      ((writtenTape c a'.write) (moveHead a'.move
        (origin + z.leftRev.length))) = true
    rw [htape, ← anchoredZipperHead_applyAction origin z z' a' happly']
    exact hmovable
  refine ⟨d, ⟨origin, rfl⟩, ?_⟩
  rw [← hafter]
  exact outer_slotZeroArrow_length_at_most_one c (.parser (.inr q)) z.focus a'
    (parserCopier_slotZero_rule _ _ _ hstep')
    (by simp [c, anchoredCopierConfig])
    (by simpa [c, anchoredCopierConfig] using anchoredZipperTape_at_head origin z)
    hmove

theorem sideCopierRealize_outerRunningStep
    (q q' : MStarCopierMicrocode.CopierState) (origin : Int)
    (z z' : MStarParserExecution.Zipper OuterTape)
    (a : FiniteOneTapeProgram.Action
      (MStarCopierMicrocode.CopierOuterState Unit) OuterTape)
    (hstep : MStarCopierMicrocode.copierStep (UState := Unit) () q z.focus =
      some a)
    (happly : MStarParserExecution.applyAction z a = some z')
    (htarget : a.target = .parser (.inr q'))
    (hmovable : MStarOuterProgram.movable
      (anchoredZipperTape origin z' (origin + z'.leftRev.length)) = true) :
    ∃ d, sideCopierRealize (.running q' z') d ∧
      OuterReaches (anchoredCopierConfig q origin z) d := by
  rcases sideCopierRealize_outerRunningStep_atMostOne q q' origin z z' a
      hstep happly htarget hmovable with ⟨d, hd, arrows, _, harrows⟩
  exact ⟨d, hd, ⟨arrows, harrows⟩⟩

theorem sideCopierRealize_outerGroupReadyStep_atMostOne
    (q : MStarCopierMicrocode.CopierState) (origin : Int)
    (z z' : MStarParserExecution.Zipper OuterTape)
    (a : FiniteOneTapeProgram.Action
      (MStarCopierMicrocode.CopierOuterState Unit) OuterTape)
    (hstep : MStarCopierMicrocode.copierStep (UState := Unit) () q z.focus =
      some a)
    (happly : MStarParserExecution.applyAction z a = some z')
    (htarget : ∃ u, a.target = .sim u)
    (hmovable : MStarOuterProgram.movable
      (anchoredZipperTape origin z' (origin + z'.leftRev.length)) = true) :
    ∃ d, sideCopierRealize (.groupReady z') d ∧
      ∃ arrows : List OuterArrow, arrows.length ≤ 1 ∧
        FiniteOneTapeSemantics.run MStarULogAssembly.program
          MStarOuterProgram.movable arrows (anchoredCopierConfig q origin z) =
            some d := by
  rcases htarget with ⟨u, htarget⟩
  cases u
  let a' := changeUnitCopierAction MStarULogAssembly.data.uStart a
  let c := anchoredCopierConfig q origin z
  let d := anchoredGroupReadyConfig origin z'
  have hstep' := copierUnitAction_to_outerAction q z.focus a hstep
  have happly' : MStarParserExecution.applyAction z a' = some z' := by
    rw [applyAction_changeUnitCopierAction]
    exact happly
  have htarget' : a'.target = (.sim MStarULogAssembly.data.uStart : OuterState) := by
    simp [a', changeUnitCopierAction, changeUnitCopierState, htarget]
  have hafter : afterAction c a' = d := by
    simp only [c, d, afterAction, anchoredCopierConfig, anchoredGroupReadyConfig,
      writtenTape]
    rw [htarget', anchoredZipperHead_applyAction origin z z' a' happly',
      anchoredZipperTape_applyAction origin z z' a' happly']
  have htape : writtenTape c a'.write = anchoredZipperTape origin z' := by
    simpa only [c, anchoredCopierConfig, writtenTape] using
      (anchoredZipperTape_applyAction origin z z' a' happly').symm
  have hmove : MStarOuterProgram.movable
      ((writtenTape c a'.write) (moveHead a'.move c.head)) = true := by
    change MStarOuterProgram.movable
      ((writtenTape c a'.write) (moveHead a'.move
        (origin + z.leftRev.length))) = true
    rw [htape, ← anchoredZipperHead_applyAction origin z z' a' happly']
    exact hmovable
  refine ⟨d, ⟨origin, rfl⟩, ?_⟩
  rw [← hafter]
  exact outer_slotZeroArrow_length_at_most_one c (.parser (.inr q)) z.focus a'
    (parserCopier_slotZero_rule _ _ _ hstep')
    (by simp [c, anchoredCopierConfig])
    (by simpa [c, anchoredCopierConfig] using anchoredZipperTape_at_head origin z)
    hmove

theorem sideCopierRealize_outerGroupReadyStep
    (q : MStarCopierMicrocode.CopierState) (origin : Int)
    (z z' : MStarParserExecution.Zipper OuterTape)
    (a : FiniteOneTapeProgram.Action
      (MStarCopierMicrocode.CopierOuterState Unit) OuterTape)
    (hstep : MStarCopierMicrocode.copierStep (UState := Unit) () q z.focus =
      some a)
    (happly : MStarParserExecution.applyAction z a = some z')
    (htarget : ∃ u, a.target = .sim u)
    (hmovable : MStarOuterProgram.movable
      (anchoredZipperTape origin z' (origin + z'.leftRev.length)) = true) :
    ∃ d, sideCopierRealize (.groupReady z') d ∧
      OuterReaches (anchoredCopierConfig q origin z) d := by
  rcases sideCopierRealize_outerGroupReadyStep_atMostOne q origin z z' a
      hstep happly htarget hmovable with ⟨d, hd, arrows, _, harrows⟩
  exact ⟨d, hd, ⟨arrows, harrows⟩⟩

private theorem copierStep_hash_rejected_all :
    ∀ q : MStarCopierMicrocode.CopierState,
      MStarCopierMicrocode.copierStep (UState := Unit) () q .hash =
        some (MStarCopierMicrocode.copyReject .hash) := by
  intro q
  cases q <;> rfl

theorem copierOneStep_hash_rejected
    (q : MStarCopierMicrocode.CopierState) (left right : List OuterTape) :
    MStarCopierExecution.oneStep (.running q ⟨left, .hash, right⟩) =
      .rejected := by
  simp [MStarCopierExecution.oneStep, copierStep_hash_rejected_all,
    MStarCopierMicrocode.copyReject, MStarParserExecution.applyAction]

theorem SideCopierCanonical.running_focus_ne_hash
    (x : ConcretePakSide.Word) (q : MStarCopierMicrocode.CopierState)
    (z : MStarParserExecution.Zipper OuterTape)
    (h : SideCopierCanonical x (.running q z)) : z.focus ≠ .hash := by
  intro hhash
  have hnext := h.oneStep x
  rw [show z = ⟨z.leftRev, .hash, z.right⟩ by
    apply MStarParserExecution.Zipper.ext <;> simp [hhash],
    copierOneStep_hash_rejected] at hnext
  exact sideCopierCanFinish_ne_rejected hnext.2

theorem SideCopierCanonical.groupReady_focus_work
    (x : ConcretePakSide.Word) (z : MStarParserExecution.Zipper OuterTape)
    (h : SideCopierCanonical x (.groupReady z)) :
    z.focus = .core MStarConcreteAlphabet.work := by
  rcases (PakSideScanner.side_parser_then_copier x).2.2 with
    ⟨z₀, hz₀, hsegment⟩
  rcases h.1 with ⟨fuel, hz⟩
  rcases hz₀ with ⟨fuel₀, hz₀⟩
  have heq := MStarCopierExecution.groupReady_output_unique
    (.running .seedCell (PakSideScanner.sideCopierSeedZipper x))
    fuel fuel₀ z z₀ hz hz₀
  subst z₀
  have hfocus := congrArg (fun xs : List OuterTape => xs.getD 1 .hash) hsegment
  simpa [MStarParserCopySpec.copiedWorkspace,
    MStarParserCopySpec.workspaceRadius, List.replicate_succ] using hfocus

/-- A canonical `groupReady` endpoint carries the unique marked workspace
produced by the concrete copier, including the untouched scanner hash tail.
This is stronger than the focus-cell fact above and is the exact suffix
interface consumed by the subsequent `U_log` bootstrap. -/
theorem SideCopierCanonical.groupReady_markedWorkspace
    (x : ConcretePakSide.Word) (z : MStarParserExecution.Zipper OuterTape)
    (h : SideCopierCanonical x (.groupReady z)) :
    .markL :: z.focus :: z.right =
      MStarParserCopySpec.copiedWorkspace
          MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
          MStarConcreteAlphabet.work x ++
        PakSideScanner.sideCopierHashTail x := by
  rcases (PakSideScanner.side_parser_then_copier x).2.2 with
    ⟨z₀, hz₀, hsegment⟩
  rcases h.1 with ⟨fuel, hz⟩
  rcases hz₀ with ⟨fuel₀, hz₀⟩
  have heq := MStarCopierExecution.groupReady_output_unique
    (.running .seedCell (PakSideScanner.sideCopierSeedZipper x))
    fuel fuel₀ z z₀ hz hz₀
  simpa [heq] using hsegment

/-- Every step on the canonical copier execution has a literal occupied outer
arrow; malformed reject/stuck branches are excluded by the genuine future
`groupReady` witness. -/
def CopierOuterStepSimulationAtMostOne
    (realize : MStarCopierExecution.Result → OuterConfig → Prop) : Prop :=
  ∀ r s c, realize r c → MStarCopierExecution.oneStep r = s →
    ∃ d, realize s d ∧
      ∃ arrows : List OuterArrow, arrows.length ≤ 1 ∧
        FiniteOneTapeSemantics.run MStarULogAssembly.program
          MStarOuterProgram.movable arrows c = some d

theorem canonicalSideCopier_outerStepSimulation_atMostOne
    (x : ConcretePakSide.Word) :
    CopierOuterStepSimulationAtMostOne (CanonicalSideCopierRealize x) := by
  intro r s c hrealize hrun
  rcases hrealize with ⟨hcanonical, hside⟩
  cases r with
  | rejected => exact (sideCopierCanFinish_ne_rejected hcanonical.2).elim
  | stuck => exact (sideCopierCanFinish_ne_stuck hcanonical.2).elim
  | groupReady z =>
      simp only [MStarCopierExecution.oneStep] at hrun
      subst s
      exact ⟨c, ⟨hcanonical, hside⟩, ⟨[], by simp, rfl⟩⟩
  | running q z =>
      cases htable : MStarCopierMicrocode.copierStep (UState := Unit) () q
          z.focus with
      | none =>
          have hbad : SideCopierCanonical x .stuck := by
            simpa [MStarCopierExecution.oneStep, htable] using
              (hcanonical.oneStep x)
          exact (sideCopierCanFinish_ne_stuck hbad.2).elim
      | some a =>
          cases happly : MStarParserExecution.applyAction z a with
          | none =>
              have hbad : SideCopierCanonical x .stuck := by
                simpa [MStarCopierExecution.oneStep, htable, happly] using
                  (hcanonical.oneStep x)
              exact (sideCopierCanFinish_ne_stuck hbad.2).elim
          | some z' =>
              cases htarget : a.target with
              | start | accept =>
                  have hbad : SideCopierCanonical x .stuck := by
                    simpa [MStarCopierExecution.oneStep, htable, happly,
                      htarget] using (hcanonical.oneStep x)
                  exact (sideCopierCanFinish_ne_stuck hbad.2).elim
              | reject =>
                  have hbad : SideCopierCanonical x .rejected := by
                    simpa [MStarCopierExecution.oneStep, htable, happly,
                      htarget] using (hcanonical.oneStep x)
                  exact (sideCopierCanFinish_ne_rejected hbad.2).elim
              | parser p =>
                  cases p with
                  | inl p =>
                      have hbad : SideCopierCanonical x .stuck := by
                        simpa [MStarCopierExecution.oneStep, htable, happly,
                          htarget] using (hcanonical.oneStep x)
                      exact (sideCopierCanFinish_ne_stuck hbad.2).elim
                  | inr q' =>
                      have hs : s = .running q' z' := by
                        simpa [MStarCopierExecution.oneStep, htable, happly,
                          htarget] using hrun.symm
                      have hnext : SideCopierCanonical x (.running q' z') := by
                        simpa [MStarCopierExecution.oneStep, htable, happly,
                          htarget] using (hcanonical.oneStep x)
                      rcases hside with ⟨origin, rfl⟩
                      have hfocus := hnext.running_focus_ne_hash x q' z'
                      have hmovable : MStarOuterProgram.movable
                          (anchoredZipperTape origin z'
                            (origin + z'.leftRev.length)) = true := by
                        rw [anchoredZipperTape_at_head]
                        cases hz : z'.focus with
                        | hash => exact (hfocus hz).elim
                        | core a | markL | markR | scratch a => rfl
                      rcases sideCopierRealize_outerRunningStep_atMostOne q q' origin z z'
                          a htable happly htarget hmovable with ⟨d, hd, hout⟩
                      refine ⟨d, ?_, hout⟩
                      rw [hs]
                      exact ⟨hnext, hd⟩
              | sim u =>
                  have hs : s = .groupReady z' := by
                    simpa [MStarCopierExecution.oneStep, htable, happly,
                      htarget] using hrun.symm
                  have hnext : SideCopierCanonical x (.groupReady z') := by
                    simpa [MStarCopierExecution.oneStep, htable, happly,
                      htarget] using (hcanonical.oneStep x)
                  rcases hside with ⟨origin, rfl⟩
                  have hfocus := hnext.groupReady_focus_work x z'
                  have hmovable : MStarOuterProgram.movable
                      (anchoredZipperTape origin z'
                        (origin + z'.leftRev.length)) = true := by
                    rw [anchoredZipperTape_at_head, hfocus]
                    rfl
                  rcases sideCopierRealize_outerGroupReadyStep_atMostOne q origin z z'
                      a htable happly ⟨u, htarget⟩ hmovable with ⟨d, hd, hout⟩
                  refine ⟨d, ?_, hout⟩
                  rw [hs]
                  exact ⟨hnext, hd⟩

theorem canonicalSideCopier_outerStepSimulation (x : ConcretePakSide.Word) :
    CopierOuterStepSimulation (CanonicalSideCopierRealize x) := by
  intro r s c hrealize hrun
  rcases canonicalSideCopier_outerStepSimulation_atMostOne x r s c hrealize
      hrun with ⟨d, hd, arrows, _, harrows⟩
  exact ⟨d, hd, ⟨arrows, harrows⟩⟩

/-- The parameter-free parser endpoint crosses its one physical entry arrow
into the canonical finite copier execution. -/
theorem sideCopyReady_enters_canonicalCopier_atMostOne
    (x : ConcretePakSide.Word) (c : OuterConfig)
    (hready : CanonicalSideParserRealize x
      (.copyReady (MStarParserExecution.extendRight
        (MStarConcreteAlphabet.finalZipper x.reverse)
        (MStarCopierExecution.parserCopierReserve x ++
          PakSideScanner.sideCopierHashTail x))) c) :
    ∃ d, CanonicalSideCopierRealize x
        (.running .seedCell (PakSideScanner.sideCopierSeedZipper x)) d ∧
      ∃ arrows : List OuterArrow, arrows.length ≤ 1 ∧
        FiniteOneTapeSemantics.run MStarULogAssembly.program
          MStarOuterProgram.movable arrows c = some d := by
  let z := MStarParserExecution.extendRight
    (MStarConcreteAlphabet.finalZipper x.reverse)
    (MStarCopierExecution.parserCopierReserve x ++
      PakSideScanner.sideCopierHashTail x)
  let seed := PakSideScanner.sideCopierSeedZipper x
  rcases hready.2 with ⟨origin, rfl⟩
  have happly : MStarParserExecution.applyAction z sideCopyEntryAction =
      some seed := by
    have hunit := (PakSideScanner.side_parser_then_copier x).2.1
    change MStarParserExecution.applyAction z
        (MStarCopierMicrocode.copyGo (UState := MStarULogAssembly.UniversalState)
          .markL .seedCell .right) = some seed
    rw [show MStarParserExecution.applyAction z
          (MStarCopierMicrocode.copyGo (UState := MStarULogAssembly.UniversalState)
            .markL .seedCell .right) =
        MStarParserExecution.applyAction z
          (MStarCopierMicrocode.copyGo (UState := Unit)
            .markL .seedCell .right) by rfl]
    simpa [z, seed] using hunit
  let c₀ := anchoredParserConfig MStarParserMicrocode.copyStart origin z
  let d := anchoredCopierConfig MStarCopierMicrocode.CopierState.seedCell
    origin seed
  have hafter : afterAction c₀ sideCopyEntryAction = d := by
    simp only [c₀, d, afterAction, anchoredParserConfig,
      anchoredCopierConfig, writtenTape]
    rw [anchoredZipperHead_applyAction origin z seed sideCopyEntryAction happly,
      anchoredZipperTape_applyAction origin z seed sideCopyEntryAction happly]
    rfl
  have htape : writtenTape c₀ sideCopyEntryAction.write =
      anchoredZipperTape origin seed := by
    simpa only [c₀, anchoredParserConfig, writtenTape] using
      (anchoredZipperTape_applyAction origin z seed sideCopyEntryAction happly).symm
  have hmove : MStarOuterProgram.movable
      ((writtenTape c₀ sideCopyEntryAction.write)
        (moveHead sideCopyEntryAction.move c₀.head)) = true := by
    change MStarOuterProgram.movable
      ((writtenTape c₀ sideCopyEntryAction.write)
        (moveHead sideCopyEntryAction.move (origin + z.leftRev.length))) = true
    rw [htape, ← anchoredZipperHead_applyAction origin z seed
      sideCopyEntryAction happly, anchoredZipperTape_at_head]
    rfl
  refine ⟨d, ⟨sideCopierCanonical_seed x, ⟨origin, rfl⟩⟩, ?_⟩
  rw [← hafter]
  refine ⟨[sideCopyEntryArrow], by simp, ?_⟩
  simp only [FiniteOneTapeSemantics.run_cons]
  rw [sideCopyEntry_outerStep c₀
    (by simp [c₀, anchoredParserConfig])
    (by
      rw [show c₀.tape c₀.head = z.focus by
        simpa [c₀, anchoredParserConfig] using anchoredZipperTape_at_head origin z]
      simp [z, MStarParserExecution.extendRight,
        MStarConcreteAlphabet.finalZipper])
    hmove]
  rfl

theorem sideCopyReady_enters_canonicalCopier
    (x : ConcretePakSide.Word) (c : OuterConfig)
    (hready : CanonicalSideParserRealize x
      (.copyReady (MStarParserExecution.extendRight
        (MStarConcreteAlphabet.finalZipper x.reverse)
        (MStarCopierExecution.parserCopierReserve x ++
          PakSideScanner.sideCopierHashTail x))) c) :
    ∃ d, CanonicalSideCopierRealize x
        (.running .seedCell (PakSideScanner.sideCopierSeedZipper x)) d ∧
      OuterReaches c d := by
  rcases sideCopyReady_enters_canonicalCopier_atMostOne x c hready with
    ⟨d, hd, arrows, _, harrows⟩
  exact ⟨d, hd, ⟨arrows, harrows⟩⟩

/-- The full concrete copier reachability witness lifts to a literal outer
arrow list with no ambient simulation parameter. -/
theorem sideCopier_reaches_outerGroupReady_arrowList
    (x : ConcretePakSide.Word) (c : OuterConfig)
    (hseed : CanonicalSideCopierRealize x
      (.running .seedCell (PakSideScanner.sideCopierSeedZipper x)) c) :
    ∃ d arrows z,
      CanonicalSideCopierRealize x (.groupReady z) d ∧
      FiniteOneTapeSemantics.run MStarULogAssembly.program
        MStarOuterProgram.movable arrows c = some d := by
  rcases (PakSideScanner.side_parser_then_copier x).2.2 with
    ⟨z, hreach, _⟩
  rcases copierReaches_outerArrowList (CanonicalSideCopierRealize x)
      (canonicalSideCopier_outerStepSimulation x) hreach hseed with
    ⟨d, arrows, hd, hrun⟩
  exact ⟨d, arrows, z, hd, hrun⟩

/-- Parser execution, the physical copier-entry edge, and the complete copier
execution concatenate to one literal outer arrow list. -/
theorem sideParserCopier_reaches_outerGroupReady_arrowList
    (x : ConcretePakSide.Word) :
    ∃ d arrows z,
      CanonicalSideCopierRealize x (.groupReady z) d ∧
      FiniteOneTapeSemantics.run MStarULogAssembly.program
        MStarOuterProgram.movable arrows
        (PakSideScannerRow.sideEncodedParserConfig x) = some d := by
  rcases sideParser_reaches_outerCopyReady_arrowList x with
    ⟨parserEnd, parserArrows, hready, hparser⟩
  rcases sideCopyReady_enters_canonicalCopier x parserEnd hready with
    ⟨seedEnd, hseed, hentry⟩
  rcases hentry with ⟨entryArrows, hentry⟩
  rcases sideCopier_reaches_outerGroupReady_arrowList x seedEnd hseed with
    ⟨finish, copierArrows, z, hfinish, hcopier⟩
  refine ⟨finish, parserArrows ++ entryArrows ++ copierArrows, z, hfinish, ?_⟩
  rw [outerRun_append (parserArrows ++ entryArrows) copierArrows,
    outerRun_append parserArrows entryArrows, hparser]
  simp only [Option.bind_some]
  rw [hentry]
  simp only [Option.bind_some]
  exact hcopier

/-- Including the scanner-derived slot-one start edge yields the complete
outer bootstrap prefix through `groupReady`. -/
theorem sideStartParserCopier_reaches_outerGroupReady_arrowList
    (x : ConcretePakSide.Word) :
    ∃ d arrows z,
      CanonicalSideCopierRealize x (.groupReady z) d ∧
      FiniteOneTapeSemantics.run MStarULogAssembly.program
        MStarOuterProgram.movable arrows
        (PakSideScannerRow.sideEncodedStartConfig x) = some d := by
  rcases sideParserCopier_reaches_outerGroupReady_arrowList x with
    ⟨finish, arrows, z, hfinish, hrun⟩
  refine ⟨finish, [PakEncodedStart.startOneArrow] ++ arrows, z, hfinish, ?_⟩
  rw [outerRun_append]
  simp only [FiniteOneTapeSemantics.run_cons, FiniteOneTapeSemantics.run_nil]
  rw [PakSideScannerRow.sideEncodedStart_slotOne_step]
  exact hrun

/-- The same front-end path with its three operational stages retained.  This
is the quantitative interface used by the square-time bound: no stage length
has been hidden by concatenating into an unlabelled reachability witness. -/
structure SideStartParserCopierStages (x : ConcretePakSide.Word) where
  parserEnd : OuterConfig
  seedEnd : OuterConfig
  finish : OuterConfig
  groupZipper : MStarParserExecution.Zipper OuterTape
  startArrow : OuterArrow
  startArrow_eq : startArrow = PakEncodedStart.startOneArrow
  parserArrows : List OuterArrow
  entryArrows : List OuterArrow
  copierArrows : List OuterArrow
  start_step : FiniteOneTapeSemantics.step MStarULogAssembly.program
    MStarOuterProgram.movable (PakSideScannerRow.sideEncodedStartConfig x)
      startArrow = some (PakSideScannerRow.sideEncodedParserConfig x)
  parser_run : FiniteOneTapeSemantics.run MStarULogAssembly.program
    MStarOuterProgram.movable parserArrows
      (PakSideScannerRow.sideEncodedParserConfig x) = some parserEnd
  parser_ready : CanonicalSideParserRealize x
    (.copyReady (MStarParserExecution.extendRight
      (MStarConcreteAlphabet.finalZipper x.reverse)
      (MStarCopierExecution.parserCopierReserve x ++
        PakSideScanner.sideCopierHashTail x))) parserEnd
  entry_run : FiniteOneTapeSemantics.run MStarULogAssembly.program
    MStarOuterProgram.movable entryArrows parserEnd = some seedEnd
  seed_ready : CanonicalSideCopierRealize x
    (.running .seedCell (PakSideScanner.sideCopierSeedZipper x)) seedEnd
  copier_run : FiniteOneTapeSemantics.run MStarULogAssembly.program
    MStarOuterProgram.movable copierArrows seedEnd = some finish
  finish_ready : CanonicalSideCopierRealize x (.groupReady groupZipper) finish

theorem sideStartParserCopier_stages (x : ConcretePakSide.Word) :
    Nonempty (SideStartParserCopierStages x) := by
  rcases sideParser_reaches_outerCopyReady_arrowList x with
    ⟨parserEnd, parserArrows, hready, hparser⟩
  rcases sideCopyReady_enters_canonicalCopier x parserEnd hready with
    ⟨seedEnd, hseed, hentry⟩
  rcases hentry with ⟨entryArrows, hentry⟩
  rcases sideCopier_reaches_outerGroupReady_arrowList x seedEnd hseed with
    ⟨finish, copierArrows, z, hfinish, hcopier⟩
  exact ⟨
    { parserEnd := parserEnd
      seedEnd := seedEnd
      finish := finish
      groupZipper := z
      startArrow := PakEncodedStart.startOneArrow
      startArrow_eq := rfl
      parserArrows := parserArrows
      entryArrows := entryArrows
      copierArrows := copierArrows
      start_step := PakSideScannerRow.sideEncodedStart_slotOne_step x
      parser_run := hparser
      parser_ready := hready
      entry_run := hentry
      seed_ready := hseed
      copier_run := hcopier
      finish_ready := hfinish }⟩

end PakFixedPolyomino.PakParserOuterBridge
