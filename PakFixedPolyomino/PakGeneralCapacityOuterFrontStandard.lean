import PakFixedPolyomino.PakGeneralCapacityParserCopierFront
import PakFixedPolyomino.PakParserKernelNoncoreRejection
import PakFixedPolyomino.PakParserOuterBridge
import PakFixedPolyomino.PakCopierOuterBridge
import PakFixedPolyomino.PakULogGeneralCapacityBootstrap

/-!
# Kernel-only literal outer parser/copier front at arbitrary scanner capacity

This preserves the literal definitions and proof structure of the frozen
`PakGeneralCapacityOuterFront` source (SHA bf3cc2dc4d41c6da82e4ceff555e80d6bda9e6d8083eae203a978117c7fad254),
while replacing its six inherited compiler-trust leaves. It is the parser
half of the capacity-indexed outer reflection.  It keeps
the *actual* finite work reserve emitted by the scanner, rather than silently
replacing it by the canonical reserve used by the old slot-one front.

The copier half intentionally lives elsewhere: this file ends at the literal
outer `copyReady` configuration and preserves the finite pairing pad and the
hash exterior needed by the later entry proof.
-/

namespace PakFixedPolyomino.PakGeneralCapacityOuterFrontStandard

open FiniteOneTapeProgram FiniteOneTapeSemantics
open MStarConcreteAlphabet MStarOuterProgram MStarParserExecution
open MStarCopierMicrocode
open PakGeneralCapacityInitialWindow
open PakGeneralCapacityParserCopierFront
open PakParserOuterBridge
open PakSlotOneScannerMultiplicity
open PakULogGeneralCapacityBootstrap

abbrev OuterTape := MStarOuterProgram.Tape MStarULogAssembly.CoreTape
abbrev OuterConfig := PakParserOuterBridge.OuterConfig
abbrev OuterArrow := PakParserOuterBridge.OuterArrow
abbrev Result := MStarParserExecution.Result MStarULogAssembly.CoreTape

/-- Parser-path membership from the literal capacity-specific input row. -/
def CapacityParserCanonical (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (r : Result) : Prop :=
  MStarParserExecution.Reaches zero one work (capacityParserInitialResult x c) r

/-- The common-state parser/outer relation at a scanner-emitted capacity. -/
def CapacitySideParserRealize (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (r : Result) (q : OuterConfig) : Prop :=
  CapacityParserCanonical x c r ∧ sideParserRealize x r q

theorem capacityParserInitialResult_shape (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) :
    ∃ z : MStarParserExecution.Zipper OuterTape,
      capacityParserInitialResult x c =
        .running (MStarParserMicrocode.fixed ⟨0, by decide⟩) z ∧
      z.leftRev = [] ∧
      anchoredZipperCells z = capacityInitialCells x c := by
  cases hcells : MStarParserExecution.inputCells zero one work
      (ConcretePakSide.encodedWord x) with
  | nil =>
      exact (MStarParserExecution.inputCells_ne_nil zero one work
        (ConcretePakSide.encodedWord x) hcells).elim
  | cons focus right =>
      let z : MStarParserExecution.Zipper OuterTape :=
        ⟨[], focus, right ++ capacityParserTail x c⟩
      refine ⟨z, ?_, by simp [z], ?_⟩
      · simp [capacityParserInitialResult, MStarParserExecution.initial, hcells,
          MStarParserExecution.extendResultRight, MStarParserExecution.extendRight, z]
      · unfold anchoredZipperCells z
        change (focus :: right) ++ capacityParserTail x c = capacityInitialCells x c
        rw [← hcells]
        exact (capacityInitialCells_eq_parserInput_append_tail x c).symm

theorem anchoredZipperTape_eq_capacityInitialTape_of_cells
    (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (z : MStarParserExecution.Zipper OuterTape)
    (hcells : anchoredZipperCells z = capacityInitialCells x c) :
    anchoredZipperTape 1 z = capacityInitialTape x c := by
  funext i
  unfold anchoredZipperTape capacityInitialTape
  by_cases hi : (1 : Int) ≤ i
  · rw [if_pos hi, if_pos hi, hcells]
  · rw [if_neg hi, if_neg hi]

theorem capacitySideParserRealize_initial (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) :
    CapacitySideParserRealize x c (capacityParserInitialResult x c)
      (capacityEncodedParserConfig x c) := by
  rcases capacityParserInitialResult_shape x c with ⟨z, hz, hzleft, hcells⟩
  constructor
  · exact MStarParserExecution.reaches_refl zero one work _
  · rw [hz]
    refine ⟨1, ?_⟩
    change
      { state := .parser MStarULogAssembly.data.parserStart
        head := 1
        tape := capacityInitialTape x c } =
      anchoredParserConfig (MStarParserMicrocode.fixed ⟨0, by decide⟩) 1 z
    simp only [anchoredParserConfig]
    rw [hzleft]
    have hstate : MStarULogAssembly.data.parserStart =
        .inl (MStarParserMicrocode.fixed ⟨0, by decide⟩) := rfl
    have htape : capacityInitialTape x c = anchoredZipperTape 1 z :=
      (anchoredZipperTape_eq_capacityInitialTape_of_cells x c z hcells).symm
    rw [hstate]
    simp only [List.length_nil, Nat.cast_zero, Int.reduceAdd]
    rw [htape]

theorem capacityParserCanonical_canAccept (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) {r : Result}
    (hr : CapacityParserCanonical x c r) :
    MStarParserSoundness.CanAcceptResult r := by
  apply MStarParserSoundness.canAcceptResult_reaches_forward hr
  apply MStarParserSoundness.canAcceptResult_of_reaches
    (reaches_capacityParser_copyReady x c)
  exact MStarParserSoundness.canAcceptResult_copyReady _

theorem capacityParserCanonical_oneStep (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) (r : Result)
    (hr : CapacityParserCanonical x c r) :
    CapacityParserCanonical x c (MStarParserExecution.oneStep zero one work r) :=
  MStarParserExecution.reaches_trans zero one work hr
    (MStarParserExecution.reaches_of_oneStep zero one work rfl)

theorem capacityParserCanonical_ne_rejected (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) {r : Result}
    (hr : CapacityParserCanonical x c r) : r ≠ .rejected := by
  intro h
  subst r
  exact MStarParserSoundness.not_canAcceptResult_rejected
    (capacityParserCanonical_canAccept x c hr)

theorem capacityParserCanonical_ne_stuck (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) {r : Result}
    (hr : CapacityParserCanonical x c r) : r ≠ .stuck := by
  intro h
  subst r
  exact MStarParserSoundness.not_canAcceptResult_stuck
    (capacityParserCanonical_canAccept x c hr)

theorem capacityParserCanonical_fixed_zero_and_right
    (x : ConcretePakSide.Word) (c : ScannerCapacity x) (k : Fin 73) (hk : k.1 < 72)
    (z : MStarParserExecution.Zipper OuterTape)
    (hr : CapacityParserCanonical x c (.running (MStarParserMicrocode.fixed k) z)) :
    z.focus = .core zero ∧ z.right ≠ [] :=
  MStarParserSoundness.fixed_canAccept_forces_zero_and_right k hk z
    (capacityParserCanonical_canAccept x c hr)

theorem capacityParserCanonical_cross_zero_and_left
    (x : ConcretePakSide.Word) (c : ScannerCapacity x) (k : Fin 73) (hk : k.1 < 72)
    (z : MStarParserExecution.Zipper OuterTape)
    (hr : CapacityParserCanonical x c (.running (MStarParserMicrocode.cross k) z)) :
    z.focus = .core zero ∧ z.leftRev ≠ [] :=
  MStarParserSoundness.cross_canAccept_forces_zero_and_left k hk z
    (capacityParserCanonical_canAccept x c hr)

theorem capacityParserCanonical_scanPad_core
    (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (z : MStarParserExecution.Zipper OuterTape)
    (hr : CapacityParserCanonical x c (.running MStarParserMicrocode.scanPad z)) :
    ∃ a : MStarULogAssembly.CoreTape, z.focus = .core a := by
  exact PakParserKernelNoncoreRejection.scanPad_accepting_core
    z.leftRev z.right z.focus (capacityParserCanonical_canAccept x c hr)

theorem capacityParserCanonical_scanLen_core
    (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (z : MStarParserExecution.Zipper OuterTape)
    (hr : CapacityParserCanonical x c (.running MStarParserMicrocode.scanLen z)) :
    ∃ a : MStarULogAssembly.CoreTape, z.focus = .core a := by
  exact PakParserKernelNoncoreRejection.scanLen_accepting_core
    z.leftRev z.right z.focus (capacityParserCanonical_canAccept x c hr)

private theorem capacity_parserStep_control_hash_rejected_all :
    ∀ q : Fin 18, q ≠ (⟨5, by decide⟩ : Fin 18) →
      q ≠ (⟨17, by decide⟩ : Fin 18) →
      MStarParserMicrocode.step (UState := Unit) zero one work
        (MStarParserMicrocode.control q) .hash =
          some (MStarParserMicrocode.reject .hash) := by
  decide

private theorem capacity_anchoredZipper_movable_of_focus_ne_hash
    (origin : Int) (z : MStarParserExecution.Zipper OuterTape)
    (hfocus : z.focus ≠ .hash) :
    MStarOuterProgram.movable
      (anchoredZipperTape origin z (origin + z.leftRev.length)) = true := by
  rw [anchoredZipperTape_at_head]
  cases hz : z.focus with
  | core a => rfl
  | hash => exact (hfocus hz).elim
  | markL => rfl
  | markR => rfl
  | scratch i => rfl

private theorem capacity_anchoredZipper_movable_of_focus_work
    (origin : Int) (z : MStarParserExecution.Zipper OuterTape)
    (hfocus : z.focus = .core work) :
    MStarOuterProgram.movable
      (anchoredZipperTape origin z (origin + z.leftRev.length)) = true := by
  rw [anchoredZipperTape_at_head, hfocus]
  rfl

/-- Apart from the abstract `copyStart` terminal, a capacity-specific
accepting parser state cannot expose the ambient hash sentinel at its focus. -/
theorem capacityParserCanonical_noncopy_focus_ne_hash
    (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (p : MStarParserMicrocode.ParserState)
    (z : MStarParserExecution.Zipper OuterTape)
    (hp : p ≠ MStarParserMicrocode.copyStart)
    (hr : CapacityParserCanonical x c (.running p z)) : z.focus ≠ .hash := by
  intro hhash
  cases p with
  | inl counters =>
      cases counters with
      | inl k =>
          by_cases hk : k.1 < 72
          · have hzero := capacityParserCanonical_fixed_zero_and_right x c k hk z hr
            exact (by simpa [hhash] using hzero.1)
          · have hkval : k.1 = 72 := by omega
            have hk72 : k = (⟨72, by decide⟩ : Fin 73) := Fin.ext hkval
            subst k
            have hnext := (MStarParserSoundness.canAcceptResult_oneStep_iff
              (.running (MStarParserMicrocode.fixed ⟨72, by decide⟩) z)).2
                (capacityParserCanonical_canAccept x c hr)
            rw [show z = ⟨z.leftRev, .hash, z.right⟩ by
              apply MStarParserExecution.Zipper.ext <;> simp [hhash],
              MStarConcreteAlphabet.oneStep_fixed_72] at hnext
            have hafter := (MStarParserSoundness.canAcceptResult_oneStep_iff
              (.running MStarParserMicrocode.scanPad
                ⟨z.leftRev, .hash, z.right⟩)).2 hnext
            rw [PakParserKernelNoncoreRejection.scanPad_noncore_rejected _ _ .hash
              (by simp)] at hafter
            exact MStarParserSoundness.not_canAcceptResult_rejected hafter
      | inr k =>
          by_cases hk : k.1 < 72
          · have hzero := capacityParserCanonical_cross_zero_and_left x c k hk z hr
            exact (by simpa [hhash] using hzero.1)
          · have hkval : k.1 = 72 := by omega
            have hk72 : k = (⟨72, by decide⟩ : Fin 73) := Fin.ext hkval
            subst k
            have hnext := (MStarParserSoundness.canAcceptResult_oneStep_iff
              (.running (MStarParserMicrocode.cross ⟨72, by decide⟩) z)).2
                (capacityParserCanonical_canAccept x c hr)
            rw [show z = ⟨z.leftRev, .hash, z.right⟩ by
              apply MStarParserExecution.Zipper.ext <;> simp [hhash]] at hnext
            have hcross72 : MStarParserExecution.oneStep zero one work
                (.running (MStarParserMicrocode.cross ⟨72, by decide⟩)
                  ⟨z.leftRev, .hash, z.right⟩) =
                .running MStarParserMicrocode.returnSepPad
                  ⟨z.leftRev, .hash, z.right⟩ := by
              rfl
            rw [hcross72] at hnext
            have hreject : MStarParserExecution.oneStep zero one work
                (.running MStarParserMicrocode.returnSepPad
                  ⟨z.leftRev, .hash, z.right⟩) = .rejected := by
              rfl
            have hafter := (MStarParserSoundness.canAcceptResult_oneStep_iff
              (.running MStarParserMicrocode.returnSepPad
                ⟨z.leftRev, .hash, z.right⟩)).2 hnext
            rw [hreject] at hafter
            exact MStarParserSoundness.not_canAcceptResult_rejected hafter
  | inr phase =>
      have hnext := (MStarParserSoundness.canAcceptResult_oneStep_iff
        (.running (MStarParserMicrocode.control phase) z)).2
          (capacityParserCanonical_canAccept x c hr)
      rw [show z = ⟨z.leftRev, .hash, z.right⟩ by
        apply MStarParserExecution.Zipper.ext <;> simp [hhash]] at hnext
      have hphase : phase ≠ (⟨17, by decide⟩ : Fin 18) := by
        intro h17
        apply hp
        simpa [MStarParserMicrocode.copyStart,
          MStarParserMicrocode.control, h17]
      by_cases h5 : phase = (⟨5, by decide⟩ : Fin 18)
      · subst phase
        change MStarParserSoundness.CanAcceptResult
          (.running MStarParserMicrocode.scanLen
            ⟨z.leftRev, .hash, z.right⟩) at hnext
        have hafter := (MStarParserSoundness.canAcceptResult_oneStep_iff
          (.running MStarParserMicrocode.scanLen
            ⟨z.leftRev, .hash, z.right⟩)).2 hnext
        rw [PakParserKernelNoncoreRejection.scanLen_noncore_rejected _ _ .hash
          (by simp)] at hafter
        exact MStarParserSoundness.not_canAcceptResult_rejected hafter
      · have hstep : MStarParserExecution.oneStep zero one work
            (.running (MStarParserMicrocode.control phase)
              ⟨z.leftRev, .hash, z.right⟩) = .rejected := by
            unfold MStarParserExecution.oneStep
            change (if MStarParserMicrocode.control phase =
                MStarParserMicrocode.copyStart then _ else _) = _
            rw [if_neg (by
              intro h
              apply hphase
              simpa [MStarParserMicrocode.control,
                MStarParserMicrocode.copyStart] using h)]
            rw [capacity_parserStep_control_hash_rejected_all phase h5 hphase]
            rfl
        rw [hstep] at hnext
        exact MStarParserSoundness.not_canAcceptResult_rejected hnext

/-- Every successful parser microstep at a literal scanner capacity is either
the zero-arrow `copyStart` identification or one real occupied outer arrow.
The proof is deliberately the same-state proof: the realizing configuration
is carried through each action rather than reconstructed from another run. -/
theorem capacitySideParser_outerStepSimulation_atMostOne
    (x : ConcretePakSide.Word) (cap : ScannerCapacity x) :
    ParserOuterStepSimulationAtMostOne zero one work
      (CapacitySideParserRealize x cap) := by
  intro r s outer hrealize hrun
  rcases hrealize with ⟨hr, hside⟩
  cases r with
  | rejected =>
      exact (capacityParserCanonical_ne_rejected x cap hr rfl).elim
  | stuck =>
      exact (capacityParserCanonical_ne_stuck x cap hr rfl).elim
  | copyReady z =>
      simp only [MStarParserExecution.oneStep] at hrun
      subst s
      exact ⟨outer,
        ⟨capacityParserCanonical_oneStep x cap (.copyReady z) hr, hside⟩,
        ⟨[], by simp, rfl⟩⟩
  | running p z =>
      by_cases hp : p = MStarParserMicrocode.copyStart
      · subst p
        simp only [MStarParserExecution.oneStep, ↓reduceIte] at hrun
        subst s
        rcases hside with ⟨origin, rfl⟩
        refine ⟨anchoredParserConfig MStarParserMicrocode.copyStart origin z,
          ⟨?_, sideParserRealize_copyReady x origin z⟩,
          ⟨[], by simp, rfl⟩⟩
        simpa [MStarParserExecution.oneStep] using
          (capacityParserCanonical_oneStep x cap
            (.running MStarParserMicrocode.copyStart z) hr)
      · cases htable : MStarParserMicrocode.step (UState := Unit)
          zero one work p z.focus with
        | none =>
            have hbad : CapacityParserCanonical x cap .stuck := by
              simpa [MStarParserExecution.oneStep, hp, htable] using
                (capacityParserCanonical_oneStep x cap (.running p z) hr)
            exact (capacityParserCanonical_ne_stuck x cap hbad rfl).elim
        | some a =>
            cases happly : MStarParserExecution.applyAction z a with
            | none =>
                have hbad : CapacityParserCanonical x cap .stuck := by
                  simpa [MStarParserExecution.oneStep, hp, htable, happly] using
                    (capacityParserCanonical_oneStep x cap (.running p z) hr)
                exact (capacityParserCanonical_ne_stuck x cap hbad rfl).elim
            | some z' =>
                rcases a with ⟨write, target, move⟩
                cases target with
                | start | accept | sim _ =>
                    have hbad : CapacityParserCanonical x cap .stuck := by
                      simpa [MStarParserExecution.oneStep, hp, htable, happly] using
                        (capacityParserCanonical_oneStep x cap (.running p z) hr)
                    exact (capacityParserCanonical_ne_stuck x cap hbad rfl).elim
                | reject =>
                    have hbad : CapacityParserCanonical x cap .rejected := by
                      simpa [MStarParserExecution.oneStep, hp, htable, happly] using
                        (capacityParserCanonical_oneStep x cap (.running p z) hr)
                    exact (capacityParserCanonical_ne_rejected x cap hbad rfl).elim
                | parser p' =>
                    have hs : s = .running p' z' := by
                      simpa [MStarParserExecution.oneStep, hp, htable, happly] using
                        hrun.symm
                    have hnext : CapacityParserCanonical x cap (.running p' z') := by
                      simpa [MStarParserExecution.oneStep, hp, htable, happly] using
                        (capacityParserCanonical_oneStep x cap (.running p z) hr)
                    have houter := PakParserKernelTableFacts.unit_action_to_outer_action p z.focus
                      { write := write, target := .parser p', move := move } hp htable
                    have happlyOuter : MStarParserExecution.applyAction z
                        (liftUnitParserAction MStarULogAssembly.data.uStart
                          { write := write, target := .parser p', move := move }) =
                        some z' := by
                      rw [applyAction_liftUnitParserAction]
                      exact happly
                    have houterTarget :
                        (liftUnitParserAction MStarULogAssembly.data.uStart
                          { write := write, target := .parser p', move := move }).target =
                          .parser (.inl p') := by
                      simp [liftUnitParserAction, liftUnitParserState]
                    rcases hside with ⟨origin, rfl⟩
                    by_cases hp' : p' = MStarParserMicrocode.copyStart
                    · subst p'
                      rcases PakParserKernelTableFacts.target_copyStart_stays_work p z.focus
                          { write := write,
                            target := .parser MStarParserMicrocode.copyStart,
                            move := move }
                          htable rfl with ⟨hstay, hwrite⟩
                      have hfocus : z'.focus = .core work := by
                        change move = .stay at hstay
                        change write = .core work at hwrite
                        subst move
                        subst write
                        have hsome : some { z with focus := (.core work : OuterTape) } =
                            some z' := by
                          simpa [MStarParserExecution.applyAction] using happly
                        exact (congrArg MStarParserExecution.Zipper.focus
                          (Option.some.inj hsome)).symm
                      have hmovable := capacity_anchoredZipper_movable_of_focus_work
                        origin z' hfocus
                      rcases sideParserRealize_outerRunningStep_atMostOne x p
                          MStarParserMicrocode.copyStart origin z z'
                          (liftUnitParserAction MStarULogAssembly.data.uStart
                            { write := write,
                              target := .parser MStarParserMicrocode.copyStart,
                              move := move })
                          houter happlyOuter houterTarget hmovable with ⟨d, hd, hout⟩
                      refine ⟨d, ?_, hout⟩
                      rw [hs]
                      exact ⟨hnext, hd⟩
                    · have hfocus := capacityParserCanonical_noncopy_focus_ne_hash
                          x cap p' z' hp' hnext
                      have hmovable := capacity_anchoredZipper_movable_of_focus_ne_hash
                        origin z' hfocus
                      rcases sideParserRealize_outerRunningStep_atMostOne x p p' origin z z'
                          (liftUnitParserAction MStarULogAssembly.data.uStart
                            { write := write, target := .parser p', move := move })
                          houter happlyOuter houterTarget hmovable with ⟨d, hd, hout⟩
                      refine ⟨d, ?_, hout⟩
                      rw [hs]
                      exact ⟨hnext, hd⟩

theorem capacitySideParser_outerStepSimulation
    (x : ConcretePakSide.Word) (cap : ScannerCapacity x) :
    ParserOuterStepSimulation zero one work (CapacitySideParserRealize x cap) := by
  intro r s outer hrealize hrun
  rcases capacitySideParser_outerStepSimulation_atMostOne x cap r s outer
      hrealize hrun with ⟨d, hd, arrows, _, harrows⟩
  exact ⟨d, hd, ⟨arrows, harrows⟩⟩

/-- The explicit parser fuel yields a literal outer arrow word at the actual
scanner capacity.  No canonical reserve is substituted in this statement. -/
theorem run_capacityParserInitial_outerArrowList
    (x : ConcretePakSide.Word) (cap : ScannerCapacity x) :
    ∃ d arrows,
      CapacitySideParserRealize x cap
        (.copyReady (MStarParserExecution.extendRight
          (MStarConcreteAlphabet.finalZipper x.reverse)
          (capacityParserTail x cap))) d ∧
      FiniteOneTapeSemantics.run MStarULogAssembly.program
        MStarOuterProgram.movable arrows (capacityEncodedParserConfig x cap) = some d := by
  apply parserReaches_outerArrowList zero one work
    (CapacitySideParserRealize x cap)
    (capacitySideParser_outerStepSimulation x cap)
    (r := capacityParserInitialResult x cap)
    (c := capacityEncodedParserConfig x cap)
  · exact reaches_capacityParser_copyReady x cap
  · exact capacitySideParserRealize_initial x cap

/-! ## Capacity-indexed copier half -/

abbrev CopierResult := MStarCopierExecution.Result

/-- Copier-path membership from the *physical* capacity emitted by the
scanner.  The future `groupReady` witness is retained independently of the
forward path, so malformed branches cannot enter the outer simulation. -/
def CapacityCopierCanonical (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (_hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.1)
    (r : CopierResult) : Prop :=
  MStarCopierExecution.Reaches
      (PakCopierReserveLowerBound.rawCopierSeed x cap.1
        (capacityCopierJunk x) (capacityHashTail x cap)) r ∧
    SideCopierCanFinish r

def CapacitySideCopierRealize (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.1)
    (r : CopierResult) (outer : OuterConfig) : Prop :=
  CapacityCopierCanonical x cap hmin r ∧ sideCopierRealize r outer

theorem capacityCopierCanonical_seed (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.1) :
    CapacityCopierCanonical x cap hmin
      (.running .seedCell (capacityRawCopierSeedZipper x cap)) := by
  have hreach := reaches_capacityCopier_generalCapacity x cap hmin
  constructor
  · rw [← rawCopierSeed_eq_capacityRawCopierSeedZipper x cap]
    exact MStarCopierExecution.reaches_refl _
  · rw [← rawCopierSeed_eq_capacityRawCopierSeedZipper x cap]
    exact ⟨_, hreach⟩

theorem CapacityCopierCanonical.oneStep (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.1)
    {r : CopierResult} (h : CapacityCopierCanonical x cap hmin r) :
    CapacityCopierCanonical x cap hmin (MStarCopierExecution.oneStep r) := by
  constructor
  · exact MStarCopierExecution.reaches_trans h.1
      (MStarCopierExecution.reaches_of_oneStep rfl)
  · exact h.2.oneStep

theorem capacityCopierCanonical_ne_rejected (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.1)
    {r : CopierResult} (h : CapacityCopierCanonical x cap hmin r) : r ≠ .rejected := by
  intro hr
  subst r
  exact sideCopierCanFinish_ne_rejected h.2

theorem capacityCopierCanonical_ne_stuck (x : ConcretePakSide.Word)
    (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.1)
    {r : CopierResult} (h : CapacityCopierCanonical x cap hmin r) : r ≠ .stuck := by
  intro hr
  subst r
  exact sideCopierCanFinish_ne_stuck h.2

theorem capacityCopierCanonical_running_focus_ne_hash
    (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.1)
    (q : MStarCopierMicrocode.CopierState)
    (z : MStarParserExecution.Zipper OuterTape)
    (h : CapacityCopierCanonical x cap hmin (.running q z)) : z.focus ≠ .hash := by
  intro hhash
  have hnext := h.oneStep x cap hmin
  rw [show z = ⟨z.leftRev, .hash, z.right⟩ by
    apply MStarParserExecution.Zipper.ext <;> simp [hhash],
    copierOneStep_hash_rejected] at hnext
  exact sideCopierCanFinish_ne_rejected hnext.2

theorem capacityCopierCanonical_groupReady_focus_work
    (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.1)
    (z : MStarParserExecution.Zipper OuterTape)
    (h : CapacityCopierCanonical x cap hmin (.groupReady z)) :
    z.focus = .core work := by
  rcases h.1 with ⟨fuel, hrun⟩
  have hz := PakCopierReserveLowerBound.successful_rawCopier_groupReady_eq_generalCapacity
    x cap.1 fuel (capacityCopierJunk x) (capacityHashTail x cap) z hrun
  rw [hz]
  rfl

/-- Capacity-specific physical copier simulation, with the same one-arrow
bound as the canonical copier but no canonical-reserve assumption. -/
theorem capacitySideCopier_outerStepSimulation_atMostOne
    (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.1) :
    CopierOuterStepSimulationAtMostOne (CapacitySideCopierRealize x cap hmin) := by
  intro r s outer hrealize hrun
  rcases hrealize with ⟨hcanonical, hside⟩
  cases r with
  | rejected => exact (sideCopierCanFinish_ne_rejected hcanonical.2).elim
  | stuck => exact (sideCopierCanFinish_ne_stuck hcanonical.2).elim
  | groupReady z =>
      simp only [MStarCopierExecution.oneStep] at hrun
      subst s
      exact ⟨outer, ⟨hcanonical, hside⟩, ⟨[], by simp, rfl⟩⟩
  | running q z =>
      cases htable : MStarCopierMicrocode.copierStep (UState := Unit) () q z.focus with
      | none =>
          have hbad : CapacityCopierCanonical x cap hmin .stuck := by
            simpa [MStarCopierExecution.oneStep, htable] using
              (hcanonical.oneStep x cap hmin)
          exact (sideCopierCanFinish_ne_stuck hbad.2).elim
      | some a =>
          cases happly : MStarParserExecution.applyAction z a with
          | none =>
              have hbad : CapacityCopierCanonical x cap hmin .stuck := by
                simpa [MStarCopierExecution.oneStep, htable, happly] using
                  (hcanonical.oneStep x cap hmin)
              exact (sideCopierCanFinish_ne_stuck hbad.2).elim
          | some z' =>
              cases htarget : a.target with
              | start | accept =>
                  have hbad : CapacityCopierCanonical x cap hmin .stuck := by
                    simpa [MStarCopierExecution.oneStep, htable, happly, htarget] using
                      (hcanonical.oneStep x cap hmin)
                  exact (sideCopierCanFinish_ne_stuck hbad.2).elim
              | reject =>
                  have hbad : CapacityCopierCanonical x cap hmin .rejected := by
                    simpa [MStarCopierExecution.oneStep, htable, happly, htarget] using
                      (hcanonical.oneStep x cap hmin)
                  exact (sideCopierCanFinish_ne_rejected hbad.2).elim
              | parser p =>
                  cases p with
                  | inl p =>
                      have hbad : CapacityCopierCanonical x cap hmin .stuck := by
                        simpa [MStarCopierExecution.oneStep, htable, happly, htarget] using
                          (hcanonical.oneStep x cap hmin)
                      exact (sideCopierCanFinish_ne_stuck hbad.2).elim
                  | inr q' =>
                      have hs : s = .running q' z' := by
                        simpa [MStarCopierExecution.oneStep, htable, happly, htarget] using
                          hrun.symm
                      have hnext : CapacityCopierCanonical x cap hmin (.running q' z') := by
                        simpa [MStarCopierExecution.oneStep, htable, happly, htarget] using
                          (hcanonical.oneStep x cap hmin)
                      rcases hside with ⟨origin, rfl⟩
                      have hfocus := capacityCopierCanonical_running_focus_ne_hash
                        x cap hmin q' z' hnext
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
                    simpa [MStarCopierExecution.oneStep, htable, happly, htarget] using
                      hrun.symm
                  have hnext : CapacityCopierCanonical x cap hmin (.groupReady z') := by
                    simpa [MStarCopierExecution.oneStep, htable, happly, htarget] using
                      (hcanonical.oneStep x cap hmin)
                  rcases hside with ⟨origin, rfl⟩
                  have hfocus := capacityCopierCanonical_groupReady_focus_work
                    x cap hmin z' hnext
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

theorem capacitySideCopier_outerStepSimulation
    (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.1) :
    CopierOuterStepSimulation (CapacitySideCopierRealize x cap hmin) := by
  intro r s outer hrealize hrun
  rcases capacitySideCopier_outerStepSimulation_atMostOne x cap hmin r s outer
      hrealize hrun with ⟨d, hd, arrows, _, harrows⟩
  exact ⟨d, hd, ⟨arrows, harrows⟩⟩

/-- The literal entry arrow, with its occupied-slot proof checked by the kernel. -/
def kernelCopyEntryArrow : OuterArrow :=
  slotZeroArrow (.parser (.inl MStarParserMicrocode.copyStart))
    (.core work) sideCopyEntryAction
    (parserCopier_slotZero_rule _ _ _ PakParserKernelTableFacts.copy_entry_microstep)

theorem kernelCopyEntryOuterStep (c : OuterConfig)
    (hstate : c.state = .parser (.inl MStarParserMicrocode.copyStart))
    (hread : c.tape c.head = .core work)
    (hmovable : MStarOuterProgram.movable
      ((writtenTape c sideCopyEntryAction.write)
        (moveHead sideCopyEntryAction.move c.head)) = true) :
    FiniteOneTapeSemantics.step MStarULogAssembly.program
        MStarOuterProgram.movable c kernelCopyEntryArrow =
      some (afterAction c sideCopyEntryAction) := by
  apply step_slotZeroArrow
  · exact hstate
  · exact hread
  · exact hmovable

/-- The parser terminal at the physical capacity crosses exactly one real
entry arrow into the capacity-specific raw copier seed. -/
theorem capacityCopyReady_enters_capacityCopier_atMostOne
    (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.1)
    (outer : OuterConfig)
    (hready : CapacitySideParserRealize x cap
      (.copyReady (MStarParserExecution.extendRight
        (MStarConcreteAlphabet.finalZipper x.reverse) (capacityParserTail x cap))) outer) :
    ∃ d, CapacitySideCopierRealize x cap hmin
        (.running .seedCell (capacityRawCopierSeedZipper x cap)) d ∧
      ∃ arrows : List OuterArrow, arrows.length ≤ 1 ∧
        FiniteOneTapeSemantics.run MStarULogAssembly.program
          MStarOuterProgram.movable arrows outer = some d := by
  let z := MStarParserExecution.extendRight
    (MStarConcreteAlphabet.finalZipper x.reverse) (capacityParserTail x cap)
  let seed := capacityRawCopierSeedZipper x cap
  rcases hready.2 with ⟨origin, rfl⟩
  have hentry := capacityCopyStart_enters_seed x cap
  have hstep := hentry.1
  have happly : MStarParserExecution.applyAction z sideCopyEntryAction = some seed := by
    change MStarParserExecution.applyAction z
        (MStarCopierMicrocode.copyGo (UState := MStarULogAssembly.UniversalState)
          .markL .seedCell .right) = some seed
    rw [show MStarParserExecution.applyAction z
          (MStarCopierMicrocode.copyGo (UState := MStarULogAssembly.UniversalState)
            .markL .seedCell .right) =
        MStarParserExecution.applyAction z
          (MStarCopierMicrocode.copyGo (UState := Unit)
            .markL .seedCell .right) by rfl]
    simpa [z, seed] using hentry.2
  let c0 := anchoredParserConfig MStarParserMicrocode.copyStart origin z
  let d := anchoredCopierConfig MStarCopierMicrocode.CopierState.seedCell origin seed
  have hafter : afterAction c0 sideCopyEntryAction = d := by
    simp only [c0, d, afterAction, anchoredParserConfig,
      anchoredCopierConfig, writtenTape]
    rw [anchoredZipperHead_applyAction origin z seed sideCopyEntryAction happly,
      anchoredZipperTape_applyAction origin z seed sideCopyEntryAction happly]
    rfl
  have htape : writtenTape c0 sideCopyEntryAction.write =
      anchoredZipperTape origin seed := by
    simpa only [c0, anchoredParserConfig, writtenTape] using
      (anchoredZipperTape_applyAction origin z seed sideCopyEntryAction happly).symm
  have hmove : MStarOuterProgram.movable
      ((writtenTape c0 sideCopyEntryAction.write)
        (moveHead sideCopyEntryAction.move c0.head)) = true := by
    change MStarOuterProgram.movable
      ((writtenTape c0 sideCopyEntryAction.write)
        (moveHead sideCopyEntryAction.move (origin + z.leftRev.length))) = true
    rw [htape, ← anchoredZipperHead_applyAction origin z seed
      sideCopyEntryAction happly, anchoredZipperTape_at_head]
    rfl
  refine ⟨d, ⟨capacityCopierCanonical_seed x cap hmin, ⟨origin, rfl⟩⟩, ?_⟩
  rw [← hafter]
  refine ⟨[kernelCopyEntryArrow], by simp, ?_⟩
  simp only [FiniteOneTapeSemantics.run_cons]
  rw [kernelCopyEntryOuterStep c0
    (by simp [c0, anchoredParserConfig])
    (by
      rw [show c0.tape c0.head = z.focus by
        simpa [c0, anchoredParserConfig] using anchoredZipperTape_at_head origin z]
      simp [z, MStarParserExecution.extendRight,
        MStarConcreteAlphabet.finalZipper])
    hmove]
  rfl

theorem capacityCopyReady_enters_capacityCopier
    (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.1)
    (outer : OuterConfig)
    (hready : CapacitySideParserRealize x cap
      (.copyReady (MStarParserExecution.extendRight
        (MStarConcreteAlphabet.finalZipper x.reverse) (capacityParserTail x cap))) outer) :
    ∃ d, CapacitySideCopierRealize x cap hmin
        (.running .seedCell (capacityRawCopierSeedZipper x cap)) d ∧
      OuterReaches outer d := by
  rcases capacityCopyReady_enters_capacityCopier_atMostOne x cap hmin outer hready with
    ⟨d, hd, arrows, _, harrows⟩
  exact ⟨d, hd, ⟨arrows, harrows⟩⟩

theorem capacityCopier_reaches_outerGroupReady_arrowList
    (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.1)
    (outer : OuterConfig)
    (hseed : CapacitySideCopierRealize x cap hmin
      (.running .seedCell (capacityRawCopierSeedZipper x cap)) outer) :
    ∃ d arrows,
      CapacitySideCopierRealize x cap hmin
        (.groupReady (PakCopierReserveLowerBound.rawGeneralCapacityGroupZipper x
          (PakCopierReserveLowerBound.actualFinalCapacity x.length cap.1)
          (capacityCopierJunk x) (capacityHashTail x cap))) d ∧
      FiniteOneTapeSemantics.run MStarULogAssembly.program
        MStarOuterProgram.movable arrows outer = some d := by
  apply copierReaches_outerArrowList (CapacitySideCopierRealize x cap hmin)
    (capacitySideCopier_outerStepSimulation x cap hmin)
    (reaches_capacityCopier_generalCapacity x cap hmin) hseed

theorem capacityParserCopier_reaches_outerGroupReady_arrowList
    (x : ConcretePakSide.Word) (cap : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ cap.1) :
    ∃ d arrows,
      CapacitySideCopierRealize x cap hmin
        (.groupReady (PakCopierReserveLowerBound.rawGeneralCapacityGroupZipper x
          (PakCopierReserveLowerBound.actualFinalCapacity x.length cap.1)
          (capacityCopierJunk x) (capacityHashTail x cap))) d ∧
      FiniteOneTapeSemantics.run MStarULogAssembly.program
        MStarOuterProgram.movable arrows (capacityEncodedParserConfig x cap) = some d := by
  rcases run_capacityParserInitial_outerArrowList x cap with
    ⟨parserEnd, parserArrows, hready, hparser⟩
  rcases capacityCopyReady_enters_capacityCopier_atMostOne x cap hmin parserEnd hready with
    ⟨seedEnd, hseed, entryArrows, _, hentry⟩
  rcases capacityCopier_reaches_outerGroupReady_arrowList x cap hmin seedEnd hseed with
    ⟨finish, copierArrows, hfinish, hcopier⟩
  refine ⟨finish, parserArrows ++ entryArrows ++ copierArrows, hfinish, ?_⟩
  rw [outerRun_append (parserArrows ++ entryArrows) copierArrows,
    outerRun_append parserArrows entryArrows, hparser]
  simp only [Option.bind_some]
  rw [hentry]
  simp only [Option.bind_some]
  exact hcopier

/-- The capacity copier's actual group-ready outer configuration is exactly
the framed `qStart` configuration for the physical final capacity. -/
theorem capacityAnchoredGroupReady_eq_framedQStart
    (x : ConcretePakSide.Word) (cap : ScannerCapacity x) (origin : Int) :
    anchoredGroupReadyConfig origin
      (PakCopierReserveLowerBound.rawGeneralCapacityGroupZipper x
        (PakCopierReserveLowerBound.actualFinalCapacity x.length cap.1)
        (capacityCopierJunk x) (capacityHashTail x cap)) =
      PakOuterULogBridge.anchoredFramedULogConfig ULogControl.qStart origin
        (PakCopierReserveLowerBound.rawGeneralCapacityGroupZipper x
          (PakCopierReserveLowerBound.actualFinalCapacity x.length cap.1)
          (capacityCopierJunk x) (capacityHashTail x cap)).leftRev
        (.markR :: capacityHashTail x cap)
        (generalCapacityCoreZipper x
          (PakCopierReserveLowerBound.actualFinalCapacity x.length cap.1)) := by
  rw [PakULogGeneralCapacityBootstrap.rawGeneralCapacityGroupZipper_eq_framed]
  rfl

end PakFixedPolyomino.PakGeneralCapacityOuterFrontStandard
