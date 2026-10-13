import PakFixedPolyomino.PakCopierOuterBridge
import PakFixedPolyomino.ULogConcreteRawReflection

/-!
# Literal `U_log` execution inside the outer M-star program

The parser/copier bridge ends in the outer state `.sim qStart`.  This module
records the remaining, type-sensitive comparison: a finite `U_log` zipper is
embedded cellwise into the core track of the literal outer tape, and every
successful deterministic `U_log` step is an occupied outer M-star arrow.
-/

namespace PakFixedPolyomino.PakOuterULogBridge

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics
open PakParserOuterBridge

abbrev OuterState := MStarULogAssembly.State
abbrev OuterTape := MStarULogAssembly.Tape
abbrev OuterConfig := PakMStarCouplingCorrectness.MStarConfig
abbrev OuterAction := Action OuterState OuterTape

/-- Cellwise inclusion of a finite `U_log` zipper into the outer core tape. -/
def liftCoreZipper (z : MStarParserExecution.Zipper ULogProgram.Tape) :
    MStarParserExecution.Zipper OuterTape :=
  ⟨z.leftRev.map .core, .core z.focus, z.right.map .core⟩

/-- Inclusion of a `U_log` zipper into a larger physical zipper.  The extra
lists contain the copier's left bookkeeping and the right `.markR`/hash
suffix.  They stay beyond the finite `U_log` support throughout every
successful zipper action. -/
def frameCoreZipper (leftExtra rightExtra : List OuterTape)
    (z : MStarParserExecution.Zipper ULogProgram.Tape) :
    MStarParserExecution.Zipper OuterTape :=
  ⟨z.leftRev.map .core ++ leftExtra, .core z.focus,
    z.right.map .core ++ rightExtra⟩

/-- The literal integer-indexed outer configuration represented by a running
finite `U_log` zipper. -/
def anchoredULogConfig (q : ULogControl.State) (origin : Int)
    (z : MStarParserExecution.Zipper ULogProgram.Tape) : OuterConfig :=
  { state := .sim q
    head := origin + z.leftRev.length
    tape := anchoredZipperTape origin (liftCoreZipper z) }

def anchoredFramedULogConfig (q : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z : MStarParserExecution.Zipper ULogProgram.Tape) : OuterConfig :=
  { state := .sim q
    head := origin + (frameCoreZipper leftExtra rightExtra z).leftRev.length
    tape := anchoredZipperTape origin
      (frameCoreZipper leftExtra rightExtra z) }

def anchoredFramedOuterAcceptConfig (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z : MStarParserExecution.Zipper ULogProgram.Tape) : OuterConfig :=
  { state := .accept
    head := origin + (frameCoreZipper leftExtra rightExtra z).leftRev.length
    tape := anchoredZipperTape origin
      (frameCoreZipper leftExtra rightExtra z) }

/-- The exponential work radius actually produced by the copier before its
final `+1` endpoint cell is included. -/
def copiedCoreRadius (x : ConcretePakSide.Word) : ℕ :=
  2 ^ MStarParserCopySpec.timeExponent x.length

/-- The maximal all-core `U_log` zipper exposed between the copier's two
physical markers. -/
def copiedULogStartZipper (x : ConcretePakSide.Word) :
    MStarParserExecution.Zipper ULogProgram.Tape :=
  ⟨[], MStarConcreteAlphabet.work,
    List.replicate (copiedCoreRadius x) MStarConcreteAlphabet.work ++
      x.map ULogProgram.bitTape ++
        List.replicate (copiedCoreRadius x + 1)
          MStarConcreteAlphabet.work⟩

theorem copiedCoreRadius_ge_256 (x : ConcretePakSide.Word) :
    256 ≤ copiedCoreRadius x := by
  have hexp : 8 ≤ MStarParserCopySpec.timeExponent x.length := by
    simp [MStarParserCopySpec.timeExponent]
  calc
    256 = 2 ^ 8 := by norm_num
    _ ≤ 2 ^ MStarParserCopySpec.timeExponent x.length :=
      Nat.pow_le_pow_right (by decide) hexp
    _ = copiedCoreRadius x := rfl

/-- The unused suffix of the copied right work buffer after reserving the
fixed bootstrap scratch cells. -/
def copiedBootstrapTail (x input : ConcretePakSide.Word) :
    List ULogProgram.Tape :=
  match input with
  | [] => List.replicate (copiedCoreRadius x - 6) MStarConcreteAlphabet.work
  | _ :: _ =>
      List.replicate (copiedCoreRadius x - 5) MStarConcreteAlphabet.work

theorem copied_rightBuffer_eq_runtimeWorkspace
    (x input : ConcretePakSide.Word) :
    List.replicate (copiedCoreRadius x + 1) MStarConcreteAlphabet.work =
      MStarConcreteAlphabet.work ::
        ULogBootstrapExecution.payloadRuntimeWorkspace input
          (copiedBootstrapTail x input) := by
  have hn := copiedCoreRadius_ge_256 x
  cases input with
  | nil =>
      have heq : copiedCoreRadius x + 1 =
          7 + (copiedCoreRadius x - 6) := by omega
      rw [heq, List.replicate_add]
      simp [copiedBootstrapTail,
        ULogBootstrapExecution.payloadRuntimeWorkspace,
        ULogBootstrapExecution.initializationWorkspace,
        List.replicate_succ, List.append_assoc]
  | cons b bs =>
      have heq : copiedCoreRadius x + 1 =
          6 + (copiedCoreRadius x - 5) := by omega
      rw [heq, List.replicate_add]
      simp [copiedBootstrapTail,
        ULogBootstrapExecution.payloadRuntimeWorkspace,
        ULogBootstrapExecution.initializationWorkspace,
        List.replicate_succ, List.append_assoc]

/-- When the copied word is a literal universal instance, the exposed core
zipper is definitionally the bootstrap input expected by the verified
`U_log` initialization theorem. -/
theorem copiedULogStartZipper_eq_bootstrap
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    copiedULogStartZipper x =
      ⟨[], MStarConcreteAlphabet.work,
        List.replicate (copiedCoreRadius x) MStarConcreteAlphabet.work ++
          (ULogBytecode.encodeProgram rules ++
            ULogBytecode.encodePayload input padding).map ULogProgram.bitTape ++
          MStarConcreteAlphabet.work ::
            ULogBootstrapExecution.payloadRuntimeWorkspace input
              (copiedBootstrapTail x input)⟩ := by
  subst x
  apply MStarParserExecution.Zipper.ext
  · rfl
  · rfl
  · dsimp only [copiedULogStartZipper]
    rw [copied_rightBuffer_eq_runtimeWorkspace]

/-- Canonical copier completion exposes exactly the framed all-core zipper
above.  The left bookkeeping and right marker/hash tail are retained
literally, rather than collapsed into abstract sentinel cells. -/
theorem SideCopierCanonical.groupReady_eq_framedULogStart
    (x : ConcretePakSide.Word)
    (z : MStarParserExecution.Zipper OuterTape)
    (h : PakParserOuterBridge.SideCopierCanonical x (.groupReady z)) :
    z = frameCoreZipper z.leftRev
      (.markR :: PakSideScanner.sideCopierHashTail x)
      (copiedULogStartZipper x) := by
  have hsegment := h.groupReady_markedWorkspace x z
  rcases z with ⟨left, focus, right⟩
  simp only [MStarParserExecution.Zipper.leftRev]
  simp [MStarParserCopySpec.copiedWorkspace,
    MStarParserCopySpec.workspaceRadius, copiedCoreRadius,
    copiedULogStartZipper, frameCoreZipper,
    MStarCopierExecution.coreBit, ULogProgram.bitTape,
    List.replicate_succ, List.append_assoc] at hsegment ⊢
  have hmap :
      x.map (fun b =>
        MStarOuterProgram.Tape.core
          (MStarParserCopySpec.bitLetter MStarConcreteAlphabet.zero
            MStarConcreteAlphabet.one b)) =
      x.map (MStarOuterProgram.Tape.core ∘ ULogProgram.bitTape) := by
    apply List.map_congr_left
    intro b hb
    cases b <;> rfl
  exact ⟨hsegment.1, by simpa only [hmap] using hsegment.2⟩

/-- Every concrete canonical group-ready outer configuration is therefore a
literal framed `U_log` start configuration. -/
theorem canonicalGroupReady_outer_eq_framedULogStart
    (x : ConcretePakSide.Word)
    (z : MStarParserExecution.Zipper OuterTape) (d : OuterConfig)
    (h : PakParserOuterBridge.CanonicalSideCopierRealize x (.groupReady z) d) :
    ∃ origin leftExtra,
      d = anchoredFramedULogConfig ULogControl.qStart origin leftExtra
        (.markR :: PakSideScanner.sideCopierHashTail x)
        (copiedULogStartZipper x) := by
  rcases h.2 with ⟨origin, rfl⟩
  refine ⟨origin, z.leftRev, ?_⟩
  have hz := SideCopierCanonical.groupReady_eq_framedULogStart x z h.1
  unfold PakParserOuterBridge.anchoredGroupReadyConfig
  unfold anchoredFramedULogConfig
  rw [hz]
  rfl

/-- The entire verified deterministic bootstrap runs directly from the core
zipper produced by the copier. -/
theorem copiedULogStart_reaches_semanticStart
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    ULogBootstrapExecution.Reaches
      (.running ULogControl.qStart (copiedULogStartZipper x))
      (ULogBootstrapExecution.semanticCycleEncoding input
        (ULogBootstrapExecution.clockCellsBefore
          ((ULogSemantics.startFrom rules input).right.map
            ULogBootstrapExecution.payloadNat)
          padding.length [ULogAlphabet.ulogCore ULogAlphabet.clockSep])
        2
        (List.replicate (copiedCoreRadius x) MStarConcreteAlphabet.work)
        (copiedBootstrapTail x input)
        (ULogSemantics.startFrom rules input)) := by
  rw [copiedULogStartZipper_eq_bootstrap x rules input padding hword]
  simpa [ULogControl.qStart] using
    (ULogBootstrapExecution.reaches_bootstrap_semanticStart
      (copiedCoreRadius x) rules input padding []
        (copiedBootstrapTail x input))

def copiedSemanticStartZipper
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) :
    MStarParserExecution.Zipper ULogProgram.Tape :=
  ⟨ULogBootstrapExecution.dynamicRuleReturnPath
        ((ULogSemantics.startFrom rules input).leftRev.map
          ULogBootstrapExecution.payloadNat)
        (ULogSemantics.startFrom rules input).program input ++
      ULogAlphabet.ulogCore ULogAlphabet.pcMark ::
        List.replicate (copiedCoreRadius x) MStarConcreteAlphabet.work,
    ULogBootstrapExecution.readHeadNat
      (ULogSemantics.startFrom rules input).focus,
    ULogBootstrapExecution.clockCellsBefore
        ((ULogSemantics.startFrom rules input).right.map
          ULogBootstrapExecution.payloadNat)
        padding.length [ULogAlphabet.ulogCore ULogAlphabet.clockSep] ++
      ULogBootstrapExecution.stateWorkspace 2
        (ULogSemantics.startFrom rules input).state
        (copiedBootstrapTail x input)⟩

theorem copiedSemanticStartEncoding_eq_running
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) :
    ULogBootstrapExecution.semanticCycleEncoding input
        (ULogBootstrapExecution.clockCellsBefore
          ((ULogSemantics.startFrom rules input).right.map
            ULogBootstrapExecution.payloadNat)
          padding.length [ULogAlphabet.ulogCore ULogAlphabet.clockSep])
        2
        (List.replicate (copiedCoreRadius x) MStarConcreteAlphabet.work)
        (copiedBootstrapTail x input)
        (ULogSemantics.startFrom rules input) =
      .running ULogControl.State.cycleStart
        (copiedSemanticStartZipper x rules input padding) := rfl

/- Moved below the generic framed reachability lift.
theorem copiedULogStart_outer_reaches_semanticStart
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (origin : Int) (leftExtra rightExtra : List OuterTape) :
    OuterReaches
      (anchoredFramedULogConfig ULogControl.qStart origin leftExtra rightExtra
        (copiedULogStartZipper x))
      (anchoredFramedULogConfig ULogControl.cycleStart origin leftExtra rightExtra
        (copiedSemanticStartZipper x rules input padding)) := by
  apply ulogReaches_running_outer_framed
  have h := copiedULogStart_reaches_semanticStart x rules input padding hword
  rw [copiedSemanticStartEncoding_eq_running] at h
  exact h

/-- Scanner, parser, copier, and deterministic universal bootstrap now form
one literal outer-machine arrow path to the semantic cycle-start frame. -/
theorem sideStart_reaches_outerSemanticStart
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    ∃ origin leftExtra,
      OuterReaches (PakSideScannerRow.sideEncodedStartConfig x)
        (anchoredFramedULogConfig ULogControl.cycleStart origin leftExtra
          (.markR :: PakSideScanner.sideCopierHashTail x)
          (copiedSemanticStartZipper x rules input padding)) := by
  rcases PakParserOuterBridge.sideStartParserCopier_reaches_outerGroupReady_arrowList x with
    ⟨d, arrows, z, hd, hrun⟩
  rcases canonicalGroupReady_outer_eq_framedULogStart x z d hd with
    ⟨origin, leftExtra, hdEq⟩
  refine ⟨origin, leftExtra, outerReaches_trans ⟨arrows, hrun⟩ ?_⟩
  rw [hdEq]
  exact copiedULogStart_outer_reaches_semanticStart x rules input padding
    hword origin leftExtra (.markR :: PakSideScanner.sideCopierHashTail x)
-/

@[simp] theorem liftCoreZipper_left_length
    (z : MStarParserExecution.Zipper ULogProgram.Tape) :
    (liftCoreZipper z).leftRev.length = z.leftRev.length := by
  simp [liftCoreZipper]

@[simp] theorem liftCoreZipper_focus
    (z : MStarParserExecution.Zipper ULogProgram.Tape) :
    (liftCoreZipper z).focus = .core z.focus := rfl

/-- Mapping the state component of an action does not change its finite
zipper effect; mapping the written core letter commutes with that effect. -/
theorem liftCoreZipper_applyAction
    (z z' : MStarParserExecution.Zipper ULogProgram.Tape)
    (a : Action ULogControl.State ULogProgram.Tape)
    (happly : MStarParserExecution.applyAction z a = some z') :
    MStarParserExecution.applyAction (liftCoreZipper z)
        (MStarOuterProgram.mapUAction MStarULogAssembly.data a) =
      some (liftCoreZipper z') := by
  rcases z with ⟨left, focus, right⟩
  rcases a with ⟨write, target, move⟩
  cases move with
  | stay =>
      simp only [MStarParserExecution.applyAction] at happly
      have hz' :
          ({ leftRev := left, focus := write, right := right } :
            MStarParserExecution.Zipper ULogProgram.Tape) = z' :=
        Option.some.inj happly
      subst z'
      rfl
  | right =>
      cases right with
      | nil => simp [MStarParserExecution.applyAction] at happly
      | cons next rest =>
          simp only [MStarParserExecution.applyAction] at happly
          have hz' :
              ({ leftRev := write :: left, focus := next, right := rest } :
                MStarParserExecution.Zipper ULogProgram.Tape) = z' :=
            Option.some.inj happly
          subst z'
          simp [liftCoreZipper, MStarParserExecution.applyAction,
            MStarOuterProgram.mapUAction]
  | left =>
      cases left with
      | nil => simp [MStarParserExecution.applyAction] at happly
      | cons previous rest =>
          simp only [MStarParserExecution.applyAction] at happly
          have hz' :
              ({ leftRev := rest, focus := previous, right := write :: right } :
                MStarParserExecution.Zipper ULogProgram.Tape) = z' :=
            Option.some.inj happly
          subst z'
          simp [liftCoreZipper, MStarParserExecution.applyAction,
            MStarOuterProgram.mapUAction]

@[simp] theorem frameCoreZipper_left_length
    (leftExtra rightExtra : List OuterTape)
    (z : MStarParserExecution.Zipper ULogProgram.Tape) :
    (frameCoreZipper leftExtra rightExtra z).leftRev.length =
      z.leftRev.length + leftExtra.length := by
  simp [frameCoreZipper]

/-- Successful zipper actions commute with the framed physical inclusion. -/
theorem frameCoreZipper_applyAction
    (leftExtra rightExtra : List OuterTape)
    (z z' : MStarParserExecution.Zipper ULogProgram.Tape)
    (a : Action ULogControl.State ULogProgram.Tape)
    (happly : MStarParserExecution.applyAction z a = some z') :
    MStarParserExecution.applyAction
        (frameCoreZipper leftExtra rightExtra z)
        (MStarOuterProgram.mapUAction MStarULogAssembly.data a) =
      some (frameCoreZipper leftExtra rightExtra z') := by
  rcases z with ⟨left, focus, right⟩
  rcases a with ⟨write, target, move⟩
  cases move with
  | stay =>
      simp only [MStarParserExecution.applyAction] at happly
      have hz' :
          ({ leftRev := left, focus := write, right := right } :
            MStarParserExecution.Zipper ULogProgram.Tape) = z' :=
        Option.some.inj happly
      subst z'
      rfl
  | right =>
      cases right with
      | nil => simp [MStarParserExecution.applyAction] at happly
      | cons next rest =>
          simp only [MStarParserExecution.applyAction] at happly
          have hz' :
              ({ leftRev := write :: left, focus := next, right := rest } :
                MStarParserExecution.Zipper ULogProgram.Tape) = z' :=
            Option.some.inj happly
          subst z'
          simp [frameCoreZipper, MStarParserExecution.applyAction,
            MStarOuterProgram.mapUAction, List.append_assoc]
  | left =>
      cases left with
      | nil => simp [MStarParserExecution.applyAction] at happly
      | cons previous rest =>
          simp only [MStarParserExecution.applyAction] at happly
          have hz' :
              ({ leftRev := rest, focus := previous, right := write :: right } :
                MStarParserExecution.Zipper ULogProgram.Tape) = z' :=
            Option.some.inj happly
          subst z'
          simp [frameCoreZipper, MStarParserExecution.applyAction,
            MStarOuterProgram.mapUAction, List.append_assoc]
theorem sim_slotZero_rule
    (q : ULogControl.State) (x : ULogProgram.Tape)
    (a : Action ULogControl.State ULogProgram.Tape)
    (hrule : ULogProgram.program.rule q x 0 = some a) :
    MStarULogAssembly.program.rule (.sim q) (.core x) 0 =
      some (MStarOuterProgram.mapUAction MStarULogAssembly.data a) := by
  rw [MStarULogAssembly.sim_rule_eq, hrule]
  rfl

theorem sim_slot_rule
    (q : ULogControl.State) (x : ULogProgram.Tape) (slot : Fin 2)
    (a : Action ULogControl.State ULogProgram.Tape)
    (hrule : ULogProgram.program.rule q x slot = some a) :
    MStarULogAssembly.program.rule (.sim q) (.core x) slot =
      some (MStarOuterProgram.mapUAction MStarULogAssembly.data a) := by
  rw [MStarULogAssembly.sim_rule_eq, hrule]
  rfl

def simSlotArrow (q : ULogControl.State) (x : ULogProgram.Tape)
    (slot : Fin 2) (a : OuterAction)
    (hrule : MStarULogAssembly.program.rule (.sim q) (.core x) slot = some a) :
    MStarULogAssembly.Arrow :=
  ⟨((.sim q, .core x), slot), by simp [hrule]⟩

theorem actionOf_simSlotArrow
    (q : ULogControl.State) (x : ULogProgram.Tape)
    (slot : Fin 2) (a : OuterAction)
    (hrule : MStarULogAssembly.program.rule (.sim q) (.core x) slot = some a) :
    actionOf MStarULogAssembly.program (simSlotArrow q x slot a hrule) = a := by
  unfold actionOf
  split
  · rename_i found hfound
    exact Option.some.inj (hfound.symm.trans hrule)
  · rename_i hnone
    exact ((simSlotArrow q x slot a hrule).2 hnone).elim

@[simp] theorem simSlotArrow_source
    (q : ULogControl.State) (x : ULogProgram.Tape)
    (slot : Fin 2) (a : OuterAction)
    (hrule : MStarULogAssembly.program.rule (.sim q) (.core x) slot = some a) :
    (simSlotArrow q x slot a hrule).1.1.1 = .sim q := rfl

@[simp] theorem simSlotArrow_read
    (q : ULogControl.State) (x : ULogProgram.Tape)
    (slot : Fin 2) (a : OuterAction)
    (hrule : MStarULogAssembly.program.rule (.sim q) (.core x) slot = some a) :
    (simSlotArrow q x slot a hrule).1.1.2 = .core x := rfl

theorem outerReaches_simSlotArrow
    (c : OuterConfig) (q : ULogControl.State) (x : ULogProgram.Tape)
    (slot : Fin 2) (a : OuterAction)
    (hrule : MStarULogAssembly.program.rule (.sim q) (.core x) slot = some a)
    (hstate : c.state = .sim q) (hread : c.tape c.head = .core x)
    (hmovable : MStarOuterProgram.movable
      ((writtenTape c a.write) (moveHead a.move c.head)) = true) :
    OuterReaches c (afterAction c a) := by
  refine ⟨[simSlotArrow q x slot a hrule], ?_⟩
  simp only [run_cons, run_nil]
  simp [FiniteOneTapeSemantics.step, FiniteOneTapeProgram.transition,
    actionOf_simSlotArrow, hstate, hread, hmovable, afterAction]

theorem mapUState_eq_sim {q : ULogControl.State}
    (haccept : q ≠ ULogControl.qAccept)
    (hreject : q ≠ ULogControl.qReject) :
    MStarOuterProgram.mapUState MStarULogAssembly.data q = .sim q := by
  unfold MStarOuterProgram.mapUState
  rw [if_neg (by
    change q ≠ ULogControl.qAccept
    exact haccept), if_neg (by
    change q ≠ ULogControl.qReject
    exact hreject)]

/-- One successful nonterminal deterministic `U_log` step is one literal
occupied slot-zero arrow of the fixed outer M-star program. -/
theorem runningStep_outer
    (q q' : ULogControl.State) (origin : Int)
    (z z' : MStarParserExecution.Zipper ULogProgram.Tape)
    (a : Action ULogControl.State ULogProgram.Tape)
    (hrule : ULogProgram.program.rule q z.focus 0 = some a)
    (happly : MStarParserExecution.applyAction z a = some z')
    (htarget : a.target = q')
    (haccept : q' ≠ ULogControl.qAccept)
    (hreject : q' ≠ ULogControl.qReject) :
    OuterReaches (anchoredULogConfig q origin z)
      (anchoredULogConfig q' origin z') := by
  let a' := MStarOuterProgram.mapUAction MStarULogAssembly.data a
  let c := anchoredULogConfig q origin z
  let d := anchoredULogConfig q' origin z'
  have happly' : MStarParserExecution.applyAction (liftCoreZipper z) a' =
      some (liftCoreZipper z') := by
    exact liftCoreZipper_applyAction z z' a happly
  have htarget' : a'.target = (.sim q' : OuterState) := by
    simp only [a', MStarOuterProgram.mapUAction]
    rw [htarget, mapUState_eq_sim haccept hreject]
  have hhead : origin + z'.leftRev.length =
      moveHead a'.move (origin + z.leftRev.length) := by
    simpa [liftCoreZipper] using
      (anchoredZipperHead_applyAction origin (liftCoreZipper z)
        (liftCoreZipper z') a' happly')
  have htape' : anchoredZipperTape origin (liftCoreZipper z') =
      Function.update (anchoredZipperTape origin (liftCoreZipper z))
        (origin + z.leftRev.length) a'.write := by
    simpa [liftCoreZipper] using
      anchoredZipperTape_applyAction origin (liftCoreZipper z)
        (liftCoreZipper z') a' happly'
  have hafter : afterAction c a' = d := by
    simp only [c, d, afterAction, anchoredULogConfig, writtenTape]
    rw [htarget', ← hhead, ← htape']
  have htape : writtenTape c a'.write =
      anchoredZipperTape origin (liftCoreZipper z') := by
    simpa only [c, anchoredULogConfig, writtenTape] using htape'.symm
  have hmove : MStarOuterProgram.movable
      ((writtenTape c a'.write) (moveHead a'.move c.head)) = true := by
    change MStarOuterProgram.movable
      ((writtenTape c a'.write)
        (moveHead a'.move (origin + z.leftRev.length))) = true
    rw [htape, ← hhead]
    rw [← liftCoreZipper_left_length z']
    rw [anchoredZipperTape_at_head]
    rfl
  change OuterReaches c d
  rw [← hafter]
  exact outerReaches_slotZeroArrow c (.sim q) (.core z.focus) a'
    (sim_slotZero_rule q z.focus a hrule)
    (by simp [c, anchoredULogConfig])
    (by simpa [c, anchoredULogConfig] using
      anchoredZipperTape_at_head origin (liftCoreZipper z))
    hmove

/-- Framed version of `runningStep_outer`; the copier bookkeeping and the
right marker remain part of the physical configuration but outside the
finite core zipper on which `U_log` executes. -/
theorem framedRunningStep_outer
    (q q' : ULogControl.State) (slot : Fin 2) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z z' : MStarParserExecution.Zipper ULogProgram.Tape)
    (a : Action ULogControl.State ULogProgram.Tape)
    (hrule : ULogProgram.program.rule q z.focus slot = some a)
    (happly : MStarParserExecution.applyAction z a = some z')
    (htarget : a.target = q')
    (haccept : q' ≠ ULogControl.qAccept)
    (hreject : q' ≠ ULogControl.qReject) :
    OuterReaches
      (anchoredFramedULogConfig q origin leftExtra rightExtra z)
      (anchoredFramedULogConfig q' origin leftExtra rightExtra z') := by
  let a' := MStarOuterProgram.mapUAction MStarULogAssembly.data a
  let Z := frameCoreZipper leftExtra rightExtra z
  let Z' := frameCoreZipper leftExtra rightExtra z'
  let c := anchoredFramedULogConfig q origin leftExtra rightExtra z
  let d := anchoredFramedULogConfig q' origin leftExtra rightExtra z'
  have happly' : MStarParserExecution.applyAction Z a' = some Z' := by
    exact frameCoreZipper_applyAction leftExtra rightExtra z z' a happly
  have htarget' : a'.target = (.sim q' : OuterState) := by
    simp only [a', MStarOuterProgram.mapUAction]
    rw [htarget, mapUState_eq_sim haccept hreject]
  have hhead : origin + Z'.leftRev.length =
      moveHead a'.move (origin + Z.leftRev.length) :=
    anchoredZipperHead_applyAction origin Z Z' a' happly'
  have htape' : anchoredZipperTape origin Z' =
      Function.update (anchoredZipperTape origin Z)
        (origin + Z.leftRev.length) a'.write :=
    anchoredZipperTape_applyAction origin Z Z' a' happly'
  have hafter : afterAction c a' = d := by
    simp only [c, d, afterAction, anchoredFramedULogConfig, writtenTape]
    rw [htarget']
    congr 1
    · simpa only [Z, Z'] using hhead.symm
    · simpa only [Z, Z'] using htape'.symm
  have htape : writtenTape c a'.write = anchoredZipperTape origin Z' := by
    simpa only [c, anchoredFramedULogConfig, writtenTape, Z] using htape'.symm
  have hmove : MStarOuterProgram.movable
      ((writtenTape c a'.write) (moveHead a'.move c.head)) = true := by
    change MStarOuterProgram.movable
      ((writtenTape c a'.write)
        (moveHead a'.move (origin + Z.leftRev.length))) = true
    rw [htape, ← hhead, anchoredZipperTape_at_head]
    rfl
  change OuterReaches c d
  rw [← hafter]
  exact outerReaches_simSlotArrow c q z.focus slot a'
    (sim_slot_rule q z.focus slot a hrule)
    (by simp [c, anchoredFramedULogConfig])
    (by
      change anchoredZipperTape origin Z (origin + Z.leftRev.length) =
        .core z.focus
      rw [anchoredZipperTape_at_head]
      rfl)
    hmove

/-- A `U_log` action targeting `qAccept` is exactly an outer action targeting
the literal M-star accept state, at either occupied nondeterministic slot. -/
theorem framedAcceptingStep_outer
    (q : ULogControl.State) (slot : Fin 2) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z z' : MStarParserExecution.Zipper ULogProgram.Tape)
    (a : Action ULogControl.State ULogProgram.Tape)
    (hrule : ULogProgram.program.rule q z.focus slot = some a)
    (happly : MStarParserExecution.applyAction z a = some z')
    (htarget : a.target = ULogControl.qAccept) :
    OuterReaches
      (anchoredFramedULogConfig q origin leftExtra rightExtra z)
      (anchoredFramedOuterAcceptConfig origin leftExtra rightExtra z') := by
  let a' := MStarOuterProgram.mapUAction MStarULogAssembly.data a
  let Z := frameCoreZipper leftExtra rightExtra z
  let Z' := frameCoreZipper leftExtra rightExtra z'
  let c := anchoredFramedULogConfig q origin leftExtra rightExtra z
  let d := anchoredFramedOuterAcceptConfig origin leftExtra rightExtra z'
  have happly' : MStarParserExecution.applyAction Z a' = some Z' :=
    frameCoreZipper_applyAction leftExtra rightExtra z z' a happly
  have htarget' : a'.target = (.accept : OuterState) := by
    simp only [a', MStarOuterProgram.mapUAction, htarget]
    exact MStarULogAssembly.simulated_accept_maps_to_outer_accept
  have hhead : origin + Z'.leftRev.length =
      moveHead a'.move (origin + Z.leftRev.length) :=
    anchoredZipperHead_applyAction origin Z Z' a' happly'
  have htape' : anchoredZipperTape origin Z' =
      Function.update (anchoredZipperTape origin Z)
        (origin + Z.leftRev.length) a'.write :=
    anchoredZipperTape_applyAction origin Z Z' a' happly'
  have hafter : afterAction c a' = d := by
    simp only [c, d, afterAction, anchoredFramedULogConfig,
      anchoredFramedOuterAcceptConfig, writtenTape]
    rw [htarget']
    congr 1
    · simpa only [Z, Z'] using hhead.symm
    · simpa only [Z, Z'] using htape'.symm
  have htape : writtenTape c a'.write = anchoredZipperTape origin Z' := by
    simpa only [c, anchoredFramedULogConfig, writtenTape, Z] using htape'.symm
  have hmove : MStarOuterProgram.movable
      ((writtenTape c a'.write) (moveHead a'.move c.head)) = true := by
    change MStarOuterProgram.movable
      ((writtenTape c a'.write)
        (moveHead a'.move (origin + Z.leftRev.length))) = true
    rw [htape, ← hhead, anchoredZipperTape_at_head]
    rfl
  change OuterReaches c d
  rw [← hafter]
  exact outerReaches_simSlotArrow c q z.focus slot a'
    (sim_slot_rule q z.focus slot a hrule)
    (by simp [c, anchoredFramedULogConfig])
    (by
      change anchoredZipperTape origin Z (origin + Z.leftRev.length) =
        .core z.focus
      rw [anchoredZipperTape_at_head]
      rfl)
    hmove

@[simp] theorem ulogRun_accepted (fuel : ℕ)
    (z : MStarParserExecution.Zipper ULogProgram.Tape) :
    ULogBootstrapExecution.run fuel (.accepted z) = .accepted z := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [ULogBootstrapExecution.run,
      ULogBootstrapExecution.oneStep] using ih

@[simp] theorem ulogRun_rejected (fuel : ℕ) :
    ULogBootstrapExecution.run fuel .rejected = .rejected := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [ULogBootstrapExecution.run,
      ULogBootstrapExecution.oneStep] using ih

@[simp] theorem ulogRun_stuck (fuel : ℕ) :
    ULogBootstrapExecution.run fuel .stuck = .stuck := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [ULogBootstrapExecution.run,
      ULogBootstrapExecution.oneStep] using ih

/-- Decomposition of a deterministic `U_log` step whose endpoint is still
running.  In particular its target is neither concrete terminal state. -/
theorem ulogOneStep_eq_running_iff
    (q q' : ULogControl.State)
    (z z' : MStarParserExecution.Zipper ULogProgram.Tape) :
    ULogBootstrapExecution.oneStep (.running q z) = .running q' z' ↔
      ∃ a : Action ULogControl.State ULogProgram.Tape,
        ULogProgram.program.rule q z.focus 0 = some a ∧
        MStarParserExecution.applyAction z a = some z' ∧
        a.target = q' ∧ q' ≠ ULogControl.qAccept ∧
        q' ≠ ULogControl.qReject := by
  constructor
  · intro h
    simp only [ULogBootstrapExecution.oneStep] at h
    split at h
    · contradiction
    · rename_i a hrule
      split at h
      · contradiction
      · rename_i next happly
        split at h
        · contradiction
        · rename_i haccept
          split at h
          · contradiction
          · rename_i hreject
            have hpair : a.target = q' ∧ next = z' := by
              simpa only [ULogBootstrapExecution.Result.running.injEq] using h
            have haccept' : q' ≠ ULogControl.qAccept := by
              intro hq'
              exact haccept (hpair.1.trans hq')
            have hreject' : q' ≠ ULogControl.qReject := by
              intro hq'
              exact hreject (hpair.1.trans hq')
            exact ⟨a, hrule, happly.trans (congrArg some hpair.2),
              hpair.1, haccept', hreject'⟩
  · rintro ⟨a, hrule, happly, rfl, haccept, hreject⟩
    simp [ULogBootstrapExecution.oneStep, hrule, happly, haccept, hreject]

/-- Deterministic finite `U_log` reachability between running configurations
lifts compositionally to a literal occupied-arrow run of the outer M-star
machine. -/
theorem ulogReaches_running_outer
    (q q' : ULogControl.State) (origin : Int)
    (z z' : MStarParserExecution.Zipper ULogProgram.Tape)
    (hreach : ULogBootstrapExecution.Reaches (.running q z) (.running q' z')) :
    OuterReaches (anchoredULogConfig q origin z)
      (anchoredULogConfig q' origin z') := by
  rcases hreach with ⟨fuel, hrun⟩
  induction fuel generalizing q z with
  | zero =>
      simp only [ULogBootstrapExecution.run] at hrun
      cases hrun
      exact outerReaches_refl _
  | succ fuel ih =>
      change ULogBootstrapExecution.run fuel
        (ULogBootstrapExecution.oneStep (.running q z)) =
          .running q' z' at hrun
      cases hfirst : ULogBootstrapExecution.oneStep (.running q z) with
      | accepted za => simp [hfirst] at hrun
      | rejected => simp [hfirst] at hrun
      | stuck => simp [hfirst] at hrun
      | running q₁ z₁ =>
          have htail : ULogBootstrapExecution.run fuel (.running q₁ z₁) =
              .running q' z' := by simpa [hfirst] using hrun
          rcases (ulogOneStep_eq_running_iff q q₁ z z₁).mp hfirst with
            ⟨a, hrule, happly, htarget, haccept, hreject⟩
          exact outerReaches_trans
            (runningStep_outer q q₁ origin z z₁ a hrule happly
              htarget haccept hreject)
            (ih q₁ z₁ htail)

/-- The same reachability lift while preserving arbitrary physical framing
lists beyond the finite core zipper. -/
theorem ulogReaches_running_outer_framed
    (q q' : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z z' : MStarParserExecution.Zipper ULogProgram.Tape)
    (hreach : ULogBootstrapExecution.Reaches (.running q z) (.running q' z')) :
    OuterReaches
      (anchoredFramedULogConfig q origin leftExtra rightExtra z)
      (anchoredFramedULogConfig q' origin leftExtra rightExtra z') := by
  rcases hreach with ⟨fuel, hrun⟩
  induction fuel generalizing q z with
  | zero =>
      simp only [ULogBootstrapExecution.run] at hrun
      cases hrun
      exact outerReaches_refl _
  | succ fuel ih =>
      change ULogBootstrapExecution.run fuel
        (ULogBootstrapExecution.oneStep (.running q z)) =
          .running q' z' at hrun
      cases hfirst : ULogBootstrapExecution.oneStep (.running q z) with
      | accepted za => simp [hfirst] at hrun
      | rejected => simp [hfirst] at hrun
      | stuck => simp [hfirst] at hrun
      | running q₁ z₁ =>
          have htail : ULogBootstrapExecution.run fuel (.running q₁ z₁) =
              .running q' z' := by simpa [hfirst] using hrun
          rcases (ulogOneStep_eq_running_iff q q₁ z z₁).mp hfirst with
            ⟨a, hrule, happly, htarget, haccept, hreject⟩
          exact outerReaches_trans
            (framedRunningStep_outer q q₁ 0 origin leftExtra rightExtra
              z z₁ a hrule happly htarget haccept hreject)
            (ih q₁ z₁ htail)

theorem copiedULogStart_outer_reaches_semanticStart
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (origin : Int) (leftExtra rightExtra : List OuterTape) :
    OuterReaches
      (anchoredFramedULogConfig ULogControl.qStart origin leftExtra rightExtra
        (copiedULogStartZipper x))
      (anchoredFramedULogConfig ULogControl.State.cycleStart origin
        leftExtra rightExtra
        (copiedSemanticStartZipper x rules input padding)) := by
  apply ulogReaches_running_outer_framed
  have h := copiedULogStart_reaches_semanticStart x rules input padding hword
  rw [copiedSemanticStartEncoding_eq_running] at h
  exact h

/-- Scanner, parser, copier, and deterministic universal bootstrap now form
one literal outer-machine arrow path to the semantic cycle-start frame. -/
theorem sideStart_reaches_outerSemanticStart
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    ∃ origin leftExtra,
      OuterReaches (PakSideScannerRow.sideEncodedStartConfig x)
        (anchoredFramedULogConfig ULogControl.State.cycleStart origin leftExtra
          (.markR :: PakSideScanner.sideCopierHashTail x)
          (copiedSemanticStartZipper x rules input padding)) := by
  rcases PakParserOuterBridge.sideStartParserCopier_reaches_outerGroupReady_arrowList x with
    ⟨d, arrows, z, hd, hrun⟩
  rcases canonicalGroupReady_outer_eq_framedULogStart x z d hd with
    ⟨origin, leftExtra, hdEq⟩
  refine ⟨origin, leftExtra, outerReaches_trans ⟨arrows, hrun⟩ ?_⟩
  rw [hdEq]
  exact copiedULogStart_outer_reaches_semanticStart x rules input padding
    hword origin leftExtra (.markR :: PakSideScanner.sideCopierHashTail x)

end PakFixedPolyomino.PakOuterULogBridge
