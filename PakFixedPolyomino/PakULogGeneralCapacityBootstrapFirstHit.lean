import PakFixedPolyomino.PakULogGeneralCapacityBootstrap
import PakFixedPolyomino.PakOuterULogReflection
import PakFixedPolyomino.PakULogBootstrapExplicitFuel

/-! # First concrete cycle hit for the general-capacity bootstrap

This companion isolates the only proof obligation which is stronger than the
legacy bootstrap `Reaches` statement.  A run ending at `cycleStart` is a
genuine first hit as soon as all of its strict iterates are still in the
finite bootstrap-control region.  The lemma is deliberately parameterised by
that prefix certificate: it can be fed by an explicit-fuel decomposition
without converting a `Reaches` witness into an unsound first-hit witness.
-/

namespace PakFixedPolyomino.PakULogGeneralCapacityBootstrapFirstHit

open ULogAlphabet ULogProgram
open PakOuterULogReflection
open PakULogGeneralCapacityBootstrap

abbrev Result := ULogBootstrapExecution.Result
abbrev Zipper := MStarParserExecution.Zipper ULogProgram.Tape

def IsBootstrapRunning : Result → Prop
  | .running q _ => BootstrapControl q = true
  | _ => False

/-- The fully explicit deterministic fuel ledger transports unchanged to a
general physical capacity; only the final all-work tail is parameterised by
that capacity. -/
def generalCapacityBootstrapAllFuel
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) : ℕ :=
  PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 5 +
    PakULogBootstrapExplicitFuel.runtimeAllFuel rules input padding

def generalCapacityBootstrapPreCycleFuel
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) : ℕ :=
  PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 5 +
    PakULogBootstrapExplicitFuel.programPayloadFuel rules +
      PakULogBootstrapExplicitFuel.payloadClockFuel input padding +
        (match input with
        | [] => 3 * padding.length + 24
        | _ :: bs => bs.length + 1 + padding.length + 12)

/-- The nonempty-input initialization suffix with its final `readHead` action
removed.  Its endpoint is the single bootstrap-controlled predecessor of the
first semantic `cycleStart`. -/
theorem run_initializedRuntime_nonempty_preCycle_exact
    (b : Bool) (bs padding : List Bool)
    (base tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run ((b :: bs).length + padding.length + 12)
      (ULogBootstrapExecution.initializedPowerClock padding
        (ULogBootstrapExecution.payloadFoldedLeft (b :: bs) base)
        (ULogBootstrapExecution.initializationWorkspace (b :: bs) tail)) =
      .running ULogControl.State.readHead
        ⟨ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
            (List.replicate bs.length (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++
              ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base),
          ULogProgram.payloadTape b,
          bs.map ULogProgram.payloadTape ++
            ULogBootstrapExecution.runtimeSuffix padding tail⟩ := by
  let seekPath := ULogBootstrapExecution.headSeekPath padding (b :: bs)
  let payloadBase :=
    List.replicate bs.length (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++
      ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base
  have hframe : ULogBootstrapExecution.run 6
      (ULogBootstrapExecution.initializedPowerClock padding
        (ULogBootstrapExecution.payloadFoldedLeft (b :: bs) base)
        (ULogBootstrapExecution.initializationWorkspace (b :: bs) tail)) =
      .running ULogControl.State.seekSimHead
        (ULogBootstrapExecution.beforeLeftPath seekPath payloadBase
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
          (ULogAlphabet.ulogCore ULogAlphabet.stateSep :: tail)) := by
    simp [ULogBootstrapExecution.run,
      ULogBootstrapExecution.initializedPowerClock,
      ULogBootstrapExecution.payloadFoldedLeft,
      ULogBootstrapExecution.initializationWorkspace,
      ULogBootstrapExecution.headSeekPath,
      ULogBootstrapExecution.beforeLeftPath, seekPath, payloadBase,
      ULogBootstrapExecution.initializeState_step,
      ULogBootstrapExecution.initStateCell_zero_step,
      ULogBootstrapExecution.initStateCell_one_step,
      ULogBootstrapExecution.initStateCell_two_step,
      ULogBootstrapExecution.initStateCell_three_step,
      ULogBootstrapExecution.initStateCell_four_step,
      List.replicate_succ, List.append_assoc]
  have hscan : ULogBootstrapExecution.run seekPath.length
      (.running ULogControl.State.seekSimHead
        (ULogBootstrapExecution.beforeLeftPath seekPath payloadBase
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
          (ULogAlphabet.ulogCore ULogAlphabet.stateSep :: tail))) =
      .running ULogControl.State.seekSimHead
        (ULogBootstrapExecution.afterLeftPath seekPath payloadBase
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
          (ULogAlphabet.ulogCore ULogAlphabet.stateSep :: tail)) :=
    ULogBootstrapExecution.run_left_path_of ULogControl.State.seekSimHead seekPath
      (ULogBootstrapExecution.headSeekPath_pass padding (b :: bs)) payloadBase
      (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
      (ULogAlphabet.ulogCore ULogAlphabet.stateSep :: tail)
  have htoHead : ULogBootstrapExecution.run 1
      (.running ULogControl.State.seekSimHead
        (ULogBootstrapExecution.afterLeftPath seekPath payloadBase
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
          (ULogAlphabet.ulogCore ULogAlphabet.stateSep :: tail))) =
      .running ULogControl.State.readHead
        ⟨ULogAlphabet.ulogCore ULogAlphabet.payloadEnd :: payloadBase,
          ULogProgram.payloadTape b,
          bs.map ULogProgram.payloadTape ++
            ULogBootstrapExecution.runtimeSuffix padding tail⟩ := by
    simp only [ULogBootstrapExecution.run]
    rw [show ULogBootstrapExecution.afterLeftPath seekPath payloadBase
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
          (ULogAlphabet.ulogCore ULogAlphabet.stateSep :: tail) =
        ⟨payloadBase, ULogAlphabet.ulogCore ULogAlphabet.payloadEnd,
          seekPath.reverse ++ ULogAlphabet.ulogCore ULogAlphabet.stateSep :: tail⟩ by rfl]
    rw [show seekPath = ULogBootstrapExecution.headSeekPath padding (b :: bs) by rfl,
      ULogBootstrapExecution.headSeekPath_reverse_append]
    simpa [ULogBootstrapExecution.runtimeSuffix, List.append_assoc] using
      (ULogBootstrapExecution.seekSimHead_payloadEnd_step payloadBase
        (ULogProgram.payloadTape b)
        (bs.map ULogProgram.payloadTape ++
          ULogBootstrapExecution.runtimeSuffix padding tail))
  rw [show (b :: bs).length + padding.length + 12 =
      6 + (seekPath.length + 1) by
        simp [seekPath, ULogBootstrapExecution.headSeekPath]; omega]
  rw [ULogBootstrapExecution.run_add, hframe,
    ULogBootstrapExecution.run_add, hscan]
  simpa [payloadBase] using htoHead

/-- The final action of the empty-input right-shift suffix is likewise
separated: after the certified shift and return scan, control is still
`seekSimHead`; the next action alone creates `cycleStart`. -/
theorem run_initShiftRuntimeRight_preCycle_exact
    (carry : ULogProgram.Tape) (pre : List ULogProgram.Tape)
    (last : ULogProgram.Tape)
    (hshift : ULogBootstrapExecution.ShiftRuntimeSafe (pre ++ [last]))
    (hreturn : ULogBootstrapExecution.InitSeekReturnSafe
      (pre.reverse ++ [carry]))
    (left : List ULogProgram.Tape) (head : ULogProgram.Tape)
    (right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (2 * pre.length + 3)
      (.running (.shiftRuntime (.initRight carry))
        (ULogBootstrapExecution.beforeRightPath (pre ++ [last]) (head :: left)
          MStarConcreteAlphabet.work right)) =
      .running ULogControl.State.seekSimHead
        (ULogBootstrapExecution.afterLeftPath (pre.reverse ++ [carry]) left head
          (last :: right)) := by
  rw [show 2 * pre.length + 3 = (pre.length + 2) + (pre.length + 1) by omega,
    ULogBootstrapExecution.run_add,
    PakULogBootstrapExplicitFuel.run_initShiftRuntimeRight_exact carry pre last
      hshift left head right]
  simpa using ULogBootstrapExecution.run_left_path_of ULogControl.State.seekSimHead
    (pre.reverse ++ [carry])
    (by
      intro x hx l y r
      exact ULogBootstrapExecution.seekSimHead_init_pass x
        (hreturn x hx) l y r)
    left head (last :: right)

/-- Compose the program, payload-clock, and nonempty final-predecessor
ledgers.  This is the runtime part of the general bootstrap with precisely
its last `readHead` action omitted. -/
theorem run_runtime_nonempty_preCycle_exact
    (rules : List ULogBytecode.RuleCode) (b : Bool)
    (bs padding : List Bool) (left tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run
      (PakULogBootstrapExplicitFuel.programPayloadFuel rules +
        PakULogBootstrapExplicitFuel.payloadClockFuel (b :: bs) padding +
          ((b :: bs).length + padding.length + 12))
      (.running ULogControl.State.framePayloadLength
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          (ULogBytecode.encodeProgram rules ++
            ULogBytecode.encodePayload (b :: bs) padding).map
              ULogProgram.codeTape ++
            ULogAlphabet.ulogCore ULogAlphabet.codeEnd ::
              ULogBootstrapExecution.payloadRuntimeWorkspace (b :: bs) tail⟩) =
      .running ULogControl.State.readHead
        ⟨ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
            (List.replicate bs.length (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++
              ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone ::
                ULogBootstrapExecution.programMarkedLeft rules left),
          ULogProgram.payloadTape b,
          bs.map ULogProgram.payloadTape ++
            ULogBootstrapExecution.runtimeSuffix padding tail⟩ := by
  rw [show PakULogBootstrapExplicitFuel.programPayloadFuel rules +
      PakULogBootstrapExplicitFuel.payloadClockFuel (b :: bs) padding +
        ((b :: bs).length + padding.length + 12) =
      PakULogBootstrapExplicitFuel.programPayloadFuel rules +
        (PakULogBootstrapExplicitFuel.payloadClockFuel (b :: bs) padding +
          ((b :: bs).length + padding.length + 12)) by omega,
    ULogBootstrapExecution.run_add]
  simp only [ULogBootstrapExecution.payloadRuntimeWorkspace]
  rw [PakULogBootstrapExplicitFuel.run_programPayload_to_payloadStart_all_exact
      rules (b :: bs) padding left
      (ULogBootstrapExecution.initializationWorkspace (b :: bs) tail),
    ULogBootstrapExecution.run_add,
    PakULogBootstrapExplicitFuel.run_payloadClock_all_exact (b :: bs) padding
      (ULogBootstrapExecution.programMarkedLeft rules left)
      (ULogBootstrapExecution.initializationWorkspace (b :: bs) tail)]
  exact run_initializedRuntime_nonempty_preCycle_exact b bs padding
    (ULogBootstrapExecution.programMarkedLeft rules left) tail

/-- Empty-input initialization with the final boundary-creating action
removed. -/
theorem run_initializedRuntime_empty_preCycle_exact
    (padding : List Bool) (base tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (3 * padding.length + 24)
      (ULogBootstrapExecution.initializedPowerClock padding
        (ULogBootstrapExecution.payloadFoldedLeft [] base)
        (ULogBootstrapExecution.initializationWorkspace [] tail)) =
      .running ULogControl.State.seekSimHead
        (ULogBootstrapExecution.afterLeftPath
          ((ULogBootstrapExecution.emptyInitShiftPrefix padding).reverse ++
            [ULogBootstrapExecution.emptyInitBoundary padding])
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne :: base)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadHeadBlank)
          (ULogAlphabet.ulogCore ULogAlphabet.stateSep :: tail)) := by
  let seekPath := ULogBootstrapExecution.headSeekPath padding []
  let shiftPre := ULogBootstrapExecution.emptyInitShiftPrefix padding
  let boundary := ULogBootstrapExecution.emptyInitBoundary padding
  have hprelen : shiftPre.length = padding.length + 4 := by
    cases padding <;> simp [shiftPre, ULogBootstrapExecution.emptyInitShiftPrefix]
  have hframe : ULogBootstrapExecution.run 6
      (ULogBootstrapExecution.initializedPowerClock padding
        (ULogBootstrapExecution.payloadFoldedLeft [] base)
        (ULogBootstrapExecution.initializationWorkspace [] tail)) =
      .running ULogControl.State.seekSimHead
        (ULogBootstrapExecution.beforeLeftPath seekPath base
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne)
          (ULogAlphabet.ulogCore ULogAlphabet.stateSep ::
            MStarConcreteAlphabet.work :: tail)) := by
    simp [ULogBootstrapExecution.run,
      ULogBootstrapExecution.initializedPowerClock,
      ULogBootstrapExecution.payloadFoldedLeft,
      ULogBootstrapExecution.initializationWorkspace,
      ULogBootstrapExecution.headSeekPath,
      ULogBootstrapExecution.beforeLeftPath, seekPath,
      ULogBootstrapExecution.initializeState_step,
      ULogBootstrapExecution.initStateCell_zero_step,
      ULogBootstrapExecution.initStateCell_one_step,
      ULogBootstrapExecution.initStateCell_two_step,
      ULogBootstrapExecution.initStateCell_three_step,
      ULogBootstrapExecution.initStateCell_four_step,
      List.replicate_succ, List.append_assoc]
  have hscan : ULogBootstrapExecution.run seekPath.length
      (.running ULogControl.State.seekSimHead
        (ULogBootstrapExecution.beforeLeftPath seekPath base
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne)
          (ULogAlphabet.ulogCore ULogAlphabet.stateSep ::
            MStarConcreteAlphabet.work :: tail))) =
      .running ULogControl.State.seekSimHead
        (ULogBootstrapExecution.afterLeftPath seekPath base
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne)
          (ULogAlphabet.ulogCore ULogAlphabet.stateSep ::
            MStarConcreteAlphabet.work :: tail)) :=
    ULogBootstrapExecution.run_left_path_of ULogControl.State.seekSimHead
      seekPath (ULogBootstrapExecution.headSeekPath_pass padding []) base
      (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne)
      (ULogAlphabet.ulogCore ULogAlphabet.stateSep ::
        MStarConcreteAlphabet.work :: tail)
  have hread : ULogBootstrapExecution.run 2
      (.running ULogControl.State.seekSimHead
        (ULogBootstrapExecution.afterLeftPath seekPath base
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne)
          (ULogAlphabet.ulogCore ULogAlphabet.stateSep ::
            MStarConcreteAlphabet.work :: tail))) =
      .running (.shiftRuntime (.initRight boundary))
        (ULogBootstrapExecution.beforeRightPath
          (shiftPre ++ [ULogAlphabet.ulogCore ULogAlphabet.stateSep])
          (ULogAlphabet.ulogCore ULogAlphabet.payloadHeadBlank ::
            ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne :: base)
          MStarConcreteAlphabet.work tail) := by
    rw [show 2 = 1 + 1 by omega, ULogBootstrapExecution.run_add]
    simp only [ULogBootstrapExecution.run]
    rw [show ULogBootstrapExecution.afterLeftPath seekPath base
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne)
          (ULogAlphabet.ulogCore ULogAlphabet.stateSep ::
            MStarConcreteAlphabet.work :: tail) =
        ⟨base, ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne,
          seekPath.reverse ++ ULogAlphabet.ulogCore ULogAlphabet.stateSep ::
            MStarConcreteAlphabet.work :: tail⟩ by rfl]
    rw [show seekPath = ULogBootstrapExecution.headSeekPath padding [] by rfl,
      ULogBootstrapExecution.headSeekPath_reverse_append,
      ULogBootstrapExecution.runtimeSuffix_emptyInit]
    simp only [List.map_nil, List.nil_append]
    have hseek := ULogBootstrapExecution.seekSimHead_empty_step base boundary
      (shiftPre ++ ULogAlphabet.ulogCore ULogAlphabet.stateSep ::
        MStarConcreteAlphabet.work :: tail)
    change ULogBootstrapExecution.oneStep
        (ULogBootstrapExecution.oneStep
          (.running ULogControl.State.seekSimHead
            ⟨base, ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne,
              boundary :: shiftPre ++ ULogAlphabet.ulogCore ULogAlphabet.stateSep ::
                MStarConcreteAlphabet.work :: tail⟩)) = _
    simp only [List.cons_append] at hseek ⊢
    rw [hseek]
    cases hp : shiftPre with
    | nil =>
        simpa [ULogBootstrapExecution.beforeRightPath, hp] using
          (ULogBootstrapExecution.readHead_empty_boundary boundary
            (ULogBootstrapExecution.emptyInit_boundary padding) base
            (ULogAlphabet.ulogCore ULogAlphabet.stateSep)
            (MStarConcreteAlphabet.work :: tail))
    | cons y ys =>
        simpa [ULogBootstrapExecution.beforeRightPath, hp, List.append_assoc] using
          (ULogBootstrapExecution.readHead_empty_boundary boundary
            (ULogBootstrapExecution.emptyInit_boundary padding) base y
            (ys ++ ULogAlphabet.ulogCore ULogAlphabet.stateSep ::
              MStarConcreteAlphabet.work :: tail))
  have hshift := run_initShiftRuntimeRight_preCycle_exact boundary shiftPre
    (ULogAlphabet.ulogCore ULogAlphabet.stateSep)
    (by simpa [shiftPre, boundary] using
      ULogBootstrapExecution.emptyInit_shift_safe padding)
    (by simpa [shiftPre, boundary] using
      ULogBootstrapExecution.emptyInit_return_safe padding)
    (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne :: base)
    (ULogAlphabet.ulogCore ULogAlphabet.payloadHeadBlank) tail
  rw [show 3 * padding.length + 24 =
      6 + (seekPath.length + (2 + (2 * shiftPre.length + 3))) by
        simp [seekPath, ULogBootstrapExecution.headSeekPath, hprelen]; omega,
    ULogBootstrapExecution.run_add, hframe,
    ULogBootstrapExecution.run_add, hscan,
    ULogBootstrapExecution.run_add, hread,
    hshift]

theorem run_runtime_empty_preCycle_exact
    (rules : List ULogBytecode.RuleCode) (padding : List Bool)
    (left tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run
      (PakULogBootstrapExplicitFuel.programPayloadFuel rules +
        PakULogBootstrapExplicitFuel.payloadClockFuel [] padding +
          (3 * padding.length + 24))
      (.running ULogControl.State.framePayloadLength
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          (ULogBytecode.encodeProgram rules ++
            ULogBytecode.encodePayload [] padding).map ULogProgram.codeTape ++
            ULogAlphabet.ulogCore ULogAlphabet.codeEnd ::
              ULogBootstrapExecution.payloadRuntimeWorkspace [] tail⟩) =
      .running ULogControl.State.seekSimHead
        (ULogBootstrapExecution.afterLeftPath
          ((ULogBootstrapExecution.emptyInitShiftPrefix padding).reverse ++
            [ULogBootstrapExecution.emptyInitBoundary padding])
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne ::
            ULogBootstrapExecution.programMarkedLeft rules left)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadHeadBlank)
          (ULogAlphabet.ulogCore ULogAlphabet.stateSep :: tail)) := by
  rw [show PakULogBootstrapExplicitFuel.programPayloadFuel rules +
      PakULogBootstrapExplicitFuel.payloadClockFuel [] padding +
        (3 * padding.length + 24) =
      PakULogBootstrapExplicitFuel.programPayloadFuel rules +
        (PakULogBootstrapExplicitFuel.payloadClockFuel [] padding +
          (3 * padding.length + 24)) by omega,
    ULogBootstrapExecution.run_add]
  simp only [ULogBootstrapExecution.payloadRuntimeWorkspace]
  rw [PakULogBootstrapExplicitFuel.run_programPayload_to_payloadStart_all_exact
      rules [] padding left (ULogBootstrapExecution.initializationWorkspace [] tail),
    ULogBootstrapExecution.run_add,
    PakULogBootstrapExplicitFuel.run_payloadClock_all_exact [] padding
      (ULogBootstrapExecution.programMarkedLeft rules left)
      (ULogBootstrapExecution.initializationWorkspace [] tail)]
  exact run_initializedRuntime_empty_preCycle_exact padding
    (ULogBootstrapExecution.programMarkedLeft rules left) tail

theorem generalCapacity_preCycle_isBootstrapRunning
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (physicalCapacity : ℕ)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (hcapacity : bootstrapWorkspaceOverhead input ≤ physicalCapacity) :
    IsBootstrapRunning (ULogBootstrapExecution.run
      (generalCapacityBootstrapPreCycleFuel x rules input padding)
      (.running ULogControl.qStart
        (generalCapacityCoreZipper x physicalCapacity))) := by
  rw [generalCapacityCoreZipper_eq_bootstrap x rules input padding
    physicalCapacity hword hcapacity]
  have hne : x ≠ [] := by
    intro hx
    apply ULogBootstrapExecution.encodedUniversalInput_ne_nil rules input padding
    rw [← hword, hx]
  cases x with
  | nil => exact (hne rfl).elim
  | cons wb wbits =>
      have heq : wb :: wbits = ULogBytecode.encodeProgram rules ++
          ULogBytecode.encodePayload input padding := hword
      cases input with
      | nil =>
          have hpreamble := PakULogBootstrapExplicitFuel.run_bootstrap_workspace_exact
            (PakOuterULogBridge.copiedCoreRadius (wb :: wbits)) wb wbits []
            (ULogBootstrapExecution.payloadRuntimeWorkspace []
              (generalBootstrapTail [] physicalCapacity))
          have hrun := run_runtime_empty_preCycle_exact rules padding
            (List.replicate (PakOuterULogBridge.copiedCoreRadius (wb :: wbits))
              MStarConcreteAlphabet.work)
            (generalBootstrapTail [] physicalCapacity)
          rw [← heq] at hrun ⊢
          unfold generalCapacityBootstrapPreCycleFuel
          rw [show PakOuterULogBridge.copiedCoreRadius (wb :: wbits) +
              2 * (wb :: wbits).length + 5 +
              PakULogBootstrapExplicitFuel.programPayloadFuel rules +
                PakULogBootstrapExplicitFuel.payloadClockFuel [] padding +
                  (3 * padding.length + 24) =
              (PakOuterULogBridge.copiedCoreRadius (wb :: wbits) +
                2 * (wb :: wbits).length + 5) +
                (PakULogBootstrapExplicitFuel.programPayloadFuel rules +
                  PakULogBootstrapExplicitFuel.payloadClockFuel [] padding +
                    (3 * padding.length + 24)) by omega,
            ULogBootstrapExecution.run_add]
          simp only [ULogControl.qStart, List.map_cons, List.cons_append,
            List.append_assoc] at hpreamble ⊢
          rw [hpreamble]
          simp only [List.append_nil, List.map_cons, List.cons_append,
            List.append_assoc] at hrun ⊢
          rw [hrun]
          change BootstrapControl ULogControl.State.seekSimHead = true
          rfl
      | cons ib ibs =>
          have hpreamble := PakULogBootstrapExplicitFuel.run_bootstrap_workspace_exact
            (PakOuterULogBridge.copiedCoreRadius (wb :: wbits)) wb wbits []
            (ULogBootstrapExecution.payloadRuntimeWorkspace (ib :: ibs)
              (generalBootstrapTail (ib :: ibs) physicalCapacity))
          have hrun := run_runtime_nonempty_preCycle_exact rules ib ibs padding
            (List.replicate (PakOuterULogBridge.copiedCoreRadius (wb :: wbits))
              MStarConcreteAlphabet.work)
            (generalBootstrapTail (ib :: ibs) physicalCapacity)
          rw [← heq] at hrun ⊢
          unfold generalCapacityBootstrapPreCycleFuel
          rw [show PakOuterULogBridge.copiedCoreRadius (wb :: wbits) +
              2 * (wb :: wbits).length + 5 +
              PakULogBootstrapExplicitFuel.programPayloadFuel rules +
                PakULogBootstrapExplicitFuel.payloadClockFuel (ib :: ibs) padding +
                  (ibs.length + 1 + padding.length + 12) =
              (PakOuterULogBridge.copiedCoreRadius (wb :: wbits) +
                2 * (wb :: wbits).length + 5) +
                (PakULogBootstrapExplicitFuel.programPayloadFuel rules +
                  PakULogBootstrapExplicitFuel.payloadClockFuel (ib :: ibs) padding +
                    ((ib :: ibs).length + padding.length + 12)) by simp; omega,
            ULogBootstrapExecution.run_add]
          simp only [ULogControl.qStart, List.map_cons, List.cons_append,
            List.append_assoc] at hpreamble ⊢
          rw [hpreamble]
          simp only [List.append_nil, List.map_cons, List.cons_append,
            List.append_assoc] at hrun ⊢
          rw [hrun]
          change BootstrapControl ULogControl.State.readHead = true
          rfl

/-- A strict prefix of the deterministic bootstrap run remains in the
bootstrap-only control region.  The existential zipper is intentionally
exposed: the control invariant is about the real iterate of `run`, rather
than a separately chosen abstract state sequence. -/
def BootstrapRunPrefix (start : Result) (steps : ℕ) : Prop :=
  ∀ m, m < steps → ∃ q z,
    ULogBootstrapExecution.run m start = .running q z ∧
      BootstrapControl q = true

/-- Bool test over only the fetched Option action.  `none` is vacuously
closed, so `decide` enumerates `State × Tape × Fin 2` rather than the
whole `Action` domain. -/
def bootstrapSourceOk (q : ULogControl.State) (x : ULogProgram.Tape)
    (slot : Fin 2) : Bool :=
  match ULogProgram.program.rule q x slot with
  | none => true
  | some a =>
      if BootstrapControl a.target then BootstrapControl q else true

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem bootstrap_source_closed_table_test :
    ∀ (q : ULogControl.State) (x : ULogProgram.Tape) (slot : Fin 2),
      bootstrapSourceOk q x slot = true := by
  decide

/-- The literal table has no edge from the semantic-cycle controls back into
the bootstrap-only controls.  This is the reverse half of the control cut
used when a stage endpoint is itself still bootstrap-controlled. -/
private theorem bootstrap_source_closed_table :
    ∀ (q : ULogControl.State) (x : ULogProgram.Tape) (slot : Fin 2)
      (act : FiniteOneTapeProgram.Action ULogControl.State ULogProgram.Tape),
      ULogProgram.program.rule q x slot = some act →
      BootstrapControl act.target = true → BootstrapControl q = true := by
  intro q x slot act hrule ht
  have tested := bootstrap_source_closed_table_test q x slot
  simpa [bootstrapSourceOk, hrule, ht] using tested

private theorem validStep_running_rule_target
    (q q' : ULogControl.State) (z z' : Zipper) (slot : Fin 2)
    (hstep : ULogBootstrapExecution.validStepAt slot (.running q z) =
      some (.running q' z')) :
    ∃ act, ULogProgram.program.rule q z.focus slot = some act ∧
      act.target = q' := by
  simp only [ULogBootstrapExecution.validStepAt] at hstep
  cases hrule : ULogProgram.program.rule q z.focus slot with
  | none => simp [hrule] at hstep
  | some act =>
      refine ⟨act, rfl, ?_⟩
      have hnext : ULogBootstrapExecution.Result.running q' z' =
          ULogBootstrapExecution.oneStepAt slot (.running q z) := by
        apply Option.some.inj
        simpa [hrule] using hstep.symm
      cases happly : MStarParserExecution.applyAction z act with
      | none => simp [ULogBootstrapExecution.oneStepAt, hrule, happly] at hnext
      | some out =>
          have hnotaccept : act.target ≠ ULogControl.qAccept := by
            intro htarget
            simp [ULogBootstrapExecution.oneStepAt, hrule, happly,
              htarget] at hnext
          have hnotreject : act.target ≠ ULogControl.qReject := by
            intro htarget
            simp [ULogBootstrapExecution.oneStepAt, hrule, happly,
              htarget, show ULogControl.qReject ≠ ULogControl.qAccept by decide] at hnext
          have hnext' : ULogBootstrapExecution.Result.running q' z' =
              ULogBootstrapExecution.Result.running act.target out := by
            simpa [ULogBootstrapExecution.oneStepAt, hrule, happly,
              hnotaccept, hnotreject] using hnext
          injection hnext' with hq _
          exact hq.symm

/-- Backwards table closure upgrades a valid zero-run ending in a bootstrap
control to a control certificate for every iterate, including its endpoint. -/
theorem isBootstrapRunning_of_validZeroRun_finish_bootstrap :
    ∀ {n : ℕ} {start finish : Result},
      ULogBootstrapExecution.ValidZeroRun n start finish →
      IsBootstrapRunning finish →
      ∀ m, m ≤ n → IsBootstrapRunning (ULogBootstrapExecution.run m start) := by
  intro n start finish hvalid
  induction hvalid with
  | nil r =>
      intro hboot m hm
      have hmzero : m = 0 := Nat.eq_zero_of_le_zero hm
      subst m
      change IsBootstrapRunning r
      exact hboot
  | cons r next finish n hhead htail ih =>
      intro hboot m hm
      have htailPrefix := ih hboot
      cases m with
      | zero =>
          have hnextBoot : IsBootstrapRunning next := by
            simpa only [ULogBootstrapExecution.run] using htailPrefix 0 (by omega)
          cases r with
          | accepted za => simp [ULogBootstrapExecution.validStepAt] at hhead
          | rejected => simp [ULogBootstrapExecution.validStepAt] at hhead
          | stuck => simp [ULogBootstrapExecution.validStepAt] at hhead
          | running qstart zstart =>
              cases next with
              | accepted za => simp [IsBootstrapRunning] at hnextBoot
              | rejected => simp [IsBootstrapRunning] at hnextBoot
              | stuck => simp [IsBootstrapRunning] at hnextBoot
              | running qnext znext =>
                  rcases validStep_running_rule_target qstart qnext zstart znext 0
                    hhead with ⟨act, hrule, htarget⟩
                  exact bootstrap_source_closed_table qstart zstart.focus 0 act
                    hrule (htarget ▸ hnextBoot)
      | succ m =>
          have hm' : m ≤ n := by omega
          simpa only [ULogBootstrapExecution.run,
            ULogBootstrapExecution.validStepAt_zero_some_eq_oneStep hhead] using
              htailPrefix m hm'

theorem bootstrapRunPrefix_le_of_validZeroRun_finish_bootstrap
    {n : ℕ} {start : Result} {q : ULogControl.State} {z : Zipper}
    (hvalid : ULogBootstrapExecution.ValidZeroRun n start (.running q z))
    (hboot : BootstrapControl q = true) :
    ∀ m, m ≤ n → ∃ q' z',
      ULogBootstrapExecution.run m start = .running q' z' ∧
        BootstrapControl q' = true := by
  intro m hm
  have hstate := isBootstrapRunning_of_validZeroRun_finish_bootstrap hvalid hboot m hm
  cases hrun : ULogBootstrapExecution.run m start with
  | accepted za => simp [hrun, IsBootstrapRunning] at hstate
  | rejected => simp [hrun, IsBootstrapRunning] at hstate
  | stuck => simp [hrun, IsBootstrapRunning] at hstate
  | running q' z' =>
      rw [hrun] at hstate
      exact ⟨q', z', rfl, hstate⟩

/-- To turn a valid run ending at the boundary into an exact first hit, the
only additional datum needed is that its *penultimate* iterate is bootstrap
controlled.  The reverse table certificate above then supplies every earlier
strict iterate automatically. -/
def firstValidZeroHit_of_validZeroRun_penultimate_bootstrap
    {steps : ℕ} {start : Result} {cycleZ : Zipper}
    (hpositive : 0 < steps)
    (hvalid : ULogBootstrapExecution.ValidZeroRun steps start
      (.running .cycleStart cycleZ))
    (hpenultimate : IsBootstrapRunning
      (ULogBootstrapExecution.run (steps - 1) start)) :
    ULogBootstrapExecution.FirstValidZeroHit
      ULogBootstrapExecution.IsConcreteCycleBoundary start
      (.running .cycleStart cycleZ) := by
  refine
    { steps := steps
      valid := hvalid
      hit := by simp [ULogBootstrapExecution.IsConcreteCycleBoundary]
      before := ?_ }
  intro m hm hboundary
  have hmle : m ≤ steps - 1 := by omega
  have hprefixValid := hvalid.prefix (Nat.sub_le steps 1)
  cases hiter : ULogBootstrapExecution.run (steps - 1) start with
  | accepted za => simp [hiter, IsBootstrapRunning] at hpenultimate
  | rejected => simp [hiter, IsBootstrapRunning] at hpenultimate
  | stuck => simp [hiter, IsBootstrapRunning] at hpenultimate
  | running qpen zpen =>
      rw [hiter] at hprefixValid hpenultimate
      have hprefix := bootstrapRunPrefix_le_of_validZeroRun_finish_bootstrap
        hprefixValid hpenultimate m hmle
      rcases hprefix with ⟨q, z, hrun, hboot⟩
      rw [hrun] at hboundary
      exact bootstrap_ne_cycleStart hboot
        ((isConcreteCycleBoundary_running_iff q z).mp hboundary)

/-- Local closure in the form needed for an explicit run induction.  Unlike
`bootstrap_validStep_nonboundary_live`, no accepting suffix is required:
here the successor itself is known to remain running. -/
theorem bootstrap_validStep_running_split
    (q q' : ULogControl.State) (z z' : Zipper) (slot : Fin 2)
    (hboot : BootstrapControl q = true)
    (hstep : ULogBootstrapExecution.validStepAt slot (.running q z) =
      some (.running q' z')) :
    q' = .cycleStart ∨ BootstrapControl q' = true := by
  simp only [ULogBootstrapExecution.validStepAt] at hstep
  cases hrule : ULogProgram.program.rule q z.focus slot with
  | none => simp [hrule] at hstep
  | some act =>
      have hnext : .running q' z' =
          ULogBootstrapExecution.oneStepAt slot (.running q z) := by
        have hs : some (.running q' z') =
            some (ULogBootstrapExecution.oneStepAt slot (.running q z)) := by
          simpa [hrule] using hstep.symm
        exact Option.some.inj hs
      cases happly : MStarParserExecution.applyAction z act with
      | none =>
          simp [ULogBootstrapExecution.oneStepAt, hrule, happly] at hnext
      | some out =>
          have hnotaccept : act.target ≠ ULogControl.qAccept := by
            intro htarget
            simp [ULogBootstrapExecution.oneStepAt, hrule, happly,
              htarget] at hnext
          have hnotreject : act.target ≠ ULogControl.qReject := by
            intro htarget
            simp [ULogBootstrapExecution.oneStepAt, hrule, happly,
              htarget, show ULogControl.qReject ≠ ULogControl.qAccept by decide] at hnext
          have hnext' : ULogBootstrapExecution.Result.running q' z' =
              ULogBootstrapExecution.Result.running act.target out := by
            simpa [ULogBootstrapExecution.oneStepAt, hrule, happly,
              hnotaccept, hnotreject] using hnext
          have htarget : q' = act.target := by
            injection hnext'
          rcases bootstrap_target_closed q z.focus slot act hboot hrule with
            hreject | hcycle | hbootTarget
          · exact (hnotreject hreject).elim
          · exact Or.inl (htarget.trans hcycle)
          · exact Or.inr (htarget.symm ▸ hbootTarget)

/-- A running `cycleStart` endpoint together with a real bootstrap-control
certificate on every strict iterate gives the required genuine first valid
slot-zero hit. -/
def firstValidZeroHit_of_run_and_bootstrapPrefix
    (start : Result) (steps : ℕ) (cycleZ : Zipper)
    (hrun : ULogBootstrapExecution.run steps start =
      .running .cycleStart cycleZ)
    (hprefix : BootstrapRunPrefix start steps) :
    ULogBootstrapExecution.FirstValidZeroHit
      ULogBootstrapExecution.IsConcreteCycleBoundary start
      (.running .cycleStart cycleZ) := by
  refine
    { steps := steps
      valid := ULogBootstrapExecution.validZeroRun_of_run_eq_running hrun
      hit := by simp [ULogBootstrapExecution.IsConcreteCycleBoundary]
      before := ?_ }
  intro m hm hboundary
  rcases hprefix m hm with ⟨q, z, hiterate, hboot⟩
  rw [hiterate] at hboundary
  exact bootstrap_ne_cycleStart hboot
    ((isConcreteCycleBoundary_running_iff q z).mp hboundary)

/-- A `Reaches` witness whose chosen run has the bootstrap-prefix invariant
can be upgraded without changing its concrete endpoint. -/
noncomputable def firstValidZeroHit_of_reaches_and_bootstrapPrefix
    (start : Result) (cycleZ : Zipper)
    (hreaches : ULogBootstrapExecution.Reaches start (.running .cycleStart cycleZ))
    (hprefix : ∀ steps,
      ULogBootstrapExecution.run steps start = .running .cycleStart cycleZ →
      BootstrapRunPrefix start steps) :
    ULogBootstrapExecution.FirstValidZeroHit
      ULogBootstrapExecution.IsConcreteCycleBoundary start
      (.running .cycleStart cycleZ) := by
  classical
  let steps := Classical.choose hreaches
  have hrun : ULogBootstrapExecution.run steps start =
      .running .cycleStart cycleZ := Classical.choose_spec hreaches
  exact firstValidZeroHit_of_run_and_bootstrapPrefix start steps cycleZ hrun
    (hprefix steps hrun)

/-- The general-capacity forward bootstrap obtains the desired literal first
hit once its explicit fuel is accompanied by the corresponding strict-prefix
control trace.  This is the endpoint used by the capacity-indexed semantic
normal form. -/
def generalCapacity_firstValidZeroHit_of_explicitPrefix
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (physicalCapacity : ℕ)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (hcapacity : bootstrapWorkspaceOverhead input ≤ physicalCapacity)
    (steps : ℕ)
    (hrun : ULogBootstrapExecution.run steps
      (.running ULogControl.qStart
        (generalCapacityCoreZipper x physicalCapacity)) =
      (generalCapacitySemanticFrame x rules input padding physicalCapacity).encode)
    (hprefix : BootstrapRunPrefix
      (.running ULogControl.qStart
        (generalCapacityCoreZipper x physicalCapacity)) steps) :
    ULogBootstrapExecution.FirstValidZeroHit
      ULogBootstrapExecution.IsConcreteCycleBoundary
      (.running ULogControl.qStart
        (generalCapacityCoreZipper x physicalCapacity))
      (generalCapacitySemanticFrame x rules input padding physicalCapacity).encode := by
  change ULogBootstrapExecution.FirstValidZeroHit
    ULogBootstrapExecution.IsConcreteCycleBoundary
    (.running ULogControl.qStart
      (generalCapacityCoreZipper x physicalCapacity))
    (.running .cycleStart _)
  exact firstValidZeroHit_of_run_and_bootstrapPrefix _ steps _ hrun hprefix

/-- Penultimate-control form of the general-capacity certificate.  The
reverse finite-table theorem supplies the full strict-prefix invariant, so a
concrete explicit-fuel ledger need only expose this one final predecessor. -/
def generalCapacity_firstValidZeroHit_of_penultimate
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (physicalCapacity : ℕ)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (hcapacity : bootstrapWorkspaceOverhead input ≤ physicalCapacity)
    (steps : ℕ)
    (hrun : ULogBootstrapExecution.run steps
      (.running ULogControl.qStart
        (generalCapacityCoreZipper x physicalCapacity)) =
      (generalCapacitySemanticFrame x rules input padding physicalCapacity).encode)
    (hpositive : 0 < steps)
    (hpenultimate : IsBootstrapRunning
      (ULogBootstrapExecution.run (steps - 1)
        (.running ULogControl.qStart
          (generalCapacityCoreZipper x physicalCapacity)))) :
    ULogBootstrapExecution.FirstValidZeroHit
      ULogBootstrapExecution.IsConcreteCycleBoundary
      (.running ULogControl.qStart
        (generalCapacityCoreZipper x physicalCapacity))
      (generalCapacitySemanticFrame x rules input padding physicalCapacity).encode := by
  change ULogBootstrapExecution.FirstValidZeroHit
    ULogBootstrapExecution.IsConcreteCycleBoundary
    (.running ULogControl.qStart
      (generalCapacityCoreZipper x physicalCapacity))
    (.running .cycleStart _)
  apply firstValidZeroHit_of_validZeroRun_penultimate_bootstrap hpositive
  · exact ULogBootstrapExecution.validZeroRun_of_run_eq_running hrun
  · exact hpenultimate

/-- Exact endpoint of the complete deterministic bootstrap at a general
physical capacity. -/
theorem run_generalCapacityBootstrapAllFuel_exact
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (physicalCapacity : ℕ)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (hcapacity : bootstrapWorkspaceOverhead input ≤ physicalCapacity) :
    ULogBootstrapExecution.run
      (generalCapacityBootstrapAllFuel x rules input padding)
      (.running ULogControl.qStart
        (generalCapacityCoreZipper x physicalCapacity)) =
      (generalCapacitySemanticFrame x rules input padding physicalCapacity).encode := by
  rw [generalCapacityCoreZipper_eq_bootstrap x rules input padding
    physicalCapacity hword hcapacity]
  rw [generalCapacitySemanticFrame_encode_eq]
  have hne : x ≠ [] := by
    intro hx
    apply ULogBootstrapExecution.encodedUniversalInput_ne_nil rules input padding
    rw [← hword, hx]
  cases hx : x with
  | nil => exact (hne hx).elim
  | cons wb wbits =>
      have heq : wb :: wbits = ULogBytecode.encodeProgram rules ++
          ULogBytecode.encodePayload input padding := hx.symm.trans hword
      have hpreamble := PakULogBootstrapExplicitFuel.run_bootstrap_workspace_exact
        (PakOuterULogBridge.copiedCoreRadius x) wb wbits []
        (ULogBootstrapExecution.payloadRuntimeWorkspace input
          (generalBootstrapTail input physicalCapacity))
      have hruntime := PakULogBootstrapExplicitFuel.run_runtime_all_exact
        rules input padding
        (List.replicate (PakOuterULogBridge.copiedCoreRadius x)
          MStarConcreteAlphabet.work)
        (generalBootstrapTail input physicalCapacity)
      have hend :=
        PakULogBootstrapExplicitFuel.initializedRuntime_eq_semanticCycleEncoding_kernel
        (PakOuterULogBridge.copiedCoreRadius x) rules input padding []
          (generalBootstrapTail input physicalCapacity)
      simp only [hx] at hpreamble hruntime hend ⊢
      rw [← heq] at hruntime ⊢
      unfold generalCapacityBootstrapAllFuel
      rw [show PakOuterULogBridge.copiedCoreRadius (wb :: wbits) +
          2 * (wb :: wbits).length + 5 +
          PakULogBootstrapExplicitFuel.runtimeAllFuel rules input padding =
          (PakOuterULogBridge.copiedCoreRadius (wb :: wbits) +
            2 * (wb :: wbits).length + 5) +
            PakULogBootstrapExplicitFuel.runtimeAllFuel rules input padding by omega]
      rw [ULogBootstrapExecution.run_add]
      simp only [ULogControl.qStart]
      simp only [List.map_cons, List.cons_append, List.append_assoc] at hpreamble ⊢
      rw [hpreamble]
      simp only [List.append_nil, List.map_cons, List.cons_append,
        List.append_assoc] at hruntime ⊢
      rw [hruntime]
      simpa only [List.append_nil] using hend

theorem generalCapacityBootstrapPreCycleFuel_succ
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) :
    generalCapacityBootstrapPreCycleFuel x rules input padding + 1 =
      generalCapacityBootstrapAllFuel x rules input padding := by
  cases input with
  | nil =>
      simp [generalCapacityBootstrapPreCycleFuel,
        generalCapacityBootstrapAllFuel,
        PakULogBootstrapExplicitFuel.runtimeAllFuel,
        PakULogBootstrapExplicitFuel.initializedRuntimeFuel]
      omega
  | cons b bs =>
      simp [generalCapacityBootstrapPreCycleFuel,
        generalCapacityBootstrapAllFuel,
        PakULogBootstrapExplicitFuel.runtimeAllFuel,
        PakULogBootstrapExplicitFuel.initializedRuntimeFuel]
      omega

/-- The advertised semantic bootstrap endpoint is the literal first cycle
boundary for every physical capacity large enough to hold the exact
initialization workspace.  No prefix or predecessor premise remains. -/
def generalCapacity_firstValidZeroHit
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (physicalCapacity : ℕ)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (hcapacity : bootstrapWorkspaceOverhead input ≤ physicalCapacity) :
    ULogBootstrapExecution.FirstValidZeroHit
      ULogBootstrapExecution.IsConcreteCycleBoundary
      (.running ULogControl.qStart
        (generalCapacityCoreZipper x physicalCapacity))
      (generalCapacitySemanticFrame x rules input padding physicalCapacity).encode := by
  let steps := generalCapacityBootstrapAllFuel x rules input padding
  have hrun := run_generalCapacityBootstrapAllFuel_exact x rules input padding
    physicalCapacity hword hcapacity
  have hsucc := generalCapacityBootstrapPreCycleFuel_succ x rules input padding
  apply generalCapacity_firstValidZeroHit_of_penultimate x rules input padding
    physicalCapacity hword hcapacity steps hrun
  · dsimp [steps]
    omega
  · have hpre := generalCapacity_preCycle_isBootstrapRunning x rules input
      padding physicalCapacity hword hcapacity
    have hsub : steps - 1 =
        generalCapacityBootstrapPreCycleFuel x rules input padding := by
      dsimp [steps]
      omega
    rwa [hsub]

end PakFixedPolyomino.PakULogGeneralCapacityBootstrapFirstHit
