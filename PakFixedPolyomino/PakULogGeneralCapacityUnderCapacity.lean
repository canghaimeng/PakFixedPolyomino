import PakFixedPolyomino.PakULogGeneralCapacityBootstrapFirstHit

/-! Workspace-exhaustion atoms for the below-overhead bootstrap branch. -/

namespace PakFixedPolyomino.PakULogGeneralCapacityUnderCapacity

open ULogAlphabet ULogProgram

abbrev Tape := ULogProgram.Tape

/-- With no trailing work cell, a seek-payload scan exhausts its final input
bit at the literal right boundary. -/
theorem seekPayload_bits_no_trailingWork_stuck
    (b : Bool) (bs : List Bool) (left : List Tape) :
    ULogBootstrapExecution.run (bs.length + 1)
      (.running ULogControl.State.seekPayload
        ⟨left, ULogProgram.bitTape b, bs.map ULogProgram.bitTape⟩) = .stuck := by
  induction bs generalizing left b with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, ULogBootstrapExecution.run]
      cases b <;> rfl
  | cons c cs ih =>
      have hlen : (c :: cs).length + 1 = 1 + (cs.length + 1) := by
        simp [Nat.add_assoc, Nat.add_comm]
      have hstep : ULogBootstrapExecution.run 1
          (.running ULogControl.State.seekPayload
            ⟨left, ULogProgram.bitTape b,
              (c :: cs).map ULogProgram.bitTape⟩) =
          .running ULogControl.State.seekPayload
            ⟨ULogProgram.codeTape b :: left, ULogProgram.bitTape c,
              cs.map ULogProgram.bitTape⟩ := by
        simp only [ULogBootstrapExecution.run, List.map_cons]
        exact ULogBootstrapExecution.seekPayload_bit_step b left
          (ULogProgram.bitTape c) (cs.map ULogProgram.bitTape)
      calc
        ULogBootstrapExecution.run ((c :: cs).length + 1)
            (.running ULogControl.State.seekPayload
              ⟨left, ULogProgram.bitTape b,
                (c :: cs).map ULogProgram.bitTape⟩) =
            ULogBootstrapExecution.run (cs.length + 1)
              (ULogBootstrapExecution.run 1
                (.running ULogControl.State.seekPayload
                  ⟨left, ULogProgram.bitTape b,
                    (c :: cs).map ULogProgram.bitTape⟩)) := by
                rw [← ULogBootstrapExecution.run_add, hlen]
        _ = ULogBootstrapExecution.run (cs.length + 1)
              (.running ULogControl.State.seekPayload
                ⟨ULogProgram.codeTape b :: left, ULogProgram.bitTape c,
                  cs.map ULogProgram.bitTape⟩) := by rw [hstep]
        _ = .stuck := ih c (ULogProgram.codeTape b :: left)

/-- The iterate immediately before a no-work seek-payload failure remains in
the bootstrap control region. -/
theorem seekPayload_bits_no_trailingWork_penultimate
    (b : Bool) (bs : List Bool) (left : List Tape) :
    PakULogGeneralCapacityBootstrapFirstHit.IsBootstrapRunning
      (ULogBootstrapExecution.run bs.length
        (.running ULogControl.State.seekPayload
          ⟨left, ULogProgram.bitTape b, bs.map ULogProgram.bitTape⟩)) := by
  induction bs generalizing left b with
  | nil => rfl
  | cons c cs ih =>
      have hstep : ULogBootstrapExecution.run 1
          (.running ULogControl.State.seekPayload
            ⟨left, ULogProgram.bitTape b,
              (c :: cs).map ULogProgram.bitTape⟩) =
          .running ULogControl.State.seekPayload
            ⟨ULogProgram.codeTape b :: left, ULogProgram.bitTape c,
              cs.map ULogProgram.bitTape⟩ := by
        simp only [ULogBootstrapExecution.run, List.map_cons]
        exact ULogBootstrapExecution.seekPayload_bit_step b left
          (ULogProgram.bitTape c) (cs.map ULogProgram.bitTape)
      rw [show (c :: cs).length = 1 + cs.length by simp [Nat.add_comm],
        ULogBootstrapExecution.run_add, hstep]
      exact ih c (ULogProgram.codeTape b :: left)

/-- The frame-payload phase likewise has a literal bootstrap predecessor
before it would seek past the final copied bit. -/
theorem framePayload_no_trailingWork_penultimate
    (b : Bool) (bits : List Bool) (left : List Tape) :
    PakULogGeneralCapacityBootstrapFirstHit.IsBootstrapRunning
      (ULogBootstrapExecution.run bits.length
        (.running (.framePayload b)
          ⟨ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left,
            ULogProgram.bitTape b, bits.map ULogProgram.bitTape⟩)) := by
  cases bits with
  | nil => rfl
  | cons c cs =>
      have hstep : ULogBootstrapExecution.run 1
          (.running (.framePayload b)
            ⟨ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left,
              ULogProgram.bitTape b,
              (c :: cs).map ULogProgram.bitTape⟩) =
          .running ULogControl.State.seekPayload
            ⟨ULogProgram.codeTape b ::
                ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left,
              ULogProgram.bitTape c, cs.map ULogProgram.bitTape⟩ := by
        simp only [ULogBootstrapExecution.run, List.map_cons]
        exact ULogBootstrapExecution.framePayload_step b
          (ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
          (ULogProgram.bitTape c) (cs.map ULogProgram.bitTape)
      rw [show (c :: cs).length = 1 + cs.length by simp [Nat.add_comm],
        ULogBootstrapExecution.run_add, hstep]
      exact seekPayload_bits_no_trailingWork_penultimate c cs
        (ULogProgram.codeTape b ::
          ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)

/-- Starting a translation with no work cell after the copied word gets as
far as the final payload bit and then literally runs off the right boundary. -/
theorem start_nonempty_no_trailingWork_stuck
    (b : Bool) (bits : List Bool) (left : List Tape) :
    ULogBootstrapExecution.run (bits.length + 3)
      (.running ULogControl.State.start
        ⟨MStarConcreteAlphabet.work :: left, ULogProgram.bitTape b,
          bits.map ULogProgram.bitTape⟩) = .stuck := by
  have hstart : ULogBootstrapExecution.run 1
      (.running ULogControl.State.start
        ⟨MStarConcreteAlphabet.work :: left, ULogProgram.bitTape b,
          bits.map ULogProgram.bitTape⟩) =
      .running (.translateCode b)
        ⟨left, MStarConcreteAlphabet.work,
          ULogProgram.bitTape b :: bits.map ULogProgram.bitTape⟩ := by
    simp only [ULogBootstrapExecution.run]
    exact ULogBootstrapExecution.start_bit_step b left
      (bits.map ULogProgram.bitTape) MStarConcreteAlphabet.work
  have htranslate : ULogBootstrapExecution.run 1
      (.running (.translateCode b)
        ⟨left, MStarConcreteAlphabet.work,
          ULogProgram.bitTape b :: bits.map ULogProgram.bitTape⟩) =
      .running (.framePayload b)
        ⟨ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left,
          ULogProgram.bitTape b, bits.map ULogProgram.bitTape⟩ := by
    simp only [ULogBootstrapExecution.run]
    exact ULogBootstrapExecution.translateCode_step b left
      (bits.map ULogProgram.bitTape) (ULogProgram.bitTape b)
  have hframe : ULogBootstrapExecution.run (bits.length + 1)
      (.running (.framePayload b)
        ⟨ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left,
          ULogProgram.bitTape b, bits.map ULogProgram.bitTape⟩) = .stuck := by
    cases bits with
    | nil =>
        simp only [List.length_nil, Nat.zero_add, ULogBootstrapExecution.run]
        cases b <;> rfl
    | cons c cs =>
        have hlen : (c :: cs).length + 1 = 1 + (cs.length + 1) := by
          simp [Nat.add_assoc, Nat.add_comm]
        have hstep : ULogBootstrapExecution.run 1
            (.running (.framePayload b)
              ⟨ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left,
                ULogProgram.bitTape b,
                (c :: cs).map ULogProgram.bitTape⟩) =
            .running ULogControl.State.seekPayload
              ⟨ULogProgram.codeTape b ::
                  ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left,
                ULogProgram.bitTape c, cs.map ULogProgram.bitTape⟩ := by
          simp only [ULogBootstrapExecution.run, List.map_cons]
          exact ULogBootstrapExecution.framePayload_step b
            (ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
            (ULogProgram.bitTape c) (cs.map ULogProgram.bitTape)
        calc
          ULogBootstrapExecution.run ((c :: cs).length + 1)
              (.running (.framePayload b)
                ⟨ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left,
                  ULogProgram.bitTape b,
                  (c :: cs).map ULogProgram.bitTape⟩) =
              ULogBootstrapExecution.run (cs.length + 1)
                (ULogBootstrapExecution.run 1
                  (.running (.framePayload b)
                    ⟨ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left,
                      ULogProgram.bitTape b,
                      (c :: cs).map ULogProgram.bitTape⟩)) := by
                rw [← ULogBootstrapExecution.run_add, hlen]
          _ = ULogBootstrapExecution.run (cs.length + 1)
                (.running ULogControl.State.seekPayload
                  ⟨ULogProgram.codeTape b ::
                      ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left,
                    ULogProgram.bitTape c, cs.map ULogProgram.bitTape⟩) := by rw [hstep]
          _ = .stuck := seekPayload_bits_no_trailingWork_stuck c cs
            (ULogProgram.codeTape b ::
              ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
  rw [show bits.length + 3 = 1 + (1 + (bits.length + 1)) by omega,
    ULogBootstrapExecution.run_add, hstart,
    ULogBootstrapExecution.run_add, htranslate]
  exact hframe

/-- Immediately before the no-work start/translation path becomes `stuck`,
the machine is still running one of its bootstrap controls. -/
theorem start_nonempty_no_trailingWork_penultimate
    (b : Bool) (bits : List Bool) (left : List Tape) :
    PakULogGeneralCapacityBootstrapFirstHit.IsBootstrapRunning
      (ULogBootstrapExecution.run (bits.length + 2)
        (.running ULogControl.State.start
          ⟨MStarConcreteAlphabet.work :: left, ULogProgram.bitTape b,
            bits.map ULogProgram.bitTape⟩)) := by
  have hstart : ULogBootstrapExecution.run 1
      (.running ULogControl.State.start
        ⟨MStarConcreteAlphabet.work :: left, ULogProgram.bitTape b,
          bits.map ULogProgram.bitTape⟩) =
      .running (.translateCode b)
        ⟨left, MStarConcreteAlphabet.work,
          ULogProgram.bitTape b :: bits.map ULogProgram.bitTape⟩ := by
    simp only [ULogBootstrapExecution.run]
    exact ULogBootstrapExecution.start_bit_step b left
      (bits.map ULogProgram.bitTape) MStarConcreteAlphabet.work
  have htranslate : ULogBootstrapExecution.run 1
      (.running (.translateCode b)
        ⟨left, MStarConcreteAlphabet.work,
          ULogProgram.bitTape b :: bits.map ULogProgram.bitTape⟩) =
      .running (.framePayload b)
        ⟨ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left,
          ULogProgram.bitTape b, bits.map ULogProgram.bitTape⟩ := by
    simp only [ULogBootstrapExecution.run]
    exact ULogBootstrapExecution.translateCode_step b left
      (bits.map ULogProgram.bitTape) (ULogProgram.bitTape b)
  rw [show bits.length + 2 = 1 + (1 + bits.length) by omega,
    ULogBootstrapExecution.run_add, hstart,
    ULogBootstrapExecution.run_add, htranslate]
  exact framePayload_no_trailingWork_penultimate b bits left

set_option maxHeartbeats 1000000

/-- With zero physical cells after a valid copied universal word, the start
scan reaches the word but its final payload scan has no trailing work cell.
This is an explicit literal `stuck` run from the real `qStart` core. -/
theorem run_generalCapacity_zero_stuck
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    ULogBootstrapExecution.run
      (PakOuterULogBridge.copiedCoreRadius x + x.length + 3)
      (.running ULogControl.qStart
        (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper x 0)) =
      .stuck := by
  have hne : x ≠ [] := by
    intro hx
    apply ULogBootstrapExecution.encodedUniversalInput_ne_nil rules input padding
    rw [← hword, hx]
  cases x with
  | nil => exact (hne rfl).elim
  | cons b bits =>
      let R := PakOuterULogBridge.copiedCoreRadius (b :: bits)
      have hscan := ULogBootstrapExecution.run_start_work (R + 1)
        ([] : List Tape) (ULogProgram.bitTape b)
        (bits.map ULogProgram.bitTape)
      have hscan' : ULogBootstrapExecution.run (R + 1)
          (.running ULogControl.State.start
            (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper
              (b :: bits) 0)) =
          .running ULogControl.State.start
            ⟨List.replicate (R + 1) MStarConcreteAlphabet.work,
              ULogProgram.bitTape b, bits.map ULogProgram.bitTape⟩ := by
        simpa [PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper,
          ULogBootstrapExecution.beforeStartWork,
          ULogBootstrapExecution.afterStartWork, R,
          List.replicate_succ, List.append_assoc] using hscan
      have htail := start_nonempty_no_trailingWork_stuck b bits
        (List.replicate R MStarConcreteAlphabet.work)
      change ULogBootstrapExecution.run
        (PakOuterULogBridge.copiedCoreRadius (b :: bits) +
          (b :: bits).length + 3)
        (.running ULogControl.State.start
          (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper
            (b :: bits) 0)) = .stuck
      have hlen : PakOuterULogBridge.copiedCoreRadius (b :: bits) +
          (b :: bits).length + 3 =
          (R + 1) + (bits.length + 3) := by
        dsimp only [R]
        simp only [List.length_cons]
        omega
      rw [hlen, ULogBootstrapExecution.run_add, hscan']
      simpa only [List.replicate_succ] using htail

/-- The global `C = 0` execution is still bootstrap-running at its final
defined iterate.  Its next action is precisely the boundary failure proved
by `run_generalCapacity_zero_stuck`. -/
theorem run_generalCapacity_zero_penultimate
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    PakULogGeneralCapacityBootstrapFirstHit.IsBootstrapRunning
      (ULogBootstrapExecution.run
        (PakOuterULogBridge.copiedCoreRadius x + x.length + 3 - 1)
        (.running ULogControl.qStart
          (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper x 0))) := by
  have hne : x ≠ [] := by
    intro hx
    apply ULogBootstrapExecution.encodedUniversalInput_ne_nil rules input padding
    rw [← hword, hx]
  cases x with
  | nil => exact (hne rfl).elim
  | cons b bits =>
      let R := PakOuterULogBridge.copiedCoreRadius (b :: bits)
      have hscan := ULogBootstrapExecution.run_start_work (R + 1)
        ([] : List Tape) (ULogProgram.bitTape b)
        (bits.map ULogProgram.bitTape)
      have hscan' : ULogBootstrapExecution.run (R + 1)
          (.running ULogControl.State.start
            (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper
              (b :: bits) 0)) =
          .running ULogControl.State.start
            ⟨List.replicate (R + 1) MStarConcreteAlphabet.work,
              ULogProgram.bitTape b, bits.map ULogProgram.bitTape⟩ := by
        simpa [PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper,
          ULogBootstrapExecution.beforeStartWork,
          ULogBootstrapExecution.afterStartWork, R,
          List.replicate_succ, List.append_assoc] using hscan
      have htail := start_nonempty_no_trailingWork_penultimate b bits
        (List.replicate R MStarConcreteAlphabet.work)
      change PakULogGeneralCapacityBootstrapFirstHit.IsBootstrapRunning
        (ULogBootstrapExecution.run
          (PakOuterULogBridge.copiedCoreRadius (b :: bits) +
            (b :: bits).length + 3 - 1)
          (.running ULogControl.State.start
            (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper
              (b :: bits) 0)))
      have hlen : PakOuterULogBridge.copiedCoreRadius (b :: bits) +
          (b :: bits).length + 3 - 1 =
          (R + 1) + (bits.length + 2) := by
        dsimp only [R]
        simp only [List.length_cons]
        omega
      rw [hlen, ULogBootstrapExecution.run_add, hscan']
      simpa only [List.replicate_succ] using htail

def beforeClockPaddingNoWorkspace (padding : List Bool) (left : List Tape) :
    MStarParserExecution.Zipper Tape :=
  match padding with
  | [] => ⟨left, ULogAlphabet.ulogCore ULogAlphabet.codeEnd, []⟩
  | b :: bs => ⟨left, ULogProgram.codeTape b,
      bs.map ULogProgram.codeTape ++ [ULogAlphabet.ulogCore ULogAlphabet.codeEnd]⟩

/-- The final clock-padding pass cannot cross `codeEnd` without its physical
workspace cell. -/
theorem framePadding_no_workspace_stuck
    (padding : List Bool) (left : List Tape) :
    ULogBootstrapExecution.run (padding.length + 1)
      (.running ULogControl.State.framePadding
        (beforeClockPaddingNoWorkspace padding left)) = .stuck := by
  induction padding generalizing left with
  | nil =>
      have hzero : ULogAlphabet.ulogCore ULogAlphabet.codeEnd ≠
          ULogProgram.codeTape false :=
        ULogTapeDecoding.ulog_symbol_ne (by decide)
      have hone : ULogAlphabet.ulogCore ULogAlphabet.codeEnd ≠
          ULogProgram.codeTape true :=
        ULogTapeDecoding.ulog_symbol_ne (by decide)
      simp [ULogBootstrapExecution.run,
        beforeClockPaddingNoWorkspace,
        ULogBootstrapExecution.oneStep, ULogProgram.program,
        ULogProgram.rule, ULogProgram.deterministicStep,
        MStarParserExecution.applyAction, ULogProgram.go,
        ULogControl.qAccept, ULogControl.qReject, hzero, hone]
  | cons p ps ih =>
      have hstep : ULogBootstrapExecution.run 1
            (.running ULogControl.State.framePadding
            (beforeClockPaddingNoWorkspace (p :: ps) left)) =
          .running ULogControl.State.framePadding
            (beforeClockPaddingNoWorkspace ps
              (ULogAlphabet.ulogCore ULogAlphabet.clockZero :: left)) := by
        cases ps <;>
          simp [ULogBootstrapExecution.run,
            beforeClockPaddingNoWorkspace,
            ULogBootstrapExecution.framePadding_bit_step,
            List.append_assoc]
      rw [show (p :: ps).length + 1 = 1 + (ps.length + 1) by
        simp [Nat.add_comm], ULogBootstrapExecution.run_add, hstep]
      exact ih (ULogAlphabet.ulogCore ULogAlphabet.clockZero :: left)

theorem framePadding_no_workspace_penultimate
    (padding : List Bool) (left : List Tape) :
    PakULogGeneralCapacityBootstrapFirstHit.IsBootstrapRunning
      (ULogBootstrapExecution.run padding.length
        (.running ULogControl.State.framePadding
          (beforeClockPaddingNoWorkspace padding left))) := by
  induction padding generalizing left with
  | nil => rfl
  | cons p ps ih =>
      have hstep : ULogBootstrapExecution.run 1
          (.running ULogControl.State.framePadding
            (beforeClockPaddingNoWorkspace (p :: ps) left)) =
          .running ULogControl.State.framePadding
            (beforeClockPaddingNoWorkspace ps
              (ULogAlphabet.ulogCore ULogAlphabet.clockZero :: left)) := by
        cases ps <;>
          simp [ULogBootstrapExecution.run, beforeClockPaddingNoWorkspace,
            ULogBootstrapExecution.framePadding_bit_step]
      rw [show (p :: ps).length = 1 + ps.length by simp [Nat.add_comm],
        ULogBootstrapExecution.run_add, hstep]
      exact ih (ULogAlphabet.ulogCore ULogAlphabet.clockZero :: left)

/-- The rule-list parser itself needs no workspace after `codeEnd`; it hands
the physical deficiency unchanged to the payload-length stage. -/
theorem run_programPayload_no_workspace_exact
    (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (left : List Tape) :
    ULogBootstrapExecution.run
      (PakULogBootstrapExplicitFuel.programPayloadFuel rules)
      (.running ULogControl.State.framePayloadLength
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          (ULogBytecode.encodeProgram rules ++
            ULogBytecode.encodePayload input padding).map ULogProgram.codeTape ++
              [ULogAlphabet.ulogCore ULogAlphabet.codeEnd]⟩) =
      ULogBootstrapExecution.atBits ULogControl.State.payloadLengthStart
        (ULogBytecode.encodePayload input padding)
        (ULogBootstrapExecution.programMarkedLeft rules left)
        (ULogAlphabet.ulogCore ULogAlphabet.codeEnd) [] := by
  have hnonempty : ULogBytecode.encodePayload input padding ≠ [] :=
    ULogBootstrapExecution.encodePayload_ne_nil input padding
  cases hpayload : ULogBytecode.encodePayload input padding with
  | nil => exact (hnonempty hpayload).elim
  | cons b bs =>
      have h := PakULogBootstrapExplicitFuel.run_programPayload_all_exact
        rules b (ULogAlphabet.ulogCore ULogAlphabet.codeEnd) [] left
      cases bs with
      | nil =>
          simpa [hpayload, ULogBootstrapExecution.countExhaustedDone,
            ULogBootstrapExecution.programMarkedLeft,
            ULogBootstrapExecution.atBits, ULogProgram.codeTape,
            List.map_append, List.append_assoc] using h
      | cons c cs =>
          have h' := PakULogBootstrapExplicitFuel.run_programPayload_all_exact
            rules b (ULogProgram.codeTape c)
            (cs.map ULogProgram.codeTape ++
              [ULogAlphabet.ulogCore ULogAlphabet.codeEnd]) left
          simpa [hpayload, ULogBootstrapExecution.countExhaustedDone,
            ULogBootstrapExecution.programMarkedLeft,
            ULogBootstrapExecution.atBits, ULogProgram.codeTape,
            List.map_append, List.append_assoc] using h'

def payloadClockNoWorkspaceFuel (input padding : List Bool) : ℕ :=
  input.length + 1 +
    PakULogBootstrapExplicitFuel.payloadFoldCaseFuel input padding +
      padding.length + 1

/-- The payload/clock pass remains fully deterministic without the final
workspace cell: all decoding and folding completes, and the final clock
frame action is exactly the right-boundary failure above. -/
theorem run_payloadClock_no_workspace_stuck
    (input padding : List Bool) (base : List Tape) :
    ULogBootstrapExecution.run (payloadClockNoWorkspaceFuel input padding)
      (ULogBootstrapExecution.atBits ULogControl.State.payloadLengthStart
        (ULogBytecode.encodePayload input padding) base
        (ULogAlphabet.ulogCore ULogAlphabet.codeEnd) []) = .stuck := by
  have hdecode := PakULogBootstrapExplicitFuel.run_payloadLengthStart_exact
    input padding base (ULogAlphabet.ulogCore ULogAlphabet.codeEnd) []
  unfold payloadClockNoWorkspaceFuel
  rw [show input.length + 1 +
        PakULogBootstrapExplicitFuel.payloadFoldCaseFuel input padding +
          padding.length + 1 =
      (input.length + 1) +
        (PakULogBootstrapExplicitFuel.payloadFoldCaseFuel input padding +
          (padding.length + 1)) by omega,
    ULogBootstrapExecution.run_add, hdecode]
  cases input with
  | nil =>
      cases padding with
      | nil =>
          rw [show PakULogBootstrapExplicitFuel.payloadFoldCaseFuel [] [] +
                ([].length + 1) = 1 + 1 by rfl,
            ULogBootstrapExecution.run_add]
          have hfold := PakULogBootstrapExplicitFuel.run_payloadFold_empty_unpadded_exact
            base []
          simp only [ULogBootstrapExecution.atBits, List.map_nil,
            List.nil_append, ULogBootstrapExecution.payloadLengthMarkedLeft,
            List.length_nil] at hfold ⊢
          rw [hfold]
          simpa [ULogBootstrapExecution.run, beforeClockPaddingNoWorkspace] using
            framePadding_no_workspace_stuck []
              (ULogBootstrapExecution.payloadFoldedLeft [] base)
      | cons p ps =>
          rw [show PakULogBootstrapExplicitFuel.payloadFoldCaseFuel [] (p :: ps) +
                ((p :: ps).length + 1) = 3 + ((p :: ps).length + 1) by rfl,
            ULogBootstrapExecution.run_add]
          have hfold := PakULogBootstrapExplicitFuel.run_payloadFold_empty_padded_exact
            p ps base []
          simp [ULogBootstrapExecution.atBits,
            ULogBootstrapExecution.payloadLengthMarkedLeft,
            ULogBytecode.encodeNatField, ULogProgram.codeTape,
            List.append_assoc] at hfold ⊢
          rw [hfold]
          cases p
          · simpa [beforeClockPaddingNoWorkspace, ULogProgram.codeTape] using
              framePadding_no_workspace_stuck (false :: ps)
                (ULogBootstrapExecution.payloadFoldedLeft [] base)
          · simpa [beforeClockPaddingNoWorkspace, ULogProgram.codeTape] using
              framePadding_no_workspace_stuck (true :: ps)
                (ULogBootstrapExecution.payloadFoldedLeft [] base)
  | cons b bs =>
      cases bs with
      | nil =>
          cases padding with
          | nil =>
              rw [show PakULogBootstrapExplicitFuel.payloadFoldCaseFuel [b] [] +
                    ([].length + 1) = 6 + 1 by rfl,
                ULogBootstrapExecution.run_add]
              have hfold := PakULogBootstrapExplicitFuel.run_payloadFold_singleton_unpadded_exact
                b base []
              simp [ULogBootstrapExecution.atBits,
                ULogBootstrapExecution.payloadLengthMarkedLeft,
                ULogBytecode.encodeNatField, ULogProgram.codeTape,
                List.append_assoc] at hfold ⊢
              rw [hfold]
              simpa [ULogBootstrapExecution.run, beforeClockPaddingNoWorkspace] using
                framePadding_no_workspace_stuck []
                  (ULogBootstrapExecution.payloadFoldedLeft [b] base)
          | cons p ps =>
              rw [show PakULogBootstrapExplicitFuel.payloadFoldCaseFuel [b] (p :: ps) +
                    ((p :: ps).length + 1) = 12 + ((p :: ps).length + 1) by rfl,
                ULogBootstrapExecution.run_add]
              have hfold := PakULogBootstrapExplicitFuel.run_payloadFold_singleton_padded_exact
                b p ps base []
              simp [ULogBootstrapExecution.atBits,
                ULogBootstrapExecution.payloadLengthMarkedLeft,
                ULogBytecode.encodeNatField, ULogProgram.codeTape,
                List.append_assoc] at hfold ⊢
              rw [hfold]
              cases p
              · simpa [beforeClockPaddingNoWorkspace, ULogProgram.codeTape] using
                  framePadding_no_workspace_stuck (false :: ps)
                    (ULogBootstrapExecution.payloadFoldedLeft [b] base)
              · simpa [beforeClockPaddingNoWorkspace, ULogProgram.codeTape] using
                  framePadding_no_workspace_stuck (true :: ps)
                    (ULogBootstrapExecution.payloadFoldedLeft [b] base)
      | cons c cs =>
          cases padding with
          | nil =>
              rw [show PakULogBootstrapExplicitFuel.payloadFoldCaseFuel
                    (b :: c :: cs) [] + ([].length + 1) =
                  (5 + PakULogBootstrapExplicitFuel.payloadFoldFuel cs [false] 1 + 1) + 1 by rfl,
                ULogBootstrapExecution.run_add]
              have hfold := PakULogBootstrapExplicitFuel.run_payloadFold_nonempty_unpadded_exact
                b c cs base []
              simp [ULogBootstrapExecution.atBits,
                ULogBootstrapExecution.payloadLengthMarkedLeft,
                ULogBytecode.encodeNatField, ULogProgram.codeTape,
                List.replicate_succ, List.append_assoc] at hfold ⊢
              simp only [PakULogBootstrapExplicitFuel.payloadFoldFuel,
                List.length_cons, List.length_nil] at hfold ⊢
              rw [hfold]
              simpa [beforeClockPaddingNoWorkspace] using
                framePadding_no_workspace_stuck []
                  (ULogBootstrapExecution.payloadFoldedLeft (b :: c :: cs) base)
          | cons p ps =>
              rw [show PakULogBootstrapExplicitFuel.payloadFoldCaseFuel
                    (b :: c :: cs) (p :: ps) + ((p :: ps).length + 1) =
                  (5 + PakULogBootstrapExplicitFuel.payloadFoldFuel cs [false] 1 +
                    (4 * cs.length + 11)) + ((p :: ps).length + 1) by rfl,
                ULogBootstrapExecution.run_add]
              have hfold := PakULogBootstrapExplicitFuel.run_payloadFold_nonempty_padded_exact
                b c p cs ps base []
              simp [ULogBootstrapExecution.atBits,
                ULogBootstrapExecution.payloadLengthMarkedLeft,
                ULogBytecode.encodeNatField, ULogProgram.codeTape,
                List.replicate_succ, List.append_assoc] at hfold ⊢
              simp only [PakULogBootstrapExplicitFuel.payloadFoldFuel,
                List.length_cons, List.length_nil] at hfold ⊢
              rw [hfold]
              cases p
              · simpa [beforeClockPaddingNoWorkspace, ULogProgram.codeTape] using
                  framePadding_no_workspace_stuck (false :: ps)
                    (ULogBootstrapExecution.payloadFoldedLeft (b :: c :: cs) base)
              · simpa [beforeClockPaddingNoWorkspace, ULogProgram.codeTape] using
              framePadding_no_workspace_stuck (true :: ps)
                    (ULogBootstrapExecution.payloadFoldedLeft (b :: c :: cs) base)

/-- One step before the literal right-boundary failure of the no-work
payload/clock pass, control is still in the bootstrap program.  This is the
`C = 1` predecessor needed by the first-hit exclusion: the final
`framePadding` action, and no earlier action, creates `stuck`. -/
theorem run_payloadClock_no_workspace_penultimate
    (input padding : List Bool) (base : List Tape) :
    PakULogGeneralCapacityBootstrapFirstHit.IsBootstrapRunning
      (ULogBootstrapExecution.run (payloadClockNoWorkspaceFuel input padding - 1)
        (ULogBootstrapExecution.atBits ULogControl.State.payloadLengthStart
          (ULogBytecode.encodePayload input padding) base
          (ULogAlphabet.ulogCore ULogAlphabet.codeEnd) [])) := by
  have hdecode := PakULogBootstrapExplicitFuel.run_payloadLengthStart_exact
    input padding base (ULogAlphabet.ulogCore ULogAlphabet.codeEnd) []
  unfold payloadClockNoWorkspaceFuel
  rw [show input.length + 1 +
        PakULogBootstrapExplicitFuel.payloadFoldCaseFuel input padding +
          padding.length + 1 - 1 =
      (input.length + 1) +
        (PakULogBootstrapExplicitFuel.payloadFoldCaseFuel input padding +
          padding.length) by omega,
    ULogBootstrapExecution.run_add, hdecode]
  cases input with
  | nil =>
      cases padding with
      | nil =>
          rw [show PakULogBootstrapExplicitFuel.payloadFoldCaseFuel [] [] +
                [].length = 1 by rfl]
          have hfold := PakULogBootstrapExplicitFuel.run_payloadFold_empty_unpadded_exact
            base []
          simp only [ULogBootstrapExecution.atBits, List.map_nil,
            List.nil_append, ULogBootstrapExecution.payloadLengthMarkedLeft,
            List.length_nil] at hfold ⊢
          rw [hfold]
          rfl
      | cons p ps =>
          rw [show PakULogBootstrapExplicitFuel.payloadFoldCaseFuel [] (p :: ps) +
                (p :: ps).length = 3 + (p :: ps).length by rfl,
            ULogBootstrapExecution.run_add]
          have hfold := PakULogBootstrapExplicitFuel.run_payloadFold_empty_padded_exact
            p ps base []
          simp [ULogBootstrapExecution.atBits,
            ULogBootstrapExecution.payloadLengthMarkedLeft,
            ULogBytecode.encodeNatField, ULogProgram.codeTape,
            List.append_assoc] at hfold ⊢
          rw [hfold]
          cases p
          · simpa [beforeClockPaddingNoWorkspace, ULogProgram.codeTape] using
              framePadding_no_workspace_penultimate (false :: ps)
                (ULogBootstrapExecution.payloadFoldedLeft [] base)
          · simpa [beforeClockPaddingNoWorkspace, ULogProgram.codeTape] using
              framePadding_no_workspace_penultimate (true :: ps)
                (ULogBootstrapExecution.payloadFoldedLeft [] base)
  | cons b bs =>
      cases bs with
      | nil =>
          cases padding with
          | nil =>
              rw [show PakULogBootstrapExplicitFuel.payloadFoldCaseFuel [b] [] +
                    [].length = 6 by rfl]
              have hfold := PakULogBootstrapExplicitFuel.run_payloadFold_singleton_unpadded_exact
                b base []
              simp [ULogBootstrapExecution.atBits,
                ULogBootstrapExecution.payloadLengthMarkedLeft,
                ULogBytecode.encodeNatField, ULogProgram.codeTape,
                List.append_assoc] at hfold ⊢
              rw [hfold]
              rfl
          | cons p ps =>
              rw [show PakULogBootstrapExplicitFuel.payloadFoldCaseFuel [b] (p :: ps) +
                    (p :: ps).length = 12 + (p :: ps).length by rfl,
                ULogBootstrapExecution.run_add]
              have hfold := PakULogBootstrapExplicitFuel.run_payloadFold_singleton_padded_exact
                b p ps base []
              simp [ULogBootstrapExecution.atBits,
                ULogBootstrapExecution.payloadLengthMarkedLeft,
                ULogBytecode.encodeNatField, ULogProgram.codeTape,
                List.append_assoc] at hfold ⊢
              rw [hfold]
              cases p
              · simpa [beforeClockPaddingNoWorkspace, ULogProgram.codeTape] using
                  framePadding_no_workspace_penultimate (false :: ps)
                    (ULogBootstrapExecution.payloadFoldedLeft [b] base)
              · simpa [beforeClockPaddingNoWorkspace, ULogProgram.codeTape] using
                  framePadding_no_workspace_penultimate (true :: ps)
                    (ULogBootstrapExecution.payloadFoldedLeft [b] base)
      | cons c cs =>
          cases padding with
          | nil =>
              rw [show PakULogBootstrapExplicitFuel.payloadFoldCaseFuel
                    (b :: c :: cs) [] + [].length =
                  5 + PakULogBootstrapExplicitFuel.payloadFoldFuel cs [false] 1 + 1 by rfl]
              have hfold := PakULogBootstrapExplicitFuel.run_payloadFold_nonempty_unpadded_exact
                b c cs base []
              simp [ULogBootstrapExecution.atBits,
                ULogBootstrapExecution.payloadLengthMarkedLeft,
                ULogBytecode.encodeNatField, ULogProgram.codeTape,
                List.replicate_succ, List.append_assoc] at hfold ⊢
              simp only [PakULogBootstrapExplicitFuel.payloadFoldFuel,
                List.length_cons, List.length_nil] at hfold ⊢
              rw [hfold]
              rfl
          | cons p ps =>
              rw [show PakULogBootstrapExplicitFuel.payloadFoldCaseFuel
                    (b :: c :: cs) (p :: ps) + (p :: ps).length =
                  5 + PakULogBootstrapExplicitFuel.payloadFoldFuel cs [false] 1 +
                    (4 * cs.length + 11) + (p :: ps).length by rfl,
                ULogBootstrapExecution.run_add]
              have hfold := PakULogBootstrapExplicitFuel.run_payloadFold_nonempty_padded_exact
                b c p cs ps base []
              simp [ULogBootstrapExecution.atBits,
                ULogBootstrapExecution.payloadLengthMarkedLeft,
                ULogBytecode.encodeNatField, ULogProgram.codeTape,
                List.replicate_succ, List.append_assoc] at hfold ⊢
              simp only [PakULogBootstrapExplicitFuel.payloadFoldFuel,
                List.length_cons, List.length_nil] at hfold ⊢
              rw [hfold]
              cases p
              · simpa [beforeClockPaddingNoWorkspace, ULogProgram.codeTape] using
                  framePadding_no_workspace_penultimate (false :: ps)
                    (ULogBootstrapExecution.payloadFoldedLeft (b :: c :: cs) base)
              · simpa [beforeClockPaddingNoWorkspace, ULogProgram.codeTape] using
                  framePadding_no_workspace_penultimate (true :: ps)
                    (ULogBootstrapExecution.payloadFoldedLeft (b :: c :: cs) base)

/-- With exactly one physical cell after a valid copied word, front-end
translation succeeds but leaves no cell beyond `codeEnd`.  The explicit
no-work parser and payload-clock ledgers therefore reach `stuck`. -/
theorem run_generalCapacity_one_stuck
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    ULogBootstrapExecution.run
      (PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 5 +
        PakULogBootstrapExplicitFuel.programPayloadFuel rules +
          payloadClockNoWorkspaceFuel input padding)
      (.running ULogControl.qStart
        (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper x 1)) =
      .stuck := by
  have hne : x ≠ [] := by
    intro hx
    apply ULogBootstrapExecution.encodedUniversalInput_ne_nil rules input padding
    rw [← hword, hx]
  cases x with
  | nil => exact (hne rfl).elim
  | cons b bits =>
      have heq : b :: bits = ULogBytecode.encodeProgram rules ++
          ULogBytecode.encodePayload input padding := hword
      have hpreamble := PakULogBootstrapExplicitFuel.run_bootstrap_workspace_exact
        (PakOuterULogBridge.copiedCoreRadius (b :: bits)) b bits [] []
      have hprogram := run_programPayload_no_workspace_exact rules input padding
        (List.replicate (PakOuterULogBridge.copiedCoreRadius (b :: bits))
          MStarConcreteAlphabet.work)
      have hpayload := run_payloadClock_no_workspace_stuck input padding
        (ULogBootstrapExecution.programMarkedLeft rules
          (List.replicate (PakOuterULogBridge.copiedCoreRadius (b :: bits))
            MStarConcreteAlphabet.work))
      rw [← heq] at hprogram
      have hstart :
          PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper
            (b :: bits) 1 =
            ⟨[], MStarConcreteAlphabet.work,
              List.replicate (PakOuterULogBridge.copiedCoreRadius (b :: bits))
                  MStarConcreteAlphabet.work ++
                ULogProgram.bitTape b ::
                  (bits.map ULogProgram.bitTape ++
                    [MStarConcreteAlphabet.work])⟩ := by
        apply MStarParserExecution.Zipper.ext <;>
          simp [PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper,
            List.replicate_succ]
      rw [hstart]
      simp only [ULogControl.qStart]
      rw [show PakOuterULogBridge.copiedCoreRadius (b :: bits) +
          2 * (b :: bits).length + 5 +
          PakULogBootstrapExplicitFuel.programPayloadFuel rules +
            payloadClockNoWorkspaceFuel input padding =
          (PakOuterULogBridge.copiedCoreRadius (b :: bits) +
            2 * (b :: bits).length + 5) +
            (PakULogBootstrapExplicitFuel.programPayloadFuel rules +
              payloadClockNoWorkspaceFuel input padding) by omega,
        ULogBootstrapExecution.run_add, hpreamble]
      simp only [List.append_nil]
      rw [ULogBootstrapExecution.run_add, hprogram]
      exact hpayload

/-- At physical capacity one, the exact predecessor of the literal
right-boundary failure is still a genuine bootstrap-running state.  The
front-end and rule-list ledgers are unchanged; only the final clock-padding
action is omitted. -/
theorem run_generalCapacity_one_penultimate
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    PakULogGeneralCapacityBootstrapFirstHit.IsBootstrapRunning
      (ULogBootstrapExecution.run
        (PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 5 +
          PakULogBootstrapExplicitFuel.programPayloadFuel rules +
            payloadClockNoWorkspaceFuel input padding - 1)
        (.running ULogControl.qStart
          (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper x 1))) := by
  have hne : x ≠ [] := by
    intro hx
    apply ULogBootstrapExecution.encodedUniversalInput_ne_nil rules input padding
    rw [← hword, hx]
  cases x with
  | nil => exact (hne rfl).elim
  | cons b bits =>
      have heq : b :: bits = ULogBytecode.encodeProgram rules ++
          ULogBytecode.encodePayload input padding := hword
      have hpreamble := PakULogBootstrapExplicitFuel.run_bootstrap_workspace_exact
        (PakOuterULogBridge.copiedCoreRadius (b :: bits)) b bits [] []
      have hprogram := run_programPayload_no_workspace_exact rules input padding
        (List.replicate (PakOuterULogBridge.copiedCoreRadius (b :: bits))
          MStarConcreteAlphabet.work)
      have hpayload := run_payloadClock_no_workspace_penultimate input padding
        (ULogBootstrapExecution.programMarkedLeft rules
          (List.replicate (PakOuterULogBridge.copiedCoreRadius (b :: bits))
            MStarConcreteAlphabet.work))
      rw [← heq] at hprogram
      have hstart :
          PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper
            (b :: bits) 1 =
            ⟨[], MStarConcreteAlphabet.work,
              List.replicate (PakOuterULogBridge.copiedCoreRadius (b :: bits))
                  MStarConcreteAlphabet.work ++
                ULogProgram.bitTape b ::
                  (bits.map ULogProgram.bitTape ++
                    [MStarConcreteAlphabet.work])⟩ := by
        apply MStarParserExecution.Zipper.ext <;>
          simp [PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper,
            List.replicate_succ]
      rw [hstart]
      simp only [ULogControl.qStart]
      rw [show (PakOuterULogBridge.copiedCoreRadius (b :: bits) +
          2 * (b :: bits).length + 5 +
          PakULogBootstrapExplicitFuel.programPayloadFuel rules +
            payloadClockNoWorkspaceFuel input padding) - 1 =
          (PakOuterULogBridge.copiedCoreRadius (b :: bits) +
            2 * (b :: bits).length + 5) +
            (PakULogBootstrapExplicitFuel.programPayloadFuel rules +
              (payloadClockNoWorkspaceFuel input padding - 1)) by
                unfold payloadClockNoWorkspaceFuel
                omega,
        ULogBootstrapExecution.run_add, hpreamble]
      simp only [List.append_nil]
      rw [ULogBootstrapExecution.run_add, hprogram]
      exact hpayload

set_option maxHeartbeats 200000

/-- The first state-frame cell cannot be written without a physical work
cell to its right. -/
theorem initStateCell_zero_no_right_stuck (left : List Tape) :
    ULogBootstrapExecution.oneStep
      (.running (ULogControl.State.initStateCell 0)
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.clockSep, []⟩) = .stuck := by
  rfl

/-- Each later unary state-frame cell has the same literal right-boundary
failure when its required successor work cell is absent. -/
theorem initStateCell_one_no_right_stuck (left : List Tape) :
    ULogBootstrapExecution.oneStep
      (.running (ULogControl.State.initStateCell 1)
        ⟨left, MStarConcreteAlphabet.work, []⟩) = .stuck := by
  rfl

theorem initStateCell_two_no_right_stuck (left : List Tape) :
    ULogBootstrapExecution.oneStep
      (.running (ULogControl.State.initStateCell 2)
        ⟨left, MStarConcreteAlphabet.work, []⟩) = .stuck := by
  rfl

theorem initStateCell_three_no_right_stuck (left : List Tape) :
    ULogBootstrapExecution.oneStep
      (.running (ULogControl.State.initStateCell 3)
        ⟨left, MStarConcreteAlphabet.work, []⟩) = .stuck := by
  rfl

/-- A right-moving empty-input initialization shift has no possible final
move once its last non-work cell is at the physical right boundary. -/
theorem initShiftRuntime_no_right_stuck
    (carry x : Tape) (xs left : List Tape)
    (hsafe : ULogBootstrapExecution.ShiftRuntimeSafe (x :: xs)) :
    ULogBootstrapExecution.run (xs.length + 1)
      (.running (.shiftRuntime (.initRight carry)) ⟨left, x, xs⟩) = .stuck := by
  induction xs generalizing carry x left with
  | nil =>
      simp only [List.length_nil, ULogBootstrapExecution.run]
      have hx : x ≠ MStarConcreteAlphabet.work := hsafe x (by simp)
      fin_cases x <;> try rfl
      exact (hx rfl).elim
  | cons y ys ih =>
      have hx : x ≠ MStarConcreteAlphabet.work := hsafe x (by simp)
      have hys : ULogBootstrapExecution.ShiftRuntimeSafe (y :: ys) := by
        intro z hz
        exact hsafe z (by simp [hz])
      rw [show (y :: ys).length + 1 = (ys.length + 1) + 1 by simp,
        ULogBootstrapExecution.run]
      rw [ULogBootstrapExecution.initShiftRight_step carry x hx left y ys]
      exact ih (carry := x) (x := y) (left := carry :: left) hys

/-- One move before the empty-runtime right shift reaches the literal tape
boundary, its control is still part of the bootstrap machine. -/
theorem initShiftRuntime_no_right_penultimate
    (carry x : Tape) (xs left : List Tape)
    (hsafe : ULogBootstrapExecution.ShiftRuntimeSafe (x :: xs)) :
    PakULogGeneralCapacityBootstrapFirstHit.IsBootstrapRunning
      (ULogBootstrapExecution.run xs.length
        (.running (.shiftRuntime (.initRight carry)) ⟨left, x, xs⟩)) := by
  induction xs generalizing carry x left with
  | nil => rfl
  | cons y ys ih =>
      have hx : x ≠ MStarConcreteAlphabet.work := hsafe x (by simp)
      have hys : ULogBootstrapExecution.ShiftRuntimeSafe (y :: ys) := by
        intro z hz
        exact hsafe z (by simp [hz])
      rw [show (y :: ys).length = ys.length + 1 by simp,
        ULogBootstrapExecution.run]
      rw [ULogBootstrapExecution.initShiftRight_step carry x hx left y ys]
      exact ih (carry := x) (x := y) (left := carry :: left) hys

/-- The state-frame writer exposes the exact four-cell lower bound used by a
nonempty payload: after the frame-padding delimiter and its separating work
cell, fewer than four remaining work cells reaches the absorbing `stuck`
result before a cycle boundary can be formed. -/
theorem framePadding_stateWorkspace_underflow_stuck
    (k : ℕ) (hk : k < 4) (left : List Tape) :
    ULogBootstrapExecution.run (k + 4)
      (.running ULogControl.State.framePadding
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.codeEnd,
          MStarConcreteAlphabet.work ::
            List.replicate k MStarConcreteAlphabet.work⟩) = .stuck := by
  interval_cases k <;>
    simp [ULogBootstrapExecution.run,
      ULogBootstrapExecution.framePadding_end_step,
      ULogBootstrapExecution.initializeClock_step,
      ULogBootstrapExecution.initializeState_step,
      ULogBootstrapExecution.initStateCell_zero_step,
      ULogBootstrapExecution.initStateCell_one_step,
      ULogBootstrapExecution.initStateCell_two_step,
      ULogBootstrapExecution.initStateCell_three_step,
      List.replicate_succ] at hk ⊢
  all_goals rfl

theorem initializedPowerClock_stateWorkspace_underflow_stuck
    (padding : List Bool) (k : ℕ) (hk : k < 4) (left : List Tape) :
    ULogBootstrapExecution.run (k + 2)
      (ULogBootstrapExecution.initializedPowerClock padding left
        (List.replicate k MStarConcreteAlphabet.work)) = .stuck := by
  interval_cases k <;>
    simp [ULogBootstrapExecution.run,
      ULogBootstrapExecution.initializedPowerClock,
      ULogBootstrapExecution.initializeState_step,
      ULogBootstrapExecution.initStateCell_zero_step,
      ULogBootstrapExecution.initStateCell_one_step,
      ULogBootstrapExecution.initStateCell_two_step,
      ULogBootstrapExecution.initStateCell_three_step,
      List.replicate_succ] at hk ⊢
  all_goals rfl

/-- One microstep before the common state-frame underflow, control is still
in the literal bootstrap region. -/
theorem initializedPowerClock_stateWorkspace_underflow_penultimate
    (padding : List Bool) (k : ℕ) (hk : k < 4) (left : List Tape) :
    PakULogGeneralCapacityBootstrapFirstHit.IsBootstrapRunning
      (ULogBootstrapExecution.run (k + 1)
        (ULogBootstrapExecution.initializedPowerClock padding left
          (List.replicate k MStarConcreteAlphabet.work))) := by
  interval_cases k <;>
    simp [ULogBootstrapExecution.run,
      ULogBootstrapExecution.initializedPowerClock,
      ULogBootstrapExecution.initializeState_step,
      ULogBootstrapExecution.initStateCell_zero_step,
      ULogBootstrapExecution.initStateCell_one_step,
      ULogBootstrapExecution.initStateCell_two_step,
      ULogBootstrapExecution.initStateCell_three_step,
      ULogBootstrapExecution.initStateCell_four_step,
      List.replicate_succ] at hk ⊢ <;>
    rfl

/-- The complete deterministic bootstrap for a nonempty payload with only
`2 + k` physical cells after the copied word reaches `stuck` before any
semantic cycle can be initialized, whenever `k < 4`. -/
theorem run_generalCapacity_nonempty_shortWorkspace_stuck
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (b : Bool) (bs padding : List Bool) (k : ℕ)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload (b :: bs) padding)
    (hk : k < 4) :
    ULogBootstrapExecution.run
      (PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 5 +
        PakULogBootstrapExplicitFuel.programPayloadFuel rules +
          PakULogBootstrapExplicitFuel.payloadClockFuel (b :: bs) padding +
            (k + 2))
      (.running ULogControl.qStart
        (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper x (2 + k))) =
      .stuck := by
  have hne : x ≠ [] := by
    intro hx
    apply ULogBootstrapExecution.encodedUniversalInput_ne_nil rules (b :: bs) padding
    rw [← hword, hx]
  cases x with
  | nil => exact (hne rfl).elim
  | cons wb wbits =>
      have heq : wb :: wbits = ULogBytecode.encodeProgram rules ++
          ULogBytecode.encodePayload (b :: bs) padding := hword
      have hpreamble := PakULogBootstrapExplicitFuel.run_bootstrap_workspace_exact
        (PakOuterULogBridge.copiedCoreRadius (wb :: wbits)) wb wbits []
        (MStarConcreteAlphabet.work ::
          List.replicate k MStarConcreteAlphabet.work)
      have hprogram := PakULogBootstrapExplicitFuel.run_programPayload_to_payloadStart_all_exact
        rules (b :: bs) padding
        (List.replicate (PakOuterULogBridge.copiedCoreRadius (wb :: wbits))
          MStarConcreteAlphabet.work)
        (List.replicate k MStarConcreteAlphabet.work)
      have hclock := PakULogBootstrapExplicitFuel.run_payloadClock_all_exact
        (b :: bs) padding
        (ULogBootstrapExecution.programMarkedLeft rules
          (List.replicate (PakOuterULogBridge.copiedCoreRadius (wb :: wbits))
            MStarConcreteAlphabet.work))
        (List.replicate k MStarConcreteAlphabet.work)
      have hstuck := initializedPowerClock_stateWorkspace_underflow_stuck
        padding k hk
        (ULogBootstrapExecution.payloadFoldedLeft (b :: bs)
          (ULogBootstrapExecution.programMarkedLeft rules
            (List.replicate (PakOuterULogBridge.copiedCoreRadius (wb :: wbits))
              MStarConcreteAlphabet.work)))
      rw [← heq] at hprogram
      unfold PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper
      rw [show 2 + k = 2 + k by rfl, List.replicate_add]
      simp only [ULogControl.qStart, List.replicate_zero, List.nil_append,
        List.replicate_succ, List.map_cons, List.cons_append, List.append_assoc]
      rw [show PakOuterULogBridge.copiedCoreRadius (wb :: wbits) +
          2 * (wb :: wbits).length + 5 +
          PakULogBootstrapExplicitFuel.programPayloadFuel rules +
            PakULogBootstrapExplicitFuel.payloadClockFuel (b :: bs) padding +
              (k + 2) =
          (PakOuterULogBridge.copiedCoreRadius (wb :: wbits) +
            2 * (wb :: wbits).length + 5) +
            (PakULogBootstrapExplicitFuel.programPayloadFuel rules +
              (PakULogBootstrapExplicitFuel.payloadClockFuel (b :: bs) padding +
                (k + 2))) by omega,
        ULogBootstrapExecution.run_add, hpreamble]
      simp only [List.append_nil]
      rw [ULogBootstrapExecution.run_add, hprogram,
        ULogBootstrapExecution.run_add, hclock]
      exact hstuck

/-- The short-workspace failure is independent of whether the encoded payload
is empty.  After the common program/payload-clock pass, exactly `k` cells
remain for the state frame, and `k < 4` reaches the same literal underflow. -/
theorem run_generalCapacity_shortWorkspace_stuck
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (k : ℕ)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (hk : k < 4) :
    ULogBootstrapExecution.run
      (PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 5 +
        PakULogBootstrapExplicitFuel.programPayloadFuel rules +
          PakULogBootstrapExplicitFuel.payloadClockFuel input padding +
            (k + 2))
      (.running ULogControl.qStart
        (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper x (2 + k))) =
      .stuck := by
  have hne : x ≠ [] := by
    intro hx
    apply ULogBootstrapExecution.encodedUniversalInput_ne_nil rules input padding
    rw [← hword, hx]
  cases x with
  | nil => exact (hne rfl).elim
  | cons wb wbits =>
      have heq : wb :: wbits = ULogBytecode.encodeProgram rules ++
          ULogBytecode.encodePayload input padding := hword
      have hpreamble := PakULogBootstrapExplicitFuel.run_bootstrap_workspace_exact
        (PakOuterULogBridge.copiedCoreRadius (wb :: wbits)) wb wbits []
        (MStarConcreteAlphabet.work ::
          List.replicate k MStarConcreteAlphabet.work)
      have hprogram := PakULogBootstrapExplicitFuel.run_programPayload_to_payloadStart_all_exact
        rules input padding
        (List.replicate (PakOuterULogBridge.copiedCoreRadius (wb :: wbits))
          MStarConcreteAlphabet.work)
        (List.replicate k MStarConcreteAlphabet.work)
      have hclock := PakULogBootstrapExplicitFuel.run_payloadClock_all_exact
        input padding
        (ULogBootstrapExecution.programMarkedLeft rules
          (List.replicate (PakOuterULogBridge.copiedCoreRadius (wb :: wbits))
            MStarConcreteAlphabet.work))
        (List.replicate k MStarConcreteAlphabet.work)
      have hstuck := initializedPowerClock_stateWorkspace_underflow_stuck
        padding k hk
        (ULogBootstrapExecution.payloadFoldedLeft input
          (ULogBootstrapExecution.programMarkedLeft rules
            (List.replicate (PakOuterULogBridge.copiedCoreRadius (wb :: wbits))
              MStarConcreteAlphabet.work)))
      rw [← heq] at hprogram
      unfold PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper
      rw [show 2 + k = 2 + k by rfl, List.replicate_add]
      simp only [ULogControl.qStart, List.replicate_zero, List.nil_append,
        List.replicate_succ, List.map_cons, List.cons_append, List.append_assoc]
      rw [show PakOuterULogBridge.copiedCoreRadius (wb :: wbits) +
          2 * (wb :: wbits).length + 5 +
          PakULogBootstrapExplicitFuel.programPayloadFuel rules +
            PakULogBootstrapExplicitFuel.payloadClockFuel input padding +
              (k + 2) =
          (PakOuterULogBridge.copiedCoreRadius (wb :: wbits) +
            2 * (wb :: wbits).length + 5) +
            (PakULogBootstrapExplicitFuel.programPayloadFuel rules +
              (PakULogBootstrapExplicitFuel.payloadClockFuel input padding +
                (k + 2))) by omega,
        ULogBootstrapExecution.run_add, hpreamble]
      simp only [List.append_nil]
      rw [ULogBootstrapExecution.run_add, hprogram,
        ULogBootstrapExecution.run_add, hclock]
      exact hstuck

/-- The exact short-workspace ledger also records its penultimate iterate:
the machine is still in a bootstrap-only state immediately before underflow. -/
theorem run_generalCapacity_shortWorkspace_penultimate
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (k : ℕ)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (hk : k < 4) :
    PakULogGeneralCapacityBootstrapFirstHit.IsBootstrapRunning
      (ULogBootstrapExecution.run
        (PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 5 +
          PakULogBootstrapExplicitFuel.programPayloadFuel rules +
            PakULogBootstrapExplicitFuel.payloadClockFuel input padding +
              (k + 2) - 1)
        (.running ULogControl.qStart
          (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper x (2 + k)))) := by
  have hne : x ≠ [] := by
    intro hx
    apply ULogBootstrapExecution.encodedUniversalInput_ne_nil rules input padding
    rw [← hword, hx]
  cases x with
  | nil => exact (hne rfl).elim
  | cons wb wbits =>
      have heq : wb :: wbits = ULogBytecode.encodeProgram rules ++
          ULogBytecode.encodePayload input padding := hword
      have hpreamble := PakULogBootstrapExplicitFuel.run_bootstrap_workspace_exact
        (PakOuterULogBridge.copiedCoreRadius (wb :: wbits)) wb wbits []
        (MStarConcreteAlphabet.work ::
          List.replicate k MStarConcreteAlphabet.work)
      have hprogram := PakULogBootstrapExplicitFuel.run_programPayload_to_payloadStart_all_exact
        rules input padding
        (List.replicate (PakOuterULogBridge.copiedCoreRadius (wb :: wbits))
          MStarConcreteAlphabet.work)
        (List.replicate k MStarConcreteAlphabet.work)
      have hclock := PakULogBootstrapExplicitFuel.run_payloadClock_all_exact
        input padding
        (ULogBootstrapExecution.programMarkedLeft rules
          (List.replicate (PakOuterULogBridge.copiedCoreRadius (wb :: wbits))
            MStarConcreteAlphabet.work))
        (List.replicate k MStarConcreteAlphabet.work)
      have hpenult := initializedPowerClock_stateWorkspace_underflow_penultimate
        padding k hk
        (ULogBootstrapExecution.payloadFoldedLeft input
          (ULogBootstrapExecution.programMarkedLeft rules
            (List.replicate (PakOuterULogBridge.copiedCoreRadius (wb :: wbits))
              MStarConcreteAlphabet.work)))
      rw [← heq] at hprogram
      unfold PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper
      rw [show 2 + k = 2 + k by rfl, List.replicate_add]
      simp only [ULogControl.qStart, List.replicate_zero, List.nil_append,
        List.replicate_succ, List.map_cons, List.cons_append, List.append_assoc]
      rw [show (PakOuterULogBridge.copiedCoreRadius (wb :: wbits) +
          2 * (wb :: wbits).length + 5 +
          PakULogBootstrapExplicitFuel.programPayloadFuel rules +
            PakULogBootstrapExplicitFuel.payloadClockFuel input padding +
              (k + 2)) - 1 =
          (PakOuterULogBridge.copiedCoreRadius (wb :: wbits) +
            2 * (wb :: wbits).length + 5) +
            (PakULogBootstrapExplicitFuel.programPayloadFuel rules +
              (PakULogBootstrapExplicitFuel.payloadClockFuel input padding +
                (k + 1))) by omega,
        ULogBootstrapExecution.run_add, hpreamble]
      simp only [List.append_nil]
      rw [ULogBootstrapExecution.run_add, hprogram,
        ULogBootstrapExecution.run_add, hclock]
      exact hpenult

/-- At physical capacity six the empty-input bootstrap reaches the empty
initialization probe with no work cell remaining to its right.  The four
state-frame work cells are sufficient for the frame itself, but the next
empty-input `readHead` action needs one further physical work cell and is
therefore literally stuck. -/
theorem initializedPowerClock_empty_fourWorkspace_stuck
    (padding : List Bool) (base : List Tape) :
    ULogBootstrapExecution.run
      (6 + (ULogBootstrapExecution.headSeekPath padding []).length +
        (ULogBootstrapExecution.emptyInitShiftPrefix padding).length + 3)
      (ULogBootstrapExecution.initializedPowerClock padding
        (ULogBootstrapExecution.payloadFoldedLeft [] base)
        (List.replicate 4 MStarConcreteAlphabet.work)) = .stuck := by
  let seekPath := ULogBootstrapExecution.headSeekPath padding []
  have hframe : ULogBootstrapExecution.run 6
      (ULogBootstrapExecution.initializedPowerClock padding
        (ULogBootstrapExecution.payloadFoldedLeft [] base)
        (List.replicate 4 MStarConcreteAlphabet.work)) =
      .running ULogControl.State.seekSimHead
        (ULogBootstrapExecution.beforeLeftPath seekPath base
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne)
          [ULogAlphabet.ulogCore ULogAlphabet.stateSep]) := by
    simp [ULogBootstrapExecution.run,
      ULogBootstrapExecution.initializedPowerClock,
      ULogBootstrapExecution.payloadFoldedLeft,
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
          [ULogAlphabet.ulogCore ULogAlphabet.stateSep])) =
      .running ULogControl.State.seekSimHead
        (ULogBootstrapExecution.afterLeftPath seekPath base
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne)
          [ULogAlphabet.ulogCore ULogAlphabet.stateSep]) :=
    ULogBootstrapExecution.run_left_path_of ULogControl.State.seekSimHead
      seekPath (ULogBootstrapExecution.headSeekPath_pass padding []) base
      (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne)
      [ULogAlphabet.ulogCore ULogAlphabet.stateSep]
  let pre := ULogBootstrapExecution.emptyInitShiftPrefix padding
  let boundary := ULogBootstrapExecution.emptyInitBoundary padding
  have hpre : pre ≠ [] := by
    cases padding <;>
      simp [pre, ULogBootstrapExecution.emptyInitShiftPrefix]
  have hfail : ULogBootstrapExecution.run (pre.length + 3)
      (.running ULogControl.State.seekSimHead
        (ULogBootstrapExecution.afterLeftPath seekPath base
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne)
          [ULogAlphabet.ulogCore ULogAlphabet.stateSep])) = .stuck := by
    rw [show ULogBootstrapExecution.afterLeftPath seekPath base
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne)
          [ULogAlphabet.ulogCore ULogAlphabet.stateSep] =
        ⟨base, ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne,
          seekPath.reverse ++ [ULogAlphabet.ulogCore ULogAlphabet.stateSep]⟩ by rfl]
    rw [show seekPath = ULogBootstrapExecution.headSeekPath padding [] by rfl,
      ULogBootstrapExecution.headSeekPath_reverse]
    rw [show ULogBootstrapExecution.runtimeSuffix padding [] =
        boundary :: pre ++ [ULogAlphabet.ulogCore ULogAlphabet.stateSep] by
      simp [boundary, pre, ULogBootstrapExecution.runtimeSuffix_emptyInit_after]]
    simp only [List.map_nil, List.nil_append]
    cases hpre' : pre with
    | nil => exact (hpre hpre').elim
    | cons y ys =>
        have hboundary := ULogBootstrapExecution.emptyInit_boundary padding
        have hseek : ULogBootstrapExecution.run 1
            (.running ULogControl.State.seekSimHead
              ⟨base, ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne,
                boundary :: (y :: ys) ++
                  [ULogAlphabet.ulogCore ULogAlphabet.stateSep]⟩) =
            .running ULogControl.State.readHead
              ⟨ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne :: base,
                boundary, (y :: ys) ++
                  [ULogAlphabet.ulogCore ULogAlphabet.stateSep]⟩ := by
          simp only [ULogBootstrapExecution.run]
          exact ULogBootstrapExecution.seekSimHead_empty_step base boundary _
        have hread : ULogBootstrapExecution.run 1
            (.running ULogControl.State.readHead
              ⟨ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne :: base,
                boundary, y :: ys ++
                  [ULogAlphabet.ulogCore ULogAlphabet.stateSep]⟩) =
            .running (.shiftRuntime (.initRight boundary))
              ⟨ULogAlphabet.ulogCore ULogAlphabet.payloadHeadBlank ::
                  ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne :: base,
                y, ys ++ [ULogAlphabet.ulogCore ULogAlphabet.stateSep]⟩ := by
          simp only [ULogBootstrapExecution.run]
          exact ULogBootstrapExecution.readHead_empty_boundary boundary hboundary
            base y (ys ++ [ULogAlphabet.ulogCore ULogAlphabet.stateSep])
        have hsafe : ULogBootstrapExecution.ShiftRuntimeSafe
            (y :: ys ++ [ULogAlphabet.ulogCore ULogAlphabet.stateSep]) := by
          simpa [pre, hpre', List.append_assoc] using
            ULogBootstrapExecution.emptyInit_shift_safe padding
        have hshift := initShiftRuntime_no_right_stuck boundary y
          (ys ++ [ULogAlphabet.ulogCore ULogAlphabet.stateSep])
          (ULogAlphabet.ulogCore ULogAlphabet.payloadHeadBlank ::
            ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne :: base) hsafe
        have hlen : (y :: ys).length + 3 = 1 + (1 + ((ys ++
            [ULogAlphabet.ulogCore ULogAlphabet.stateSep]).length + 1)) := by
          simp
          omega
        rw [hlen,
          ULogBootstrapExecution.run_add, hseek,
          ULogBootstrapExecution.run_add, hread]
        simpa using hshift
  rw [show 6 + seekPath.length + pre.length + 3 =
      6 + (seekPath.length + (pre.length + 3)) by omega,
    ULogBootstrapExecution.run_add, hframe,
    ULogBootstrapExecution.run_add, hscan]
  simpa [pre] using hfail

/-- The capacity-six empty initialization has a certified bootstrap-running
predecessor immediately before its final right-shift boundary failure. -/
theorem initializedPowerClock_empty_fourWorkspace_penultimate
    (padding : List Bool) (base : List Tape) :
    PakULogGeneralCapacityBootstrapFirstHit.IsBootstrapRunning
      (ULogBootstrapExecution.run
        (6 + (ULogBootstrapExecution.headSeekPath padding []).length +
          (ULogBootstrapExecution.emptyInitShiftPrefix padding).length + 3 - 1)
        (ULogBootstrapExecution.initializedPowerClock padding
          (ULogBootstrapExecution.payloadFoldedLeft [] base)
          (List.replicate 4 MStarConcreteAlphabet.work))) := by
  let seekPath := ULogBootstrapExecution.headSeekPath padding []
  have hframe : ULogBootstrapExecution.run 6
      (ULogBootstrapExecution.initializedPowerClock padding
        (ULogBootstrapExecution.payloadFoldedLeft [] base)
        (List.replicate 4 MStarConcreteAlphabet.work)) =
      .running ULogControl.State.seekSimHead
        (ULogBootstrapExecution.beforeLeftPath seekPath base
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne)
          [ULogAlphabet.ulogCore ULogAlphabet.stateSep]) := by
    simp [ULogBootstrapExecution.run,
      ULogBootstrapExecution.initializedPowerClock,
      ULogBootstrapExecution.payloadFoldedLeft,
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
          [ULogAlphabet.ulogCore ULogAlphabet.stateSep])) =
      .running ULogControl.State.seekSimHead
        (ULogBootstrapExecution.afterLeftPath seekPath base
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne)
          [ULogAlphabet.ulogCore ULogAlphabet.stateSep]) :=
    ULogBootstrapExecution.run_left_path_of ULogControl.State.seekSimHead
      seekPath (ULogBootstrapExecution.headSeekPath_pass padding []) base
      (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne)
      [ULogAlphabet.ulogCore ULogAlphabet.stateSep]
  let pre := ULogBootstrapExecution.emptyInitShiftPrefix padding
  let boundary := ULogBootstrapExecution.emptyInitBoundary padding
  have hpre : pre ≠ [] := by
    cases padding <;>
      simp [pre, ULogBootstrapExecution.emptyInitShiftPrefix]
  have hpenult : PakULogGeneralCapacityBootstrapFirstHit.IsBootstrapRunning
      (ULogBootstrapExecution.run (pre.length + 2)
        (.running ULogControl.State.seekSimHead
          (ULogBootstrapExecution.afterLeftPath seekPath base
            (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne)
            [ULogAlphabet.ulogCore ULogAlphabet.stateSep]))) := by
    rw [show ULogBootstrapExecution.afterLeftPath seekPath base
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne)
          [ULogAlphabet.ulogCore ULogAlphabet.stateSep] =
        ⟨base, ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne,
          seekPath.reverse ++ [ULogAlphabet.ulogCore ULogAlphabet.stateSep]⟩ by rfl]
    rw [show seekPath = ULogBootstrapExecution.headSeekPath padding [] by rfl,
      ULogBootstrapExecution.headSeekPath_reverse]
    rw [show ULogBootstrapExecution.runtimeSuffix padding [] =
        boundary :: pre ++ [ULogAlphabet.ulogCore ULogAlphabet.stateSep] by
      simp [boundary, pre, ULogBootstrapExecution.runtimeSuffix_emptyInit_after]]
    simp only [List.map_nil, List.nil_append]
    cases hpre' : pre with
    | nil => exact (hpre hpre').elim
    | cons y ys =>
        have hboundary := ULogBootstrapExecution.emptyInit_boundary padding
        have hseek : ULogBootstrapExecution.run 1
            (.running ULogControl.State.seekSimHead
              ⟨base, ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne,
                boundary :: (y :: ys) ++
                  [ULogAlphabet.ulogCore ULogAlphabet.stateSep]⟩) =
            .running ULogControl.State.readHead
              ⟨ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne :: base,
                boundary, (y :: ys) ++
                  [ULogAlphabet.ulogCore ULogAlphabet.stateSep]⟩ := by
          simp only [ULogBootstrapExecution.run]
          exact ULogBootstrapExecution.seekSimHead_empty_step base boundary _
        have hread : ULogBootstrapExecution.run 1
            (.running ULogControl.State.readHead
              ⟨ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne :: base,
                boundary, y :: ys ++
                  [ULogAlphabet.ulogCore ULogAlphabet.stateSep]⟩) =
            .running (.shiftRuntime (.initRight boundary))
              ⟨ULogAlphabet.ulogCore ULogAlphabet.payloadHeadBlank ::
                  ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne :: base,
                y, ys ++ [ULogAlphabet.ulogCore ULogAlphabet.stateSep]⟩ := by
          simp only [ULogBootstrapExecution.run]
          exact ULogBootstrapExecution.readHead_empty_boundary boundary hboundary
            base y (ys ++ [ULogAlphabet.ulogCore ULogAlphabet.stateSep])
        have hsafe : ULogBootstrapExecution.ShiftRuntimeSafe
            (y :: ys ++ [ULogAlphabet.ulogCore ULogAlphabet.stateSep]) := by
          simpa [pre, hpre', List.append_assoc] using
            ULogBootstrapExecution.emptyInit_shift_safe padding
        have hshift := initShiftRuntime_no_right_penultimate boundary y
          (ys ++ [ULogAlphabet.ulogCore ULogAlphabet.stateSep])
          (ULogAlphabet.ulogCore ULogAlphabet.payloadHeadBlank ::
            ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne :: base) hsafe
        have hlen : (y :: ys).length + 2 = 1 + (1 +
            (ys ++ [ULogAlphabet.ulogCore ULogAlphabet.stateSep]).length) := by
          simp
          omega
        rw [hlen,
          ULogBootstrapExecution.run_add, hseek,
          ULogBootstrapExecution.run_add, hread]
        simpa using hshift
  rw [show 6 + seekPath.length + pre.length + 3 - 1 =
      6 + (seekPath.length + (pre.length + 2)) by omega,
    ULogBootstrapExecution.run_add, hframe,
    ULogBootstrapExecution.run_add, hscan]
  simpa [pre] using hpenult

/-- The physical capacity-six empty-input core has five cells after the
translated code word.  The program/payload-clock pass leaves four cells for
the state frame, so the explicit empty initialization probe above reaches
`stuck`. -/
theorem run_generalCapacity_empty_six_stuck
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload [] padding) :
    ULogBootstrapExecution.run
      (PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 5 +
        PakULogBootstrapExplicitFuel.programPayloadFuel rules +
          PakULogBootstrapExplicitFuel.payloadClockFuel [] padding +
            (6 + (ULogBootstrapExecution.headSeekPath padding []).length +
              (ULogBootstrapExecution.emptyInitShiftPrefix padding).length + 3))
      (.running ULogControl.qStart
        (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper x 6)) =
      .stuck := by
  have hne : x ≠ [] := by
    intro hx
    apply ULogBootstrapExecution.encodedUniversalInput_ne_nil rules [] padding
    rw [← hword, hx]
  cases x with
  | nil => exact (hne rfl).elim
  | cons wb wbits =>
      have heq : wb :: wbits = ULogBytecode.encodeProgram rules ++
          ULogBytecode.encodePayload [] padding := hword
      have hpreamble := PakULogBootstrapExplicitFuel.run_bootstrap_workspace_exact
        (PakOuterULogBridge.copiedCoreRadius (wb :: wbits)) wb wbits []
        (List.replicate 5 MStarConcreteAlphabet.work)
      have hprogram := PakULogBootstrapExplicitFuel.run_programPayload_to_payloadStart_all_exact
        rules [] padding
        (List.replicate (PakOuterULogBridge.copiedCoreRadius (wb :: wbits))
          MStarConcreteAlphabet.work)
        (List.replicate 4 MStarConcreteAlphabet.work)
      have hclock := PakULogBootstrapExplicitFuel.run_payloadClock_all_exact
        [] padding
        (ULogBootstrapExecution.programMarkedLeft rules
          (List.replicate (PakOuterULogBridge.copiedCoreRadius (wb :: wbits))
            MStarConcreteAlphabet.work))
        (List.replicate 4 MStarConcreteAlphabet.work)
      have hstuck := initializedPowerClock_empty_fourWorkspace_stuck padding
        (ULogBootstrapExecution.programMarkedLeft rules
          (List.replicate (PakOuterULogBridge.copiedCoreRadius (wb :: wbits))
            MStarConcreteAlphabet.work))
      rw [← heq] at hprogram
      have hstart :
          PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper
            (wb :: wbits) 6 =
            ⟨[], MStarConcreteAlphabet.work,
              List.replicate (PakOuterULogBridge.copiedCoreRadius (wb :: wbits))
                  MStarConcreteAlphabet.work ++
                ULogProgram.bitTape wb ::
                  (wbits.map ULogProgram.bitTape ++
                    MStarConcreteAlphabet.work ::
                      List.replicate 5 MStarConcreteAlphabet.work)⟩ := by
        apply MStarParserExecution.Zipper.ext <;>
          simp [PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper,
            List.replicate_succ]
      rw [hstart]
      simp only [ULogControl.qStart]
      rw [show PakOuterULogBridge.copiedCoreRadius (wb :: wbits) +
          2 * (wb :: wbits).length + 5 +
          PakULogBootstrapExplicitFuel.programPayloadFuel rules +
            PakULogBootstrapExplicitFuel.payloadClockFuel [] padding +
              (6 + (ULogBootstrapExecution.headSeekPath padding []).length +
                (ULogBootstrapExecution.emptyInitShiftPrefix padding).length + 3) =
          (PakOuterULogBridge.copiedCoreRadius (wb :: wbits) +
            2 * (wb :: wbits).length + 5) +
            (PakULogBootstrapExplicitFuel.programPayloadFuel rules +
              (PakULogBootstrapExplicitFuel.payloadClockFuel [] padding +
                (6 + (ULogBootstrapExecution.headSeekPath padding []).length +
                  (ULogBootstrapExecution.emptyInitShiftPrefix padding).length + 3))) by omega,
        ULogBootstrapExecution.run_add, hpreamble]
      simp only [List.append_nil]
      have hfive : List.replicate 5 MStarConcreteAlphabet.work =
          MStarConcreteAlphabet.work ::
            List.replicate 4 MStarConcreteAlphabet.work := by
        norm_num [List.replicate_succ]
      rw [hfive]
      rw [ULogBootstrapExecution.run_add, hprogram,
        ULogBootstrapExecution.run_add, hclock]
      exact hstuck

/-- The capacity-six empty-input global execution remains bootstrap-running
at the iterate immediately before the explicit empty-runtime boundary
underflow. -/
theorem run_generalCapacity_empty_six_penultimate
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload [] padding) :
    PakULogGeneralCapacityBootstrapFirstHit.IsBootstrapRunning
      (ULogBootstrapExecution.run
        (PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 5 +
          PakULogBootstrapExplicitFuel.programPayloadFuel rules +
            PakULogBootstrapExplicitFuel.payloadClockFuel [] padding +
              (6 + (ULogBootstrapExecution.headSeekPath padding []).length +
                (ULogBootstrapExecution.emptyInitShiftPrefix padding).length + 3) - 1)
        (.running ULogControl.qStart
          (PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper x 6))) := by
  have hne : x ≠ [] := by
    intro hx
    apply ULogBootstrapExecution.encodedUniversalInput_ne_nil rules [] padding
    rw [← hword, hx]
  cases x with
  | nil => exact (hne rfl).elim
  | cons wb wbits =>
      have heq : wb :: wbits = ULogBytecode.encodeProgram rules ++
          ULogBytecode.encodePayload [] padding := hword
      have hpreamble := PakULogBootstrapExplicitFuel.run_bootstrap_workspace_exact
        (PakOuterULogBridge.copiedCoreRadius (wb :: wbits)) wb wbits []
        (List.replicate 5 MStarConcreteAlphabet.work)
      have hprogram := PakULogBootstrapExplicitFuel.run_programPayload_to_payloadStart_all_exact
        rules [] padding
        (List.replicate (PakOuterULogBridge.copiedCoreRadius (wb :: wbits))
          MStarConcreteAlphabet.work)
        (List.replicate 4 MStarConcreteAlphabet.work)
      have hclock := PakULogBootstrapExplicitFuel.run_payloadClock_all_exact
        [] padding
        (ULogBootstrapExecution.programMarkedLeft rules
          (List.replicate (PakOuterULogBridge.copiedCoreRadius (wb :: wbits))
            MStarConcreteAlphabet.work))
        (List.replicate 4 MStarConcreteAlphabet.work)
      have hpenult := initializedPowerClock_empty_fourWorkspace_penultimate padding
        (ULogBootstrapExecution.programMarkedLeft rules
          (List.replicate (PakOuterULogBridge.copiedCoreRadius (wb :: wbits))
            MStarConcreteAlphabet.work))
      rw [← heq] at hprogram
      have hstart :
          PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper
            (wb :: wbits) 6 =
            ⟨[], MStarConcreteAlphabet.work,
              List.replicate (PakOuterULogBridge.copiedCoreRadius (wb :: wbits))
                  MStarConcreteAlphabet.work ++
                ULogProgram.bitTape wb ::
                  (wbits.map ULogProgram.bitTape ++
                    MStarConcreteAlphabet.work ::
                      List.replicate 5 MStarConcreteAlphabet.work)⟩ := by
        apply MStarParserExecution.Zipper.ext <;>
          simp [PakULogGeneralCapacityBootstrap.generalCapacityCoreZipper,
            List.replicate_succ]
      rw [hstart]
      simp only [ULogControl.qStart]
      rw [show (PakOuterULogBridge.copiedCoreRadius (wb :: wbits) +
          2 * (wb :: wbits).length + 5 +
          PakULogBootstrapExplicitFuel.programPayloadFuel rules +
            PakULogBootstrapExplicitFuel.payloadClockFuel [] padding +
              (6 + (ULogBootstrapExecution.headSeekPath padding []).length +
                (ULogBootstrapExecution.emptyInitShiftPrefix padding).length + 3) - 1 =
          (PakOuterULogBridge.copiedCoreRadius (wb :: wbits) +
            2 * (wb :: wbits).length + 5) +
            (PakULogBootstrapExplicitFuel.programPayloadFuel rules +
              (PakULogBootstrapExplicitFuel.payloadClockFuel [] padding +
                (6 + (ULogBootstrapExecution.headSeekPath padding []).length +
                  (ULogBootstrapExecution.emptyInitShiftPrefix padding).length + 3 - 1)))) by
                    omega,
        ULogBootstrapExecution.run_add, hpreamble]
      simp only [List.append_nil]
      have hfive : List.replicate 5 MStarConcreteAlphabet.work =
          MStarConcreteAlphabet.work ::
            List.replicate 4 MStarConcreteAlphabet.work := by
        norm_num [List.replicate_succ]
      rw [hfive]
      rw [ULogBootstrapExecution.run_add, hprogram,
        ULogBootstrapExecution.run_add, hclock]
      exact hpenult

end PakFixedPolyomino.PakULogGeneralCapacityUnderCapacity
