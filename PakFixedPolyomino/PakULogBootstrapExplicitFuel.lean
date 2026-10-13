import PakFixedPolyomino.PakULogExplicitFuel

/-!
# Explicit outer-arrow fuel for the deterministic `U_log` bootstrap

The existing bridge records the bootstrap only as `OuterReaches`: its witness
is an existential run length.  This file keeps that length as a named,
minimal natural number and lifts the *same* `U_log` run one physical outer
arrow at a time.  No semantic-time bound is assumed here.
-/

namespace PakFixedPolyomino.PakULogBootstrapExplicitFuel

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics
open PakParserOuterBridge
open PakOuterULogBridge
  (anchoredFramedULogConfig copiedULogStartZipper copiedSemanticStartZipper
    copiedULogStart_reaches_semanticStart copiedSemanticStartEncoding_eq_running
    ulogOneStep_eq_running_iff)
open PakOuterFrontQuantitative
  (OuterReachesAtMost outerReachesAtMost_refl outerReachesAtMost_trans)
open PakULogExplicitFuel (framedRunningStep_outer_atMostOne)

abbrev OuterTape := PakParserOuterBridge.OuterTape
abbrev OuterConfig := PakOuterFrontQuantitative.OuterConfig

/-- A running finite `U_log` execution with `fuel` microsteps lifts to at
most `fuel` literal outer arrows.  This is the quantitative version of the
old existential framed reachability lift. -/
theorem ulogRun_running_outer_framed_atMost
    (fuel : ℕ) (q q' : ULogControl.State) (origin : Int)
    (leftExtra rightExtra : List OuterTape)
    (z z' : MStarParserExecution.Zipper ULogProgram.Tape)
    (hrun : ULogBootstrapExecution.run fuel (.running q z) = .running q' z') :
    OuterReachesAtMost fuel
      (anchoredFramedULogConfig q origin leftExtra rightExtra z)
      (anchoredFramedULogConfig q' origin leftExtra rightExtra z') := by
  induction fuel generalizing q z with
  | zero =>
      simp only [ULogBootstrapExecution.run] at hrun
      cases hrun
      exact outerReachesAtMost_refl _
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
          have hstep := framedRunningStep_outer_atMostOne q q₁ 0 origin
            leftExtra rightExtra z z₁ a hrule happly htarget haccept hreject
          have hrest := ih q₁ z₁ htail
          simpa [Nat.succ_eq_add_one, Nat.add_comm] using
            outerReachesAtMost_trans hstep hrest

/-- The least deterministic bootstrap microstep count from the copied
universal instance to the semantic cycle-start frame.  This is a concrete
natural number determined by the executable `U_log` transition table and
the supplied instance; it is not an assumed asymptotic budget. -/
noncomputable def bootstrapFuel
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) : ℕ :=
  Nat.find (copiedULogStart_reaches_semanticStart x rules input padding hword)

theorem run_bootstrapFuel
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    ULogBootstrapExecution.run (bootstrapFuel x rules input padding hword)
      (.running ULogControl.qStart (copiedULogStartZipper x)) =
      .running ULogControl.State.cycleStart
        (copiedSemanticStartZipper x rules input padding) := by
  exact Nat.find_spec
    (copiedULogStart_reaches_semanticStart x rules input padding hword)

/-- Any concrete bootstrap run has length at least `bootstrapFuel`; this is
the useful exact residual numerical obligation for a later closed-form
bootstrap cost analysis. -/
theorem bootstrapFuel_le_of_run
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (fuel : ℕ)
    (hrun : ULogBootstrapExecution.run fuel
      (.running ULogControl.qStart (copiedULogStartZipper x)) =
      .running ULogControl.State.cycleStart
        (copiedSemanticStartZipper x rules input padding)) :
    bootstrapFuel x rules input padding hword ≤ fuel := by
  unfold bootstrapFuel
  exact Nat.find_min'
    (copiedULogStart_reaches_semanticStart x rules input padding hword) hrun

/-- The old bootstrap bridge with an explicit literal outer-arrow budget.
The bound is exactly the least finite-bootstrap microstep count, because each
successful simulated microstep is realized by one outer arrow. -/
theorem copiedULogStart_outer_reaches_semanticStart_atMost
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (origin : Int) (leftExtra rightExtra : List OuterTape) :
    OuterReachesAtMost (bootstrapFuel x rules input padding hword)
      (anchoredFramedULogConfig ULogControl.qStart origin leftExtra rightExtra
        (copiedULogStartZipper x))
      (anchoredFramedULogConfig ULogControl.State.cycleStart origin
        leftExtra rightExtra
        (copiedSemanticStartZipper x rules input padding)) := by
  exact ulogRun_running_outer_framed_atMost
    (bootstrapFuel x rules input padding hword)
    ULogControl.qStart ULogControl.State.cycleStart origin leftExtra rightExtra
    (copiedULogStartZipper x) (copiedSemanticStartZipper x rules input padding)
    (run_bootstrapFuel x rules input padding hword)

/-- The scanner/translator prefix of bootstrap has a closed exact cost.  The
input word is written as its nonempty first bit followed by `bits`; the five
pieces are the three fixed entry actions, a forward scan, the code-end turn,
the return scan, and the final framing action. -/
theorem run_bootstrap_nonempty_exact
    (b : Bool) (bits : List Bool) (left tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (2 * bits.length + 6)
      (.running ULogControl.State.start
        ⟨MStarConcreteAlphabet.work :: left, ULogProgram.bitTape b,
          bits.map ULogProgram.bitTape ++ MStarConcreteAlphabet.work :: tail⟩) =
      .running ULogControl.State.framePayloadLength
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          (b :: bits).map ULogProgram.codeTape ++
            ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail⟩ := by
  have hentry : ULogBootstrapExecution.run 3
      (.running ULogControl.State.start
        ⟨MStarConcreteAlphabet.work :: left, ULogProgram.bitTape b,
          bits.map ULogProgram.bitTape ++ MStarConcreteAlphabet.work :: tail⟩) =
      .running ULogControl.State.seekPayload
        (ULogBootstrapExecution.beforePayload bits
          (ULogProgram.codeTape b ::
            ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left) tail) := by
    cases bits <;>
      simp [ULogBootstrapExecution.run, ULogBootstrapExecution.beforePayload,
        ULogBootstrapExecution.start_bit_step,
        ULogBootstrapExecution.translateCode_step,
        ULogBootstrapExecution.framePayload_step]
  have hscan : ULogBootstrapExecution.run bits.length
      (.running ULogControl.State.seekPayload
        (ULogBootstrapExecution.beforePayload bits
          (ULogProgram.codeTape b ::
            ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left) tail)) =
      .running ULogControl.State.seekPayload
        (ULogBootstrapExecution.afterPayload bits
          (ULogProgram.codeTape b ::
            ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left) tail) :=
    ULogBootstrapExecution.run_seekPayload_bits bits _ tail
  have hturn : ULogBootstrapExecution.run 1
      (.running ULogControl.State.seekPayload
        (ULogBootstrapExecution.afterPayload bits
          (ULogProgram.codeTape b ::
            ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left) tail)) =
      .running ULogControl.State.translateReturn
        (ULogBootstrapExecution.beforeReturn (b :: bits) left tail) := by
    unfold ULogBootstrapExecution.run ULogBootstrapExecution.beforeReturn
      ULogBootstrapExecution.afterPayload
    simp only [ULogBootstrapExecution.run]
    rw [show (b :: bits).reverse = bits.reverse ++ [b] by simp]
    cases hrev : bits.reverse with
    | nil =>
        have hbits : bits = [] := by
          simpa using congrArg List.reverse hrev
        subst bits
        simpa using ULogBootstrapExecution.seekPayload_end_step
          (ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left) tail
          (ULogProgram.codeTape b)
    | cons c cs =>
        have hmap : (bits.map ULogProgram.codeTape).reverse =
            ULogProgram.codeTape c ::
              cs.map ULogProgram.codeTape := by
          calc
            (bits.map ULogProgram.codeTape).reverse =
                bits.reverse.map ULogProgram.codeTape := by
              exact (List.map_reverse (l := bits)
                (f := ULogProgram.codeTape)).symm
            _ = ULogProgram.codeTape c ::
                cs.map ULogProgram.codeTape := by rw [hrev]; rfl
        simp only [List.cons_append, List.map_append, List.map_cons,
          List.map_nil]
        simpa [List.append_assoc] using
          ULogBootstrapExecution.seekPayload_end_step
            (cs.map ULogProgram.codeTape ++
              ULogProgram.codeTape b ::
                ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
            tail (ULogProgram.codeTape c)
  have hreturn : ULogBootstrapExecution.run (b :: bits).length
      (.running ULogControl.State.translateReturn
        (ULogBootstrapExecution.beforeReturn (b :: bits) left tail)) =
      .running ULogControl.State.translateReturn
        (ULogBootstrapExecution.afterReturn (b :: bits) left tail) :=
    ULogBootstrapExecution.run_translateReturn_bits (b :: bits) left tail
  have hframe : ULogBootstrapExecution.run 1
      (.running ULogControl.State.translateReturn
        (ULogBootstrapExecution.afterReturn (b :: bits) left tail)) =
      .running ULogControl.State.framePayloadLength
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          (b :: bits).map ULogProgram.codeTape ++
            ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail⟩ := by
    simpa [ULogBootstrapExecution.run, ULogBootstrapExecution.afterReturn] using
      ULogBootstrapExecution.translateReturn_mark_step left
        ((b :: bits).map ULogProgram.codeTape ++
          ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail)
  rw [show 2 * bits.length + 6 =
      3 + (bits.length + (1 + ((b :: bits).length + 1))) by simp; omega]
  rw [ULogBootstrapExecution.run_add, hentry]
  rw [ULogBootstrapExecution.run_add, hscan]
  rw [ULogBootstrapExecution.run_add, hturn]
  rw [ULogBootstrapExecution.run_add, hreturn]
  exact hframe

/-- Moving over the copied all-work prefix and translating the nonempty
universal word has exact cost `R + 2 * |word| + 5`. -/
theorem run_bootstrap_workspace_exact
    (n : ℕ) (b : Bool) (bits : List Bool)
    (source tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (n + 2 * (b :: bits).length + 5)
      (.running ULogControl.State.start
        ⟨source, MStarConcreteAlphabet.work,
          List.replicate n MStarConcreteAlphabet.work ++
            ULogProgram.bitTape b ::
              (bits.map ULogProgram.bitTape ++
                MStarConcreteAlphabet.work :: tail)⟩) =
      .running ULogControl.State.framePayloadLength
        ⟨List.replicate n MStarConcreteAlphabet.work ++ source,
          ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          (b :: bits).map ULogProgram.codeTape ++
            ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail⟩ := by
  rw [show n + 2 * (b :: bits).length + 5 =
      (n + 1) + (2 * bits.length + 6) by simp; omega]
  rw [ULogBootstrapExecution.run_add]
  change ULogBootstrapExecution.run (2 * bits.length + 6)
      (ULogBootstrapExecution.run (n + 1)
        (.running ULogControl.State.start
          (ULogBootstrapExecution.beforeStartWork (n + 1) source
            (ULogProgram.bitTape b)
            (bits.map ULogProgram.bitTape ++
              MStarConcreteAlphabet.work :: tail)))) = _
  rw [ULogBootstrapExecution.run_start_work]
  simpa [ULogBootstrapExecution.afterStartWork, List.replicate_succ,
    List.append_assoc] using
    (run_bootstrap_nonempty_exact b bits
      (List.replicate n MStarConcreteAlphabet.work ++ source) tail)

/-- Kernel-only copy of the frozen `initializedRuntime_eq_semanticCycleEncoding`
identity.  The four cell equations are `simp`/`rfl` rather than compiler-trust
`native_decide`. -/
theorem initializedRuntime_eq_semanticCycleEncoding_kernel
    (n : ℕ) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (source tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.initializedRuntime padding input
        (ULogBootstrapExecution.programMarkedLeft rules
          (List.replicate n MStarConcreteAlphabet.work ++ source)) tail =
      ULogBootstrapExecution.semanticCycleEncoding input
        (ULogBootstrapExecution.clockCellsBefore
          ((ULogSemantics.startFrom rules input).right.map
            ULogBootstrapExecution.payloadNat)
          padding.length [ULogAlphabet.ulogCore ULogAlphabet.clockSep])
        2 (List.replicate n MStarConcreteAlphabet.work ++ source) tail
        (ULogSemantics.startFrom rules input) := by
  cases input with
  | nil =>
      simp [ULogBootstrapExecution.initializedRuntime,
        ULogBootstrapExecution.semanticCycleEncoding,
        ULogSemantics.startFrom, ULogSemantics.initialTape,
        ULogSemantics.startCode, ULogSemantics.blankCode,
        ULogBootstrapExecution.dynamicRuleReturnPath,
        ULogBootstrapExecution.ruleReturnPath,
        ULogBootstrapExecution.payloadProgramPrefix,
        ULogBootstrapExecution.programMarkedLeft,
        ULogBootstrapExecution.clockCellsBefore,
        ULogBootstrapExecution.runtimeSuffix,
        ULogBootstrapExecution.stateWorkspace,
        ULogBootstrapExecution.readHeadNat,
        ULogBootstrapExecution.payloadNat, ULogProgram.codeTape,
        List.append_assoc]
  | cons b bs =>
      have hz : ULogProgram.payloadTape false =
          ULogProgram.unheadTape
            (ULogAlphabet.ulogCore ULogAlphabet.payloadHeadZero) := by
        decide
      have ho : ULogProgram.payloadTape true =
          ULogProgram.unheadTape
            (ULogAlphabet.ulogCore ULogAlphabet.payloadHeadOne) := by
        decide
      have hn₀ : ULogBootstrapExecution.payloadNat 0 =
          ULogAlphabet.ulogCore ULogAlphabet.dataZero := by
        decide
      have hn₁ : ULogBootstrapExecution.payloadNat 1 =
          ULogAlphabet.ulogCore ULogAlphabet.dataOne := by
        decide
      cases b <;>
        simp [ULogBootstrapExecution.initializedRuntime,
          ULogBootstrapExecution.semanticCycleEncoding,
          ULogSemantics.startFrom, ULogSemantics.initialTape,
          ULogSemantics.startCode, ULogSemantics.bitCode,
          ULogBootstrapExecution.dynamicRuleReturnPath,
          ULogBootstrapExecution.ruleReturnPath,
          ULogBootstrapExecution.payloadProgramPrefix,
          ULogBootstrapExecution.programMarkedLeft,
          ULogBootstrapExecution.clockCellsBefore,
          ULogBootstrapExecution.runtimeSuffix,
          ULogBootstrapExecution.stateWorkspace,
          ULogBootstrapExecution.readHeadNat, ULogProgram.payloadTape,
          ULogProgram.codeTape, List.map_map, hz, ho, hn₀, hn₁,
          List.append_assoc]

/-- The runtime-initialization endpoint is definitionally the copied semantic
cycle-start zipper.  Stating this equality separately prevents the remaining
bootstrap cost from being hidden behind a representation conversion. -/
theorem copied_initializedRuntime_eq_semanticStart
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) :
    ULogBootstrapExecution.initializedRuntime padding input
      (ULogBootstrapExecution.programMarkedLeft rules
        (List.replicate (PakOuterULogBridge.copiedCoreRadius x)
          MStarConcreteAlphabet.work))
      (PakOuterULogBridge.copiedBootstrapTail x input) =
      .running ULogControl.State.cycleStart
        (copiedSemanticStartZipper x rules input padding) := by
  have hinit := initializedRuntime_eq_semanticCycleEncoding_kernel
    (PakOuterULogBridge.copiedCoreRadius x) rules input padding []
    (PakOuterULogBridge.copiedBootstrapTail x input)
  simp only [List.append_nil] at hinit
  exact hinit.trans (copiedSemanticStartEncoding_eq_running x rules input padding)

/-- The unresolved payload/clock/runtime portion has a separately named
least fuel.  The preceding scanner/translator cost is already closed by
`run_bootstrap_workspace_exact`; this definition makes the sole remaining
numeric subproblem visible rather than burying it in bootstrap reachability. -/
noncomputable def copiedRuntimeInitializationFuel
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) : ℕ :=
  Nat.find (ULogBootstrapExecution.reaches_payloadRuntimeInitialized rules
    input padding
    (List.replicate (PakOuterULogBridge.copiedCoreRadius x)
      MStarConcreteAlphabet.work)
    (PakOuterULogBridge.copiedBootstrapTail x input))

/-- The clock-framing suffix after payload folding is genuinely closed: one
pass over the padding and two fixed actions. -/
theorem run_initializedPowerClock_exact
    (padding : List Bool) (left tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (padding.length + 2)
      (.running ULogControl.State.framePadding
        (ULogBootstrapExecution.beforeClockPadding padding left tail)) =
      ULogBootstrapExecution.initializedPowerClock padding left tail := by
  rw [show padding.length + 2 = padding.length + (1 + 1) by omega]
  rw [ULogBootstrapExecution.run_add,
    ULogBootstrapExecution.run_framePadding]
  simp [ULogBootstrapExecution.run, ULogBootstrapExecution.afterClockPadding,
    ULogBootstrapExecution.framePadding_end_step,
    ULogBootstrapExecution.initializeClock_step,
    ULogBootstrapExecution.initializedPowerClock]

/-- A first exact primitive inside the remaining payload fold: returning
across `processed` has the literal cost `|processed| + 1`. -/
theorem run_payloadReturn_end_exact
    (carry : Bool) (processed : List Bool)
    (counter right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (processed.length + 1)
      (.running (ULogControl.State.fieldReturn .payloadLength)
        ⟨processed.reverse.map ULogProgram.payloadTape ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadEnd :: counter,
          ULogProgram.codeTape carry, right⟩) =
      .running (ULogControl.State.payloadReturn carry)
        ⟨counter, ULogAlphabet.ulogCore ULogAlphabet.payloadEnd,
          processed.map ULogProgram.payloadTape ++
            ULogProgram.branchTape carry :: right⟩ := by
  let path := processed.reverse.map ULogProgram.payloadTape
  have hstep : ULogBootstrapExecution.run 1
      (.running (ULogControl.State.fieldReturn .payloadLength)
        ⟨path ++ ULogAlphabet.ulogCore ULogAlphabet.payloadEnd :: counter,
          ULogProgram.codeTape carry, right⟩) =
      .running (ULogControl.State.payloadReturn carry)
        (ULogBootstrapExecution.beforeLeftPath path counter
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
          (ULogProgram.branchTape carry :: right)) := by
    unfold ULogBootstrapExecution.run
    cases hp : path with
    | nil =>
        simp [ULogBootstrapExecution.run, ULogBootstrapExecution.beforeLeftPath,
          ULogBootstrapExecution.fieldReturn_payload_step]
    | cons x xs =>
        simp [ULogBootstrapExecution.run, ULogBootstrapExecution.beforeLeftPath,
          ULogBootstrapExecution.fieldReturn_payload_step,
          List.cons_append]
  have hpath : ULogBootstrapExecution.run path.length
      (.running (ULogControl.State.payloadReturn carry)
        (ULogBootstrapExecution.beforeLeftPath path counter
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
          (ULogProgram.branchTape carry :: right))) =
      .running (ULogControl.State.payloadReturn carry)
        (ULogBootstrapExecution.afterLeftPath path counter
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
          (ULogProgram.branchTape carry :: right)) := by
    exact ULogBootstrapExecution.run_left_path_of
      (ULogControl.State.payloadReturn carry) path (by
        intro x hx l y r
        rcases List.mem_map.mp hx with ⟨b, -, rfl⟩
        exact ULogBootstrapExecution.payloadReturn_pass_code carry b l y r)
      counter (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
      (ULogProgram.branchTape carry :: right)
  rw [show processed.length + 1 = 1 + path.length by
    simp [path]; omega]
  rw [ULogBootstrapExecution.run_add, hstep, hpath]
  simp [path, ULogBootstrapExecution.afterLeftPath, List.map_reverse]

/-- The terminal payload-fold action is also exact.  Together with
`run_payloadReturn_end_exact`, this exposes the base case of the recursive
payload fold as `2|processed| + 2·done + 5` microsteps. -/
theorem run_payloadFreshStart_exact
    (carry : Bool) (next : ULogProgram.Tape)
    (processed : List Bool) (done : ℕ) (base right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (2 * processed.length + 2 * done + 5)
      (.running (ULogControl.State.fieldReturn .payloadLength)
        ⟨processed.reverse.map ULogProgram.payloadTape ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
              List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++
                ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base,
          ULogProgram.codeTape carry, next :: right⟩) =
      .running (ULogControl.State.fieldReturn .payloadLength)
        ⟨(processed ++ [carry]).reverse.map ULogProgram.payloadTape ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
              List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++
                ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base,
          next, right⟩ := by
  let donePath := List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.payloadDone)
  have h₀ := run_payloadReturn_end_exact carry processed
    (donePath ++ ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base)
    (next :: right)
  have h₁ : ULogBootstrapExecution.run 1
      (.running (ULogControl.State.payloadReturn carry)
        ⟨donePath ++ ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base,
          ULogAlphabet.ulogCore ULogAlphabet.payloadEnd,
          processed.map ULogProgram.payloadTape ++
            ULogProgram.branchTape carry :: next :: right⟩) =
      .running (ULogControl.State.payloadCount carry)
        (ULogBootstrapExecution.beforeLeftPath donePath base
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
            processed.map ULogProgram.payloadTape ++
              ULogProgram.branchTape carry :: next :: right)) := by
    cases done <;>
      simp [ULogBootstrapExecution.run, donePath,
        ULogBootstrapExecution.beforeLeftPath,
        ULogBootstrapExecution.payloadReturn_end_step,
        List.replicate_succ]
  have h₂ : ULogBootstrapExecution.run done
      (.running (ULogControl.State.payloadCount carry)
        (ULogBootstrapExecution.beforeLeftPath donePath base
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
            processed.map ULogProgram.payloadTape ++
              ULogProgram.branchTape carry :: next :: right))) =
      .running (ULogControl.State.payloadCount carry)
        (ULogBootstrapExecution.afterLeftPath donePath base
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
            processed.map ULogProgram.payloadTape ++
              ULogProgram.branchTape carry :: next :: right)) := by
    simpa [donePath] using ULogBootstrapExecution.run_left_path_of
      (ULogControl.State.payloadCount carry) donePath (by
        intro x hx l y r
        have hm : done ≠ 0 ∧ x = ULogAlphabet.ulogCore ULogAlphabet.payloadDone := by
          simpa [donePath, List.mem_replicate] using hx
        rw [hm.2]
        exact ULogBootstrapExecution.payloadCount_done_step carry l y r)
      base (ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero)
      (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
        processed.map ULogProgram.payloadTape ++
          ULogProgram.branchTape carry :: next :: right)
  have h₃ : ULogBootstrapExecution.run 1
      (.running (ULogControl.State.payloadCount carry)
        (ULogBootstrapExecution.afterLeftPath donePath base
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
            processed.map ULogProgram.payloadTape ++
              ULogProgram.branchTape carry :: next :: right))) =
      .running (ULogControl.State.payloadSeekReturn carry false)
        (ULogBootstrapExecution.beforeRightPath donePath
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
          (processed.map ULogProgram.payloadTape ++
            ULogProgram.branchTape carry :: next :: right)) := by
    cases done <;>
      simp [ULogBootstrapExecution.run, donePath,
        ULogBootstrapExecution.afterLeftPath,
        ULogBootstrapExecution.beforeRightPath,
        ULogBootstrapExecution.payloadCount_start_step,
        List.replicate_succ]
  have h₄ : ULogBootstrapExecution.run done
      (.running (ULogControl.State.payloadSeekReturn carry false)
        (ULogBootstrapExecution.beforeRightPath donePath
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
          (processed.map ULogProgram.payloadTape ++
            ULogProgram.branchTape carry :: next :: right))) =
      .running (ULogControl.State.payloadSeekReturn carry false)
        (ULogBootstrapExecution.afterRightPath donePath
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
          (processed.map ULogProgram.payloadTape ++
            ULogProgram.branchTape carry :: next :: right)) := by
    simpa [donePath] using ULogBootstrapExecution.run_right_path_of
      (ULogControl.State.payloadSeekReturn carry false) donePath (by
        intro x hx l y r
        have hm : done ≠ 0 ∧ x = ULogAlphabet.ulogCore ULogAlphabet.payloadDone := by
          simpa [donePath, List.mem_replicate] using hx
        rw [hm.2]
        exact ULogBootstrapExecution.payloadSeek_done_step carry false l y r)
      (ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base)
      (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
      (processed.map ULogProgram.payloadTape ++
        ULogProgram.branchTape carry :: next :: right)
  have h₅ : ULogBootstrapExecution.run 1
      (.running (ULogControl.State.payloadSeekReturn carry false)
        (ULogBootstrapExecution.afterRightPath donePath
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
          (processed.map ULogProgram.payloadTape ++
            ULogProgram.branchTape carry :: next :: right))) =
      .running (ULogControl.State.payloadRestore carry false)
        (ULogBootstrapExecution.beforeRightPath
          (processed.map ULogProgram.payloadTape)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd :: donePath ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base)
          (ULogProgram.branchTape carry) (next :: right)) := by
    cases done <;> cases processed <;>
      simp [ULogBootstrapExecution.run, donePath,
        ULogBootstrapExecution.afterRightPath,
        ULogBootstrapExecution.beforeRightPath,
        ULogBootstrapExecution.payloadSeek_end_step,
        List.replicate_succ]
  have h₆ : ULogBootstrapExecution.run processed.length
      (.running (ULogControl.State.payloadRestore carry false)
        (ULogBootstrapExecution.beforeRightPath
          (processed.map ULogProgram.payloadTape)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd :: donePath ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base)
          (ULogProgram.branchTape carry) (next :: right))) =
      .running (ULogControl.State.payloadRestore carry false)
        (ULogBootstrapExecution.afterRightPath
          (processed.map ULogProgram.payloadTape)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd :: donePath ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base)
          (ULogProgram.branchTape carry) (next :: right)) := by
    simpa using ULogBootstrapExecution.run_right_path_of
      (ULogControl.State.payloadRestore carry false)
      (processed.map ULogProgram.payloadTape) (by
        intro x hx l y r
        rcases List.mem_map.mp hx with ⟨b, -, rfl⟩
        exact ULogBootstrapExecution.payloadRestore_pass_code carry false b l y r)
      (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd :: donePath ++
        ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base)
      (ULogProgram.branchTape carry) (next :: right)
  have h₇ : ULogBootstrapExecution.run 1
      (.running (ULogControl.State.payloadRestore carry false)
        (ULogBootstrapExecution.afterRightPath
          (processed.map ULogProgram.payloadTape)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd :: donePath ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base)
          (ULogProgram.branchTape carry) (next :: right))) =
      .running (ULogControl.State.fieldReturn .payloadLength)
        ⟨(processed ++ [carry]).reverse.map ULogProgram.payloadTape ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadEnd :: donePath ++
              ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base,
          next, right⟩ := by
    simp [ULogBootstrapExecution.run, ULogBootstrapExecution.afterRightPath,
      ULogBootstrapExecution.payloadRestore_fresh_any,
      List.map_reverse, List.reverse_append, List.append_assoc]
  rw [show 2 * processed.length + 2 * done + 5 =
      (processed.length + 1) +
        (1 + (done + (1 + (done + (1 + (processed.length + 1)))))) by
        omega]
  simp only [donePath, List.cons_append] at h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ ⊢
  rw [ULogBootstrapExecution.run_add]
  have h₀' : ULogBootstrapExecution.run (processed.length + 1)
      (.running (ULogControl.State.fieldReturn .payloadLength)
        ⟨processed.reverse.map ULogProgram.payloadTape ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
              List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++
                ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base,
          ULogProgram.codeTape carry, next :: right⟩) =
      .running (ULogControl.State.payloadReturn carry)
        ⟨List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base,
          ULogAlphabet.ulogCore ULogAlphabet.payloadEnd,
          processed.map ULogProgram.payloadTape ++
            ULogProgram.branchTape carry :: next :: right⟩ := by
    simpa [List.append_assoc] using h₀
  rw [h₀']
  rw [ULogBootstrapExecution.run_add, h₁]
  rw [ULogBootstrapExecution.run_add, h₂]
  rw [ULogBootstrapExecution.run_add, h₃]
  rw [ULogBootstrapExecution.run_add, h₄]
  rw [ULogBootstrapExecution.run_add, h₅]
  rw [ULogBootstrapExecution.run_add, h₆]
  simpa [donePath, List.append_assoc] using h₇

/-- The recursive payload-fold branch has the same exact cost as its terminal
case.  It consumes one pending zero, turns it into a `payloadDone` cell, and
returns to the next pending position without any hidden reachability fuel. -/
theorem run_payloadFreshZero_exact
    (carry : Bool) (next : ULogProgram.Tape)
    (processed : List Bool) (remaining done : ℕ)
    (base right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (2 * processed.length + 2 * done + 5)
      (.running (ULogControl.State.fieldReturn .payloadLength)
        ⟨processed.reverse.map ULogProgram.payloadTape ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
              List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++
                List.replicate (remaining + 1)
                  (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++
                  ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base,
          ULogProgram.codeTape carry, next :: right⟩) =
      .running (ULogControl.State.fieldReturn .payloadLength)
        ⟨(processed ++ [carry]).reverse.map ULogProgram.payloadTape ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
              List.replicate (done + 1)
                (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++
                List.replicate remaining
                  (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++
                  ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base,
          next, right⟩ := by
  let donePath := List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.payloadDone)
  let freshRest := List.replicate remaining (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++
    ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base
  have h₀ := run_payloadReturn_end_exact carry processed
    (donePath ++ ULogAlphabet.ulogCore ULogAlphabet.codeZero :: freshRest)
    (next :: right)
  have h₁ : ULogBootstrapExecution.run 1
      (.running (ULogControl.State.payloadReturn carry)
        ⟨donePath ++ ULogAlphabet.ulogCore ULogAlphabet.codeZero :: freshRest,
          ULogAlphabet.ulogCore ULogAlphabet.payloadEnd,
          processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: next :: right⟩) =
      .running (ULogControl.State.payloadCount carry)
        (ULogBootstrapExecution.beforeLeftPath donePath freshRest
          (ULogAlphabet.ulogCore ULogAlphabet.codeZero)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
            processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: next :: right)) := by
    cases done <;>
      simp [ULogBootstrapExecution.run, donePath, freshRest,
        ULogBootstrapExecution.beforeLeftPath,
        ULogBootstrapExecution.payloadReturn_end_step, List.replicate_succ]
  have h₂ : ULogBootstrapExecution.run done
      (.running (ULogControl.State.payloadCount carry)
        (ULogBootstrapExecution.beforeLeftPath donePath freshRest
          (ULogAlphabet.ulogCore ULogAlphabet.codeZero)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
            processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: next :: right))) =
      .running (ULogControl.State.payloadCount carry)
        (ULogBootstrapExecution.afterLeftPath donePath freshRest
          (ULogAlphabet.ulogCore ULogAlphabet.codeZero)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
            processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: next :: right)) := by
    simpa [donePath] using ULogBootstrapExecution.run_left_path_of
      (ULogControl.State.payloadCount carry) donePath (by
        intro y hy l z r
        have hm : done ≠ 0 ∧ y = ULogAlphabet.ulogCore ULogAlphabet.payloadDone := by
          simpa [donePath, List.mem_replicate] using hy
        rw [hm.2]
        exact ULogBootstrapExecution.payloadCount_done_step carry l z r)
      freshRest (ULogAlphabet.ulogCore ULogAlphabet.codeZero)
      (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
        processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: next :: right)
  have h₃ : ULogBootstrapExecution.run 1
      (.running (ULogControl.State.payloadCount carry)
        (ULogBootstrapExecution.afterLeftPath donePath freshRest
          (ULogAlphabet.ulogCore ULogAlphabet.codeZero)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
            processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: next :: right))) =
      .running (ULogControl.State.payloadSeekReturn carry false)
        (ULogBootstrapExecution.beforeRightPath donePath
          (ULogAlphabet.ulogCore ULogAlphabet.payloadDone :: freshRest)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
          (processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: next :: right)) := by
    cases done <;>
      simp [ULogBootstrapExecution.run, donePath, freshRest,
        ULogBootstrapExecution.afterLeftPath,
        ULogBootstrapExecution.beforeRightPath,
        ULogBootstrapExecution.payloadCount_zero_step, List.replicate_succ]
  have h₄ : ULogBootstrapExecution.run done
      (.running (ULogControl.State.payloadSeekReturn carry false)
        (ULogBootstrapExecution.beforeRightPath donePath
          (ULogAlphabet.ulogCore ULogAlphabet.payloadDone :: freshRest)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
          (processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: next :: right))) =
      .running (ULogControl.State.payloadSeekReturn carry false)
        (ULogBootstrapExecution.afterRightPath donePath
          (ULogAlphabet.ulogCore ULogAlphabet.payloadDone :: freshRest)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
          (processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: next :: right)) := by
    simpa [donePath] using ULogBootstrapExecution.run_right_path_of
      (ULogControl.State.payloadSeekReturn carry false) donePath (by
        intro y hy l z r
        have hm : done ≠ 0 ∧ y = ULogAlphabet.ulogCore ULogAlphabet.payloadDone := by
          simpa [donePath, List.mem_replicate] using hy
        rw [hm.2]
        exact ULogBootstrapExecution.payloadSeek_done_step carry false l z r)
      (ULogAlphabet.ulogCore ULogAlphabet.payloadDone :: freshRest)
      (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
      (processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: next :: right)
  have h₅ : ULogBootstrapExecution.run 1
      (.running (ULogControl.State.payloadSeekReturn carry false)
        (ULogBootstrapExecution.afterRightPath donePath
          (ULogAlphabet.ulogCore ULogAlphabet.payloadDone :: freshRest)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
          (processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: next :: right))) =
      .running (ULogControl.State.payloadRestore carry false)
        (ULogBootstrapExecution.beforeRightPath (processed.map ULogProgram.payloadTape)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
            List.replicate (done + 1) (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++ freshRest)
          (ULogProgram.branchTape carry) (next :: right)) := by
    cases done <;> cases processed <;>
      simp [ULogBootstrapExecution.run, donePath, freshRest,
        ULogBootstrapExecution.afterRightPath,
        ULogBootstrapExecution.beforeRightPath,
        ULogBootstrapExecution.payloadSeek_end_step, List.replicate_succ]
  have h₆ : ULogBootstrapExecution.run processed.length
      (.running (ULogControl.State.payloadRestore carry false)
        (ULogBootstrapExecution.beforeRightPath (processed.map ULogProgram.payloadTape)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
            List.replicate (done + 1) (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++ freshRest)
          (ULogProgram.branchTape carry) (next :: right))) =
      .running (ULogControl.State.payloadRestore carry false)
        (ULogBootstrapExecution.afterRightPath (processed.map ULogProgram.payloadTape)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
            List.replicate (done + 1) (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++ freshRest)
          (ULogProgram.branchTape carry) (next :: right)) := by
    simpa using ULogBootstrapExecution.run_right_path_of
      (ULogControl.State.payloadRestore carry false)
      (processed.map ULogProgram.payloadTape) (by
        intro y hy l z r
        rcases List.mem_map.mp hy with ⟨b, -, rfl⟩
        exact ULogBootstrapExecution.payloadRestore_pass_code carry false b l z r)
      (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
        List.replicate (done + 1) (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++ freshRest)
      (ULogProgram.branchTape carry) (next :: right)
  have h₇ : ULogBootstrapExecution.run 1
      (.running (ULogControl.State.payloadRestore carry false)
        (ULogBootstrapExecution.afterRightPath (processed.map ULogProgram.payloadTape)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
            List.replicate (done + 1) (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++ freshRest)
          (ULogProgram.branchTape carry) (next :: right))) =
      .running (ULogControl.State.fieldReturn .payloadLength)
        ⟨(processed ++ [carry]).reverse.map ULogProgram.payloadTape ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
              List.replicate (done + 1) (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++ freshRest,
          next, right⟩ := by
    simp [ULogBootstrapExecution.run, ULogBootstrapExecution.afterRightPath,
      ULogBootstrapExecution.payloadRestore_fresh_any,
      List.map_reverse, List.reverse_append, List.append_assoc]
  rw [show 2 * processed.length + 2 * done + 5 =
      (processed.length + 1) +
        (1 + (done + (1 + (done + (1 + (processed.length + 1)))))) by omega]
  simp only [donePath, freshRest, List.cons_append] at h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ ⊢
  rw [ULogBootstrapExecution.run_add]
  simp only [List.replicate_succ]
  have h₀' : ULogBootstrapExecution.run (processed.length + 1)
      (.running (ULogControl.State.fieldReturn .payloadLength)
        ⟨processed.reverse.map ULogProgram.payloadTape ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
              List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++
                ULogAlphabet.ulogCore ULogAlphabet.codeZero ::
                  List.replicate remaining (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++
                    ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base,
          ULogProgram.codeTape carry, next :: right⟩) =
      .running (ULogControl.State.payloadReturn carry)
        ⟨List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++
            ULogAlphabet.ulogCore ULogAlphabet.codeZero ::
              List.replicate remaining (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++
                ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base,
          ULogAlphabet.ulogCore ULogAlphabet.payloadEnd,
          processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: next :: right⟩ := by
    simpa [List.append_assoc] using h₀
  rw [h₀', ULogBootstrapExecution.run_add]
  have h₁' : ULogBootstrapExecution.run 1
      (.running (ULogControl.State.payloadReturn carry)
        ⟨List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++
            ULogAlphabet.ulogCore ULogAlphabet.codeZero ::
              List.replicate remaining (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++
                ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base,
          ULogAlphabet.ulogCore ULogAlphabet.payloadEnd,
          processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: next :: right⟩) =
      .running (ULogControl.State.payloadCount carry)
        (ULogBootstrapExecution.beforeLeftPath
          (List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.payloadDone))
          (List.replicate remaining (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base)
          (ULogAlphabet.ulogCore ULogAlphabet.codeZero)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
            processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: next :: right)) := by
    simpa [List.append_assoc] using h₁
  rw [h₁', ULogBootstrapExecution.run_add]
  change ULogBootstrapExecution.run (1 + (done + (1 + (processed.length + 1))))
      (ULogBootstrapExecution.run done
        (.running (ULogControl.State.payloadCount carry)
          (ULogBootstrapExecution.beforeLeftPath
            (List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.payloadDone))
            (List.replicate remaining (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++
              ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base)
            (ULogAlphabet.ulogCore ULogAlphabet.codeZero)
            (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
              (processed.map ULogProgram.payloadTape ++
                ULogProgram.branchTape carry :: next :: right))))) = _
  rw [h₂,
    ULogBootstrapExecution.run_add, h₃,
    ULogBootstrapExecution.run_add, h₄,
    ULogBootstrapExecution.run_add, h₅,
    ULogBootstrapExecution.run_add, h₆]
  simpa [List.append_assoc, List.replicate_succ] using h₇

/-- The first nonempty payload bit has a genuinely constant entry cost.
This is kept separate from the recursive fold because it changes the
counter representation from the leading unary one into the first completed
payload cell. -/
theorem run_payloadFirstZero_exact
    (carry : Bool) (next : ULogProgram.Tape) (remaining : ℕ)
    (base : List ULogProgram.Tape) (right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run 5
      (.running (ULogControl.State.fieldReturn .payloadLength)
        ⟨ULogAlphabet.ulogCore ULogAlphabet.codeOne ::
            ULogAlphabet.ulogCore ULogAlphabet.codeZero ::
              List.replicate remaining
                (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++
                ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base,
          ULogProgram.codeTape carry, next :: right⟩) =
      .running (ULogControl.State.fieldReturn .payloadLength)
        ⟨ULogProgram.payloadTape carry ::
            ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
              ULogAlphabet.ulogCore ULogAlphabet.payloadDone ::
                List.replicate remaining
                  (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++
                  ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base,
          next, right⟩ := by
  simp [ULogBootstrapExecution.run,
    ULogBootstrapExecution.fieldReturn_payload_step,
    ULogBootstrapExecution.payloadReturn_codeOne_step,
    ULogBootstrapExecution.payloadCount_zero_step,
    ULogBootstrapExecution.payloadSeek_end_step,
    ULogBootstrapExecution.payloadRestore_fresh_any,
    List.append_assoc]

/-- The singleton-payload entry has the same five-step constant cost, but
lands directly on the terminal payload-start marker. -/
theorem run_payloadFirstStart_exact
    (carry : Bool) (next : ULogProgram.Tape)
    (base : List ULogProgram.Tape) (right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run 5
      (.running (ULogControl.State.fieldReturn .payloadLength)
        ⟨ULogAlphabet.ulogCore ULogAlphabet.codeOne ::
            ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base,
          ULogProgram.codeTape carry, next :: right⟩) =
      .running (ULogControl.State.fieldReturn .payloadLength)
        ⟨ULogProgram.payloadTape carry ::
            ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
              ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base,
          next, right⟩ := by
  simp [ULogBootstrapExecution.run,
    ULogBootstrapExecution.fieldReturn_payload_step,
    ULogBootstrapExecution.payloadReturn_codeOne_step,
    ULogBootstrapExecution.payloadCount_start_step,
    ULogBootstrapExecution.payloadSeek_end_step,
    ULogBootstrapExecution.payloadRestore_fresh_any]

/-- Once the payload-start marker has been consumed, the final return/count
round has the same exact scan cost as an ordinary fresh round, and enters
clock framing. -/
theorem run_payloadExhausted_exact
    (carry : Bool) (processed : List Bool) (done : ℕ)
    (base right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (2 * processed.length + 2 * done + 5)
      (.running (ULogControl.State.fieldReturn .payloadLength)
        ⟨processed.reverse.map ULogProgram.payloadTape ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
              List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++
                ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base,
          ULogProgram.codeTape carry, right⟩) =
      .running ULogControl.State.framePadding
        ⟨processed.reverse.map ULogProgram.payloadTape ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
              List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++
                ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base,
          ULogProgram.codeTape carry, right⟩ := by
  let donePath := List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.payloadDone)
  have h₀ := run_payloadReturn_end_exact carry processed
    (donePath ++ ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base) right
  have h₁ : ULogBootstrapExecution.run 1
      (.running (ULogControl.State.payloadReturn carry)
        ⟨donePath ++ ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base,
          ULogAlphabet.ulogCore ULogAlphabet.payloadEnd,
          processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: right⟩) =
      .running (ULogControl.State.payloadCount carry)
        (ULogBootstrapExecution.beforeLeftPath donePath base
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
            processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: right)) := by
    cases done <;>
      simp [ULogBootstrapExecution.run, donePath,
        ULogBootstrapExecution.beforeLeftPath,
        ULogBootstrapExecution.payloadReturn_end_step, List.replicate_succ]
  have h₂ : ULogBootstrapExecution.run done
      (.running (ULogControl.State.payloadCount carry)
        (ULogBootstrapExecution.beforeLeftPath donePath base
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
            processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: right))) =
      .running (ULogControl.State.payloadCount carry)
        (ULogBootstrapExecution.afterLeftPath donePath base
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
            processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: right)) := by
    simpa [donePath] using ULogBootstrapExecution.run_left_path_of
      (ULogControl.State.payloadCount carry) donePath (by
        intro y hy l z r
        have hm : done ≠ 0 ∧ y = ULogAlphabet.ulogCore ULogAlphabet.payloadDone := by
          simpa [donePath, List.mem_replicate] using hy
        rw [hm.2]
        exact ULogBootstrapExecution.payloadCount_done_step carry l z r)
      base (ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone)
      (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
        processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: right)
  have h₃ : ULogBootstrapExecution.run 1
      (.running (ULogControl.State.payloadCount carry)
        (ULogBootstrapExecution.afterLeftPath donePath base
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
            processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: right))) =
      .running (ULogControl.State.payloadSeekReturn carry true)
        (ULogBootstrapExecution.beforeRightPath donePath
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
          (processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: right)) := by
    cases done <;>
      simp [ULogBootstrapExecution.run, donePath,
        ULogBootstrapExecution.afterLeftPath,
        ULogBootstrapExecution.beforeRightPath,
        ULogBootstrapExecution.payloadCount_exhausted_step, List.replicate_succ]
  have h₄ : ULogBootstrapExecution.run done
      (.running (ULogControl.State.payloadSeekReturn carry true)
        (ULogBootstrapExecution.beforeRightPath donePath
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
          (processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: right))) =
      .running (ULogControl.State.payloadSeekReturn carry true)
        (ULogBootstrapExecution.afterRightPath donePath
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
          (processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: right)) := by
    simpa [donePath] using ULogBootstrapExecution.run_right_path_of
      (ULogControl.State.payloadSeekReturn carry true) donePath (by
        intro y hy l z r
        have hm : done ≠ 0 ∧ y = ULogAlphabet.ulogCore ULogAlphabet.payloadDone := by
          simpa [donePath, List.mem_replicate] using hy
        rw [hm.2]
        exact ULogBootstrapExecution.payloadSeek_done_step carry true l z r)
      (ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base)
      (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
      (processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: right)
  have h₅ : ULogBootstrapExecution.run 1
      (.running (ULogControl.State.payloadSeekReturn carry true)
        (ULogBootstrapExecution.afterRightPath donePath
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
          (processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: right))) =
      .running (ULogControl.State.payloadRestore carry true)
        (ULogBootstrapExecution.beforeRightPath (processed.map ULogProgram.payloadTape)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd :: donePath ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base)
          (ULogProgram.branchTape carry) right) := by
    cases done <;> cases processed <;>
      simp [ULogBootstrapExecution.run, donePath,
        ULogBootstrapExecution.afterRightPath,
        ULogBootstrapExecution.beforeRightPath,
        ULogBootstrapExecution.payloadSeek_end_step, List.replicate_succ]
  have h₆ : ULogBootstrapExecution.run processed.length
      (.running (ULogControl.State.payloadRestore carry true)
        (ULogBootstrapExecution.beforeRightPath (processed.map ULogProgram.payloadTape)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd :: donePath ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base)
          (ULogProgram.branchTape carry) right)) =
      .running (ULogControl.State.payloadRestore carry true)
        (ULogBootstrapExecution.afterRightPath (processed.map ULogProgram.payloadTape)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd :: donePath ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base)
          (ULogProgram.branchTape carry) right) := by
    simpa using ULogBootstrapExecution.run_right_path_of
      (ULogControl.State.payloadRestore carry true)
      (processed.map ULogProgram.payloadTape) (by
        intro y hy l z r
        rcases List.mem_map.mp hy with ⟨b, -, rfl⟩
        exact ULogBootstrapExecution.payloadRestore_pass_code carry true b l z r)
      (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd :: donePath ++
        ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base)
      (ULogProgram.branchTape carry) right
  have h₇ : ULogBootstrapExecution.run 1
      (.running (ULogControl.State.payloadRestore carry true)
        (ULogBootstrapExecution.afterRightPath (processed.map ULogProgram.payloadTape)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd :: donePath ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base)
          (ULogProgram.branchTape carry) right)) =
      .running ULogControl.State.framePadding
        ⟨processed.reverse.map ULogProgram.payloadTape ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadEnd :: donePath ++
              ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base,
          ULogProgram.codeTape carry, right⟩ := by
    simp [ULogBootstrapExecution.run, ULogBootstrapExecution.afterRightPath,
      ULogBootstrapExecution.payloadRestore_exhausted_step,
      List.map_reverse, List.append_assoc]
  rw [show 2 * processed.length + 2 * done + 5 =
      (processed.length + 1) +
        (1 + (done + (1 + (done + (1 + (processed.length + 1)))))) by
        omega]
  simp only [donePath, List.cons_append] at h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ ⊢
  rw [ULogBootstrapExecution.run_add]
  have h₀' : ULogBootstrapExecution.run (processed.length + 1)
      (.running (ULogControl.State.fieldReturn .payloadLength)
        ⟨processed.reverse.map ULogProgram.payloadTape ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
              List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++
                ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base,
          ULogProgram.codeTape carry, right⟩) =
      .running (ULogControl.State.payloadReturn carry)
        ⟨List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base,
          ULogAlphabet.ulogCore ULogAlphabet.payloadEnd,
          processed.map ULogProgram.payloadTape ++ ULogProgram.branchTape carry :: right⟩ := by
    simpa [List.append_assoc] using h₀
  rw [h₀', ULogBootstrapExecution.run_add, h₁]
  rw [ULogBootstrapExecution.run_add, h₂,
    ULogBootstrapExecution.run_add, h₃,
    ULogBootstrapExecution.run_add, h₄,
    ULogBootstrapExecution.run_add, h₅,
    ULogBootstrapExecution.run_add, h₆]
  simpa [List.append_assoc] using h₇

/-- Closed sum of the exact per-bit payload-fold costs.  It is quadratic in
the pending tail and is the fuel used by the forthcoming structural induction. -/
def payloadFoldFuel (pending processed : List Bool) (done : ℕ) : ℕ :=
  2 * pending.length ^ 2 +
    pending.length * (2 * processed.length + 2 * done + 7) +
      2 * processed.length + 2 * done + 5

theorem payloadFoldFuel_nil (carry : Bool) (processed : List Bool) (done : ℕ) :
    payloadFoldFuel [] processed done = 2 * processed.length + 2 * done + 5 := by
  simp [payloadFoldFuel]

theorem payloadFoldFuel_cons (carry next : Bool) (pending processed : List Bool)
    (done : ℕ) :
    payloadFoldFuel (next :: pending) processed done =
      (2 * processed.length + 2 * done + 5) +
        payloadFoldFuel pending (processed ++ [carry]) (done + 1) := by
  simp [payloadFoldFuel]
  ring

/-- The payload-length fold has an explicit run, not merely an existential
`Reaches` witness. Each pending bit takes the fresh-zero branch; the final
fresh-start branch closes the fold. -/
theorem run_payloadFold_exact
    (carry : Bool) (pending processed : List Bool) (done : ℕ)
    (base : List ULogProgram.Tape) (after : ULogProgram.Tape)
    (right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (payloadFoldFuel pending processed done)
      (.running (ULogControl.State.fieldReturn .payloadLength)
        ⟨processed.reverse.map ULogProgram.payloadTape ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
              List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++
                List.replicate pending.length
                  (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++
                    ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base,
          ULogProgram.codeTape carry,
          pending.map ULogProgram.codeTape ++ after :: right⟩) =
      .running (ULogControl.State.fieldReturn .payloadLength)
        ⟨(processed ++ carry :: pending).reverse.map ULogProgram.payloadTape ++
            ULogAlphabet.ulogCore ULogAlphabet.payloadEnd ::
              List.replicate (done + pending.length)
                (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++
                  ULogAlphabet.ulogCore ULogAlphabet.payloadStartDone :: base,
          after, right⟩ := by
  induction pending generalizing carry processed done with
  | nil =>
      simpa [payloadFoldFuel] using
        (run_payloadFreshStart_exact carry after processed done base right)
  | cons next pending ih =>
      rw [payloadFoldFuel_cons]
      rw [ULogBootstrapExecution.run_add]
      simp only [List.length_cons, List.map_cons, List.cons_append]
      have hzero := run_payloadFreshZero_exact carry
        (ULogProgram.codeTape next) processed pending.length done base
        (pending.map ULogProgram.codeTape ++ after :: right)
      rw [hzero]
      have htail := ih next (processed ++ [carry]) (done + 1)
      simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm, List.replicate_succ] using htail

/-- A coarse closed form for the exact fold ledger.  The useful point is
that the universal machine's per-bit return scans contribute only quadratic
fuel in the total already-materialized payload state. -/
theorem payloadFoldFuel_le_quadratic
    (pending processed : List Bool) (done : ℕ) :
    payloadFoldFuel pending processed done ≤
      2 * (processed.length + pending.length + done + 2) ^ 2 := by
  unfold payloadFoldFuel
  have hp : pending.length ≤ processed.length + pending.length + done := by omega
  have hs : processed.length ≤ processed.length + pending.length + done := by omega
  have hd : done ≤ processed.length + pending.length + done := by omega
  nlinarith

/-- Exact fuel for one unary bytecode field.  This elementary primitive is
the building block for the still-pending program-count and rule-list pass. -/
theorem run_field_exact
    (field : ULogControl.BytecodeField) (n : ℕ)
    (left : List ULogProgram.Tape) (y : ULogProgram.Tape)
    (right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (n + 1)
      (ULogBootstrapExecution.beforeFieldZeros field n left y right) =
      .running (ULogControl.State.fieldReturn field)
        ⟨ULogAlphabet.ulogCore ULogAlphabet.codeOne ::
            List.replicate n (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++ left,
          y, right⟩ := by
  rw [ULogBootstrapExecution.run_add,
    ULogBootstrapExecution.run_fieldSeek_zeros]
  exact ULogBootstrapExecution.fieldSeek_one_step field _ _ _

/-- Exact fuel for a unary field embedded in the actual bit-list zipper.
Unlike the old reachability lemma, the cost is retained as `n + 1`. -/
theorem run_field_prefix_exact
    (field : ULogControl.BytecodeField) (n : ℕ)
    (tail : List Bool) (left : List ULogProgram.Tape)
    (after : ULogProgram.Tape) (right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (n + 1)
      (ULogBootstrapExecution.atBits (.fieldSeek field)
        (ULogBytecode.encodeNatField n ++ tail) left after right) =
      ULogBootstrapExecution.atBits (.fieldReturn field) tail
        ((ULogBytecode.encodeNatField n).reverse.map ULogProgram.codeTape ++ left)
        after right := by
  cases tail with
  | nil =>
      cases n with
      | zero =>
          simpa [ULogBootstrapExecution.atBits,
            ULogBootstrapExecution.beforeFieldZeros,
            ULogBytecode.encodeNatField, ULogProgram.codeTape] using
            (run_field_exact field 0 left after right)
      | succ n =>
          simpa [ULogBootstrapExecution.atBits,
            ULogBootstrapExecution.beforeFieldZeros,
            ULogBytecode.encodeNatField, ULogProgram.codeTape, List.replicate_succ,
            List.map_append, List.reverse_append, List.append_assoc] using
            (run_field_exact field (n + 1) left after right)
  | cons b bs =>
      cases n with
      | zero =>
          simpa [ULogBootstrapExecution.atBits,
            ULogBootstrapExecution.beforeFieldZeros,
            ULogBytecode.encodeNatField, ULogProgram.codeTape] using
            (run_field_exact field 0 left (ULogProgram.codeTape b)
              (bs.map ULogProgram.codeTape ++ after :: right))
      | succ n =>
          simpa [ULogBootstrapExecution.atBits,
            ULogBootstrapExecution.beforeFieldZeros,
            ULogBytecode.encodeNatField, ULogProgram.codeTape, List.replicate_succ,
            List.map_append, List.reverse_append, List.append_assoc] using
            (run_field_exact field (n + 1) left (ULogProgram.codeTape b)
              (bs.map ULogProgram.codeTape ++ after :: right))

/-- Concrete path lengths used by the program-count round. -/
theorem returnPath_length_exact (skipped : List Bool) (remaining done : ℕ) :
    (ULogBootstrapExecution.returnPath skipped remaining done).length =
      skipped.length + remaining + done + 1 := by
  simp [ULogBootstrapExecution.returnPath]
  omega

theorem seekPath_length_exact (skipped : List Bool) (remaining : ℕ) :
    (ULogBootstrapExecution.seekPath skipped remaining).length =
      skipped.length + remaining + 1 := by
  simp [ULogBootstrapExecution.seekPath]
  omega

/-- The literal self-delimiting instruction width.  This is the second
ingredient, after `run_field_prefix_exact`, needed to sum exact rule costs. -/
theorem encodeRule_length_exact (r : ULogBytecode.RuleCode) :
    (ULogBytecode.encodeRule r).length =
      r.source + r.read + r.action.write + r.action.target + 7 := by
  rcases r with ⟨source, read, slot, ⟨write, target, move⟩⟩
  cases move <;>
    simp [ULogBytecode.encodeRule, ULogBytecode.encodeAction,
      ULogBytecode.encodeMove, List.append_assoc] <;> omega

/-- One nonterminal program-count round has a closed, exact cost.  It
scans the return path, the completed-count cells, and the remaining seek
path before exposing the next rule's source field. -/
theorem run_countFresh_exact
    (carry : Bool) (skipped : List Bool) (remaining done : ℕ)
    (left right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run
      (2 * skipped.length + 2 * remaining + 2 * done + 7)
      (ULogBootstrapExecution.countCheckStart carry skipped (remaining + 1)
        done left right) =
      ULogBootstrapExecution.countFreshDone carry skipped remaining done left right := by
  let returnPath := ULogBootstrapExecution.returnPath skipped (remaining + 1) done
  let seekPath := ULogBootstrapExecution.seekPath skipped remaining
  let scanPath := ULogBootstrapExecution.seekPath skipped (remaining + 1)
  have hnonempty : returnPath ≠ [] := by
    simp [returnPath, ULogBootstrapExecution.returnPath]
  have hscanNonempty : scanPath ≠ [] := by
    simp [scanPath, ULogBootstrapExecution.seekPath]
  have h₀ : ULogBootstrapExecution.run 1
      (ULogBootstrapExecution.countCheckStart carry skipped (remaining + 1)
        done left right) =
      ULogBootstrapExecution.countReturnStarted carry skipped (remaining + 1)
        done left right := by
    cases hp : returnPath with
    | nil => exact (hnonempty hp).elim
    | cons a as =>
        simp [ULogBootstrapExecution.run,
          ULogBootstrapExecution.countCheckStart,
          ULogBootstrapExecution.countReturnStarted,
          ULogBootstrapExecution.beforeLeftPath, returnPath, hp,
          ULogBootstrapExecution.fieldReturn_count_step]
  have h₁ : ULogBootstrapExecution.run returnPath.length
      (ULogBootstrapExecution.countReturnStarted carry skipped (remaining + 1)
        done left right) =
      ULogBootstrapExecution.countAtMark carry skipped (remaining + 1)
        done left right := by
    simpa [ULogBootstrapExecution.countReturnStarted,
      ULogBootstrapExecution.countAtMark] using
      ULogBootstrapExecution.run_left_path_of (.returnToPc carry) returnPath
        (by
          intro a ha l y r
          exact ULogBootstrapExecution.returnPath_pass carry skipped
            (remaining + 1) done a (by simpa [returnPath] using ha) l y r)
        left (ULogAlphabet.ulogCore ULogAlphabet.pcMark)
        (ULogProgram.branchTape carry :: right)
  have h₂ : ULogBootstrapExecution.run 1
      (ULogBootstrapExecution.countAtMark carry skipped (remaining + 1)
        done left right) =
      ULogBootstrapExecution.countScanStarted carry skipped (remaining + 1)
        done left right := by
    cases hs : scanPath with
    | nil => exact (hscanNonempty hs).elim
    | cons a as =>
        cases done <;>
          simp [ULogBootstrapExecution.run,
            ULogBootstrapExecution.countAtMark,
            ULogBootstrapExecution.countScanStarted,
            ULogBootstrapExecution.afterLeftPath,
            ULogBootstrapExecution.beforeRightPath, returnPath,
            ULogBootstrapExecution.returnPath_reverse, scanPath, hs,
            ULogBootstrapExecution.returnToPc_mark, List.replicate_succ,
            List.append_assoc]
  have h₃ : ULogBootstrapExecution.run done
      (ULogBootstrapExecution.countScanStarted carry skipped (remaining + 1)
        done left right) =
      ULogBootstrapExecution.countAfterDone carry skipped (remaining + 1)
        done left right := by
    cases hs : scanPath with
    | nil => exact (hscanNonempty hs).elim
    | cons a as =>
        simpa [ULogBootstrapExecution.countScanStarted,
          ULogBootstrapExecution.countAfterDone, scanPath, hs] using
          ULogBootstrapExecution.run_right_path_of (.countScan carry)
            (List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.pcDone)) (by
              intro z hz l y r
              have hzmem : done ≠ 0 ∧ z = ULogAlphabet.ulogCore ULogAlphabet.pcDone := by
                simpa only [List.mem_replicate] using hz
              rw [hzmem.2]
              exact ULogBootstrapExecution.countScan_done carry l y r)
            (ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left) a
            (as ++ ULogProgram.branchTape carry :: right)
  have h₄ : ULogBootstrapExecution.run 1
      (ULogBootstrapExecution.countAfterDone carry skipped (remaining + 1)
        done left right) =
      ULogBootstrapExecution.countFreshStarted carry skipped remaining done left right := by
    cases remaining <;>
      simp [ULogBootstrapExecution.run,
        ULogBootstrapExecution.countAfterDone,
        ULogBootstrapExecution.countFreshStarted,
        ULogBootstrapExecution.seekPath,
        ULogBootstrapExecution.beforeRightPath,
        ULogBootstrapExecution.afterRightPath,
        ULogBootstrapExecution.countScan_fresh, List.replicate_succ,
        List.append_assoc]
  have h₅ : ULogBootstrapExecution.run seekPath.length
      (ULogBootstrapExecution.countFreshStarted carry skipped remaining done left right) =
      ULogBootstrapExecution.countFreshReturned carry skipped remaining done left right := by
    simpa [ULogBootstrapExecution.countFreshStarted,
      ULogBootstrapExecution.countFreshReturned, seekPath] using
      ULogBootstrapExecution.run_right_path_of (.seekReturn carry false) seekPath
        (by
          intro a ha l y r
          exact ULogBootstrapExecution.seekPath_pass carry false skipped remaining
            a (by simpa [seekPath] using ha) l y r)
        (ULogAlphabet.ulogCore ULogAlphabet.pcDone ::
          List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.pcDone) ++
            ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
        (ULogProgram.branchTape carry) right
  have h₆ : ULogBootstrapExecution.run 1
      (ULogBootstrapExecution.countFreshReturned carry skipped remaining done left right) =
      ULogBootstrapExecution.countFreshDone carry skipped remaining done left right := by
    simp [ULogBootstrapExecution.run,
      ULogBootstrapExecution.countFreshReturned,
      ULogBootstrapExecution.countFreshDone,
      ULogBootstrapExecution.afterRightPath, ULogBootstrapExecution.seekReturn_marker]
  rw [show 2 * skipped.length + 2 * remaining + 2 * done + 7 =
      1 + (returnPath.length + (1 + (done + (1 + (seekPath.length + 1))))) by
        simp [returnPath, seekPath, ULogBootstrapExecution.returnPath,
          ULogBootstrapExecution.seekPath]; omega]
  rw [ULogBootstrapExecution.run_add, h₀,
    ULogBootstrapExecution.run_add, h₁,
    ULogBootstrapExecution.run_add, h₂,
    ULogBootstrapExecution.run_add, h₃,
    ULogBootstrapExecution.run_add, h₄,
    ULogBootstrapExecution.run_add, h₅]
  exact h₆

/-- Parsing and skipping one literal rule has exact fuel equal to its
bytecode width plus two control handoffs.  No rule-table search is hidden in
this lemma: it is just the four unary fields, slot bit, and two move bits. -/
theorem run_skipRule_exact
    (r : ULogBytecode.RuleCode) (left : List ULogProgram.Tape)
    (after : ULogProgram.Tape) (right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run ((ULogBytecode.encodeRule r).length + 2)
      (ULogBootstrapExecution.atBits (.fieldSeek .source)
        (ULogBytecode.encodeRule r) left after right) =
      .running ULogControl.State.skipRule
        ⟨(ULogBytecode.encodeRule r).reverse.map ULogProgram.codeTape ++ left,
          after, right⟩ := by
  rcases r with ⟨source, read, slot, ⟨write, target, move⟩⟩
  let sBits := ULogBytecode.encodeNatField source
  let rBits := ULogBytecode.encodeNatField read
  let wBits := ULogBytecode.encodeNatField write
  let tBits := ULogBytecode.encodeNatField target
  let mBits := [ULogBootstrapExecution.moveFirst move,
    ULogBootstrapExecution.moveSecond move]
  have hmove : ULogBytecode.encodeMove move = mBits := by
    cases move <;> rfl
  let lS := sBits.reverse.map ULogProgram.codeTape ++ left
  let lR := rBits.reverse.map ULogProgram.codeTape ++ lS
  let lSlot := ULogProgram.codeTape slot :: lR
  let lW := wBits.reverse.map ULogProgram.codeTape ++ lSlot
  let lT := tBits.reverse.map ULogProgram.codeTape ++ lW
  let lM₁ := ULogProgram.codeTape (ULogBootstrapExecution.moveFirst move) :: lT
  let lM₂ := ULogProgram.codeTape (ULogBootstrapExecution.moveSecond move) :: lM₁
  have hS : ULogBootstrapExecution.run (source + 1)
      (ULogBootstrapExecution.atBits (.fieldSeek .source)
        (sBits ++ rBits ++ [slot] ++ wBits ++ tBits ++ mBits)
        left after right) =
      ULogBootstrapExecution.atBits (.fieldReturn .source)
        (rBits ++ [slot] ++ wBits ++ tBits ++ mBits) lS after right := by
    simpa only [List.append_assoc] using
      (run_field_prefix_exact .source source
        (rBits ++ [slot] ++ wBits ++ tBits ++ mBits) left after right)
  have hSH : ULogBootstrapExecution.run 1
      (ULogBootstrapExecution.atBits (.fieldReturn .source)
        (rBits ++ [slot] ++ wBits ++ tBits ++ mBits) lS after right) =
      ULogBootstrapExecution.atBits (.fieldSeek .read)
        (rBits ++ [slot] ++ wBits ++ tBits ++ mBits) lS after right := by
    simp [ULogBootstrapExecution.run,
      ULogBootstrapExecution.atBits_source_handoff_nonempty,
      rBits, ULogBytecode.encodeNatField]
  have hR : ULogBootstrapExecution.run (read + 1)
      (ULogBootstrapExecution.atBits (.fieldSeek .read)
        (rBits ++ [slot] ++ wBits ++ tBits ++ mBits) lS after right) =
      ULogBootstrapExecution.atBits (.fieldReturn .read)
        ([slot] ++ wBits ++ tBits ++ mBits) lR after right := by
    simpa only [List.append_assoc] using
      (run_field_prefix_exact .read read ([slot] ++ wBits ++ tBits ++ mBits)
        lS after right)
  have hSlot : ULogBootstrapExecution.run 1
      (ULogBootstrapExecution.atBits (.fieldReturn .read)
        ([slot] ++ wBits ++ tBits ++ mBits) lR after right) =
      ULogBootstrapExecution.atBits (.fieldSeek .write)
        (wBits ++ tBits ++ mBits) lSlot after right := by
    simp [ULogBootstrapExecution.run, lSlot,
      ULogBootstrapExecution.atBits_read_slot, List.append_assoc]
  have hW : ULogBootstrapExecution.run (write + 1)
      (ULogBootstrapExecution.atBits (.fieldSeek .write)
        (wBits ++ tBits ++ mBits) lSlot after right) =
      ULogBootstrapExecution.atBits (.fieldReturn .write)
        (tBits ++ mBits) lW after right := by
    simpa only [List.append_assoc] using
      (run_field_prefix_exact .write write (tBits ++ mBits) lSlot after right)
  have hWH : ULogBootstrapExecution.run 1
      (ULogBootstrapExecution.atBits (.fieldReturn .write)
        (tBits ++ mBits) lW after right) =
      ULogBootstrapExecution.atBits (.fieldSeek .target)
        (tBits ++ mBits) lW after right := by
    simp [ULogBootstrapExecution.run,
      ULogBootstrapExecution.atBits_write_handoff_nonempty,
      tBits, mBits, ULogBytecode.encodeNatField]
  have hT : ULogBootstrapExecution.run (target + 1)
      (ULogBootstrapExecution.atBits (.fieldSeek .target) (tBits ++ mBits) lW after right) =
      ULogBootstrapExecution.atBits (.fieldReturn .target) mBits lT after right := by
    simpa only [List.append_assoc] using
      (run_field_prefix_exact .target target mBits lW after right)
  have hM₁ : ULogBootstrapExecution.run 1
      (ULogBootstrapExecution.atBits (.fieldReturn .target) mBits lT after right) =
      ULogBootstrapExecution.atBits
        (.skipMoveSecond (ULogBootstrapExecution.moveFirst move))
        [ULogBootstrapExecution.moveSecond move] lM₁ after right := by
    simp [ULogBootstrapExecution.run, mBits, lM₁,
      ULogBootstrapExecution.atBits_target_first]
  have hM₂ : ULogBootstrapExecution.run 1
      (ULogBootstrapExecution.atBits
        (.skipMoveSecond (ULogBootstrapExecution.moveFirst move))
        [ULogBootstrapExecution.moveSecond move] lM₁ after right) =
      .running ULogControl.State.skipRule ⟨lM₂, after, right⟩ := by
    simpa [ULogBootstrapExecution.run, ULogBootstrapExecution.atBits, lM₂] using
      (ULogBootstrapExecution.atBits_move_second move [] lM₁ after right)
  have hmoveLength : (ULogBytecode.encodeMove move).length = 2 := by
    rw [hmove]
    simp [mBits]
  have hcost : (ULogBytecode.encodeRule
      ⟨source, read, slot, ⟨write, target, move⟩⟩).length + 2 =
      (source + 1) + (1 + ((read + 1) +
        (1 + ((write + 1) + (1 + ((target + 1) + (1 + 1))))))) := by
    simp [ULogBytecode.encodeRule, ULogBytecode.encodeAction,
      hmoveLength, List.append_assoc]
    omega
  have hstart : ULogBootstrapExecution.atBits (.fieldSeek .source)
      (ULogBytecode.encodeRule
        ⟨source, read, slot, ⟨write, target, move⟩⟩) left after right =
      ULogBootstrapExecution.atBits (.fieldSeek .source)
        (sBits ++ rBits ++ [slot] ++ wBits ++ tBits ++ mBits) left after right := by
    simp [sBits, rBits, wBits, tBits, mBits,
      ULogBytecode.encodeRule, ULogBytecode.encodeAction,
      hmove, List.append_assoc]
  rw [hcost, hstart, ULogBootstrapExecution.run_add, hS,
    ULogBootstrapExecution.run_add, hSH,
    ULogBootstrapExecution.run_add, hR,
    ULogBootstrapExecution.run_add, hSlot,
    ULogBootstrapExecution.run_add, hW,
    ULogBootstrapExecution.run_add, hWH,
    ULogBootstrapExecution.run_add, hT,
    ULogBootstrapExecution.run_add, hM₁]
  simpa [sBits, rBits, wBits, tBits, mBits, lS, lR, lSlot, lW, lT,
    lM₁, lM₂, ULogBytecode.encodeRule, ULogBytecode.encodeAction,
    List.reverse_append, List.map_append, List.append_assoc] using hM₂

/-- The count round is insensitive to how the next unread bit is physically
represented: its explicit ledger lifts from a `countCheckStart` to the
actual `atBits` state. -/
theorem run_countFresh_bits_exact
    (bits : List Bool) (hbits : bits ≠ [])
    (skipped : List Bool) (remaining done : ℕ) (left : List ULogProgram.Tape)
    (after : ULogProgram.Tape) (right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run
      (2 * skipped.length + 2 * remaining + 2 * done + 7)
      (ULogBootstrapExecution.atBits (.fieldReturn .programCount) bits
        (ULogBootstrapExecution.returnPath skipped (remaining + 1) done ++
          ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left) after right) =
      ULogBootstrapExecution.atBits (.fieldSeek .source) bits
        (ULogBootstrapExecution.freshRuleLeft skipped remaining done left)
        after right := by
  cases bits with
  | nil => exact (hbits rfl).elim
  | cons b bs =>
      simpa [ULogBootstrapExecution.atBits,
        ULogBootstrapExecution.countCheckStart,
        ULogBootstrapExecution.countFreshDone,
        ULogBootstrapExecution.freshRuleLeft] using
        (run_countFresh_exact b skipped remaining done left
          (bs.map ULogProgram.codeTape ++ after :: right))

/-- Exact skip-parser fuel remains valid when a following bit stream shares
the same zipper: the suffix is merely the next physical focus after the
literal rule. -/
theorem run_skipRule_prefix_exact
    (r : ULogBytecode.RuleCode) (tail : List Bool)
    (left : List ULogProgram.Tape) (after : ULogProgram.Tape)
    (right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run ((ULogBytecode.encodeRule r).length + 2)
      (ULogBootstrapExecution.atBits (.fieldSeek .source)
        (ULogBytecode.encodeRule r ++ tail) left after right) =
      ULogBootstrapExecution.atBits ULogControl.State.skipRule tail
        ((ULogBytecode.encodeRule r).reverse.map ULogProgram.codeTape ++ left)
        after right := by
  cases tail with
  | nil =>
      cases he : ULogBytecode.encodeRule r with
      | nil =>
          have hne := ULogBootstrapExecution.encodeRule_ne_nil r
          exact (hne he).elim
      | cons a as =>
          simpa [ULogBootstrapExecution.atBits, he] using
            (run_skipRule_exact r left after right)
  | cons b bs =>
      cases he : ULogBytecode.encodeRule r with
      | nil =>
          have hne := ULogBootstrapExecution.encodeRule_ne_nil r
          exact (hne he).elim
      | cons a as =>
          simpa [ULogBootstrapExecution.atBits, he, List.map_append,
            List.append_assoc] using
            (run_skipRule_exact r left (ULogProgram.codeTape b)
              (bs.map ULogProgram.codeTape ++ after :: right))

/-- Explicit cost of one nonfinal rule round.  The first summand accounts for
the count scan, the second for parsing the literal rule, and the final unit
for re-entering `fieldReturn programCount` on the remaining bit stream. -/
def ruleRoundFuel (skipped : List Bool) (remaining done : ℕ)
    (r : ULogBytecode.RuleCode) : ℕ :=
  (2 * skipped.length + 2 * remaining + 2 * done + 7) +
    (ULogBytecode.encodeRule r).length + 3

/-- Local algebraic bound for one rule round under a width budget. -/
theorem ruleRoundFuel_le_of_encodeRule_le
    (skipped : List Bool) (remaining done R : ℕ)
    (r : ULogBytecode.RuleCode)
    (hwidth : (ULogBytecode.encodeRule r).length ≤ R) :
    ruleRoundFuel skipped remaining done r ≤
      2 * skipped.length + 2 * remaining + 2 * done + R + 10 := by
  unfold ruleRoundFuel
  omega

theorem run_ruleRound_next_exact
    (skipped : List Bool) (done remaining : ℕ)
    (r : ULogBytecode.RuleCode) (tail : List Bool) (htail : tail ≠ [])
    (left : List ULogProgram.Tape) (after : ULogProgram.Tape)
    (right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (ruleRoundFuel skipped remaining done r)
      (ULogBootstrapExecution.atBits (.fieldReturn .programCount)
        (ULogBytecode.encodeRule r ++ tail)
        (ULogBootstrapExecution.returnPath skipped (remaining + 1) done ++
          ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left) after right) =
      ULogBootstrapExecution.atBits (.fieldReturn .programCount) tail
        (ULogBootstrapExecution.returnPath
          (skipped ++ ULogBytecode.encodeRule r) remaining (done + 1) ++
          ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left) after right := by
  unfold ruleRoundFuel
  rw [show
    (2 * skipped.length + 2 * remaining + 2 * done + 7) +
        (ULogBytecode.encodeRule r).length + 3 =
      (2 * skipped.length + 2 * remaining + 2 * done + 7) +
        (((ULogBytecode.encodeRule r).length + 2) + 1) by omega]
  rw [ULogBootstrapExecution.run_add,
    run_countFresh_bits_exact (ULogBytecode.encodeRule r ++ tail) (by
      intro h
      have henc : ULogBytecode.encodeRule r ≠ [] := ULogBootstrapExecution.encodeRule_ne_nil r
      simpa [henc] using h),
    ULogBootstrapExecution.run_add,
    run_skipRule_prefix_exact r tail]
  have hstep : ULogBootstrapExecution.run 1
      (ULogBootstrapExecution.atBits ULogControl.State.skipRule tail
        ((ULogBytecode.encodeRule r).reverse.map ULogProgram.codeTape ++
          ULogBootstrapExecution.freshRuleLeft skipped remaining done left)
        after right) =
      ULogBootstrapExecution.atBits (.fieldReturn .programCount) tail
        ((ULogBytecode.encodeRule r).reverse.map ULogProgram.codeTape ++
          ULogBootstrapExecution.freshRuleLeft skipped remaining done left)
        after right := by
    cases tail with
    | nil => exact (htail rfl).elim
    | cons b bs =>
        simpa [ULogBootstrapExecution.run] using
          (ULogBootstrapExecution.atBits_skipRule_next_nonempty (b :: bs)
            (by simp) _ after right)
  rw [hstep]
  rw [ULogBootstrapExecution.freshRuleLeft_eq_returnPath]

/-- Exact terminal program-count pass after the final rule. -/
theorem run_finalCountExhausted_exact
    (carry : Bool) (skipped : List Bool) (done : ℕ)
    (left right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (2 * skipped.length + 2 * done + 7)
      (ULogBootstrapExecution.finalCountCheckStart carry skipped done left right) =
      ULogBootstrapExecution.finalCountDone carry skipped done left right := by
  let returnPath := ULogBootstrapExecution.finalReturnPath skipped done
  let seekPath := ULogBootstrapExecution.finalSeekPath skipped
  have hreturn : returnPath ≠ [] := by
    simp [returnPath, ULogBootstrapExecution.finalReturnPath]
  have h₀ : ULogBootstrapExecution.run 1
      (ULogBootstrapExecution.finalCountCheckStart carry skipped done left right) =
      .running (.returnToPc carry)
        (ULogBootstrapExecution.beforeLeftPath returnPath left
          (ULogAlphabet.ulogCore ULogAlphabet.pcMark)
          (ULogProgram.branchTape carry :: right)) := by
    cases hp : returnPath with
    | nil => exact (hreturn hp).elim
    | cons a as =>
        simp [ULogBootstrapExecution.run,
          ULogBootstrapExecution.finalCountCheckStart,
          ULogBootstrapExecution.beforeLeftPath, returnPath, hp,
          ULogBootstrapExecution.fieldReturn_count_step]
  have h₁ : ULogBootstrapExecution.run returnPath.length
      (.running (.returnToPc carry)
        (ULogBootstrapExecution.beforeLeftPath returnPath left
          (ULogAlphabet.ulogCore ULogAlphabet.pcMark)
          (ULogProgram.branchTape carry :: right))) =
      ULogBootstrapExecution.finalCountAtMark carry skipped done left right := by
    simpa [ULogBootstrapExecution.finalCountAtMark] using
      ULogBootstrapExecution.run_left_path_of (.returnToPc carry) returnPath
        (by
          intro a ha l y r
          exact ULogBootstrapExecution.finalReturnPath_pass carry skipped done a
            (by simpa [returnPath] using ha) l y r)
        left (ULogAlphabet.ulogCore ULogAlphabet.pcMark)
        (ULogProgram.branchTape carry :: right)
  have h₂ : ULogBootstrapExecution.run 1
      (ULogBootstrapExecution.finalCountAtMark carry skipped done left right) =
      .running (.countScan carry)
        (ULogBootstrapExecution.beforeRightPath
          (List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.pcDone))
          (ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
          (ULogProgram.codeTape true)
          (seekPath ++ ULogProgram.branchTape carry :: right)) := by
    cases done <;>
      simp [ULogBootstrapExecution.run,
        ULogBootstrapExecution.finalCountAtMark,
        ULogBootstrapExecution.afterLeftPath,
        ULogBootstrapExecution.beforeRightPath,
        ULogBootstrapExecution.finalReturnPath_reverse, seekPath,
        ULogBootstrapExecution.returnToPc_mark, List.replicate_succ,
        List.append_assoc]
  have h₃ : ULogBootstrapExecution.run done
      (.running (.countScan carry)
        (ULogBootstrapExecution.beforeRightPath
          (List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.pcDone))
          (ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
          (ULogProgram.codeTape true)
          (seekPath ++ ULogProgram.branchTape carry :: right))) =
      ULogBootstrapExecution.finalCountAfterDone carry skipped done left right := by
    simpa [ULogBootstrapExecution.finalCountAfterDone, seekPath] using
      ULogBootstrapExecution.run_right_path_of (.countScan carry)
        (List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.pcDone)) (by
          intro z hz l y r
          have hzmem : done ≠ 0 ∧ z = ULogAlphabet.ulogCore ULogAlphabet.pcDone := by
            simpa only [List.mem_replicate] using hz
          rw [hzmem.2]
          exact ULogBootstrapExecution.countScan_done carry l y r)
        (ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
        (ULogProgram.codeTape true)
        (seekPath ++ ULogProgram.branchTape carry :: right)
  have h₄ : ULogBootstrapExecution.run 1
      (ULogBootstrapExecution.finalCountAfterDone carry skipped done left right) =
      ULogBootstrapExecution.finalSeekStarted carry skipped done left right := by
    cases skipped <;>
      simp [ULogBootstrapExecution.run,
        ULogBootstrapExecution.finalCountAfterDone,
        ULogBootstrapExecution.finalSeekStarted,
        ULogBootstrapExecution.finalSeekPath,
        ULogBootstrapExecution.afterRightPath,
        ULogBootstrapExecution.beforeRightPath,
        ULogBootstrapExecution.countScan_exhausted,
        List.append_assoc]
  have h₅ : ULogBootstrapExecution.run seekPath.length
      (ULogBootstrapExecution.finalSeekStarted carry skipped done left right) =
      ULogBootstrapExecution.finalSeekReturned carry skipped done left right := by
    simpa [ULogBootstrapExecution.finalSeekStarted,
      ULogBootstrapExecution.finalSeekReturned, seekPath] using
      ULogBootstrapExecution.run_right_path_of (.seekReturn carry true) seekPath
        (by
          intro a ha l y r
          exact ULogBootstrapExecution.finalSeekPath_pass carry skipped a
            (by simpa [seekPath] using ha) l y r)
        (ULogProgram.codeTape true ::
          List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.pcDone) ++
            ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
        (ULogProgram.branchTape carry) right
  have h₆ : ULogBootstrapExecution.run 1
      (ULogBootstrapExecution.finalSeekReturned carry skipped done left right) =
      ULogBootstrapExecution.finalCountDone carry skipped done left right := by
    simp [ULogBootstrapExecution.run,
      ULogBootstrapExecution.finalSeekReturned,
      ULogBootstrapExecution.finalCountDone,
      ULogBootstrapExecution.afterRightPath,
      ULogBootstrapExecution.seekReturn_marker]
  rw [show 2 * skipped.length + 2 * done + 7 =
      1 + (returnPath.length + (1 + (done + (1 + (seekPath.length + 1))))) by
        simp [returnPath, seekPath, ULogBootstrapExecution.finalReturnPath,
          ULogBootstrapExecution.finalSeekPath]; omega]
  rw [ULogBootstrapExecution.run_add, h₀,
    ULogBootstrapExecution.run_add, h₁,
    ULogBootstrapExecution.run_add, h₂,
    ULogBootstrapExecution.run_add, h₃,
    ULogBootstrapExecution.run_add, h₄,
    ULogBootstrapExecution.run_add, h₅]
  exact h₆

/-- Exact terminal count pass for the payload-carry route.  Unlike
`run_finalCountExhausted_exact`, it deliberately leaves the physical
`codeEnd` on the right, so its result is the canonical payload-length start
state rather than the frozen final-count normal form. -/
theorem run_countExhausted_exact
    (carry : Bool) (skipped : List Bool) (done : ℕ)
    (left right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (2 * skipped.length + 2 * done + 5)
      (ULogBootstrapExecution.countCheckStart carry skipped 0 done left right) =
      ULogBootstrapExecution.countExhaustedDone carry skipped done left right := by
  let returnPath := ULogBootstrapExecution.returnPath skipped 0 done
  let seekPath := skipped.map ULogProgram.codeTape
  have hreturn : returnPath ≠ [] := by
    simp [returnPath, ULogBootstrapExecution.returnPath]
  have h₀ : ULogBootstrapExecution.run 1
      (ULogBootstrapExecution.countCheckStart carry skipped 0 done left right) =
      .running (.returnToPc carry)
        (ULogBootstrapExecution.beforeLeftPath returnPath left
          (ULogAlphabet.ulogCore ULogAlphabet.pcMark)
          (ULogProgram.branchTape carry :: right)) := by
    cases hp : returnPath with
    | nil => exact (hreturn hp).elim
    | cons a as =>
        simp [ULogBootstrapExecution.run,
          ULogBootstrapExecution.countCheckStart,
          ULogBootstrapExecution.beforeLeftPath, returnPath, hp,
          ULogBootstrapExecution.fieldReturn_count_step]
  have h₁ : ULogBootstrapExecution.run returnPath.length
      (.running (.returnToPc carry)
        (ULogBootstrapExecution.beforeLeftPath returnPath left
          (ULogAlphabet.ulogCore ULogAlphabet.pcMark)
          (ULogProgram.branchTape carry :: right))) =
      ULogBootstrapExecution.countAtMark carry skipped 0 done left right := by
    simpa [ULogBootstrapExecution.countAtMark] using
      ULogBootstrapExecution.run_left_path_of (.returnToPc carry) returnPath
        (by
          intro a ha l y r
          exact ULogBootstrapExecution.returnPath_pass carry skipped 0 done a
            (by simpa [returnPath] using ha) l y r)
        left (ULogAlphabet.ulogCore ULogAlphabet.pcMark)
        (ULogProgram.branchTape carry :: right)
  have h₂ : ULogBootstrapExecution.run 1
      (ULogBootstrapExecution.countAtMark carry skipped 0 done left right) =
      .running (.countScan carry)
        (ULogBootstrapExecution.beforeRightPath
          (List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.pcDone))
          (ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
          (ULogProgram.codeTape true)
          (seekPath ++ ULogProgram.branchTape carry :: right)) := by
    cases done <;>
      simp [ULogBootstrapExecution.run, ULogBootstrapExecution.countAtMark,
        ULogBootstrapExecution.afterLeftPath,
        ULogBootstrapExecution.beforeRightPath,
        ULogBootstrapExecution.returnPath_reverse,
        ULogBootstrapExecution.seekPath, seekPath,
        ULogBootstrapExecution.returnToPc_mark, List.replicate_succ,
        List.append_assoc]
  have h₃ : ULogBootstrapExecution.run done
      (.running (.countScan carry)
        (ULogBootstrapExecution.beforeRightPath
          (List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.pcDone))
          (ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
          (ULogProgram.codeTape true)
          (seekPath ++ ULogProgram.branchTape carry :: right))) =
      ULogBootstrapExecution.countAfterDone carry skipped 0 done left right := by
    simpa [ULogBootstrapExecution.countAfterDone,
      ULogBootstrapExecution.seekPath, seekPath] using
      ULogBootstrapExecution.run_right_path_of (.countScan carry)
        (List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.pcDone)) (by
          intro z hz l y r
          have hzmem : done ≠ 0 ∧ z = ULogAlphabet.ulogCore ULogAlphabet.pcDone := by
            simpa only [List.mem_replicate] using hz
          rw [hzmem.2]
          exact ULogBootstrapExecution.countScan_done carry l y r)
        (ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
        (ULogProgram.codeTape true)
        (seekPath ++ ULogProgram.branchTape carry :: right)
  have h₄ : ULogBootstrapExecution.run 1
      (ULogBootstrapExecution.countAfterDone carry skipped 0 done left right) =
      ULogBootstrapExecution.countExhaustedStarted carry skipped done left right := by
    cases skipped <;>
      simp [ULogBootstrapExecution.run,
        ULogBootstrapExecution.countAfterDone,
        ULogBootstrapExecution.countExhaustedStarted,
        ULogBootstrapExecution.seekPath,
        ULogBootstrapExecution.afterRightPath,
        ULogBootstrapExecution.beforeRightPath,
        ULogBootstrapExecution.countScan_exhausted,
        List.append_assoc]
  have h₅ : ULogBootstrapExecution.run seekPath.length
      (ULogBootstrapExecution.countExhaustedStarted carry skipped done left right) =
      ULogBootstrapExecution.countExhaustedReturned carry skipped done left right := by
    simpa [ULogBootstrapExecution.countExhaustedStarted,
      ULogBootstrapExecution.countExhaustedReturned, seekPath] using
      ULogBootstrapExecution.run_right_path_of (.seekReturn carry true) seekPath
        (by
          intro a ha l y r
          have ha' : a ∈ skipped.map ULogProgram.codeTape := by
            simpa [seekPath] using ha
          rcases List.mem_map.mp ha' with ⟨b, -, rfl⟩
          exact ULogBootstrapExecution.seekReturn_pass_code carry true b l y r)
        (ULogProgram.codeTape true ::
          List.replicate done (ULogAlphabet.ulogCore ULogAlphabet.pcDone) ++
            ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
        (ULogProgram.branchTape carry) right
  have h₆ : ULogBootstrapExecution.run 1
      (ULogBootstrapExecution.countExhaustedReturned carry skipped done left right) =
      ULogBootstrapExecution.countExhaustedDone carry skipped done left right := by
    simp [ULogBootstrapExecution.run,
      ULogBootstrapExecution.countExhaustedReturned,
      ULogBootstrapExecution.countExhaustedDone,
      ULogBootstrapExecution.afterRightPath,
      ULogBootstrapExecution.seekReturn_marker]
  rw [show 2 * skipped.length + 2 * done + 5 =
      1 + (returnPath.length + (1 + (done + (1 + (seekPath.length + 1))))) by
        simp [returnPath, seekPath, ULogBootstrapExecution.returnPath]; omega]
  rw [ULogBootstrapExecution.run_add, h₀,
    ULogBootstrapExecution.run_add, h₁,
    ULogBootstrapExecution.run_add, h₂,
    ULogBootstrapExecution.run_add, h₃,
    ULogBootstrapExecution.run_add, h₄,
    ULogBootstrapExecution.run_add, h₅]
  exact h₆

/-- Recursive exact ledger for the payload-carry variant of rule-list
decoding.  Its terminal branch is `countExhaustedDone`, hence it preserves
the live right-side `codeEnd` needed by payload-length parsing. -/
def payloadRuleListFuel : List ULogBytecode.RuleCode → List Bool → ℕ → ℕ
  | [], skipped, done => 2 * skipped.length + 2 * done + 5
  | r :: rs, skipped, done =>
      ruleRoundFuel skipped rs.length done r +
        payloadRuleListFuel rs (skipped ++ ULogBytecode.encodeRule r) (done + 1)

/-- A single scalar envelope is invariant under the recursive rule-list
pass: bytes moved from `remaining` to `skipped` and one rule moved to
`done` do not increase their total encoded width.  This deliberately coarse
bound is stated before the execution theorem so later bootstrap arithmetic
does not have to unfold the run proof. -/
theorem payloadRuleListFuel_le_rounds_mul
    (rules : List ULogBytecode.RuleCode) (skipped : List Bool) (done : ℕ) :
    let B := skipped.length + (ULogBytecode.encodeRules rules).length +
      done + rules.length + 1
    payloadRuleListFuel rules skipped done ≤
      (rules.length + 1) * (7 * B + 10) := by
  induction rules generalizing skipped done with
  | nil =>
      simp [payloadRuleListFuel, ULogBytecode.encodeRules]
      omega
  | cons r rs ih =>
      let B := skipped.length +
        (ULogBytecode.encodeRules (r :: rs)).length +
          done + (r :: rs).length + 1
      have hskip : skipped.length ≤ B := by
        simp only [B]
        omega
      have hremain : rs.length ≤ B := by
        simp only [B, List.length_cons]
        omega
      have hdone : done ≤ B := by
        simp only [B]
        omega
      have hrule : (ULogBytecode.encodeRule r).length ≤ B := by
        simp only [B, ULogBytecode.encodeRules, List.length_append,
          List.length_cons]
        omega
      have hround : ruleRoundFuel skipped rs.length done r ≤ 7 * B + 10 := by
        have hlocal := ruleRoundFuel_le_of_encodeRule_le skipped rs.length done B r hrule
        omega
      have hB :
          skipped.length + (ULogBytecode.encodeRules (r :: rs)).length +
                done + (r :: rs).length + 1 =
            (skipped ++ ULogBytecode.encodeRule r).length +
              (ULogBytecode.encodeRules rs).length + (done + 1) +
                rs.length + 1 := by
        simp [ULogBytecode.encodeRules]
        omega
      have htail := ih (skipped ++ ULogBytecode.encodeRule r) (done + 1)
      simp only [payloadRuleListFuel]
      change ruleRoundFuel skipped rs.length done r +
          payloadRuleListFuel rs (skipped ++ ULogBytecode.encodeRule r) (done + 1) ≤
        ((r :: rs).length + 1) * (7 * B + 10)
      have htail' :
          payloadRuleListFuel rs (skipped ++ ULogBytecode.encodeRule r) (done + 1) ≤
            (rs.length + 1) * (7 * B + 10) := by
        dsimp only at htail
        rw [← hB] at htail
        exact htail
      calc
        ruleRoundFuel skipped rs.length done r +
            payloadRuleListFuel rs (skipped ++ ULogBytecode.encodeRule r) (done + 1) ≤
          (7 * B + 10) + (rs.length + 1) * (7 * B + 10) :=
            Nat.add_le_add hround htail'
        _ = ((r :: rs).length + 1) * (7 * B + 10) := by
          simp only [List.length_cons]
          ring

/-- Uniform cubic envelope for the exact recursive rule-list fuel.  The
actual estimate above is quadratic; the cubic form is convenient when all
bootstrap phases are absorbed into the copied-radius budget. -/
theorem payloadRuleListFuel_le_cube
    (rules : List ULogBytecode.RuleCode) (skipped : List Bool) (done : ℕ) :
    let B := skipped.length + (ULogBytecode.encodeRules rules).length +
      done + rules.length + 1
    payloadRuleListFuel rules skipped done ≤ 20 * B ^ 3 := by
  let B := skipped.length + (ULogBytecode.encodeRules rules).length +
    done + rules.length + 1
  have hB : 1 ≤ B := by
    simp only [B]
    omega
  have hrules : rules.length + 1 ≤ B := by
    simp only [B]
    omega
  have hmain := payloadRuleListFuel_le_rounds_mul rules skipped done
  change payloadRuleListFuel rules skipped done ≤ 20 * B ^ 3
  have hlinear : 7 * B + 10 ≤ 17 * B := by omega
  calc
    payloadRuleListFuel rules skipped done ≤
        (rules.length + 1) * (7 * B + 10) := by simpa [B] using hmain
    _ ≤ B * (17 * B) := Nat.mul_le_mul hrules hlinear
    _ = 17 * B ^ 2 := by ring
    _ ≤ 17 * B ^ 3 := by
      exact Nat.mul_le_mul_left 17
        (Nat.pow_le_pow_right hB (by decide : 2 ≤ 3))
    _ ≤ 20 * B ^ 3 := by
      exact Nat.mul_le_mul_right (B ^ 3) (by omega)

theorem run_payloadRuleList_exact
    (rules : List ULogBytecode.RuleCode)
    (skipped : List Bool) (done : ℕ) (payloadCarry : Bool)
    (left : List ULogProgram.Tape) (after : ULogProgram.Tape)
    (right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (payloadRuleListFuel rules skipped done)
      (ULogBootstrapExecution.atBits (.fieldReturn .programCount)
        (ULogBytecode.encodeRules rules ++ [payloadCarry])
        (ULogBootstrapExecution.returnPath skipped rules.length done ++
          ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
        after right) =
      ULogBootstrapExecution.countExhaustedDone payloadCarry
        (skipped ++ ULogBytecode.encodeRules rules) (done + rules.length)
        left (after :: right) := by
  induction rules generalizing skipped done with
  | nil =>
      simpa [payloadRuleListFuel, ULogBytecode.encodeRules,
        ULogBootstrapExecution.atBits, ULogBootstrapExecution.countCheckStart,
        List.append_assoc] using
        (run_countExhausted_exact payloadCarry skipped done left (after :: right))
  | cons r rs ih =>
      let tailBits := ULogBytecode.encodeRules rs ++ [payloadCarry]
      have htail : tailBits ≠ [] := by simp [tailBits]
      have hround := run_ruleRound_next_exact skipped done rs.length r tailBits
        htail left after right
      have hrest := ih (skipped ++ ULogBytecode.encodeRule r) (done + 1)
      simp only [payloadRuleListFuel]
      rw [ULogBootstrapExecution.run_add]
      have hround' : ULogBootstrapExecution.run
          (ruleRoundFuel skipped rs.length done r)
          (ULogBootstrapExecution.atBits (.fieldReturn .programCount)
            (ULogBytecode.encodeRules (r :: rs) ++ [payloadCarry])
            (ULogBootstrapExecution.returnPath skipped (r :: rs).length done ++
              ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
            after right) =
          ULogBootstrapExecution.atBits (.fieldReturn .programCount)
            (ULogBytecode.encodeRules rs ++ [payloadCarry])
            (ULogBootstrapExecution.returnPath
              (skipped ++ ULogBytecode.encodeRule r) rs.length (done + 1) ++
              ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
            after right := by
        simpa [tailBits, ULogBytecode.encodeRules,
          List.append_assoc] using hround
      rw [hround']
      simpa [ULogBytecode.encodeRules, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

/-- Exact nonempty-program prefix on the live payload-carry route.  Unlike
`run_programRules_exact`, this theorem keeps the first payload bit at the
head and hence has the canonical `countExhaustedDone` endpoint. -/
def programPayloadFuel (rules : List ULogBytecode.RuleCode) : ℕ :=
  rules.length + 2 + payloadRuleListFuel rules [] 0

/-- The complete program-count / rule-list pass is cubic in the literal
program word.  This bound is intentionally generous so it composes without
case-specific constant optimization. -/
theorem programPayloadFuel_le_cube (rules : List ULogBytecode.RuleCode) :
    programPayloadFuel rules ≤
      22 * ((ULogBytecode.encodeProgram rules).length + 1) ^ 3 := by
  have hlist := payloadRuleListFuel_le_cube rules [] 0
  have hlen : (ULogBytecode.encodeProgram rules).length =
      rules.length + 1 + (ULogBytecode.encodeRules rules).length := by
    simp [ULogBytecode.encodeProgram]
  have hrules : rules.length + 2 ≤
      (ULogBytecode.encodeProgram rules).length + 1 := by
    rw [hlen]
    omega
  unfold programPayloadFuel
  have hlist' : payloadRuleListFuel rules [] 0 ≤
      20 * (ULogBytecode.encodeProgram rules).length ^ 3 := by
    simpa [hlen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlist
  have hmono : (ULogBytecode.encodeProgram rules).length ^ 3 ≤
      ((ULogBytecode.encodeProgram rules).length + 1) ^ 3 :=
    Nat.pow_le_pow_left (by omega) 3
  nlinarith

theorem run_programPayload_exact
    (rules : List ULogBytecode.RuleCode) (hrules : rules ≠ [])
    (payloadCarry : Bool) (after : ULogProgram.Tape)
    (right : List ULogProgram.Tape) (left : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (programPayloadFuel rules)
      (.running ULogControl.State.framePayloadLength
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          (ULogBytecode.encodeProgram rules ++ [payloadCarry]).map
            ULogProgram.codeTape ++ after :: right⟩) =
      ULogBootstrapExecution.countExhaustedDone payloadCarry
        (ULogBytecode.encodeRules rules) rules.length left (after :: right) := by
  unfold programPayloadFuel
  rw [show rules.length + 2 + payloadRuleListFuel rules [] 0 =
      (rules.length + 2) + payloadRuleListFuel rules [] 0 by omega]
  rw [ULogBootstrapExecution.run_add]
  have henc : ULogBytecode.encodeRules rules ≠ [] :=
    ULogBootstrapExecution.encodeRules_ne_nil hrules
  cases he : ULogBytecode.encodeRules rules with
  | nil => exact (henc he).elim
  | cons b bs =>
      have hcount : ULogBootstrapExecution.run (rules.length + 2)
          (.running ULogControl.State.framePayloadLength
            ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
              List.replicate rules.length
                (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++
                ULogAlphabet.ulogCore ULogAlphabet.codeOne ::
                  ULogProgram.codeTape b ::
                    bs.map ULogProgram.codeTape ++
                      ULogProgram.codeTape payloadCarry :: after :: right⟩) =
          .running (ULogControl.State.fieldReturn .programCount)
            ⟨ULogAlphabet.ulogCore ULogAlphabet.codeOne ::
                List.replicate rules.length
                  (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++
                    ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left,
              ULogProgram.codeTape b,
              bs.map ULogProgram.codeTape ++ ULogProgram.codeTape payloadCarry ::
                after :: right⟩ := by
        have hentry : ULogBootstrapExecution.run 1
            (.running ULogControl.State.framePayloadLength
              ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
                List.replicate rules.length
                  (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++
                  ULogAlphabet.ulogCore ULogAlphabet.codeOne ::
                    ULogProgram.codeTape b ::
                      bs.map ULogProgram.codeTape ++
                        ULogProgram.codeTape payloadCarry :: after :: right⟩) =
            ULogBootstrapExecution.beforeFieldZeros .programCount rules.length
              (ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
              (ULogProgram.codeTape b)
              (bs.map ULogProgram.codeTape ++ ULogProgram.codeTape payloadCarry ::
                after :: right) := by
          cases rules.length <;>
            simp [ULogBootstrapExecution.run,
              ULogBootstrapExecution.beforeFieldZeros,
              ULogBootstrapExecution.framePayloadLength_step,
              List.replicate_succ, List.append_assoc]
        rw [show rules.length + 2 = 1 + (rules.length + 1) by omega,
          ULogBootstrapExecution.run_add, hentry]
        simpa using (run_field_exact .programCount rules.length
          (ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
          (ULogProgram.codeTape b)
          (bs.map ULogProgram.codeTape ++ ULogProgram.codeTape payloadCarry ::
            after :: right))
      have hcount' : ULogBootstrapExecution.run (rules.length + 2)
          (.running ULogControl.State.framePayloadLength
            ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
              (ULogBytecode.encodeProgram rules ++ [payloadCarry]).map
                ULogProgram.codeTape ++ after :: right⟩) =
          ULogBootstrapExecution.atBits (.fieldReturn .programCount)
            (ULogBytecode.encodeRules rules ++ [payloadCarry])
            (ULogBootstrapExecution.returnPath [] rules.length 0 ++
              ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
            after right := by
        simpa [ULogBytecode.encodeProgram, ULogBytecode.encodeNatField, he,
          ULogBootstrapExecution.atBits, ULogBootstrapExecution.returnPath,
          ULogProgram.codeTape, List.map_append, List.append_assoc] using hcount
      rw [hcount']
      simpa [Nat.zero_add, he] using
        (run_payloadRuleList_exact rules [] 0 payloadCarry left after right)

/-- The empty bytecode program follows the same live payload-carry protocol:
the unary zero count is consumed in two steps and the exact exhausted-count
base case costs five more. -/
theorem run_programPayload_empty_exact
    (payloadCarry : Bool) (after : ULogProgram.Tape)
    (right left : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (programPayloadFuel [])
      (.running ULogControl.State.framePayloadLength
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          (ULogBytecode.encodeProgram [] ++ [payloadCarry]).map
            ULogProgram.codeTape ++ after :: right⟩) =
      ULogBootstrapExecution.countExhaustedDone payloadCarry [] 0
        left (after :: right) := by
  have hentry : ULogBootstrapExecution.run 1
      (.running ULogControl.State.framePayloadLength
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          ULogAlphabet.ulogCore ULogAlphabet.codeOne ::
            ULogProgram.codeTape payloadCarry :: after :: right⟩) =
      ULogBootstrapExecution.beforeFieldZeros .programCount 0
        (ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
        (ULogProgram.codeTape payloadCarry) (after :: right) := by
    simp [ULogBootstrapExecution.run,
      ULogBootstrapExecution.beforeFieldZeros,
      ULogBootstrapExecution.framePayloadLength_step]
  have hcount : ULogBootstrapExecution.run 2
      (.running ULogControl.State.framePayloadLength
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          ULogAlphabet.ulogCore ULogAlphabet.codeOne ::
            ULogProgram.codeTape payloadCarry :: after :: right⟩) =
      .running (ULogControl.State.fieldReturn .programCount)
        ⟨ULogAlphabet.ulogCore ULogAlphabet.codeOne ::
            ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left,
          ULogProgram.codeTape payloadCarry, after :: right⟩ := by
    rw [show 2 = 1 + 1 by omega, ULogBootstrapExecution.run_add, hentry]
    simpa using (run_field_exact .programCount 0
      (ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
      (ULogProgram.codeTape payloadCarry) (after :: right))
  have hbase := run_payloadRuleList_exact [] [] 0 payloadCarry left after right
  unfold programPayloadFuel
  rw [show [].length + 2 + payloadRuleListFuel [] [] 0 =
      2 + payloadRuleListFuel [] [] 0 by rfl,
    ULogBootstrapExecution.run_add]
  have hcount' : ULogBootstrapExecution.run 2
      (.running ULogControl.State.framePayloadLength
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          (ULogBytecode.encodeProgram [] ++ [payloadCarry]).map
            ULogProgram.codeTape ++ after :: right⟩) =
      ULogBootstrapExecution.atBits (.fieldReturn .programCount) [payloadCarry]
        (ULogBootstrapExecution.returnPath [] 0 0 ++
          ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left) after right := by
    simpa [ULogBytecode.encodeProgram, ULogBytecode.encodeRules,
      ULogBytecode.encodeNatField, ULogBootstrapExecution.atBits,
      ULogBootstrapExecution.returnPath, ULogProgram.codeTape,
      List.append_assoc] using hcount
  rw [hcount']
  simpa [ULogBytecode.encodeRules] using hbase

/-- Uniform exact live-carry program prefix, including the genuinely possible
empty compiled program. -/
theorem run_programPayload_all_exact
    (rules : List ULogBytecode.RuleCode)
    (payloadCarry : Bool) (after : ULogProgram.Tape)
    (right left : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (programPayloadFuel rules)
      (.running ULogControl.State.framePayloadLength
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          (ULogBytecode.encodeProgram rules ++ [payloadCarry]).map
            ULogProgram.codeTape ++ after :: right⟩) =
      ULogBootstrapExecution.countExhaustedDone payloadCarry
        (ULogBytecode.encodeRules rules) rules.length left (after :: right) := by
  cases rules with
  | nil => exact run_programPayload_empty_exact payloadCarry after right left
  | cons r rs =>
      exact run_programPayload_exact (r :: rs) (by simp) payloadCarry after right left

/-- Physical handoff from the payload-carry program parser to the canonical
payload-length zipper.  This is the point at which the preserved right-side
`codeEnd` is essential. -/
theorem run_programPayload_to_payloadStart_exact
    (rules : List ULogBytecode.RuleCode) (hrules : rules ≠ [])
    (input padding : List Bool) (left tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (programPayloadFuel rules)
      (.running ULogControl.State.framePayloadLength
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          (ULogBytecode.encodeProgram rules ++
            ULogBytecode.encodePayload input padding).map ULogProgram.codeTape ++
              ULogAlphabet.ulogCore ULogAlphabet.codeEnd ::
                MStarConcreteAlphabet.work :: tail⟩) =
      ULogBootstrapExecution.atBits ULogControl.State.payloadLengthStart
        (ULogBytecode.encodePayload input padding)
        (ULogBootstrapExecution.programMarkedLeft rules left)
        (ULogAlphabet.ulogCore ULogAlphabet.codeEnd)
        (MStarConcreteAlphabet.work :: tail) := by
  have hnonempty : ULogBytecode.encodePayload input padding ≠ [] :=
    ULogBootstrapExecution.encodePayload_ne_nil input padding
  cases hpayload : ULogBytecode.encodePayload input padding with
  | nil => exact (hnonempty hpayload).elim
  | cons b bs =>
      cases bs with
      | nil =>
          have h := run_programPayload_exact rules hrules b
            (ULogAlphabet.ulogCore ULogAlphabet.codeEnd)
            (MStarConcreteAlphabet.work :: tail) left
          simpa [hpayload, ULogBootstrapExecution.countExhaustedDone,
            ULogBootstrapExecution.programMarkedLeft,
            ULogBootstrapExecution.atBits, ULogProgram.codeTape,
            List.map_append, List.append_assoc] using h
      | cons c cs =>
          have h := run_programPayload_exact rules hrules b
            (ULogProgram.codeTape c)
            (cs.map ULogProgram.codeTape ++
              ULogAlphabet.ulogCore ULogAlphabet.codeEnd ::
                MStarConcreteAlphabet.work :: tail) left
          simpa [hpayload, ULogBootstrapExecution.countExhaustedDone,
            ULogBootstrapExecution.programMarkedLeft,
            ULogBootstrapExecution.atBits, ULogProgram.codeTape,
            List.map_append, List.append_assoc] using h

/-- Uniform program-to-payload handoff with no nonempty-program guard. -/
theorem run_programPayload_to_payloadStart_all_exact
    (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (left tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (programPayloadFuel rules)
      (.running ULogControl.State.framePayloadLength
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          (ULogBytecode.encodeProgram rules ++
            ULogBytecode.encodePayload input padding).map ULogProgram.codeTape ++
              ULogAlphabet.ulogCore ULogAlphabet.codeEnd ::
                MStarConcreteAlphabet.work :: tail⟩) =
      ULogBootstrapExecution.atBits ULogControl.State.payloadLengthStart
        (ULogBytecode.encodePayload input padding)
        (ULogBootstrapExecution.programMarkedLeft rules left)
        (ULogAlphabet.ulogCore ULogAlphabet.codeEnd)
        (MStarConcreteAlphabet.work :: tail) := by
  have hnonempty : ULogBytecode.encodePayload input padding ≠ [] :=
    ULogBootstrapExecution.encodePayload_ne_nil input padding
  cases hpayload : ULogBytecode.encodePayload input padding with
  | nil => exact (hnonempty hpayload).elim
  | cons b bs =>
      cases bs with
      | nil =>
          have h := run_programPayload_all_exact rules b
            (ULogAlphabet.ulogCore ULogAlphabet.codeEnd)
            (MStarConcreteAlphabet.work :: tail) left
          simpa [hpayload, ULogBootstrapExecution.countExhaustedDone,
            ULogBootstrapExecution.programMarkedLeft,
            ULogBootstrapExecution.atBits, ULogProgram.codeTape,
            List.map_append, List.append_assoc] using h
      | cons c cs =>
          have h := run_programPayload_all_exact rules b
            (ULogProgram.codeTape c)
            (cs.map ULogProgram.codeTape ++
              ULogAlphabet.ulogCore ULogAlphabet.codeEnd ::
                MStarConcreteAlphabet.work :: tail) left
          simpa [hpayload, ULogBootstrapExecution.countExhaustedDone,
            ULogBootstrapExecution.programMarkedLeft,
            ULogBootstrapExecution.atBits, ULogProgram.codeTape,
            List.map_append, List.append_assoc] using h

/-- Exact cost of processing the last program rule, including the final
program-count exhaustion pass that hands control to payload-length framing. -/
def finalRuleFuel (skipped : List Bool) (done : ℕ)
    (r : ULogBytecode.RuleCode) : ℕ :=
  (2 * skipped.length + 2 * done + 7) +
    ((ULogBytecode.encodeRule r).length + 3) +
      (2 * (skipped ++ ULogBytecode.encodeRule r).length +
        2 * (done + 1) + 7)

theorem run_finalRule_exact
    (skipped : List Bool) (done : ℕ) (r : ULogBytecode.RuleCode)
    (payloadCarry : Bool) (left right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (finalRuleFuel skipped done r)
      (ULogBootstrapExecution.atBits (.fieldReturn .programCount)
        (ULogBytecode.encodeRule r)
        (ULogBootstrapExecution.returnPath skipped 1 done ++
          ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
        (ULogAlphabet.ulogCore ULogAlphabet.codeEnd)
        (ULogProgram.codeTape payloadCarry :: right)) =
      ULogBootstrapExecution.finalCountDone payloadCarry
        (skipped ++ ULogBytecode.encodeRule r) (done + 1) left right := by
  unfold finalRuleFuel
  rw [show
      (2 * skipped.length + 2 * done + 7) +
          ((ULogBytecode.encodeRule r).length + 3) +
            (2 * (skipped ++ ULogBytecode.encodeRule r).length +
              2 * (done + 1) + 7) =
      (2 * skipped.length + 2 * done + 7) +
        (((ULogBytecode.encodeRule r).length + 2) +
          (1 + (2 * (skipped ++ ULogBytecode.encodeRule r).length +
            2 * (done + 1) + 7))) by omega]
  rw [ULogBootstrapExecution.run_add]
  have hcf := run_countFresh_bits_exact (ULogBytecode.encodeRule r)
    (ULogBootstrapExecution.encodeRule_ne_nil r) skipped 0 done left
    (ULogAlphabet.ulogCore ULogAlphabet.codeEnd)
    (ULogProgram.codeTape payloadCarry :: right)
  have hcf' : ULogBootstrapExecution.run (2 * skipped.length + 2 * done + 7)
      (ULogBootstrapExecution.atBits (.fieldReturn .programCount)
        (ULogBytecode.encodeRule r)
        (ULogBootstrapExecution.returnPath skipped 1 done ++
          ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
        (ULogAlphabet.ulogCore ULogAlphabet.codeEnd)
        (ULogProgram.codeTape payloadCarry :: right)) =
      ULogBootstrapExecution.atBits (.fieldSeek .source)
        (ULogBytecode.encodeRule r)
        (ULogBootstrapExecution.freshRuleLeft skipped 0 done left)
        (ULogAlphabet.ulogCore ULogAlphabet.codeEnd)
        (ULogProgram.codeTape payloadCarry :: right) := by
    simpa using hcf
  rw [hcf', ULogBootstrapExecution.run_add, run_skipRule_exact r]
  have hterm : ULogBootstrapExecution.run 1
      (.running ULogControl.State.skipRule
        ⟨(ULogBytecode.encodeRule r).reverse.map ULogProgram.codeTape ++
            ULogBootstrapExecution.freshRuleLeft skipped 0 done left,
          ULogAlphabet.ulogCore ULogAlphabet.codeEnd,
          ULogProgram.codeTape payloadCarry :: right⟩) =
      ULogBootstrapExecution.finalCountCheckStart payloadCarry
        (skipped ++ ULogBytecode.encodeRule r) (done + 1) left right := by
    have hstep := ULogBootstrapExecution.skipRule_end_step
      ((ULogBytecode.encodeRule r).reverse.map ULogProgram.codeTape ++
        ULogBootstrapExecution.freshRuleLeft skipped 0 done left)
      payloadCarry right
    simp only [ULogBootstrapExecution.run]
    have heq : (ULogBytecode.encodeRule r).reverse.map ULogProgram.codeTape ++
        ULogBootstrapExecution.freshRuleLeft skipped 0 done left =
        ULogBootstrapExecution.returnPath
          (skipped ++ ULogBytecode.encodeRule r) 0 (done + 1) ++
          ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left := by
      rw [ULogBootstrapExecution.freshRuleLeft_eq_returnPath]
    rw [heq]
    rw [heq] at hstep
    simpa [ULogBootstrapExecution.finalCountCheckStart,
      ULogBootstrapExecution.finalReturnPath,
      ULogBootstrapExecution.returnPath] using hstep
  rw [ULogBootstrapExecution.run_add, hterm]
  exact run_finalCountExhausted_exact payloadCarry
    (skipped ++ ULogBytecode.encodeRule r) (done + 1) left right

/-- Closed recursive ledger for a nonempty list of universal bytecode rules.
The recursive case consumes one nonfinal round; the singleton case is the
fully quantified terminal round. -/
def ruleListFuel : List ULogBytecode.RuleCode → List Bool → ℕ → ℕ
  | [], _, _ => 0
  | [r], skipped, done => finalRuleFuel skipped done r
  | r :: s :: rs, skipped, done =>
      ruleRoundFuel skipped (s :: rs).length done r +
        ruleListFuel (s :: rs) (skipped ++ ULogBytecode.encodeRule r) (done + 1)

theorem run_ruleList_exact
    (rules : List ULogBytecode.RuleCode) (hrules : rules ≠ [])
    (skipped : List Bool) (done : ℕ) (payloadCarry : Bool)
    (left right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (ruleListFuel rules skipped done)
      (ULogBootstrapExecution.atBits (.fieldReturn .programCount)
        (ULogBytecode.encodeRules rules)
        (ULogBootstrapExecution.returnPath skipped rules.length done ++
          ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
        (ULogAlphabet.ulogCore ULogAlphabet.codeEnd)
        (ULogProgram.codeTape payloadCarry :: right)) =
      ULogBootstrapExecution.finalCountDone payloadCarry
        (skipped ++ ULogBytecode.encodeRules rules) (done + rules.length)
        left right := by
  induction rules generalizing skipped done with
  | nil => exact (hrules rfl).elim
  | cons r rs ih =>
      cases rs with
      | nil =>
          simpa [ruleListFuel, ULogBytecode.encodeRules] using
            (run_finalRule_exact skipped done r payloadCarry left right)
      | cons s rs =>
          let tailRules : List ULogBytecode.RuleCode := s :: rs
          have htail : ULogBytecode.encodeRules tailRules ≠ [] := by
            exact ULogBootstrapExecution.encodeRules_ne_nil (by simp [tailRules])
          have hround := run_ruleRound_next_exact skipped done tailRules.length r
            (ULogBytecode.encodeRules tailRules) htail left
            (ULogAlphabet.ulogCore ULogAlphabet.codeEnd)
            (ULogProgram.codeTape payloadCarry :: right)
          have hrest := ih (by simp) (skipped ++ ULogBytecode.encodeRule r) (done + 1)
          simp only [ruleListFuel]
          rw [ULogBootstrapExecution.run_add]
          have hround' : ULogBootstrapExecution.run
              (ruleRoundFuel skipped tailRules.length done r)
              (ULogBootstrapExecution.atBits (.fieldReturn .programCount)
                (ULogBytecode.encodeRules (r :: tailRules))
                (ULogBootstrapExecution.returnPath skipped
                  ((r :: tailRules).length) done ++
                  ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
                (ULogAlphabet.ulogCore ULogAlphabet.codeEnd)
                (ULogProgram.codeTape payloadCarry :: right)) =
              ULogBootstrapExecution.atBits (.fieldReturn .programCount)
                (ULogBytecode.encodeRules tailRules)
                (ULogBootstrapExecution.returnPath
                  (skipped ++ ULogBytecode.encodeRule r) tailRules.length
                  (done + 1) ++ ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
                (ULogAlphabet.ulogCore ULogAlphabet.codeEnd)
                (ULogProgram.codeTape payloadCarry :: right) := by
            simpa [tailRules, ULogBytecode.encodeRules,
              List.append_assoc] using hround
          rw [hround']
          simpa [tailRules, ULogBytecode.encodeRules,
            List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hrest

/-- Exact initial unary program-count scan, before the rule-list ledger
begins. -/
theorem run_programCount_exact
    (n : ℕ) (left : List ULogProgram.Tape)
    (y : ULogProgram.Tape) (right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (n + 2)
      (.running ULogControl.State.framePayloadLength
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          List.replicate n (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++
            ULogAlphabet.ulogCore ULogAlphabet.codeOne :: y :: right⟩) =
      .running (ULogControl.State.fieldReturn .programCount)
        ⟨ULogAlphabet.ulogCore ULogAlphabet.codeOne ::
            List.replicate n (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++
              ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left,
          y, right⟩ := by
  have hentry : ULogBootstrapExecution.run 1
      (.running ULogControl.State.framePayloadLength
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          List.replicate n (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++
            ULogAlphabet.ulogCore ULogAlphabet.codeOne :: y :: right⟩) =
      ULogBootstrapExecution.beforeFieldZeros .programCount n
        (ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left) y right := by
    cases n <;>
      simp [ULogBootstrapExecution.run,
        ULogBootstrapExecution.beforeFieldZeros,
        ULogBootstrapExecution.framePayloadLength_step,
        List.replicate_succ, List.append_assoc]
  rw [show n + 2 = 1 + (n + 1) by omega]
  rw [ULogBootstrapExecution.run_add, hentry]
  simpa using (run_field_exact .programCount n
    (ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left) y right)

/-- Exact program-count and rule-list prefix for every nonempty universal
program.  The resulting `payloadLengthStart` frame is the precise handoff to
the input-length decoder. -/
def programRulesFuel (rules : List ULogBytecode.RuleCode) : ℕ :=
  rules.length + 2 + ruleListFuel rules [] 0

theorem run_programRules_exact
    (rules : List ULogBytecode.RuleCode) (hrules : rules ≠ [])
    (payloadCarry : Bool) (left right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (programRulesFuel rules)
      (.running ULogControl.State.framePayloadLength
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          (ULogBytecode.encodeProgram rules).map ULogProgram.codeTape ++
            ULogAlphabet.ulogCore ULogAlphabet.codeEnd ::
              ULogProgram.codeTape payloadCarry :: right⟩) =
      ULogBootstrapExecution.finalCountDone payloadCarry
        (ULogBytecode.encodeRules rules) rules.length left right := by
  unfold programRulesFuel
  rw [show rules.length + 2 + ruleListFuel rules [] 0 =
      (rules.length + 2) + ruleListFuel rules [] 0 by omega]
  rw [ULogBootstrapExecution.run_add]
  have henc : ULogBytecode.encodeRules rules ≠ [] :=
    ULogBootstrapExecution.encodeRules_ne_nil hrules
  cases he : ULogBytecode.encodeRules rules with
  | nil => exact (henc he).elim
  | cons b bs =>
    have hcount := run_programCount_exact rules.length left
      (ULogProgram.codeTape b)
      (bs.map ULogProgram.codeTape ++
        ULogAlphabet.ulogCore ULogAlphabet.codeEnd ::
          ULogProgram.codeTape payloadCarry :: right)
    have hcount' : ULogBootstrapExecution.run (rules.length + 2)
        (.running ULogControl.State.framePayloadLength
          ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
            (ULogBytecode.encodeProgram rules).map ULogProgram.codeTape ++
              ULogAlphabet.ulogCore ULogAlphabet.codeEnd ::
                ULogProgram.codeTape payloadCarry :: right⟩) =
        ULogBootstrapExecution.atBits (.fieldReturn .programCount)
          (ULogBytecode.encodeRules rules)
          (ULogBootstrapExecution.returnPath [] rules.length 0 ++
            ULogAlphabet.ulogCore ULogAlphabet.pcMark :: left)
          (ULogAlphabet.ulogCore ULogAlphabet.codeEnd)
          (ULogProgram.codeTape payloadCarry :: right) := by
      simpa [ULogBytecode.encodeProgram, ULogBytecode.encodeNatField, he,
        ULogBootstrapExecution.atBits, ULogBootstrapExecution.returnPath,
        ULogProgram.codeTape, List.map_append, List.append_assoc] using hcount
    rw [hcount']
    simpa [Nat.zero_add, he] using
      (run_ruleList_exact rules hrules [] 0 payloadCarry left right)

/-- Exact decoding of the self-delimiting payload length once the program
prefix has handed off to `payloadLengthStart`.  Its cost is exactly one plus
the actual payload length, including the empty-payload case. -/
theorem run_payloadLengthStart_exact
    (input padding : List Bool) (base : List ULogProgram.Tape)
    (after : ULogProgram.Tape) (right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (input.length + 1)
      (ULogBootstrapExecution.atBits ULogControl.State.payloadLengthStart
        (ULogBytecode.encodePayload input padding) base after right) =
      ULogBootstrapExecution.atBits (.fieldReturn .payloadLength)
        (input ++ padding)
        (ULogBootstrapExecution.payloadLengthMarkedLeft input.length base)
        after right := by
  cases input with
  | nil =>
      cases padding with
      | nil =>
          simpa [ULogBootstrapExecution.run, ULogBootstrapExecution.atBits,
            ULogBytecode.encodePayload, ULogBytecode.encodeNatField,
            ULogBootstrapExecution.payloadLengthMarkedLeft,
            ULogProgram.codeTape] using
            (ULogBootstrapExecution.payloadLengthStart_one_step base after right)
      | cons p ps =>
          simpa [ULogBootstrapExecution.run, ULogBootstrapExecution.atBits,
            ULogBytecode.encodePayload, ULogBytecode.encodeNatField,
            ULogBootstrapExecution.payloadLengthMarkedLeft,
            ULogProgram.codeTape] using
            (ULogBootstrapExecution.payloadLengthStart_one_step base
              (ULogProgram.codeTape p)
              (ps.map ULogProgram.codeTape ++ after :: right))
  | cons b input =>
      have hstart : ULogBootstrapExecution.run 1
          (ULogBootstrapExecution.atBits ULogControl.State.payloadLengthStart
            (ULogBytecode.encodePayload (b :: input) padding) base after right) =
          ULogBootstrapExecution.atBits (.fieldSeek .payloadLength)
            (ULogBytecode.encodeNatField input.length ++ ((b :: input) ++ padding))
            (ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base)
            after right := by
        cases input <;>
          simp [ULogBootstrapExecution.run, ULogBootstrapExecution.atBits,
            ULogBytecode.encodePayload, ULogBytecode.encodeNatField,
            ULogBootstrapExecution.payloadLengthStart_zero_step,
            List.replicate_succ, List.append_assoc]
      rw [show (b :: input).length + 1 = 1 + (input.length + 1) by simp; omega]
      rw [ULogBootstrapExecution.run_add, hstart]
      simpa [ULogBootstrapExecution.payloadLengthMarkedLeft,
        List.append_assoc] using
        (run_field_prefix_exact .payloadLength input.length
          ((b :: input) ++ padding)
          (ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base)
          after right)

/-- Exact nonempty-payload fold in the branch with a nonempty clock padding.
This is the main runtime case: after one first-zero action, the structural
fold consumes the remaining input bits and the terminal pass exposes the
first padding bit for clock framing. -/
theorem run_payloadFold_nonempty_padded_exact
    (b c p : Bool) (cs ps : List Bool)
    (base tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run
      (5 + payloadFoldFuel cs [b] 1 + (4 * cs.length + 11))
      (.running (ULogControl.State.fieldReturn .payloadLength)
        ⟨ULogAlphabet.ulogCore ULogAlphabet.codeOne ::
            ULogAlphabet.ulogCore ULogAlphabet.codeZero ::
              List.replicate cs.length
                (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++
                ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base,
          ULogProgram.codeTape b,
          ULogProgram.codeTape c :: cs.map ULogProgram.codeTape ++
            ULogProgram.codeTape p ::
              ps.map ULogProgram.codeTape ++
                ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail⟩) =
      .running ULogControl.State.framePadding
        ⟨ULogBootstrapExecution.payloadFoldedLeft (b :: c :: cs) base,
          ULogProgram.codeTape p,
          ps.map ULogProgram.codeTape ++
            ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail⟩ := by
  have hfirst := run_payloadFirstZero_exact b (ULogProgram.codeTape c)
    cs.length base
    (cs.map ULogProgram.codeTape ++ ULogProgram.codeTape p ::
      ps.map ULogProgram.codeTape ++
        ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail)
  have hfold := run_payloadFold_exact c cs [b] 1 base
    (ULogProgram.codeTape p)
    (ps.map ULogProgram.codeTape ++ ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail)
  have hexhaust := run_payloadExhausted_exact p ([b] ++ c :: cs)
    (1 + cs.length) base
    (ps.map ULogProgram.codeTape ++ ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail)
  rw [show 5 + payloadFoldFuel cs [b] 1 + (4 * cs.length + 11) =
      5 + (payloadFoldFuel cs [b] 1 +
        (2 * ([b] ++ c :: cs).length + 2 * (1 + cs.length) + 5)) by
        simp; omega]
  rw [ULogBootstrapExecution.run_add]
  simp [List.replicate_succ] at hfold
  simp only [List.cons_append, List.append_assoc] at hfirst hfold ⊢
  rw [hfirst,
    ULogBootstrapExecution.run_add, hfold]
  simpa [ULogBootstrapExecution.payloadFoldedLeft,
    List.append_assoc, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hexhaust

/-- Exact singleton-payload branch with nonempty padding. -/
theorem run_payloadFold_singleton_padded_exact
    (b p : Bool) (ps : List Bool)
    (base tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run 12
      (.running (ULogControl.State.fieldReturn .payloadLength)
        ⟨ULogAlphabet.ulogCore ULogAlphabet.codeOne ::
            ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base,
          ULogProgram.codeTape b,
          ULogProgram.codeTape p :: ps.map ULogProgram.codeTape ++
            ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail⟩) =
      .running ULogControl.State.framePadding
        ⟨ULogBootstrapExecution.payloadFoldedLeft [b] base,
          ULogProgram.codeTape p,
          ps.map ULogProgram.codeTape ++
            ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail⟩ := by
  have hfirst := run_payloadFirstStart_exact b (ULogProgram.codeTape p) base
    (ps.map ULogProgram.codeTape ++ ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail)
  have hexhaust := run_payloadExhausted_exact p [b] 0 base
    (ps.map ULogProgram.codeTape ++ ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail)
  rw [show 12 = 5 + (2 * [b].length + 2 * 0 + 5) by simp]
  rw [ULogBootstrapExecution.run_add]
  simp only [List.cons_append, List.append_assoc] at hfirst ⊢
  rw [hfirst]
  simpa [ULogBootstrapExecution.payloadFoldedLeft] using hexhaust

/-- Empty input with nonempty padding takes the fixed three-step probe path. -/
theorem run_payloadFold_empty_padded_exact
    (p : Bool) (ps : List Bool)
    (base tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run 3
      (.running (ULogControl.State.fieldReturn .payloadLength)
        ⟨ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne :: base,
          ULogProgram.codeTape p,
          ps.map ULogProgram.codeTape ++
            ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail⟩) =
      .running ULogControl.State.framePadding
        ⟨ULogBootstrapExecution.payloadFoldedLeft [] base,
          ULogProgram.codeTape p,
          ps.map ULogProgram.codeTape ++
            ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail⟩ := by
  simp [ULogBootstrapExecution.run,
    ULogBootstrapExecution.payloadFoldedLeft,
    ULogBootstrapExecution.fieldReturn_payload_step,
    ULogBootstrapExecution.payloadReturn_empty_step,
    ULogBootstrapExecution.payloadRestore_exhausted_step]

/-- Empty input and empty padding terminate payload framing in one literal
transition. -/
theorem run_payloadFold_empty_unpadded_exact
    (base tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run 1
      (.running (ULogControl.State.fieldReturn .payloadLength)
        ⟨ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne :: base,
          ULogAlphabet.ulogCore ULogAlphabet.codeEnd, tail⟩) =
      .running ULogControl.State.framePadding
        ⟨ULogBootstrapExecution.payloadFoldedLeft [] base,
          ULogAlphabet.ulogCore ULogAlphabet.codeEnd, tail⟩ := by
  simpa [ULogBootstrapExecution.run,
    ULogBootstrapExecution.payloadFoldedLeft] using
    (ULogBootstrapExecution.fieldReturn_payload_end_step
      (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne :: base) tail)

/-- Singleton input with no clock padding: first-start followed by the
literal code-end terminal transition. -/
theorem run_payloadFold_singleton_unpadded_exact
    (b : Bool) (base tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run 6
      (.running (ULogControl.State.fieldReturn .payloadLength)
        ⟨ULogAlphabet.ulogCore ULogAlphabet.codeOne ::
            ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base,
          ULogProgram.codeTape b,
          ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail⟩) =
      .running ULogControl.State.framePadding
        ⟨ULogBootstrapExecution.payloadFoldedLeft [b] base,
          ULogAlphabet.ulogCore ULogAlphabet.codeEnd, tail⟩ := by
  have hfirst := run_payloadFirstStart_exact b
    (ULogAlphabet.ulogCore ULogAlphabet.codeEnd) base tail
  have hend : ULogBootstrapExecution.run 1
      (.running (ULogControl.State.fieldReturn .payloadLength)
        ⟨ULogBootstrapExecution.payloadFoldedLeft [b] base,
          ULogAlphabet.ulogCore ULogAlphabet.codeEnd, tail⟩) =
      .running ULogControl.State.framePadding
        ⟨ULogBootstrapExecution.payloadFoldedLeft [b] base,
          ULogAlphabet.ulogCore ULogAlphabet.codeEnd, tail⟩ := by
    simpa [ULogBootstrapExecution.run] using
      (ULogBootstrapExecution.fieldReturn_payload_end_step
        (ULogBootstrapExecution.payloadFoldedLeft [b] base) tail)
  rw [show 6 = 5 + 1 by omega, ULogBootstrapExecution.run_add]
  rw [hfirst]
  simpa [ULogBootstrapExecution.payloadFoldedLeft] using hend

/-- The longer nonempty input branch with no padding has the same recursive
fold ledger as the padded case; its terminal action is the code-end exit. -/
theorem run_payloadFold_nonempty_unpadded_exact
    (b c : Bool) (cs : List Bool)
    (base tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (5 + payloadFoldFuel cs [b] 1 + 1)
      (.running (ULogControl.State.fieldReturn .payloadLength)
        ⟨ULogAlphabet.ulogCore ULogAlphabet.codeOne ::
            ULogAlphabet.ulogCore ULogAlphabet.codeZero ::
              List.replicate cs.length
                (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++
                ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base,
          ULogProgram.codeTape b,
          ULogProgram.codeTape c :: cs.map ULogProgram.codeTape ++
            ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail⟩) =
      .running ULogControl.State.framePadding
        ⟨ULogBootstrapExecution.payloadFoldedLeft (b :: c :: cs) base,
          ULogAlphabet.ulogCore ULogAlphabet.codeEnd, tail⟩ := by
  have hfirst := run_payloadFirstZero_exact b (ULogProgram.codeTape c)
    cs.length base
    (cs.map ULogProgram.codeTape ++ ULogAlphabet.ulogCore ULogAlphabet.codeEnd :: tail)
  have hfold := run_payloadFold_exact c cs [b] 1 base
    (ULogAlphabet.ulogCore ULogAlphabet.codeEnd) tail
  rw [show 5 + payloadFoldFuel cs [b] 1 + 1 =
      5 + (payloadFoldFuel cs [b] 1 + 1) by omega]
  rw [ULogBootstrapExecution.run_add]
  simp [List.replicate_succ] at hfold
  simp only [List.cons_append, List.append_assoc] at hfirst hfold ⊢
  rw [hfirst, ULogBootstrapExecution.run_add, hfold]
  have hend : ULogBootstrapExecution.run 1
      (.running (ULogControl.State.fieldReturn .payloadLength)
        ⟨ULogBootstrapExecution.payloadFoldedLeft (b :: c :: cs) base,
          ULogAlphabet.ulogCore ULogAlphabet.codeEnd, tail⟩) =
      .running ULogControl.State.framePadding
        ⟨ULogBootstrapExecution.payloadFoldedLeft (b :: c :: cs) base,
          ULogAlphabet.ulogCore ULogAlphabet.codeEnd, tail⟩ := by
    simpa [ULogBootstrapExecution.run] using
      (ULogBootstrapExecution.fieldReturn_payload_end_step
        (ULogBootstrapExecution.payloadFoldedLeft (b :: c :: cs) base) tail)
  simpa [ULogBootstrapExecution.payloadFoldedLeft,
    Nat.add_comm] using hend

/-- Exact branch ledger for the payload fold itself.  The six constructors
are the real empty/singleton/long crossed with unpadded/padded cases. -/
def payloadFoldCaseFuel : List Bool → List Bool → ℕ
  | [], [] => 1
  | [], _ :: _ => 3
  | [_], [] => 6
  | [_], _ :: _ => 12
  | _ :: _ :: cs, [] => 5 + payloadFoldFuel cs [false] 1 + 1
  | _ :: _ :: cs, _ :: _ =>
      5 + payloadFoldFuel cs [false] 1 + (4 * cs.length + 11)

/-- Full payload-length decoding, fold, and power-clock initialization with
no cardinality guard on either input or padding. -/
def payloadClockFuel (input padding : List Bool) : ℕ :=
  input.length + 1 + payloadFoldCaseFuel input padding + padding.length + 2

theorem run_payloadClock_all_exact
    (input padding : List Bool) (base tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (payloadClockFuel input padding)
      (ULogBootstrapExecution.atBits ULogControl.State.payloadLengthStart
        (ULogBytecode.encodePayload input padding) base
        (ULogAlphabet.ulogCore ULogAlphabet.codeEnd)
        (MStarConcreteAlphabet.work :: tail)) =
      ULogBootstrapExecution.initializedPowerClock padding
        (ULogBootstrapExecution.payloadFoldedLeft input base) tail := by
  have hdecode := run_payloadLengthStart_exact input padding base
    (ULogAlphabet.ulogCore ULogAlphabet.codeEnd)
    (MStarConcreteAlphabet.work :: tail)
  unfold payloadClockFuel
  rw [show input.length + 1 + payloadFoldCaseFuel input padding +
        padding.length + 2 =
      (input.length + 1) +
        (payloadFoldCaseFuel input padding + (padding.length + 2)) by omega,
    ULogBootstrapExecution.run_add, hdecode]
  cases input with
  | nil =>
      cases padding with
      | nil =>
          rw [show payloadFoldCaseFuel [] [] + ([].length + 2) = 1 + 2 by rfl,
            ULogBootstrapExecution.run_add]
          have hfold := run_payloadFold_empty_unpadded_exact base
            (MStarConcreteAlphabet.work :: tail)
          simp only [ULogBootstrapExecution.atBits, List.map_nil,
            List.nil_append, ULogBootstrapExecution.payloadLengthMarkedLeft,
            List.length_nil] at hfold ⊢
          rw [hfold]
          exact run_initializedPowerClock_exact []
            (ULogBootstrapExecution.payloadFoldedLeft [] base) tail
      | cons p ps =>
          rw [show payloadFoldCaseFuel [] (p :: ps) + ((p :: ps).length + 2) =
              3 + ((p :: ps).length + 2) by rfl,
            ULogBootstrapExecution.run_add]
          have hfold := run_payloadFold_empty_padded_exact p ps base
            (MStarConcreteAlphabet.work :: tail)
          simp [ULogBootstrapExecution.atBits,
            ULogBootstrapExecution.payloadLengthMarkedLeft,
            ULogBytecode.encodeNatField, ULogProgram.codeTape,
            List.append_assoc] at hfold ⊢
          rw [hfold]
          exact run_initializedPowerClock_exact (p :: ps)
            (ULogBootstrapExecution.payloadFoldedLeft [] base) tail
  | cons b bs =>
      cases bs with
      | nil =>
          cases padding with
          | nil =>
              rw [show payloadFoldCaseFuel [b] [] + ([].length + 2) = 6 + 2 by rfl,
                ULogBootstrapExecution.run_add]
              have hfold := run_payloadFold_singleton_unpadded_exact b base
                (MStarConcreteAlphabet.work :: tail)
              simp [ULogBootstrapExecution.atBits,
                ULogBootstrapExecution.payloadLengthMarkedLeft,
                ULogBytecode.encodeNatField, ULogProgram.codeTape,
                List.append_assoc] at hfold ⊢
              rw [hfold]
              exact run_initializedPowerClock_exact []
                (ULogBootstrapExecution.payloadFoldedLeft [b] base) tail
          | cons p ps =>
              rw [show payloadFoldCaseFuel [b] (p :: ps) +
                    ((p :: ps).length + 2) = 12 + ((p :: ps).length + 2) by rfl,
                ULogBootstrapExecution.run_add]
              have hfold := run_payloadFold_singleton_padded_exact b p ps base
                (MStarConcreteAlphabet.work :: tail)
              simp [ULogBootstrapExecution.atBits,
                ULogBootstrapExecution.payloadLengthMarkedLeft,
                ULogBytecode.encodeNatField, ULogProgram.codeTape,
                List.append_assoc] at hfold ⊢
              rw [hfold]
              exact run_initializedPowerClock_exact (p :: ps)
                (ULogBootstrapExecution.payloadFoldedLeft [b] base) tail
      | cons c cs =>
          cases padding with
          | nil =>
              rw [show payloadFoldCaseFuel (b :: c :: cs) [] +
                    ([].length + 2) =
                  (5 + payloadFoldFuel cs [false] 1 + 1) + 2 by rfl,
                ULogBootstrapExecution.run_add]
              have hfold := run_payloadFold_nonempty_unpadded_exact b c cs base
                (MStarConcreteAlphabet.work :: tail)
              simp [ULogBootstrapExecution.atBits,
                ULogBootstrapExecution.payloadLengthMarkedLeft,
                ULogBytecode.encodeNatField, ULogProgram.codeTape,
                List.replicate_succ, List.append_assoc] at hfold ⊢
              simp only [payloadFoldFuel, List.length_cons,
                List.length_nil] at hfold ⊢
              rw [hfold]
              exact run_initializedPowerClock_exact []
                (ULogBootstrapExecution.payloadFoldedLeft (b :: c :: cs) base) tail
          | cons p ps =>
              rw [show payloadFoldCaseFuel (b :: c :: cs) (p :: ps) +
                    ((p :: ps).length + 2) =
                  (5 + payloadFoldFuel cs [false] 1 + (4 * cs.length + 11)) +
                    ((p :: ps).length + 2) by rfl,
                ULogBootstrapExecution.run_add]
              have hfold := run_payloadFold_nonempty_padded_exact b c p cs ps base
                (MStarConcreteAlphabet.work :: tail)
              simp [ULogBootstrapExecution.atBits,
                ULogBootstrapExecution.payloadLengthMarkedLeft,
                ULogBytecode.encodeNatField, ULogProgram.codeTape,
                List.replicate_succ, List.append_assoc] at hfold ⊢
              simp only [payloadFoldFuel, List.length_cons,
                List.length_nil] at hfold ⊢
              rw [hfold]
              exact run_initializedPowerClock_exact (p :: ps)
                (ULogBootstrapExecution.payloadFoldedLeft (b :: c :: cs) base) tail

theorem payloadFoldCaseFuel_le_square (input padding : List Bool) :
    payloadFoldCaseFuel input padding ≤
      4 * (input.length + padding.length + 4) ^ 2 := by
  cases input with
  | nil =>
      cases padding with
      | nil => norm_num [payloadFoldCaseFuel]
      | cons p ps =>
          simp only [payloadFoldCaseFuel, List.length_cons, List.length_nil,
            Nat.zero_add]
          have hbase : 1 ≤ ps.length + 1 + 4 := by omega
          have hsq : 1 ≤ (ps.length + 1 + 4) ^ 2 := by
            simpa using Nat.pow_le_pow_left hbase 2
          omega
  | cons b bs =>
      cases bs with
      | nil =>
          cases padding with
          | nil => norm_num [payloadFoldCaseFuel]
          | cons p ps =>
              simp only [payloadFoldCaseFuel, List.length_cons, List.length_nil,
                Nat.zero_add]
              have harg : 2 ≤ 1 + (ps.length + 1) + 4 := by omega
              have hsq : 4 ≤ (1 + (ps.length + 1) + 4) ^ 2 := by nlinarith
              omega
      | cons c cs =>
          have hfold := payloadFoldFuel_le_quadratic cs [false] 1
          cases padding with
          | nil =>
              simp only [payloadFoldCaseFuel, List.length_cons,
                List.length_nil, Nat.add_zero]
              simp only [List.length_cons, List.length_nil] at hfold
              let E := cs.length + 2 + 4
              change 5 + payloadFoldFuel cs [false] 1 + 1 ≤ 4 * E ^ 2
              have harg : 1 + cs.length + 1 + 2 ≤ E := by
                simp [E]
                omega
              have hfold' : payloadFoldFuel cs [false] 1 ≤ 2 * E ^ 2 :=
                hfold.trans (Nat.mul_le_mul_left 2
                  (Nat.pow_le_pow_left harg 2))
              have hE : 2 ≤ E := by simp [E]
              have hsq : 4 ≤ E ^ 2 := by
                simpa using Nat.pow_le_pow_left hE 2
              have hfour : 6 ≤ 2 * E ^ 2 := by omega
              omega
          | cons p ps =>
              simp only [payloadFoldCaseFuel, List.length_cons]
              simp only [List.length_cons, List.length_nil] at hfold
              let E := cs.length + 1 + 1 + (ps.length + 1) + 4
              change 5 + payloadFoldFuel cs [false] 1 +
                (4 * cs.length + 11) ≤ 4 * E ^ 2
              have harg : 1 + cs.length + 1 + 2 ≤ E := by
                simp [E]
                omega
              have hfold' : payloadFoldFuel cs [false] 1 ≤ 2 * E ^ 2 :=
                hfold.trans (Nat.mul_le_mul_left 2
                  (Nat.pow_le_pow_left harg 2))
              have hE : 2 ≤ E := by simp [E]
              have hlin : 4 * cs.length + 16 ≤ 4 * E := by
                simp [E]
                omega
              have htwice : 2 * E ≤ E ^ 2 := by
                simpa [pow_two, Nat.mul_assoc, Nat.mul_comm,
                  Nat.mul_left_comm] using Nat.mul_le_mul_right E hE
              have hfour : 4 * E ≤ 2 * E ^ 2 := by
                calc
                  4 * E = 2 * (2 * E) := by ring
                  _ ≤ 2 * E ^ 2 := Nat.mul_le_mul_left 2 htwice
              omega

theorem payloadClockFuel_le_square (input padding : List Bool) :
    payloadClockFuel input padding ≤
      6 * (input.length + padding.length + 4) ^ 2 := by
  have hfold := payloadFoldCaseFuel_le_square input padding
  have hE : 1 ≤ input.length + padding.length + 4 := by omega
  have hlinear : input.length + 1 + padding.length + 2 ≤
      2 * (input.length + padding.length + 4) ^ 2 := by nlinarith
  unfold payloadClockFuel
  omega

/-- Full exact payload-to-clock initialization in the principal branch:
at least two payload bits and nonempty padding.  The trailing work cell is
kept explicit because it is the physical separator used by clock framing. -/
theorem run_payloadClock_nonempty_padded_exact
    (b c p : Bool) (cs ps : List Bool)
    (base tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run
      ((b :: c :: cs).length + 1 +
        (5 + payloadFoldFuel cs [b] 1 + (4 * cs.length + 11)) +
          (p :: ps).length + 2)
      (ULogBootstrapExecution.atBits ULogControl.State.payloadLengthStart
        (ULogBytecode.encodePayload (b :: c :: cs) (p :: ps)) base
        (ULogAlphabet.ulogCore ULogAlphabet.codeEnd)
        (MStarConcreteAlphabet.work :: tail)) =
      ULogBootstrapExecution.initializedPowerClock (p :: ps)
        (ULogBootstrapExecution.payloadFoldedLeft (b :: c :: cs) base) tail := by
  have hdecode := run_payloadLengthStart_exact (b :: c :: cs) (p :: ps)
    base (ULogAlphabet.ulogCore ULogAlphabet.codeEnd)
    (MStarConcreteAlphabet.work :: tail)
  have hfold := run_payloadFold_nonempty_padded_exact b c p cs ps base
    (MStarConcreteAlphabet.work :: tail)
  have hclock := run_initializedPowerClock_exact (p :: ps)
    (ULogBootstrapExecution.payloadFoldedLeft (b :: c :: cs) base) tail
  rw [show
      (b :: c :: cs).length + 1 +
          (5 + payloadFoldFuel cs [b] 1 + (4 * cs.length + 11)) +
            (p :: ps).length + 2 =
      ((b :: c :: cs).length + 1) +
        ((5 + payloadFoldFuel cs [b] 1 + (4 * cs.length + 11)) +
          ((p :: ps).length + 2)) by omega]
  rw [ULogBootstrapExecution.run_add, hdecode,
    ULogBootstrapExecution.run_add]
  have hdecode' : ULogBootstrapExecution.atBits
      (.fieldReturn .payloadLength) (b :: c :: cs ++ p :: ps)
      (ULogBootstrapExecution.payloadLengthMarkedLeft (b :: c :: cs).length base)
      (ULogAlphabet.ulogCore ULogAlphabet.codeEnd)
      (MStarConcreteAlphabet.work :: tail) =
      (.running (ULogControl.State.fieldReturn .payloadLength)
        ⟨ULogAlphabet.ulogCore ULogAlphabet.codeOne ::
            ULogAlphabet.ulogCore ULogAlphabet.codeZero ::
              List.replicate cs.length
                (ULogAlphabet.ulogCore ULogAlphabet.codeZero) ++
                ULogAlphabet.ulogCore ULogAlphabet.payloadStartZero :: base,
          ULogProgram.codeTape b,
          ULogProgram.codeTape c :: cs.map ULogProgram.codeTape ++
            ULogProgram.codeTape p :: ps.map ULogProgram.codeTape ++
              ULogAlphabet.ulogCore ULogAlphabet.codeEnd ::
                MStarConcreteAlphabet.work :: tail⟩) := by
    simp [ULogBootstrapExecution.atBits,
      ULogBootstrapExecution.payloadLengthMarkedLeft,
      ULogBytecode.encodeNatField, ULogProgram.codeTape,
      List.replicate_succ, List.append_assoc]
  rw [hdecode']
  rw [show ULogBootstrapExecution.run
      (5 + payloadFoldFuel cs [b] 1 + (4 * cs.length + 11))
      _ = _ from hfold]
  simpa [ULogBootstrapExecution.beforeClockPadding,
    ULogBootstrapExecution.payloadLengthMarkedLeft,
    ULogBytecode.encodeNatField, List.replicate_succ,
    List.append_assoc] using hclock

/-- Full exact runtime initialization for the principal nonempty-program,
multi-bit-input, nonempty-padding branch. -/
theorem run_runtime_nonemptyProgram_main_exact
    (rules : List ULogBytecode.RuleCode) (hrules : rules ≠ [])
    (b c p : Bool) (cs ps : List Bool)
    (left tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run
      (programPayloadFuel rules +
        ((b :: c :: cs).length + 1 +
          (5 + payloadFoldFuel cs [b] 1 + (4 * cs.length + 11)) +
            (p :: ps).length + 2))
      (.running ULogControl.State.framePayloadLength
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          (ULogBytecode.encodeProgram rules ++
            ULogBytecode.encodePayload (b :: c :: cs) (p :: ps)).map
              ULogProgram.codeTape ++
            ULogAlphabet.ulogCore ULogAlphabet.codeEnd ::
              MStarConcreteAlphabet.work :: tail⟩) =
      ULogBootstrapExecution.initializedPowerClock (p :: ps)
        (ULogBootstrapExecution.payloadFoldedLeft (b :: c :: cs)
          (ULogBootstrapExecution.programMarkedLeft rules left)) tail := by
  rw [ULogBootstrapExecution.run_add,
    run_programPayload_to_payloadStart_exact rules hrules
      (b :: c :: cs) (p :: ps) left tail]
  exact run_payloadClock_nonempty_padded_exact b c p cs ps
    (ULogBootstrapExecution.programMarkedLeft rules left) tail

/-- Named exact ledger for the principal nonempty-program, at-least-two-bit
payload, nonempty-padding initialization branch.  Its value is independent
of the bit values and depends only on the three literal lengths. -/
def runtimeMainFuel (rules : List ULogBytecode.RuleCode)
    (payloadTail paddingTail : List Bool) : ℕ :=
  programPayloadFuel rules +
    ((payloadTail.length + 2) + 1 +
      (5 + payloadFoldFuel payloadTail [false] 1 +
        (4 * payloadTail.length + 11)) +
      (paddingTail.length + 1) + 2)

theorem run_runtime_nonemptyProgram_mainFuel_exact
    (rules : List ULogBytecode.RuleCode) (hrules : rules ≠ [])
    (b c p : Bool) (cs ps : List Bool)
    (left tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (runtimeMainFuel rules cs ps)
      (.running ULogControl.State.framePayloadLength
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          (ULogBytecode.encodeProgram rules ++
            ULogBytecode.encodePayload (b :: c :: cs) (p :: ps)).map
              ULogProgram.codeTape ++
            ULogAlphabet.ulogCore ULogAlphabet.codeEnd ::
              MStarConcreteAlphabet.work :: tail⟩) =
      ULogBootstrapExecution.initializedPowerClock (p :: ps)
        (ULogBootstrapExecution.payloadFoldedLeft (b :: c :: cs)
          (ULogBootstrapExecution.programMarkedLeft rules left)) tail := by
  simpa [runtimeMainFuel, payloadFoldFuel] using
    (run_runtime_nonemptyProgram_main_exact rules hrules b c p cs ps left tail)

/-- The complete principal runtime-initialization ledger is cubic in a
single literal-size envelope.  The exact formula is only quadratic after
the program pass; `32` is chosen to make later radius absorption mechanical. -/
theorem runtimeMainFuel_le_cube
    (rules : List ULogBytecode.RuleCode)
    (payloadTail paddingTail : List Bool) :
    runtimeMainFuel rules payloadTail paddingTail ≤
      32 * ((ULogBytecode.encodeProgram rules).length +
        payloadTail.length + paddingTail.length + 4) ^ 3 := by
  let E := (ULogBytecode.encodeProgram rules).length +
    payloadTail.length + paddingTail.length + 4
  have hE : 1 ≤ E := by
    simp only [E]
    omega
  have hprogram := programPayloadFuel_le_cube rules
  have hprogramMono :
      ((ULogBytecode.encodeProgram rules).length + 1) ^ 3 ≤ E ^ 3 := by
    apply Nat.pow_le_pow_left
    simp only [E]
    omega
  have hfold := payloadFoldFuel_le_quadratic payloadTail [false] 1
  have htail : payloadTail.length + 4 ≤ E := by
    simp only [E]
    omega
  have htail' : 1 + payloadTail.length + 1 + 2 ≤ E := by omega
  have hfold' : payloadFoldFuel payloadTail [false] 1 ≤ 2 * E ^ 2 := by
    exact hfold.trans (Nat.mul_le_mul_left 2
      (Nat.pow_le_pow_left htail' 2))
  have hlinear : 5 * payloadTail.length + paddingTail.length + 22 ≤ 7 * E := by
    simp only [E]
    omega
  have hE2 : E ^ 2 ≤ E ^ 3 :=
    Nat.pow_le_pow_right hE (by decide : 2 ≤ 3)
  unfold runtimeMainFuel
  have hprogram' : programPayloadFuel rules ≤ 22 * E ^ 3 :=
    hprogram.trans (Nat.mul_le_mul_left 22 hprogramMono)
  calc
    programPayloadFuel rules +
        ((payloadTail.length + 2) + 1 +
          (5 + payloadFoldFuel payloadTail [false] 1 +
            (4 * payloadTail.length + 11)) +
          (paddingTail.length + 1) + 2) ≤
      22 * E ^ 3 + (2 * E ^ 2 + 7 * E) := by omega
    _ ≤ 22 * E ^ 3 + 9 * E ^ 3 := by
      have hE1 : E ≤ E ^ 3 := by
        exact (Nat.le_trans (show E ≤ E ^ 2 from
          (by simpa using Nat.pow_le_pow_right hE (by decide : 1 ≤ 2))) hE2)
      omega
    _ ≤ 32 * E ^ 3 := by omega

/-- Exact fuel hidden by the older reachability-only right-shift lemma. -/
theorem run_initShiftRuntimeRight_exact
    (carry : ULogProgram.Tape) (pre : List ULogProgram.Tape)
    (last : ULogProgram.Tape)
    (hsafe : ULogBootstrapExecution.ShiftRuntimeSafe (pre ++ [last]))
    (left : List ULogProgram.Tape) (head : ULogProgram.Tape)
    (right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (pre.length + 2)
      (.running (.shiftRuntime (.initRight carry))
        (ULogBootstrapExecution.beforeRightPath (pre ++ [last]) (head :: left)
          MStarConcreteAlphabet.work right)) =
      .running ULogControl.State.seekSimHead
        (ULogBootstrapExecution.beforeLeftPath (pre.reverse ++ [carry]) left head
          (last :: right)) := by
  induction pre generalizing carry left head with
  | nil =>
      simp only [List.nil_append, List.reverse_nil]
      have hlast : last ≠ MStarConcreteAlphabet.work := hsafe last (by simp)
      rw [show [].length + 2 = 1 + 1 by rfl,
        ULogBootstrapExecution.run_add]
      simp only [ULogBootstrapExecution.run]
      rw [show ULogBootstrapExecution.oneStep
          (.running (.shiftRuntime (.initRight carry))
            (ULogBootstrapExecution.beforeRightPath ([last]) (head :: left)
              MStarConcreteAlphabet.work right)) =
          .running (.shiftRuntime (.initRight last))
            ⟨carry :: head :: left, MStarConcreteAlphabet.work, right⟩ by
        simpa [ULogBootstrapExecution.beforeRightPath] using
          (ULogBootstrapExecution.initShiftRight_step carry last hlast
            (head :: left) MStarConcreteAlphabet.work right)]
      simpa [ULogBootstrapExecution.run,
        ULogBootstrapExecution.beforeLeftPath] using
        (ULogBootstrapExecution.initShiftRight_end last
          (head :: left) carry right)
  | cons x xs ih =>
      have hx : x ≠ MStarConcreteAlphabet.work := hsafe x (by simp)
      have hxs : ULogBootstrapExecution.ShiftRuntimeSafe (xs ++ [last]) := by
        intro y hy
        exact hsafe y (by simp [hy])
      have hfirst : ULogBootstrapExecution.run 1
          (.running (.shiftRuntime (.initRight carry))
            (ULogBootstrapExecution.beforeRightPath ((x :: xs) ++ [last])
              (head :: left) MStarConcreteAlphabet.work right)) =
          .running (.shiftRuntime (.initRight x))
            (ULogBootstrapExecution.beforeRightPath (xs ++ [last])
              (carry :: head :: left) MStarConcreteAlphabet.work right) := by
        simp only [ULogBootstrapExecution.run]
        cases xs with
        | nil =>
            simpa [ULogBootstrapExecution.beforeRightPath] using
              (ULogBootstrapExecution.initShiftRight_step carry x hx
                (head :: left) last (MStarConcreteAlphabet.work :: right))
        | cons z zs =>
            simpa [ULogBootstrapExecution.beforeRightPath,
              List.append_assoc] using
              (ULogBootstrapExecution.initShiftRight_step carry x hx
                (head :: left) z
                (zs ++ last :: MStarConcreteAlphabet.work :: right))
      rw [show (x :: xs).length + 2 = 1 + (xs.length + 2) by
            simp only [List.length_cons]; omega,
        ULogBootstrapExecution.run_add, hfirst]
      have hrest := ih x hxs (head :: left) carry
      rw [List.reverse_cons]
      rw [ULogBootstrapExecution.beforeLeftPath_append_singleton
        (xs.reverse ++ [x]) carry (by simp)]
      exact hrest

theorem run_seekSimHead_return_exact
    (path : List ULogProgram.Tape)
    (hsafe : ULogBootstrapExecution.InitSeekReturnSafe path)
    (left : List ULogProgram.Tape) (head : ULogProgram.Tape)
    (hhead : ULogProgram.choiceHead head = true)
    (right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (path.length + 1)
      (.running ULogControl.State.seekSimHead
        (ULogBootstrapExecution.beforeLeftPath path left head right)) =
      .running ULogControl.State.cycleStart
        (ULogBootstrapExecution.afterLeftPath path left head right) := by
  rw [ULogBootstrapExecution.run_add,
    ULogBootstrapExecution.run_left_path_of ULogControl.State.seekSimHead path
      (by
        intro x hx l y r
        exact ULogBootstrapExecution.seekSimHead_init_pass x
          (hsafe x hx) l y r)
      left head right]
  simp only [ULogBootstrapExecution.run]
  simpa [ULogBootstrapExecution.afterLeftPath] using
    (ULogBootstrapExecution.seekSimHead_existing_head head hhead left
      (path.reverse ++ right))

theorem run_initShiftRuntimeRight_cycle_exact
    (carry : ULogProgram.Tape) (pre : List ULogProgram.Tape)
    (last : ULogProgram.Tape)
    (hshift : ULogBootstrapExecution.ShiftRuntimeSafe (pre ++ [last]))
    (hreturn : ULogBootstrapExecution.InitSeekReturnSafe
      (pre.reverse ++ [carry]))
    (left : List ULogProgram.Tape) (head : ULogProgram.Tape)
    (hhead : ULogProgram.choiceHead head = true)
    (right : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (2 * pre.length + 4)
      (.running (.shiftRuntime (.initRight carry))
        (ULogBootstrapExecution.beforeRightPath (pre ++ [last]) (head :: left)
          MStarConcreteAlphabet.work right)) =
      .running ULogControl.State.cycleStart
        ⟨left, head, carry :: pre ++ last :: right⟩ := by
  rw [show 2 * pre.length + 4 = (pre.length + 2) + (pre.length + 2) by omega,
    ULogBootstrapExecution.run_add,
    run_initShiftRuntimeRight_exact carry pre last hshift left head right]
  have hret := run_seekSimHead_return_exact (pre.reverse ++ [carry]) hreturn
    left head hhead (last :: right)
  simpa [ULogBootstrapExecution.afterLeftPath, List.reverse_append,
    List.append_assoc] using hret

/-- After power-clock initialization, a nonempty payload needs exactly one
six-step state-frame write, one scan over the materialized clock/payload
prefix, and the two fixed head actions.  This closes the final deterministic
suffix which was existential in `reaches_initializedRuntime`. -/
theorem run_initializedRuntime_nonempty_exact
    (b : Bool) (bs padding : List Bool)
    (base tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run ((b :: bs).length + padding.length + 13)
      (ULogBootstrapExecution.initializedPowerClock padding
        (ULogBootstrapExecution.payloadFoldedLeft (b :: bs) base)
        (ULogBootstrapExecution.initializationWorkspace (b :: bs) tail)) =
      ULogBootstrapExecution.initializedRuntime padding (b :: bs) base tail := by
  let seekPath := ULogBootstrapExecution.headSeekPath padding (b :: bs)
  let payloadBase :=
    List.replicate bs.length
      (ULogAlphabet.ulogCore ULogAlphabet.payloadDone) ++
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
      ULogBootstrapExecution.beforeLeftPath,
      seekPath, payloadBase,
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
          (ULogAlphabet.ulogCore ULogAlphabet.stateSep :: tail)) := by
    exact ULogBootstrapExecution.run_left_path_of
      ULogControl.State.seekSimHead seekPath
      (ULogBootstrapExecution.headSeekPath_pass padding (b :: bs))
      payloadBase (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd)
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
          seekPath.reverse ++
            ULogAlphabet.ulogCore ULogAlphabet.stateSep :: tail⟩ by rfl]
    rw [show seekPath = ULogBootstrapExecution.headSeekPath padding (b :: bs) by rfl,
      ULogBootstrapExecution.headSeekPath_reverse_append]
    simpa [ULogBootstrapExecution.runtimeSuffix, List.append_assoc] using
      (ULogBootstrapExecution.seekSimHead_payloadEnd_step payloadBase
        (ULogProgram.payloadTape b)
        (bs.map ULogProgram.payloadTape ++
          ULogBootstrapExecution.runtimeSuffix padding tail))
  have hmark : ULogBootstrapExecution.run 1
      (.running ULogControl.State.readHead
        ⟨ULogAlphabet.ulogCore ULogAlphabet.payloadEnd :: payloadBase,
          ULogProgram.payloadTape b,
          bs.map ULogProgram.payloadTape ++
            ULogBootstrapExecution.runtimeSuffix padding tail⟩) =
      ULogBootstrapExecution.initializedRuntime padding (b :: bs) base tail := by
    simp only [ULogBootstrapExecution.run]
    simpa [ULogBootstrapExecution.initializedRuntime, payloadBase] using
      (ULogBootstrapExecution.readHead_step b
        (ULogAlphabet.ulogCore ULogAlphabet.payloadEnd :: payloadBase)
        (bs.map ULogProgram.payloadTape ++
          ULogBootstrapExecution.runtimeSuffix padding tail))
  rw [show (b :: bs).length + padding.length + 13 =
      6 + (seekPath.length + (1 + 1)) by
        simp [seekPath, ULogBootstrapExecution.headSeekPath]; omega]
  rw [ULogBootstrapExecution.run_add, hframe,
    ULogBootstrapExecution.run_add, hscan,
    ULogBootstrapExecution.run_add, htoHead]
  exact hmark

/-- Empty payloads require the special one-cell right shift used to install
the blank simulated head.  Its exact cost is still linear in the padding. -/
theorem run_initializedRuntime_empty_exact
    (padding : List Bool) (base tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (3 * padding.length + 25)
      (ULogBootstrapExecution.initializedPowerClock padding
        (ULogBootstrapExecution.payloadFoldedLeft [] base)
        (ULogBootstrapExecution.initializationWorkspace [] tail)) =
      ULogBootstrapExecution.initializedRuntime padding [] base tail := by
  let seekPath := ULogBootstrapExecution.headSeekPath padding []
  let shiftPre := ULogBootstrapExecution.emptyInitShiftPrefix padding
  let boundary := ULogBootstrapExecution.emptyInitBoundary padding
  have hprelen : shiftPre.length = padding.length + 4 := by
    cases padding <;>
      simp [shiftPre, ULogBootstrapExecution.emptyInitShiftPrefix]
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
            MStarConcreteAlphabet.work :: tail)) := by
    exact ULogBootstrapExecution.run_left_path_of
      ULogControl.State.seekSimHead seekPath
      (ULogBootstrapExecution.headSeekPath_pass padding []) base
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
              boundary :: shiftPre ++
                ULogAlphabet.ulogCore ULogAlphabet.stateSep ::
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
        simpa [ULogBootstrapExecution.beforeRightPath, hp,
          List.append_assoc] using
          (ULogBootstrapExecution.readHead_empty_boundary boundary
            (ULogBootstrapExecution.emptyInit_boundary padding) base y
            (ys ++ ULogAlphabet.ulogCore ULogAlphabet.stateSep ::
              MStarConcreteAlphabet.work :: tail))
  have hshift := run_initShiftRuntimeRight_cycle_exact boundary shiftPre
    (ULogAlphabet.ulogCore ULogAlphabet.stateSep)
    (by simpa [shiftPre, boundary] using
      ULogBootstrapExecution.emptyInit_shift_safe padding)
    (by simpa [shiftPre, boundary] using
      ULogBootstrapExecution.emptyInit_return_safe padding)
    (ULogAlphabet.ulogCore ULogAlphabet.payloadStartOne :: base)
    (ULogAlphabet.ulogCore ULogAlphabet.payloadHeadBlank)
    (by simp [ULogProgram.choiceHead]) tail
  rw [show 3 * padding.length + 25 =
      6 + (seekPath.length + (2 + (2 * shiftPre.length + 4))) by
        simp [seekPath, ULogBootstrapExecution.headSeekPath, hprelen]; omega,
    ULogBootstrapExecution.run_add, hframe,
    ULogBootstrapExecution.run_add, hscan,
    ULogBootstrapExecution.run_add, hread,
    hshift]
  simp [ULogBootstrapExecution.initializedRuntime,
    ULogBootstrapExecution.runtimeSuffix_emptyInit_after,
    shiftPre, boundary, List.append_assoc]

def initializedRuntimeFuel (input padding : List Bool) : ℕ :=
  match input with
  | [] => 3 * padding.length + 25
  | _ :: _ => input.length + padding.length + 13

theorem run_initializedRuntime_all_exact
    (input padding : List Bool) (base tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (initializedRuntimeFuel input padding)
      (ULogBootstrapExecution.initializedPowerClock padding
        (ULogBootstrapExecution.payloadFoldedLeft input base)
        (ULogBootstrapExecution.initializationWorkspace input tail)) =
      ULogBootstrapExecution.initializedRuntime padding input base tail := by
  cases input with
  | nil => exact run_initializedRuntime_empty_exact padding base tail
  | cons b bs => exact run_initializedRuntime_nonempty_exact b bs padding base tail

theorem initializedRuntimeFuel_le_linear (input padding : List Bool) :
    initializedRuntimeFuel input padding ≤
      4 * (input.length + padding.length + 7) := by
  cases input <;> simp [initializedRuntimeFuel] <;> omega

/-- Guard-free exact runtime initialization ledger. -/
def runtimeAllFuel (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) : ℕ :=
  programPayloadFuel rules + payloadClockFuel input padding +
    initializedRuntimeFuel input padding

theorem run_runtime_all_exact
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool)
    (left tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (runtimeAllFuel rules input padding)
      (.running ULogControl.State.framePayloadLength
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          (ULogBytecode.encodeProgram rules ++
            ULogBytecode.encodePayload input padding).map
              ULogProgram.codeTape ++
            ULogAlphabet.ulogCore ULogAlphabet.codeEnd ::
              ULogBootstrapExecution.payloadRuntimeWorkspace input tail⟩) =
      ULogBootstrapExecution.initializedRuntime padding input
        (ULogBootstrapExecution.programMarkedLeft rules left) tail := by
  unfold runtimeAllFuel
  rw [show programPayloadFuel rules + payloadClockFuel input padding +
        initializedRuntimeFuel input padding =
      programPayloadFuel rules +
        (payloadClockFuel input padding + initializedRuntimeFuel input padding) by
          omega,
    ULogBootstrapExecution.run_add]
  simp only [ULogBootstrapExecution.payloadRuntimeWorkspace]
  rw [
    run_programPayload_to_payloadStart_all_exact rules input padding left
      (ULogBootstrapExecution.initializationWorkspace input tail),
    ULogBootstrapExecution.run_add,
    run_payloadClock_all_exact input padding
      (ULogBootstrapExecution.programMarkedLeft rules left)
      (ULogBootstrapExecution.initializationWorkspace input tail),
    run_initializedRuntime_all_exact input padding
      (ULogBootstrapExecution.programMarkedLeft rules left) tail]

theorem runtimeAllFuel_le_cube
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool) :
    runtimeAllFuel rules input padding ≤
      32 * ((ULogBytecode.encodeProgram rules).length + input.length +
        padding.length + 7) ^ 3 := by
  let E := (ULogBytecode.encodeProgram rules).length + input.length +
    padding.length + 7
  have hE : 1 ≤ E := by simp [E]
  have hprogram := programPayloadFuel_le_cube rules
  have hpayload := payloadClockFuel_le_square input padding
  have hinit := initializedRuntimeFuel_le_linear input padding
  have hp : (ULogBytecode.encodeProgram rules).length + 1 ≤ E := by
    simp only [E]
    omega
  have hi : input.length + padding.length + 4 ≤ E := by
    simp only [E]
    omega
  have hi7 : input.length + padding.length + 7 ≤ E := by
    simp only [E]
    omega
  have hprogram' : programPayloadFuel rules ≤ 22 * E ^ 3 :=
    hprogram.trans (Nat.mul_le_mul_left 22 (Nat.pow_le_pow_left hp 3))
  have hpayload' : payloadClockFuel input padding ≤ 6 * E ^ 2 :=
    hpayload.trans (Nat.mul_le_mul_left 6 (Nat.pow_le_pow_left hi 2))
  have hinit' : initializedRuntimeFuel input padding ≤ 4 * E :=
    hinit.trans (Nat.mul_le_mul_left 4 hi7)
  have hE2 : E ^ 2 ≤ E ^ 3 :=
    Nat.pow_le_pow_right hE (by decide : 2 ≤ 3)
  have hE1 : E ≤ E ^ 3 := by
    simpa using Nat.pow_le_pow_right hE (by decide : 1 ≤ 3)
  unfold runtimeAllFuel
  change programPayloadFuel rules + payloadClockFuel input padding +
      initializedRuntimeFuel input padding ≤ 32 * E ^ 3
  calc
    programPayloadFuel rules + payloadClockFuel input padding +
        initializedRuntimeFuel input padding ≤
      22 * E ^ 3 + 6 * E ^ 2 + 4 * E := by omega
    _ ≤ 22 * E ^ 3 + 6 * E ^ 3 + 4 * E ^ 3 := by omega
    _ = 32 * E ^ 3 := by ring

/-- Exact total of the principal payload/clock/runtime branch, including
the final state-frame/head-seek suffix. -/
def runtimeMainTotalFuel (rules : List ULogBytecode.RuleCode)
    (payloadTail paddingTail : List Bool) : ℕ :=
  runtimeMainFuel rules payloadTail paddingTail +
    (payloadTail.length + 2) + (paddingTail.length + 1) + 13

theorem runtimeMainTotalFuel_le_cube
    (rules : List ULogBytecode.RuleCode)
    (payloadTail paddingTail : List Bool) :
    runtimeMainTotalFuel rules payloadTail paddingTail ≤
      36 * ((ULogBytecode.encodeProgram rules).length +
        payloadTail.length + paddingTail.length + 4) ^ 3 := by
  let E := (ULogBytecode.encodeProgram rules).length +
    payloadTail.length + paddingTail.length + 4
  have hE : 1 ≤ E := by simp [E]
  have hmain := runtimeMainFuel_le_cube rules payloadTail paddingTail
  have hsuffix : payloadTail.length + 2 + (paddingTail.length + 1) + 13 ≤
      4 * E := by
    simp only [E]
    omega
  have hlin : 4 * E ≤ 4 * E ^ 3 := by
    exact Nat.mul_le_mul_left 4
      (by simpa using Nat.pow_le_pow_right hE (by decide : 1 ≤ 3))
  unfold runtimeMainTotalFuel
  change runtimeMainFuel rules payloadTail paddingTail +
      (payloadTail.length + 2) + (paddingTail.length + 1) + 13 ≤ 36 * E ^ 3
  have hmain' : runtimeMainFuel rules payloadTail paddingTail ≤ 32 * E ^ 3 := by
    simpa [E] using hmain
  omega

theorem run_runtime_nonemptyProgram_total_exact
    (rules : List ULogBytecode.RuleCode) (hrules : rules ≠ [])
    (b c p : Bool) (cs ps : List Bool)
    (left tail : List ULogProgram.Tape) :
    ULogBootstrapExecution.run (runtimeMainTotalFuel rules cs ps)
      (.running ULogControl.State.framePayloadLength
        ⟨left, ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          (ULogBytecode.encodeProgram rules ++
            ULogBytecode.encodePayload (b :: c :: cs) (p :: ps)).map
              ULogProgram.codeTape ++
            ULogAlphabet.ulogCore ULogAlphabet.codeEnd ::
              ULogBootstrapExecution.payloadRuntimeWorkspace (b :: c :: cs)
                tail⟩) =
      ULogBootstrapExecution.initializedRuntime (p :: ps) (b :: c :: cs)
        (ULogBootstrapExecution.programMarkedLeft rules left) tail := by
  unfold runtimeMainTotalFuel
  rw [show runtimeMainFuel rules cs ps + (cs.length + 2) +
        (ps.length + 1) + 13 =
      runtimeMainFuel rules cs ps +
        ((b :: c :: cs).length + (p :: ps).length + 13) by simp; omega]
  rw [ULogBootstrapExecution.run_add]
  have hmain := run_runtime_nonemptyProgram_mainFuel_exact
    rules hrules b c p cs ps left
      (ULogBootstrapExecution.initializationWorkspace (b :: c :: cs) tail)
  simp only [ULogBootstrapExecution.payloadRuntimeWorkspace,
    ULogBootstrapExecution.initializationWorkspace] at hmain ⊢
  rw [hmain]
  exact run_initializedRuntime_nonempty_exact b (c :: cs) (p :: ps)
    (ULogBootstrapExecution.programMarkedLeft rules left) tail

/-- Every literal copied word fits in the exponential work radius created
by the parser/copier.  This fact is independent of bytecode well-formedness. -/
theorem word_length_le_copiedCoreRadius (x : ConcretePakSide.Word) :
    x.length ≤ PakOuterULogBridge.copiedCoreRadius x := by
  have hsmall : x.length ≤ 2 ^ x.length :=
    (x.length.lt_pow_self (by decide : 1 < 2)).le
  have hmono : 2 ^ x.length ≤ 2 ^ (8 * (x.length + 1)) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  exact hsmall.trans (by
    simpa [PakOuterULogBridge.copiedCoreRadius,
      MStarParserCopySpec.timeExponent] using hmono)

/-- In the principal universal-instance branch the one scalar runtime
envelope is already bounded by the literal copied word, hence by the copied
radius.  This is the structural envelope needed by the polynomial estimate. -/
theorem runtimeMain_envelope_le_word
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (b c p : Bool) (cs ps : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload (b :: c :: cs) (p :: ps)) :
    (ULogBytecode.encodeProgram rules).length + cs.length + ps.length + 4 ≤
      x.length := by
  subst x
  simp [ULogBytecode.length_encodePayload]
  omega

theorem runtimeMainTotalFuel_le_radius_cube
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (b c p : Bool) (cs ps : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload (b :: c :: cs) (p :: ps)) :
    runtimeMainTotalFuel rules cs ps ≤
      36 * (PakOuterULogBridge.copiedCoreRadius x) ^ 3 := by
  have hmain := runtimeMainTotalFuel_le_cube rules cs ps
  have hwordLen := runtimeMain_envelope_le_word x rules b c p cs ps hword
  have hx := word_length_le_copiedCoreRadius x
  have hpow :
      ((ULogBytecode.encodeProgram rules).length + cs.length + ps.length + 4) ^ 3 ≤
        (PakOuterULogBridge.copiedCoreRadius x) ^ 3 :=
    Nat.pow_le_pow_left (hwordLen.trans hx) 3
  exact hmain.trans (Nat.mul_le_mul_left 36 hpow)

/-- Closed total bootstrap fuel for the principal universal input branch. -/
def bootstrapMainFuel (x : ConcretePakSide.Word)
    (rules : List ULogBytecode.RuleCode)
    (payloadTail paddingTail : List Bool) : ℕ :=
  PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 5 +
    runtimeMainTotalFuel rules payloadTail paddingTail

theorem run_bootstrapMainFuel_exact
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (hrules : rules ≠ []) (b c p : Bool) (cs ps : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload (b :: c :: cs) (p :: ps)) :
    ULogBootstrapExecution.run (bootstrapMainFuel x rules cs ps)
      (.running ULogControl.qStart (copiedULogStartZipper x)) =
      .running ULogControl.State.cycleStart
        (copiedSemanticStartZipper x rules (b :: c :: cs) (p :: ps)) := by
  have hne : x ≠ [] := by
    intro hx
    have henc := ULogBootstrapExecution.encodedUniversalInput_ne_nil
      rules (b :: c :: cs) (p :: ps)
    apply henc
    rw [← hword, hx]
  cases hx : x with
  | nil => exact (hne hx).elim
  | cons wb wbits =>
      rw [← hx]
      have hstart := PakOuterULogBridge.copiedULogStartZipper_eq_bootstrap x rules
        (b :: c :: cs) (p :: ps) hword
      have hpreamble := run_bootstrap_workspace_exact
        (PakOuterULogBridge.copiedCoreRadius x) wb wbits []
        (ULogBootstrapExecution.payloadRuntimeWorkspace (b :: c :: cs)
          (PakOuterULogBridge.copiedBootstrapTail x (b :: c :: cs)))
      have hruntime := run_runtime_nonemptyProgram_total_exact rules hrules
        b c p cs ps
        (List.replicate (PakOuterULogBridge.copiedCoreRadius x)
          MStarConcreteAlphabet.work)
        (PakOuterULogBridge.copiedBootstrapTail x (b :: c :: cs))
      have hend := copied_initializedRuntime_eq_semanticStart x rules
        (b :: c :: cs) (p :: ps)
      have heq : wb :: wbits = ULogBytecode.encodeProgram rules ++
          ULogBytecode.encodePayload (b :: c :: cs) (p :: ps) :=
        hx.symm.trans hword
      rw [← heq] at hstart hruntime
      unfold bootstrapMainFuel
      rw [show PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 5 +
            runtimeMainTotalFuel rules cs ps =
          (PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 5) +
            runtimeMainTotalFuel rules cs ps by omega]
      rw [hstart]
      rw [ULogBootstrapExecution.run_add]
      have hxlen : x.length = (wb :: wbits).length := by rw [hx]
      rw [hxlen]
      simp only [List.map_cons, List.cons_append,
        List.append_assoc] at hpreamble ⊢
      simp only [ULogControl.qStart]
      rw [hpreamble]
      simp only [List.append_nil, List.map_cons, List.cons_append,
        List.append_assoc] at hruntime ⊢
      rw [hruntime]
      exact hend

theorem bootstrapMainFuel_lt_radius_pow_nine
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (b c p : Bool) (cs ps : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload (b :: c :: cs) (p :: ps)) :
    bootstrapMainFuel x rules cs ps <
      (PakOuterULogBridge.copiedCoreRadius x) ^ 9 := by
  let R := PakOuterULogBridge.copiedCoreRadius x
  have hR : 256 ≤ R := PakOuterULogBridge.copiedCoreRadius_ge_256 x
  have hx : x.length ≤ R := word_length_le_copiedCoreRadius x
  have hrun : runtimeMainTotalFuel rules cs ps ≤ 36 * R ^ 3 := by
    simpa [R] using runtimeMainTotalFuel_le_radius_cube x rules b c p cs ps hword
  have hpreamble : R + 2 * x.length + 5 ≤ 4 * R := by omega
  have hlin : 4 * R ≤ R ^ 3 := by
    have hR2 : 4 ≤ R ^ 2 := by nlinarith
    calc
      4 * R ≤ R ^ 2 * R := Nat.mul_le_mul_right R hR2
      _ = R ^ 3 := by ring
  have htotal : bootstrapMainFuel x rules cs ps ≤ 37 * R ^ 3 := by
    unfold bootstrapMainFuel
    change R + 2 * x.length + 5 + runtimeMainTotalFuel rules cs ps ≤ _
    omega
  have hpow : 37 * R ^ 3 < R ^ 9 := by
    have hR3 : 256 ^ 3 ≤ R ^ 3 := Nat.pow_le_pow_left hR 3
    calc
      37 * R ^ 3 < R ^ 3 * R ^ 3 := by
        have : 37 < R ^ 3 := by nlinarith
        nlinarith [Nat.zero_le (R ^ 3)]
      _ ≤ R ^ 3 * R ^ 6 := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_right (by omega) (by decide : 3 ≤ 6)
      _ = R ^ 9 := by ring
  exact htotal.trans_lt hpow

theorem bootstrapFuel_lt_radius_pow_nine_main
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (hrules : rules ≠ []) (b c p : Bool) (cs ps : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload (b :: c :: cs) (p :: ps)) :
    bootstrapFuel x rules (b :: c :: cs) (p :: ps) hword <
      (PakOuterULogBridge.copiedCoreRadius x) ^ 9 := by
  have hleast := bootstrapFuel_le_of_run x rules (b :: c :: cs) (p :: ps)
    hword (bootstrapMainFuel x rules cs ps)
    (run_bootstrapMainFuel_exact x rules hrules b c p cs ps hword)
  exact hleast.trans_lt
    (bootstrapMainFuel_lt_radius_pow_nine x rules b c p cs ps hword)

/-- Literal outer-arrow form of the principal bootstrap bound.  The same
explicit finite-machine run is lifted one microstep per occupied outer arrow;
the final budget is the copier's advertised ninth-power radius. -/
theorem copiedULogStart_outer_reaches_semanticStart_radius_pow_nine_main
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (hrules : rules ≠ []) (b c p : Bool) (cs ps : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload (b :: c :: cs) (p :: ps))
    (origin : Int) (leftExtra rightExtra : List OuterTape) :
    OuterReachesAtMost (PakOuterULogBridge.copiedCoreRadius x ^ 9)
      (anchoredFramedULogConfig ULogControl.qStart origin leftExtra rightExtra
        (copiedULogStartZipper x))
      (anchoredFramedULogConfig ULogControl.State.cycleStart origin
        leftExtra rightExtra
        (copiedSemanticStartZipper x rules (b :: c :: cs) (p :: ps))) := by
  have hlift := ulogRun_running_outer_framed_atMost
    (bootstrapMainFuel x rules cs ps)
    ULogControl.qStart ULogControl.State.cycleStart origin leftExtra rightExtra
    (copiedULogStartZipper x)
    (copiedSemanticStartZipper x rules (b :: c :: cs) (p :: ps))
    (run_bootstrapMainFuel_exact x rules hrules b c p cs ps hword)
  rcases hlift with ⟨arrows, harrows, hrun⟩
  refine ⟨arrows, harrows.trans ?_, hrun⟩
  exact Nat.le_of_lt
    (bootstrapMainFuel_lt_radius_pow_nine x rules b c p cs ps hword)

/-- The guard-free runtime envelope is at most twice the copied radius. -/
theorem runtimeAll_envelope_le_two_radius
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    (ULogBytecode.encodeProgram rules).length + input.length +
        padding.length + 7 ≤
      2 * PakOuterULogBridge.copiedCoreRadius x := by
  have hx := word_length_le_copiedCoreRadius x
  have hR := PakOuterULogBridge.copiedCoreRadius_ge_256 x
  have hlen : x.length = (ULogBytecode.encodeProgram rules).length +
      2 * input.length + padding.length + 1 := by
    rw [hword]
    simp [ULogBytecode.length_encodePayload]
    omega
  omega

theorem runtimeAllFuel_le_radius_cube
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    runtimeAllFuel rules input padding ≤
      256 * PakOuterULogBridge.copiedCoreRadius x ^ 3 := by
  let R := PakOuterULogBridge.copiedCoreRadius x
  let E := (ULogBytecode.encodeProgram rules).length + input.length +
    padding.length + 7
  have hrun := runtimeAllFuel_le_cube rules input padding
  have hE : E ≤ 2 * R := by
    simpa [E, R] using runtimeAll_envelope_le_two_radius x rules input padding hword
  have hpow : E ^ 3 ≤ (2 * R) ^ 3 := Nat.pow_le_pow_left hE 3
  calc
    runtimeAllFuel rules input padding ≤ 32 * E ^ 3 := by simpa [E] using hrun
    _ ≤ 32 * (2 * R) ^ 3 := Nat.mul_le_mul_left 32 hpow
    _ = 256 * R ^ 3 := by ring

def bootstrapAllFuel (x : ConcretePakSide.Word)
    (rules : List ULogBytecode.RuleCode) (input padding : List Bool) : ℕ :=
  PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 5 +
    runtimeAllFuel rules input padding

theorem run_bootstrapAllFuel_exact
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    ULogBootstrapExecution.run (bootstrapAllFuel x rules input padding)
      (.running ULogControl.qStart (copiedULogStartZipper x)) =
      .running ULogControl.State.cycleStart
        (copiedSemanticStartZipper x rules input padding) := by
  have hne : x ≠ [] := by
    intro hx
    apply ULogBootstrapExecution.encodedUniversalInput_ne_nil rules input padding
    rw [← hword, hx]
  cases hx : x with
  | nil => exact (hne hx).elim
  | cons wb wbits =>
      rw [← hx]
      have hstart := PakOuterULogBridge.copiedULogStartZipper_eq_bootstrap x
        rules input padding hword
      have hpreamble := run_bootstrap_workspace_exact
        (PakOuterULogBridge.copiedCoreRadius x) wb wbits []
        (ULogBootstrapExecution.payloadRuntimeWorkspace input
          (PakOuterULogBridge.copiedBootstrapTail x input))
      have hruntime := run_runtime_all_exact rules input padding
        (List.replicate (PakOuterULogBridge.copiedCoreRadius x)
          MStarConcreteAlphabet.work)
        (PakOuterULogBridge.copiedBootstrapTail x input)
      have hend := copied_initializedRuntime_eq_semanticStart x rules input padding
      have heq : wb :: wbits = ULogBytecode.encodeProgram rules ++
          ULogBytecode.encodePayload input padding := hx.symm.trans hword
      rw [← heq] at hstart hruntime
      unfold bootstrapAllFuel
      rw [show PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 5 +
            runtimeAllFuel rules input padding =
          (PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 5) +
            runtimeAllFuel rules input padding by omega,
        hstart, ULogBootstrapExecution.run_add]
      have hxlen : x.length = (wb :: wbits).length := by rw [hx]
      rw [hxlen]
      simp only [List.map_cons, List.cons_append,
        List.append_assoc] at hpreamble ⊢
      simp only [ULogControl.qStart]
      rw [hpreamble]
      simp only [List.append_nil, List.map_cons, List.cons_append,
        List.append_assoc] at hruntime ⊢
      rw [hruntime]
      exact hend

theorem bootstrapAllFuel_lt_radius_pow_nine
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    bootstrapAllFuel x rules input padding <
      PakOuterULogBridge.copiedCoreRadius x ^ 9 := by
  let R := PakOuterULogBridge.copiedCoreRadius x
  have hR : 256 ≤ R := PakOuterULogBridge.copiedCoreRadius_ge_256 x
  have hx : x.length ≤ R := word_length_le_copiedCoreRadius x
  have hrun : runtimeAllFuel rules input padding ≤ 256 * R ^ 3 := by
    simpa [R] using runtimeAllFuel_le_radius_cube x rules input padding hword
  have hpreamble : R + 2 * x.length + 5 ≤ 4 * R := by omega
  have hlin : 4 * R ≤ R ^ 3 := by
    have hR2 : 4 ≤ R ^ 2 := by nlinarith
    calc
      4 * R ≤ R ^ 2 * R := Nat.mul_le_mul_right R hR2
      _ = R ^ 3 := by ring
  have htotal : bootstrapAllFuel x rules input padding ≤ 257 * R ^ 3 := by
    unfold bootstrapAllFuel
    change R + 2 * x.length + 5 + runtimeAllFuel rules input padding ≤ _
    omega
  have hpow : 257 * R ^ 3 < R ^ 9 := by
    have hR3 : 256 ^ 3 ≤ R ^ 3 := Nat.pow_le_pow_left hR 3
    calc
      257 * R ^ 3 < R ^ 3 * R ^ 3 := by
        have : 257 < R ^ 3 := by nlinarith
        nlinarith [Nat.zero_le (R ^ 3)]
      _ ≤ R ^ 3 * R ^ 6 := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_right (by omega) (by decide : 3 ≤ 6)
      _ = R ^ 9 := by ring
  exact htotal.trans_lt hpow

/-- Sharpened bootstrap bound used by the combined bootstrap/simulation
ledger.  The explicit cubic estimate leaves five powers of radius as slack. -/
theorem bootstrapAllFuel_lt_radius_pow_eight
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    bootstrapAllFuel x rules input padding <
      PakOuterULogBridge.copiedCoreRadius x ^ 8 := by
  let R := PakOuterULogBridge.copiedCoreRadius x
  have hR : 256 ≤ R := PakOuterULogBridge.copiedCoreRadius_ge_256 x
  have hx : x.length ≤ R := word_length_le_copiedCoreRadius x
  have hrun : runtimeAllFuel rules input padding ≤ 256 * R ^ 3 := by
    simpa [R] using runtimeAllFuel_le_radius_cube x rules input padding hword
  have htotal : bootstrapAllFuel x rules input padding ≤ 257 * R ^ 3 := by
    unfold bootstrapAllFuel
    change R + 2 * x.length + 5 + runtimeAllFuel rules input padding ≤ _
    have hpreamble : R + 2 * x.length + 5 ≤ R ^ 3 := by
      have hR2 : 4 ≤ R ^ 2 := by nlinarith
      have hlin : R + 2 * x.length + 5 ≤ 4 * R := by omega
      calc
        R + 2 * x.length + 5 ≤ 4 * R := hlin
        _ ≤ R ^ 2 * R := Nat.mul_le_mul_right R hR2
        _ = R ^ 3 := by ring
    omega
  have hR5 : 256 ^ 5 ≤ R ^ 5 := Nat.pow_le_pow_left hR 5
  have hcoef : 257 < R ^ 5 := by
    have : 257 < 256 ^ 5 := by norm_num
    exact this.trans_le hR5
  have hR3pos : 0 < R ^ 3 := pow_pos (by omega) _
  have hpow : 257 * R ^ 3 < R ^ 8 := by
    calc
      257 * R ^ 3 < R ^ 5 * R ^ 3 :=
        Nat.mul_lt_mul_of_pos_right hcoef hR3pos
      _ = R ^ 8 := by ring
  exact htotal.trans_lt hpow

theorem bootstrapFuel_lt_radius_pow_eight_all
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    bootstrapFuel x rules input padding hword <
      PakOuterULogBridge.copiedCoreRadius x ^ 8 := by
  exact (bootstrapFuel_le_of_run x rules input padding hword
    (bootstrapAllFuel x rules input padding)
    (run_bootstrapAllFuel_exact x rules input padding hword)).trans_lt
      (bootstrapAllFuel_lt_radius_pow_eight x rules input padding hword)

theorem bootstrapFuel_lt_radius_pow_nine_all
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    bootstrapFuel x rules input padding hword <
      PakOuterULogBridge.copiedCoreRadius x ^ 9 := by
  exact (bootstrapFuel_le_of_run x rules input padding hword
    (bootstrapAllFuel x rules input padding)
    (run_bootstrapAllFuel_exact x rules input padding hword)).trans_lt
      (bootstrapAllFuel_lt_radius_pow_nine x rules input padding hword)

theorem copiedULogStart_outer_reaches_semanticStart_radius_pow_nine_all
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (origin : Int) (leftExtra rightExtra : List OuterTape) :
    OuterReachesAtMost (PakOuterULogBridge.copiedCoreRadius x ^ 9)
      (anchoredFramedULogConfig ULogControl.qStart origin leftExtra rightExtra
        (copiedULogStartZipper x))
      (anchoredFramedULogConfig ULogControl.State.cycleStart origin
        leftExtra rightExtra
        (copiedSemanticStartZipper x rules input padding)) := by
  have hlift := ulogRun_running_outer_framed_atMost
    (bootstrapAllFuel x rules input padding)
    ULogControl.qStart ULogControl.State.cycleStart origin leftExtra rightExtra
    (copiedULogStartZipper x)
    (copiedSemanticStartZipper x rules input padding)
    (run_bootstrapAllFuel_exact x rules input padding hword)
  rcases hlift with ⟨arrows, harrows, hrun⟩
  refine ⟨arrows, harrows.trans ?_, hrun⟩
  exact Nat.le_of_lt
    (bootstrapAllFuel_lt_radius_pow_nine x rules input padding hword)

/-- Literal outer bootstrap history with the strengthened eighth-power
budget. -/
theorem copiedULogStart_outer_reaches_semanticStart_radius_pow_eight_all
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (origin : Int) (leftExtra rightExtra : List OuterTape) :
    OuterReachesAtMost (PakOuterULogBridge.copiedCoreRadius x ^ 8)
      (anchoredFramedULogConfig ULogControl.qStart origin leftExtra rightExtra
        (copiedULogStartZipper x))
      (anchoredFramedULogConfig ULogControl.State.cycleStart origin
        leftExtra rightExtra
        (copiedSemanticStartZipper x rules input padding)) := by
  have hlift := ulogRun_running_outer_framed_atMost
    (bootstrapAllFuel x rules input padding)
    ULogControl.qStart ULogControl.State.cycleStart origin leftExtra rightExtra
    (copiedULogStartZipper x)
    (copiedSemanticStartZipper x rules input padding)
    (run_bootstrapAllFuel_exact x rules input padding hword)
  rcases hlift with ⟨arrows, harrows, hrun⟩
  refine ⟨arrows, harrows.trans ?_, hrun⟩
  exact Nat.le_of_lt
    (bootstrapAllFuel_lt_radius_pow_eight x rules input padding hword)

/-- The only unquantified substage before clock framing is the concrete
program-count/payload-fold pass.  Keeping it separate makes its recursive
cost, rather than the whole bootstrap, the next proof target. -/
noncomputable def copiedPayloadFoldFuel
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) : ℕ :=
  Nat.find (ULogBootstrapExecution.reaches_payloadFolded rules input padding
    (List.replicate (PakOuterULogBridge.copiedCoreRadius x)
      MStarConcreteAlphabet.work)
    (MStarConcreteAlphabet.work ::
      PakOuterULogBridge.copiedBootstrapTail x input))

theorem run_copiedPayloadFoldFuel
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) :
    ULogBootstrapExecution.run (copiedPayloadFoldFuel x rules input padding)
      (.running ULogControl.State.framePayloadLength
        ⟨List.replicate (PakOuterULogBridge.copiedCoreRadius x)
            MStarConcreteAlphabet.work,
          ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          (ULogBytecode.encodeProgram rules ++
            ULogBytecode.encodePayload input padding).map ULogProgram.codeTape ++
            ULogAlphabet.ulogCore ULogAlphabet.codeEnd ::
              MStarConcreteAlphabet.work ::
                PakOuterULogBridge.copiedBootstrapTail x input⟩) =
      .running ULogControl.State.framePadding
        (match padding with
        | [] =>
            ⟨ULogBootstrapExecution.payloadFoldedLeft input
                (ULogBootstrapExecution.programMarkedLeft rules
                  (List.replicate (PakOuterULogBridge.copiedCoreRadius x)
                    MStarConcreteAlphabet.work)),
              ULogAlphabet.ulogCore ULogAlphabet.codeEnd,
              MStarConcreteAlphabet.work ::
                PakOuterULogBridge.copiedBootstrapTail x input⟩
        | b :: bs =>
            ⟨ULogBootstrapExecution.payloadFoldedLeft input
                (ULogBootstrapExecution.programMarkedLeft rules
                  (List.replicate (PakOuterULogBridge.copiedCoreRadius x)
                    MStarConcreteAlphabet.work)),
              ULogProgram.codeTape b,
              bs.map ULogProgram.codeTape ++
                ULogAlphabet.ulogCore ULogAlphabet.codeEnd ::
                  MStarConcreteAlphabet.work ::
                    PakOuterULogBridge.copiedBootstrapTail x input⟩) := by
  exact Nat.find_spec
    (ULogBootstrapExecution.reaches_payloadFolded rules input padding
      (List.replicate (PakOuterULogBridge.copiedCoreRadius x)
        MStarConcreteAlphabet.work)
      (MStarConcreteAlphabet.work ::
        PakOuterULogBridge.copiedBootstrapTail x input))

/-- Exact composed cost of payload folding followed by clock framing. -/
noncomputable def copiedPayloadClockDecompositionFuel
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) : ℕ :=
  copiedPayloadFoldFuel x rules input padding + padding.length + 2

theorem run_copiedPayloadClockDecompositionFuel
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) :
    ULogBootstrapExecution.run
      (copiedPayloadClockDecompositionFuel x rules input padding)
      (.running ULogControl.State.framePayloadLength
        ⟨List.replicate (PakOuterULogBridge.copiedCoreRadius x)
            MStarConcreteAlphabet.work,
          ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          (ULogBytecode.encodeProgram rules ++
            ULogBytecode.encodePayload input padding).map ULogProgram.codeTape ++
            ULogAlphabet.ulogCore ULogAlphabet.codeEnd ::
              MStarConcreteAlphabet.work ::
                PakOuterULogBridge.copiedBootstrapTail x input⟩) =
      ULogBootstrapExecution.initializedPowerClock padding
        (ULogBootstrapExecution.payloadFoldedLeft input
          (ULogBootstrapExecution.programMarkedLeft rules
            (List.replicate (PakOuterULogBridge.copiedCoreRadius x)
              MStarConcreteAlphabet.work)))
        (PakOuterULogBridge.copiedBootstrapTail x input) := by
  unfold copiedPayloadClockDecompositionFuel
  rw [show copiedPayloadFoldFuel x rules input padding + padding.length + 2 =
      copiedPayloadFoldFuel x rules input padding + (padding.length + 2) by
        omega]
  rw [ULogBootstrapExecution.run_add, run_copiedPayloadFoldFuel]
  cases padding with
  | nil =>
      simpa [ULogBootstrapExecution.beforeClockPadding] using
        (run_initializedPowerClock_exact ([] : List Bool)
          (ULogBootstrapExecution.payloadFoldedLeft input
            (ULogBootstrapExecution.programMarkedLeft rules
              (List.replicate (PakOuterULogBridge.copiedCoreRadius x)
                MStarConcreteAlphabet.work)))
          (PakOuterULogBridge.copiedBootstrapTail x input))
  | cons b bs =>
      simpa [ULogBootstrapExecution.beforeClockPadding] using
        (run_initializedPowerClock_exact (b :: bs)
        (ULogBootstrapExecution.payloadFoldedLeft input
          (ULogBootstrapExecution.programMarkedLeft rules
            (List.replicate (PakOuterULogBridge.copiedCoreRadius x)
              MStarConcreteAlphabet.work)))
        (PakOuterULogBridge.copiedBootstrapTail x input))

theorem run_copiedRuntimeInitializationFuel
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) :
    ULogBootstrapExecution.run
      (copiedRuntimeInitializationFuel x rules input padding)
      (.running ULogControl.State.framePayloadLength
        ⟨List.replicate (PakOuterULogBridge.copiedCoreRadius x)
            MStarConcreteAlphabet.work,
          ULogAlphabet.ulogCore ULogAlphabet.pcMark,
          (ULogBytecode.encodeProgram rules ++
            ULogBytecode.encodePayload input padding).map ULogProgram.codeTape ++
            ULogAlphabet.ulogCore ULogAlphabet.codeEnd ::
              ULogBootstrapExecution.payloadRuntimeWorkspace input
                (PakOuterULogBridge.copiedBootstrapTail x input)⟩) =
      ULogBootstrapExecution.initializedRuntime padding input
        (ULogBootstrapExecution.programMarkedLeft rules
          (List.replicate (PakOuterULogBridge.copiedCoreRadius x)
            MStarConcreteAlphabet.work))
        (PakOuterULogBridge.copiedBootstrapTail x input) := by
  exact Nat.find_spec
    (ULogBootstrapExecution.reaches_payloadRuntimeInitialized rules input padding
      (List.replicate (PakOuterULogBridge.copiedCoreRadius x)
        MStarConcreteAlphabet.work)
      (PakOuterULogBridge.copiedBootstrapTail x input))

/-- Closed preamble plus the explicitly isolated runtime-init fuel. -/
noncomputable def bootstrapDecompositionFuel
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) : ℕ :=
  PakOuterULogBridge.copiedCoreRadius x + 2 * x.length + 5 +
    copiedRuntimeInitializationFuel x rules input padding

/-- A composable exact bootstrap run: the closed scanner/translator preamble
is followed by precisely the still-isolated runtime initialization stage. -/
theorem run_bootstrapDecompositionFuel
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    ULogBootstrapExecution.run (bootstrapDecompositionFuel x rules input padding)
      (.running ULogControl.qStart (copiedULogStartZipper x)) =
      .running ULogControl.State.cycleStart
        (copiedSemanticStartZipper x rules input padding) := by
  subst x
  generalize henc : ULogBytecode.encodeProgram rules ++
    ULogBytecode.encodePayload input padding = word
  have hne : word ≠ [] := by
    intro hnil
    apply ULogBootstrapExecution.encodedUniversalInput_ne_nil rules input padding
    simpa [henc] using hnil
  cases word with
  | nil => exact (hne rfl).elim
  | cons b bits =>
      have hstart : copiedULogStartZipper (b :: bits) =
          ⟨[], MStarConcreteAlphabet.work,
            List.replicate (PakOuterULogBridge.copiedCoreRadius (b :: bits))
                MStarConcreteAlphabet.work ++
              ULogProgram.bitTape b ::
                (bits.map ULogProgram.bitTape ++
                  MStarConcreteAlphabet.work ::
                    ULogBootstrapExecution.payloadRuntimeWorkspace input
                      (PakOuterULogBridge.copiedBootstrapTail (b :: bits) input))⟩ := by
        unfold copiedULogStartZipper
        rw [PakOuterULogBridge.copied_rightBuffer_eq_runtimeWorkspace
          (b :: bits) input]
        simp [List.append_assoc]
      have hpre := run_bootstrap_workspace_exact
        (PakOuterULogBridge.copiedCoreRadius (b :: bits)) b bits []
        (ULogBootstrapExecution.payloadRuntimeWorkspace input
          (PakOuterULogBridge.copiedBootstrapTail (b :: bits) input))
      have hrun := run_copiedRuntimeInitializationFuel (b :: bits)
        rules input padding
      rw [henc] at hrun
      have hend := copied_initializedRuntime_eq_semanticStart (b :: bits)
        rules input padding
      unfold bootstrapDecompositionFuel
      rw [show PakOuterULogBridge.copiedCoreRadius (b :: bits) +
          2 * (b :: bits).length + 5 +
            copiedRuntimeInitializationFuel (b :: bits) rules input padding =
          (PakOuterULogBridge.copiedCoreRadius (b :: bits) +
            2 * (b :: bits).length + 5) +
            copiedRuntimeInitializationFuel (b :: bits) rules input padding by
          omega]
      rw [ULogBootstrapExecution.run_add, hstart]
      simp only [ULogControl.qStart]
      simp only [List.append_nil] at hpre
      rw [hpre, hrun]
      exact hend

/-- The least bootstrap fuel is bounded by the explicit preamble plus the
isolated runtime-initialization fuel.  Thus the remaining numerical proof is
exactly a bound on `copiedRuntimeInitializationFuel`, not a hidden outer-run
existential. -/
theorem bootstrapFuel_le_decompositionFuel
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    bootstrapFuel x rules input padding hword ≤
      bootstrapDecompositionFuel x rules input padding :=
  bootstrapFuel_le_of_run x rules input padding hword
    (bootstrapDecompositionFuel x rules input padding)
    (run_bootstrapDecompositionFuel x rules input padding hword)

end PakFixedPolyomino.PakULogBootstrapExplicitFuel
