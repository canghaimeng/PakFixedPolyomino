import PakFixedPolyomino.PakULogSlotRunLedger
import PakFixedPolyomino.PakULogCursorFuelExact

/-!
# Quantitative phase interface for raw `U_log` cycles

An `ExactConcreteCycle` records first-hit *correctness*, but the existing
resource invariant records only semantic capacity and work reserve.  This
file isolates the sound way to obtain a numerical raw-step bound: provide
literal choice-free and stop-free phase certificates, then first-hit
minimality turns their lengths into bounds for the exact cycle stored by the
canonical forward trace.  No bound is inferred from a finite configuration
space.
-/

namespace PakFixedPolyomino.PakULogCycleResourceBound

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution
open ULogBootstrapExecution
open PakULogCursorFuelExact

/-- A first valid hit is no later than any explicit valid run reaching the
same stopping predicate.  This is the quantitative consequence of
first-hit minimality used below. -/
theorem FirstValidZeroHit.steps_le_of_validHit
    {stop : Result → Prop}
    {start finish candidate : Result} {n : ℕ}
    (first : FirstValidZeroHit stop start finish)
    (path : ValidZeroRun n start candidate)
    (hcandidate : stop candidate) :
    first.steps ≤ n := by
  by_contra hnot
  have hlt : n < first.steps := Nat.lt_of_not_ge hnot
  exact first.before n hlt (by
    rw [path.eq_run]
    exact hcandidate)

/-- First-hit lengths are invariant under a literal identification of their
source configurations.  This is the transport lemma needed when a semantic
frame encoding is unfolded into the physical clock/payload zipper. -/
theorem FirstValidZeroHit.steps_eq_of_start_eq
    {stop : Result → Prop} {start₁ start₂ finish₁ finish₂ : Result}
    (hstart : start₁ = start₂)
    (first₁ : FirstValidZeroHit stop start₁ finish₁)
    (first₂ : FirstValidZeroHit stop start₂ finish₂) :
    first₁.steps = first₂.steps := by
  subst start₂
  exact first₁.steps_eq first₂

/-- A choice-free phase ending at a choice is an explicit upper bound for
every stored exact-cycle choice prefix from the same source. -/
theorem choicePrefix_steps_le_of_phase
    {slot : Bool} {start finish candidate : Result} {n : ℕ}
    (cycle : ExactConcreteCycle slot start finish)
    (phase : ChoiceFreeValidZeroRun n start candidate)
    (hchoice : IsConcreteChoice candidate) :
    cycle.choicePrefix.steps ≤ n := by
  exact cycle.choicePrefix.steps_le (phase.toFirstHit hchoice)

/-- Likewise, a stop-free phase ending at a concrete cycle stop controls the
stored exact-cycle suffix. -/
theorem cycleSuffix_steps_le_of_phase
    {slot : Bool} {start finish candidate : Result} {n : ℕ}
    (cycle : ExactConcreteCycle slot start finish)
    (phase : StopFreeValidZeroRun n cycle.branch candidate)
    (hstop : IsConcreteCycleStop candidate) :
    cycle.cycleSuffix.steps ≤ n := by
  exact cycle.cycleSuffix.steps_le (phase.toFirstHit hstop)

/-- A literal pair of phase certificates gives a literal microstep bound for
one exact cycle.  The middle selected labelled arrow contributes exactly one
step. -/
theorem microFuel_le_of_phases
    {slot : Bool} {start finish choiceCandidate stopCandidate : Result}
    {prefixFuel suffixFuel : ℕ}
    (cycle : ExactConcreteCycle slot start finish)
    (prephase : ChoiceFreeValidZeroRun prefixFuel start choiceCandidate)
    (hchoice : IsConcreteChoice choiceCandidate)
    (suffix : StopFreeValidZeroRun suffixFuel cycle.branch stopCandidate)
    (hstop : IsConcreteCycleStop stopCandidate) :
    cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps ≤
      prefixFuel + 1 + suffixFuel := by
  have hp := choicePrefix_steps_le_of_phase cycle prephase hchoice
  have hs := cycleSuffix_steps_le_of_phase cycle suffix hstop
  omega

/-- A resource-scaled version of the phase interface.  Once a canonical
forward branch supplies phase bounds `A * R^a` and `B * R^b`, the raw exact
cycle is bounded by their displayed sum.  This theorem deliberately keeps
the two branch-specific phase obligations explicit. -/
theorem microFuel_le_of_resource_phases
    {slot : Bool} {start finish choiceCandidate stopCandidate : Result}
    {prefixFuel suffixFuel R A B a b : ℕ}
    (cycle : ExactConcreteCycle slot start finish)
    (prephase : ChoiceFreeValidZeroRun prefixFuel start choiceCandidate)
    (hchoice : IsConcreteChoice choiceCandidate)
    (suffix : StopFreeValidZeroRun suffixFuel cycle.branch stopCandidate)
    (hstop : IsConcreteCycleStop stopCandidate)
    (hprefix : prefixFuel ≤ A * R ^ a)
    (hsuffix : suffixFuel ≤ B * R ^ b) :
    cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps ≤
      A * R ^ a + 1 + B * R ^ b := by
  have h := microFuel_le_of_phases cycle prephase hchoice suffix hstop
  omega

/-- The concrete zero-clock cycle has an exact, non-asymptotic first-choice
phase.  In the zero-clock case the scan visits the payload rightward and
leftward once, with three fixed control transitions. -/
theorem clockDecrementCells_zero_firstChoice_steps
    (head : Tape) (hhead : choiceHead head = true)
    (payloadPath : List Tape) (hsafe : PayloadPathSafe payloadPath)
    (left suffix : List Tape) :
    (clockDecrementCells_zero_firstChoice head hhead payloadPath hsafe left suffix).steps =
      2 * payloadPath.length + 3 := by
  simp [clockDecrementCells_zero_firstChoice,
    ChoiceFreeValidZeroRun.toFirstHit, List.length_reverse, Nat.two_mul,
    Nat.add_left_comm, Nat.add_comm]
  omega

/-- The positive unary-clock choice scan has an exact linear raw-step cost.
Each leading zero contributes one consume step and one return-traversal cell,
while the payload is crossed twice.  The `k = 0` endpoint is recorded by the
separate theorem above; spelling the positive case as `n + 1` avoids a
dependent proof cast in the concrete certificate constructor. -/
theorem clockDecrementCells_succ_firstChoice_steps
    (head : Tape) (hhead : choiceHead head = true)
    (n : ℕ) (payloadPath : List Tape) (hsafe : PayloadPathSafe payloadPath)
    (left suffix : List Tape) :
    (clockDecrementCells_firstChoice head hhead (n + 1) payloadPath hsafe left suffix).steps =
      2 * payloadPath.length + 2 * (n + 1) + 3 := by
  simp [clockDecrementCells_firstChoice,
    ChoiceFreeValidZeroRun.toFirstHit, runtimeClockReturnPath,
    List.length_reverse, List.length_replicate, Nat.two_mul,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  omega

/-- Hence any exact-cycle choice prefix issued from this literal zero-clock
frame is bounded by `2 * |payloadPath| + 3`.  This is a genuine raw
 microstep bound (not a semantic-cycle count). -/
theorem exactCycle_zeroClock_choicePrefix_le
    {slot : Bool} {finish : Result}
    (cycle : ExactConcreteCycle slot
      (.running .cycleStart
        ⟨left, head, payloadPath ++ ulogCore clockOne :: suffix⟩) finish)
    (hhead : choiceHead head = true)
    (hsafe : PayloadPathSafe payloadPath) :
    cycle.choicePrefix.steps ≤ 2 * payloadPath.length + 3 := by
  let phase := clockDecrementCells_zero_firstChoice head hhead payloadPath hsafe left suffix
  have hphase : cycle.choicePrefix.steps ≤ phase.steps :=
    cycle.choicePrefix.steps_le phase
  rw [clockDecrementCells_zero_firstChoice_steps] at hphase
  exact hphase

/-- The preceding exact phase formula turns a canonical clock/payload
envelope into a numerical prefix bound for any exact stored cycle from that
same physical start state. -/
theorem exactCycle_succClock_choicePrefix_le
    {slot : Bool} {finish : Result}
    (cycle : ExactConcreteCycle slot
      (.running .cycleStart
        ⟨left, head,
          payloadPath ++ List.replicate (n + 1) (ulogCore clockZero) ++
            ulogCore clockOne :: suffix⟩) finish)
    (hhead : choiceHead head = true)
    (hsafe : PayloadPathSafe payloadPath) :
    cycle.choicePrefix.steps ≤ 2 * payloadPath.length + 2 * (n + 1) + 3 := by
  let phase := clockDecrementCells_firstChoice head hhead (n + 1) payloadPath hsafe
    left suffix
  have hphase : cycle.choicePrefix.steps ≤ phase.steps :=
    cycle.choicePrefix.steps_le phase
  rw [clockDecrementCells_succ_firstChoice_steps] at hphase
  exact hphase

/-- If the physical payload corridor and positive unary clock both fit in a
resource radius `R`, then the canonical first-choice portion of the raw
cycle costs at most `4R + 3` literal microsteps. -/
theorem exactCycle_succClock_choicePrefix_le_radius
    {slot : Bool} {finish : Result} {R : ℕ}
    (cycle : ExactConcreteCycle slot
      (.running .cycleStart
        ⟨left, head,
          payloadPath ++ List.replicate (n + 1) (ulogCore clockZero) ++
            ulogCore clockOne :: suffix⟩) finish)
    (hhead : choiceHead head = true)
    (hsafe : PayloadPathSafe payloadPath)
    (hpayload : payloadPath.length ≤ R)
    (hclock : n + 1 ≤ R) :
    cycle.choicePrefix.steps ≤ 4 * R + 3 := by
  have h := exactCycle_succClock_choicePrefix_le cycle hhead hsafe
  omega

/-- The analogous zero-clock radius specialization costs at most `2R + 3`.
It is separated because the concrete machine's zero-clock endpoint has a
different physical phase shape. -/
theorem exactCycle_zeroClock_choicePrefix_le_radius
    {slot : Bool} {finish : Result} {R : ℕ}
    (cycle : ExactConcreteCycle slot
      (.running .cycleStart
        ⟨left, head, payloadPath ++ ulogCore clockOne :: suffix⟩) finish)
    (hhead : choiceHead head = true)
    (hsafe : PayloadPathSafe payloadPath)
    (hpayload : payloadPath.length ≤ R) :
    cycle.choicePrefix.steps ≤ 2 * R + 3 := by
  have h := exactCycle_zeroClock_choicePrefix_le cycle hhead hsafe
  omega

/-- Every exact cycle issued from an actual semantic frame has a concrete
linear bound for its *choice* phase.  This is the first fully instantiated
canonical-forward branch of the resource interface: it uses the literal
clock and payload corridor stored in the frame, rather than a semantic-time
oracle.  The rule-cursor/return suffix remains a separate phase obligation.
-/
theorem exactConcreteCycle_frame_choicePrefix_le_of_clockZeros_eq
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) {slot : Bool} {finish : Result}
    (cycle : ExactConcreteCycle slot frame.encode finish)
    (hfocus : frame.config.focus < 3)
    (k : ℕ) (hclockZeros : frame.clockZeros = k) :
    cycle.choicePrefix.steps ≤
      2 * frame.config.right.length + 2 * k + 3 := by
  have hhead : choiceHead (readHeadNat frame.config.focus) = true := by
    interval_cases frame.config.focus <;> decide
  have hsafe : PayloadPathSafe (frame.config.right.map payloadNat) :=
    payloadNatList_safe frame.config.right
  cases k with
  | zero =>
      let start : Result := Result.running .cycleStart
        ⟨dynamicRuleReturnPath
            (frame.config.leftRev.map payloadNat) frame.config.program input ++
            ulogCore pcMark :: frame.outer,
          readHeadNat frame.config.focus,
          frame.config.right.map payloadNat ++ ulogCore clockOne ::
            (frame.runtime ++
              stateWorkspace frame.capacity frame.config.state suffix)⟩
      have hstart : frame.encode = start := by
        simp [start, SemanticCycleFrame.encode, semanticCycleEncoding,
          clockCellsBefore, hclockZeros, List.append_assoc]
      have hcycle : ExactConcreteCycle slot start finish := by
        rw [← hstart]
        exact cycle
      have h := exactCycle_zeroClock_choicePrefix_le
        (left := dynamicRuleReturnPath
          (frame.config.leftRev.map payloadNat) frame.config.program input ++
            ulogCore pcMark :: frame.outer)
        (head := readHeadNat frame.config.focus)
        (payloadPath := frame.config.right.map payloadNat)
        (suffix := frame.runtime ++
          stateWorkspace frame.capacity frame.config.state suffix)
        (slot := slot)
        (finish := finish)
        hcycle
        hhead hsafe
      have hprefixSteps : cycle.choicePrefix.steps =
          hcycle.choicePrefix.steps :=
        FirstValidZeroHit.steps_eq_of_start_eq hstart cycle.choicePrefix
          hcycle.choicePrefix
      calc
        cycle.choicePrefix.steps = hcycle.choicePrefix.steps := hprefixSteps
        _ ≤ 2 * frame.config.right.length + 2 * 0 + 3 := by
          simpa using h
  | succ n =>
      let start : Result := Result.running .cycleStart
        ⟨dynamicRuleReturnPath
            (frame.config.leftRev.map payloadNat) frame.config.program input ++
            ulogCore pcMark :: frame.outer,
          readHeadNat frame.config.focus,
          frame.config.right.map payloadNat ++
            List.replicate (n + 1) (ulogCore clockZero) ++
              ulogCore clockOne ::
                (frame.runtime ++
                  stateWorkspace frame.capacity frame.config.state suffix)⟩
      have hstart : frame.encode = start := by
        simp [start, SemanticCycleFrame.encode, semanticCycleEncoding,
          clockCellsBefore, hclockZeros, List.append_assoc]
      have hcycle : ExactConcreteCycle slot start finish := by
        rw [← hstart]
        exact cycle
      have h := exactCycle_succClock_choicePrefix_le
        (left := dynamicRuleReturnPath
          (frame.config.leftRev.map payloadNat) frame.config.program input ++
            ulogCore pcMark :: frame.outer)
        (head := readHeadNat frame.config.focus)
        (payloadPath := frame.config.right.map payloadNat)
        (suffix := frame.runtime ++
          stateWorkspace frame.capacity frame.config.state suffix)
        (n := n) (slot := slot) (finish := finish)
        hcycle
        hhead hsafe
      have hprefixSteps : cycle.choicePrefix.steps =
          hcycle.choicePrefix.steps :=
        FirstValidZeroHit.steps_eq_of_start_eq hstart cycle.choicePrefix
          hcycle.choicePrefix
      calc
        cycle.choicePrefix.steps = hcycle.choicePrefix.steps := hprefixSteps
        _ ≤ 2 * frame.config.right.length + 2 * (n + 1) + 3 := by
          simpa using h

/-- The user-facing frame form specializes the preceding equality-indexed
lemma to the clock stored in the frame. -/
theorem exactConcreteCycle_frame_choicePrefix_le
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) {slot : Bool} {finish : Result}
    (cycle : ExactConcreteCycle slot frame.encode finish)
    (hfocus : frame.config.focus < 3) :
    cycle.choicePrefix.steps ≤
      2 * frame.config.right.length + 2 * frame.clockZeros + 3 := by
  simpa using exactConcreteCycle_frame_choicePrefix_le_of_clockZeros_eq
    frame cycle hfocus frame.clockZeros rfl

/-- Radius-scaled canonical-forward choice bound.  It becomes a closed
numeric `4R+3` estimate as soon as the frame's payload corridor and unary
clock are charged to the same physical radius. -/
theorem exactConcreteCycle_frame_choicePrefix_le_radius
    {input : List Bool} {suffix : List Tape} {R : ℕ}
    (frame : SemanticCycleFrame input suffix) {slot : Bool} {finish : Result}
    (cycle : ExactConcreteCycle slot frame.encode finish)
    (hfocus : frame.config.focus < 3)
    (hright : frame.config.right.length ≤ R)
    (hclock : frame.clockZeros ≤ R) :
    cycle.choicePrefix.steps ≤ 4 * R + 3 := by
  have h := exactConcreteCycle_frame_choicePrefix_le frame cycle hfocus
  omega

/-- Concrete forward realization of the accepting (target-zero) semantic
branch inherits the literal frame choice bound.  This is a closed canonical
forward-constructor instance, not a bound on an arbitrary semantic cycle. -/
theorem exactAcceptingCycleRefinement_choicePrefix_le
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (next : ULogSemantics.Config)
    (ready : FrameReady frame)
    (hstep : ULogSemantics.stepSlot slot frame.config = some next)
    (haccept : ULogSemantics.accepting next = true) :
    (exactAcceptingCycleRefinement frame slot ready next hstep haccept).exact_cycle.choicePrefix.steps ≤
        2 * frame.config.right.length + 2 * frame.clockZeros + 3 := by
  exact exactConcreteCycle_frame_choicePrefix_le frame
    (exactAcceptingCycleRefinement frame slot ready next hstep haccept).exact_cycle
    ready.focus_lt_three

/-- Resource-radius specialization for that concrete terminal branch. -/
theorem exactAcceptingCycleRefinement_choicePrefix_le_radius
    {input : List Bool} {suffix : List Tape} {R : ℕ}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (next : ULogSemantics.Config)
    (ready : FrameReady frame)
    (hstep : ULogSemantics.stepSlot slot frame.config = some next)
    (haccept : ULogSemantics.accepting next = true)
    (hright : frame.config.right.length ≤ R)
    (hclock : frame.clockZeros ≤ R) :
    (exactAcceptingCycleRefinement frame slot ready next hstep haccept).exact_cycle.choicePrefix.steps ≤
      4 * R + 3 := by
  exact exactConcreteCycle_frame_choicePrefix_le_radius frame
    (exactAcceptingCycleRefinement frame slot ready next hstep haccept).exact_cycle
    ready.focus_lt_three hright hclock

/-! ## Exact accepting target-zero tail -/

/-- Once target zero has been decoded, the machine performs one setup step,
one pass through the target-rewrite corridor, and one accepting transition. -/
theorem actionTargetFinishSeek_firstStop_steps
    (path : List Tape) (hsafe : TargetFinishCorridorSafe path)
    (left : List Tape) (terminal : Tape)
    (hterminal : terminal = ulogCore stateZero ∨
      terminal = ulogCore stateOne)
    (right : List Tape) :
    (actionTargetFinishSeek_firstStop path hsafe left terminal hterminal
      right).steps = path.length + 2 := by
  simp [actionTargetFinishSeek_firstStop, StopFreeValidZeroRun.append,
    StopFreeValidZeroRun.toFirstHit, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]
  omega

/-- The target-zero wrapper changes only the spelling of the unary-state
tail; its first-stop cost is the same corridor length plus two. -/
theorem targetRawZero_firstStop_steps
    (current : ℕ) (corridor : List Tape)
    (hsafe : TargetRewriteCorridorSafe corridor)
    (left tail : List Tape) :
    (targetRawZero_firstStop current corridor hsafe left tail).2.steps =
      corridor.length + 2 := by
  cases current with
  | zero =>
      let candidate := actionTargetFinishSeek_firstStop corridor hsafe.2 left
        (ulogCore stateOne) (Or.inr rfl) (ulogCore stateSep :: tail)
      have hstart : targetRawStart 0 0 corridor left tail =
          .running .actionTarget
            ⟨left, ulogCore codeOne,
              corridor ++ ulogCore stateOne :: ulogCore stateSep :: tail⟩ := by
        simp [targetRawStart, List.append_assoc]
      have heq := FirstValidZeroHit.steps_eq_of_start_eq hstart
        (targetRawZero_firstStop 0 corridor hsafe left tail).2 candidate
      have hc : candidate.steps = corridor.length + 2 := by
        simpa [candidate] using actionTargetFinishSeek_firstStop_steps
          corridor hsafe.2 left (ulogCore stateOne) (Or.inr rfl)
            (ulogCore stateSep :: tail)
      exact heq.trans hc

  | succ n =>
      let candidate := actionTargetFinishSeek_firstStop corridor hsafe.2 left
        (ulogCore stateZero) (Or.inl rfl)
        (List.replicate n (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail)
      have hstart : targetRawStart 0 (n + 1) corridor left tail =
          .running .actionTarget
            ⟨left, ulogCore codeOne,
              corridor ++ (ulogCore stateZero ::
                (List.replicate n (ulogCore stateZero) ++
                  ulogCore stateOne :: ulogCore stateSep :: tail))⟩ := by
        simp [targetRawStart, List.replicate_succ, List.append_assoc]
      have heq := FirstValidZeroHit.steps_eq_of_start_eq hstart
        (targetRawZero_firstStop (n + 1) corridor hsafe left tail).2 candidate
      have hc : candidate.steps = corridor.length + 2 := by
        simpa [candidate] using actionTargetFinishSeek_firstStop_steps
          corridor hsafe.2 left (ulogCore stateZero) (Or.inl rfl)
            (List.replicate n (ulogCore stateZero) ++
              ulogCore stateOne :: ulogCore stateSep :: tail)
      exact heq.trans hc

/-- The generic write-head microprogram makes one outward scan, one write
turn, one return scan, and one target-boundary turn. -/
theorem actionWriteHead_fuel_eq
    (seekState : State) (hseek : seekState ≠ .cycleStart)
    (oldHead newHead : Tape) (path : List Tape)
    (hpass : ∀ x, x ∈ path → ∀ left y right,
      ULogBootstrapExecution.oneStep
        (.running seekState ⟨left, x, y :: right⟩) =
        .running seekState ⟨x :: left, y, right⟩)
    (hwrite : ∀ left y right,
      ULogBootstrapExecution.oneStep
        (.running seekState ⟨y :: left, oldHead, right⟩) =
        .running (.actionPhase .writeReturning)
          ⟨left, y, newHead :: right⟩)
    (hreturn : ∀ x, x ∈ path →
      x ≠ ulogCore actionBoundary ∧ x ≠ ulogCore pcMark)
    (left suffix : List Tape) :
    (stopFree_actionWriteHead_of seekState hseek oldHead newHead path hpass
      hwrite hreturn left suffix).1 = 2 * path.length + 2 := by
  simp [stopFree_actionWriteHead_of, StopFreeValidZeroRun.append,
    List.length_reverse, Nat.two_mul, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]
  omega

theorem actionWriteZero_fuel_eq
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (path : List Tape) (hpath : ActionWriteCorridorSafe path)
    (left suffix : List Tape) :
    (stopFree_actionWriteZero oldHead hhead path hpath left suffix).1 =
      2 * path.length + 3 := by
  simp [stopFree_actionWriteZero, stopFree_actionWriteZero_head,
    actionWriteHead_fuel_eq]
  omega

theorem actionWriteOne_fuel_eq
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (path : List Tape) (hpath : ActionWriteCorridorSafe path)
    (left suffix : List Tape) :
    (stopFree_actionWriteOne oldHead hhead path hpath left suffix).1 =
      2 * path.length + 4 := by
  simp [stopFree_actionWriteOne, stopFree_actionWriteOne_head,
    actionWriteHead_fuel_eq]
  omega

theorem actionWriteBlank_fuel_eq
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (path : List Tape) (hpath : ActionWriteCorridorSafe path)
    (left suffix : List Tape) :
    (stopFree_actionWriteBlank oldHead hhead path hpath left suffix).1 =
      2 * path.length + 5 := by
  simp [stopFree_actionWriteBlank, stopFree_actionWriteBlank_head,
    actionWriteHead_fuel_eq]
  omega

/-- The complete write-plus-target-zero accepting leaf is linear in the two
physical corridors.  The constant `9` is the maximum over the three legal
write symbols; no finite-state cardinality estimate is used. -/
theorem actionWriteTargetZero_firstStop_steps_le_radius
    (write current : ℕ) (hwrite : write < 3)
    (oldHead : Tape) (hhead : choiceHead oldHead = true)
    (corridor runtime : List Tape)
    (hwritePath : ActionWriteCorridorSafe (ulogCore codeOne :: corridor))
    (htargetPath : TargetRewriteCorridorSafe
      (corridor ++ writeHeadNat write :: runtime))
    (left tail : List Tape) {R : ℕ}
    (hcorridor : corridor.length ≤ R)
    (htargetCorridor :
      (corridor ++ writeHeadNat write :: runtime).length ≤ R) :
    (actionWriteTargetZero_firstStop write current hwrite oldHead hhead
      corridor runtime hwritePath htargetPath left tail).2.steps ≤
      3 * R + 9 := by
  let suffix := runtime ++ List.replicate current (ulogCore stateZero) ++
    ulogCore stateOne :: ulogCore stateSep :: tail
  let targetCorridor := corridor ++ writeHeadNat write :: runtime
  let targetHit :=
    (targetRawZero_firstStop current targetCorridor htargetPath
      (ulogCore codeOne ::
        List.replicate write (ulogCore codeZero) ++ left) tail).2
  have ht : targetHit.steps = targetCorridor.length + 2 := by
    dsimp [targetHit]
    exact targetRawZero_firstStop_steps current targetCorridor htargetPath
      (ulogCore codeOne ::
        List.replicate write (ulogCore codeZero) ++ left) tail
  have hwriteCases : write = 0 ∨ write = 1 ∨ write = 2 := by omega
  rcases hwriteCases with rfl | rfl | rfl
  · let writeRun := stopFree_actionWriteZero oldHead hhead
      (ulogCore codeOne :: corridor) hwritePath left suffix
    have hw : writeRun.1 = 2 * (ulogCore codeOne :: corridor).length + 3 := by
      dsimp [writeRun]
      exact actionWriteZero_fuel_eq oldHead hhead
        (ulogCore codeOne :: corridor) hwritePath left suffix
    have writeRun' : StopFreeValidZeroRun writeRun.1
        (actionWriteStart 0 left (ulogCore codeOne :: corridor) oldHead suffix)
        (targetRawStart 0 current targetCorridor
          (ulogCore codeOne :: left) tail) := by
      simpa [writeRun, targetCorridor, suffix, targetRawStart, actionWriteStart,
        beforeRightPath, writeHeadNat, List.append_assoc] using writeRun.2
    let candidate := writeRun'.appendFirstHit targetHit
    have heq :=
      (actionWriteTargetZero_firstStop 0 current hwrite oldHead hhead
        corridor runtime hwritePath htargetPath left tail).2.steps_eq candidate
    calc
      _ = candidate.steps := heq
      _ = writeRun.1 + targetHit.steps := rfl
      _ ≤ 3 * R + 9 := by
        rw [hw, ht]
        dsimp [targetCorridor]
        omega

  · let writeRun := stopFree_actionWriteOne oldHead hhead
      (ulogCore codeOne :: corridor) hwritePath left suffix
    have hw : writeRun.1 = 2 * (ulogCore codeOne :: corridor).length + 4 := by
      dsimp [writeRun]
      exact actionWriteOne_fuel_eq oldHead hhead
        (ulogCore codeOne :: corridor) hwritePath left suffix
    have writeRun' : StopFreeValidZeroRun writeRun.1
        (actionWriteStart 1 left (ulogCore codeOne :: corridor) oldHead suffix)
        (targetRawStart 0 current targetCorridor
          (ulogCore codeOne :: ulogCore codeZero :: left) tail) := by
      simpa [writeRun, targetCorridor, suffix, targetRawStart, actionWriteStart,
        beforeRightPath, writeHeadNat, List.replicate_succ,
        List.append_assoc] using writeRun.2
    let candidate := writeRun'.appendFirstHit targetHit
    have heq :=
      (actionWriteTargetZero_firstStop 1 current hwrite oldHead hhead
        corridor runtime hwritePath htargetPath left tail).2.steps_eq candidate
    calc
      _ = candidate.steps := heq
      _ = writeRun.1 + targetHit.steps := rfl
      _ ≤ 3 * R + 9 := by
        rw [hw, ht]
        dsimp [targetCorridor]
        omega

  · let writeRun := stopFree_actionWriteBlank oldHead hhead
      (ulogCore codeOne :: corridor) hwritePath left suffix
    have hw : writeRun.1 = 2 * (ulogCore codeOne :: corridor).length + 5 := by
      dsimp [writeRun]
      exact actionWriteBlank_fuel_eq oldHead hhead
        (ulogCore codeOne :: corridor) hwritePath left suffix
    have writeRun' : StopFreeValidZeroRun writeRun.1
        (actionWriteStart 2 left (ulogCore codeOne :: corridor) oldHead suffix)
        (targetRawStart 0 current targetCorridor
          (ulogCore codeOne :: ulogCore codeZero ::
            ulogCore codeZero :: left) tail) := by
      simpa [writeRun, targetCorridor, suffix, targetRawStart, actionWriteStart,
        beforeRightPath, writeHeadNat, List.replicate_succ,
        List.append_assoc] using writeRun.2
    let candidate := writeRun'.appendFirstHit targetHit
    have heq :=
      (actionWriteTargetZero_firstStop 2 current hwrite oldHead hhead
        corridor runtime hwritePath htargetPath left tail).2.steps_eq candidate
    calc
      _ = candidate.steps := heq
      _ = writeRun.1 + targetHit.steps := rfl
      _ ≤ 3 * R + 9 := by
        rw [hw, ht]
        dsimp [targetCorridor]
        omega

/-! ## Matched read dispatch -/

/-- A successful read-head comparison scans and returns across the same
corridor, with one match turn and one boundary turn. -/
theorem readHeadMatch_fuel_eq
    (slot : Bool) (seekState : State) (hseek : seekState ≠ .cycleStart)
    (head : Tape) (path : List Tape)
    (hpass : ∀ x, x ∈ path → ∀ left y right,
      ULogBootstrapExecution.oneStep
        (.running seekState ⟨left, x, y :: right⟩) =
        .running seekState ⟨x :: left, y, right⟩)
    (hmatch : ∀ left y right,
      ULogBootstrapExecution.oneStep
        (.running seekState ⟨y :: left, head, right⟩) =
        .running (.readPhase .returning slot) ⟨left, y, head :: right⟩)
    (hreturn : ∀ x, x ∈ path →
      x ≠ ulogCore readBoundary ∧ x ≠ ulogCore pcMark)
    (left suffix : List Tape) :
    (stopFree_readHeadMatch_of slot seekState hseek head path hpass hmatch
      hreturn left suffix).1 = 2 * path.length + 2 := by
  simp [stopFree_readHeadMatch_of, StopFreeValidZeroRun.append,
    List.length_reverse, Nat.two_mul, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]
  omega

theorem readZero_slotMatch_fuel_eq
    (slot : Bool) (path : List Tape)
    (hpath : ReadCorridorSafe (codeTape slot :: path))
    (left suffix : List Tape) :
    (stopFree_readZero_slotMatch slot path hpath left suffix).1 =
      2 * path.length + 6 := by
  simp [stopFree_readZero_slotMatch, stopFree_readZero_head,
    readHeadMatch_fuel_eq]
  omega

theorem readOne_slotMatch_fuel_eq
    (slot : Bool) (path : List Tape)
    (hpath : ReadCorridorSafe (codeTape slot :: path))
    (left suffix : List Tape) :
    (stopFree_readOne_slotMatch slot path hpath left suffix).1 =
      2 * path.length + 7 := by
  simp [stopFree_readOne_slotMatch, stopFree_readOne_head,
    readHeadMatch_fuel_eq]
  omega

theorem readBlank_slotMatch_fuel_eq
    (slot : Bool) (path : List Tape)
    (hpath : ReadCorridorSafe (codeTape slot :: path))
    (left suffix : List Tape) :
    (stopFree_readBlank_slotMatch slot path hpath left suffix).1 =
      2 * path.length + 8 := by
  simp [stopFree_readBlank_slotMatch, stopFree_readBlank_head,
    readHeadMatch_fuel_eq]
  omega

theorem readZero_toSlot_fuel_eq
    (slot : Bool) (slotCell : Tape) (path : List Tape)
    (hpath : ReadCorridorSafe (slotCell :: path))
    (left suffix : List Tape) :
    (stopFree_readZero_toSlot slot slotCell path hpath left suffix).1 =
      2 * path.length + 5 := by
  simp [stopFree_readZero_toSlot, stopFree_readZero_head,
    readHeadMatch_fuel_eq]
  omega

theorem readOne_toSlot_fuel_eq
    (slot : Bool) (slotCell : Tape) (path : List Tape)
    (hpath : ReadCorridorSafe (slotCell :: path))
    (left suffix : List Tape) :
    (stopFree_readOne_toSlot slot slotCell path hpath left suffix).1 =
      2 * path.length + 6 := by
  simp [stopFree_readOne_toSlot, stopFree_readOne_head,
    readHeadMatch_fuel_eq]
  omega

theorem readBlank_toSlot_fuel_eq
    (slot : Bool) (slotCell : Tape) (path : List Tape)
    (hpath : ReadCorridorSafe (slotCell :: path))
    (left suffix : List Tape) :
    (stopFree_readBlank_toSlot slot slotCell path hpath left suffix).1 =
      2 * path.length + 7 := by
  simp [stopFree_readBlank_toSlot, stopFree_readBlank_head,
    readHeadMatch_fuel_eq]
  omega

theorem sourceReadAtSlotMismatchZero_fuel_eq
    (slot : Bool) (source : ℕ) (boundary : ULogLetter)
    (base actionPath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe (codeTape (!slot) :: actionPath)) :
    (stopFree_sourceReadAtSlotMismatchZero_boundary slot source boundary
      base actionPath runtime suffix hsafe).1 = 2 * actionPath.length + 6 := by
  simp [stopFree_sourceReadAtSlotMismatchZero_boundary,
    stopFree_readZero_toSlot, stopFree_readZero_head,
    readHeadMatch_fuel_eq]
  omega

theorem sourceReadAtSlotMismatchOne_fuel_eq
    (slot : Bool) (source : ℕ) (boundary : ULogLetter)
    (base actionPath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe (codeTape (!slot) :: actionPath)) :
    (stopFree_sourceReadAtSlotMismatchOne_boundary slot source boundary
      base actionPath runtime suffix hsafe).1 = 2 * actionPath.length + 7 := by
  simp [stopFree_sourceReadAtSlotMismatchOne_boundary,
    stopFree_readOne_toSlot, stopFree_readOne_head,
    readHeadMatch_fuel_eq]
  omega

theorem sourceReadAtSlotMismatchBlank_fuel_eq
    (slot : Bool) (source : ℕ) (boundary : ULogLetter)
    (base actionPath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe (codeTape (!slot) :: actionPath)) :
    (stopFree_sourceReadAtSlotMismatchBlank_boundary slot source boundary
      base actionPath runtime suffix hsafe).1 = 2 * actionPath.length + 8 := by
  simp [stopFree_sourceReadAtSlotMismatchBlank_boundary,
    stopFree_readBlank_toSlot, stopFree_readBlank_head,
    readHeadMatch_fuel_eq]
  omega

/-- A bounded stop-free certificate.  Its data live in `Type`, since the
underlying concrete trace itself is data-valued. -/
structure QuantifiedStopFreeRun (B : ℕ) (start finish : Result) : Type where
  steps : ℕ
  le_bound : steps ≤ B
  run : StopFreeValidZeroRun steps start finish

/-- Uniform read/slot-mismatch prefix ending at the restore controller. -/
theorem sourceReadAtSlotMismatch_bounded_radius
    (slot : Bool) (source read : ℕ) (hread : read < 3)
    (boundary : ULogLetter) (base actionPath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe (codeTape (!slot) :: actionPath))
    {R : ℕ} (hpath : actionPath.length ≤ R) :
    Nonempty (QuantifiedStopFreeRun (2 * R + 8)
      (sourceReadStartedAt slot source boundary (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape (!slot) :: actionPath ++ readHeadNat read :: runtime)
        suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath (slotMismatchRestorePath source read)
          base (ulogCore boundary)
          (codeTape (!slot) :: actionPath ++ readHeadNat read :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)))) := by
  cases read with
  | zero =>
      let run := stopFree_sourceReadAtSlotMismatchZero_boundary slot source
        boundary base actionPath runtime suffix hsafe
      refine ⟨
        { steps := run.1
          le_bound := ?_
          run := by simpa [run] using run.2 }⟩
      rw [show run.1 = 2 * actionPath.length + 6 by
        dsimp [run]
        exact sourceReadAtSlotMismatchZero_fuel_eq slot source boundary
          base actionPath runtime suffix hsafe]
      omega
  | succ read => cases read with
    | zero =>
        let run := stopFree_sourceReadAtSlotMismatchOne_boundary slot source
          boundary base actionPath runtime suffix hsafe
        refine ⟨
          { steps := run.1
            le_bound := ?_
            run := by simpa [run] using run.2 }⟩
        rw [show run.1 = 2 * actionPath.length + 7 by
          dsimp [run]
          exact sourceReadAtSlotMismatchOne_fuel_eq slot source boundary
            base actionPath runtime suffix hsafe]
        omega
    | succ read => cases read with
      | zero =>
          let run := stopFree_sourceReadAtSlotMismatchBlank_boundary slot source
            boundary base actionPath runtime suffix hsafe
          refine ⟨
            { steps := run.1
              le_bound := ?_
              run := by simpa [run] using run.2 }⟩
          rw [show run.1 = 2 * actionPath.length + 8 by
            dsimp [run]
            exact sourceReadAtSlotMismatchBlank_fuel_eq slot source boundary
              base actionPath runtime suffix hsafe]
          omega
      | succ read => omega

/-- Uniform matched-read dispatch.  For the three supported read symbols the
exact costs are respectively `2|path|+6`, `+7`, and `+8`; the write value
changes only the spelling of the following action state. -/
theorem sourceReadAtValid_actionWrite_bounded_radius
    (slot : Bool) (source read write target : ℕ)
    (boundary : ULogLetter) (m : OneTapeTableau.Move)
    (hread : read < 3) (hwrite : write < 3)
    (base movePath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe
      (codeTape slot :: encodedActionPath write target m movePath))
    {R : ℕ}
    (hpath : (encodedActionPath write target m movePath).length ≤ R) :
    Nonempty (QuantifiedStopFreeRun (2 * R + 8)
      (sourceReadStartedAt slot source boundary (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape slot :: encodedActionPath write target m movePath ++
            readHeadNat read :: runtime) suffix)
      (actionWriteStart write
        (matchedReadLeftAt slot source read boundary base)
        (List.replicate target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits m ++ movePath)
        (readHeadNat read)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))) := by
  have hreadCases : read = 0 ∨ read = 1 ∨ read = 2 := by omega
  have hwriteCases : write = 0 ∨ write = 1 ∨ write = 2 := by omega
  rcases hreadCases with rfl | rfl | rfl
  · exact by
      let run := stopFree_readZero_slotMatch slot
        (encodedActionPath write target m movePath) hsafe
        (ulogCore codeOne :: List.replicate source (ulogCore codeZero) ++
          ulogCore boundary :: base)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)
      refine ⟨
        { steps := run.1
          le_bound := ?_
          run := ?_ }⟩
      · rw [show run.1 = 2 *
            (encodedActionPath write target m movePath).length + 6 by
          dsimp [run]
          exact readZero_slotMatch_fuel_eq slot
            (encodedActionPath write target m movePath) hsafe
            (ulogCore codeOne ::
              List.replicate source (ulogCore codeZero) ++
                ulogCore boundary :: base)
            (runtime ++ List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)]
        omega
      · cases write with
        | zero => cases target <;> simpa [run, sourceReadStartedAt,
            matchedReadLeftAt, encodedActionPath,
            ULogBytecode.encodeNatField, actionWriteStart, unaryFieldFirst,
            readHeadNat, beforeRightPath, List.map_append,
            List.replicate_succ, List.append_assoc, codeTape] using run.2
        | succ w => cases w with
          | zero => cases target <;> simpa [run, sourceReadStartedAt,
              matchedReadLeftAt, encodedActionPath,
              ULogBytecode.encodeNatField, actionWriteStart, unaryFieldFirst,
              readHeadNat, beforeRightPath, List.map_append,
              List.replicate_succ, List.append_assoc, codeTape] using run.2
          | succ w => cases w with
            | zero => cases target <;> simpa [run, sourceReadStartedAt,
                matchedReadLeftAt, encodedActionPath,
                ULogBytecode.encodeNatField, actionWriteStart,
                unaryFieldFirst, readHeadNat, beforeRightPath,
                List.map_append, List.replicate_succ, List.append_assoc,
                codeTape] using run.2
            | succ w => omega
  · exact by
      let run := stopFree_readOne_slotMatch slot
        (encodedActionPath write target m movePath) hsafe
        (ulogCore codeOne :: List.replicate source (ulogCore codeZero) ++
          ulogCore boundary :: base)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)
      refine ⟨
        { steps := run.1
          le_bound := ?_
          run := ?_ }⟩
      · rw [show run.1 = 2 *
            (encodedActionPath write target m movePath).length + 7 by
          dsimp [run]
          exact readOne_slotMatch_fuel_eq slot
            (encodedActionPath write target m movePath) hsafe
            (ulogCore codeOne ::
              List.replicate source (ulogCore codeZero) ++
                ulogCore boundary :: base)
            (runtime ++ List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)]
        omega
      · cases write with
        | zero => cases target <;> simpa [run, sourceReadStartedAt,
            matchedReadLeftAt, encodedActionPath,
            ULogBytecode.encodeNatField, actionWriteStart, unaryFieldFirst,
            readHeadNat, beforeRightPath, List.map_append,
            List.replicate_succ, List.append_assoc, codeTape] using run.2
        | succ w => cases w with
          | zero => cases target <;> simpa [run, sourceReadStartedAt,
              matchedReadLeftAt, encodedActionPath,
              ULogBytecode.encodeNatField, actionWriteStart, unaryFieldFirst,
              readHeadNat, beforeRightPath, List.map_append,
              List.replicate_succ, List.append_assoc, codeTape] using run.2
          | succ w => cases w with
            | zero => cases target <;> simpa [run, sourceReadStartedAt,
                matchedReadLeftAt, encodedActionPath,
                ULogBytecode.encodeNatField, actionWriteStart,
                unaryFieldFirst, readHeadNat, beforeRightPath,
                List.map_append, List.replicate_succ, List.append_assoc,
                codeTape] using run.2
            | succ w => omega
  · exact by
      let run := stopFree_readBlank_slotMatch slot
        (encodedActionPath write target m movePath) hsafe
        (ulogCore codeOne :: List.replicate source (ulogCore codeZero) ++
          ulogCore boundary :: base)
        (runtime ++ List.replicate source (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)
      refine ⟨
        { steps := run.1
          le_bound := ?_
          run := ?_ }⟩
      · rw [show run.1 = 2 *
            (encodedActionPath write target m movePath).length + 8 by
          dsimp [run]
          exact readBlank_slotMatch_fuel_eq slot
            (encodedActionPath write target m movePath) hsafe
            (ulogCore codeOne ::
              List.replicate source (ulogCore codeZero) ++
                ulogCore boundary :: base)
            (runtime ++ List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)]
        omega
      · cases write with
        | zero => cases target <;> simpa [run, sourceReadStartedAt,
            matchedReadLeftAt, encodedActionPath,
            ULogBytecode.encodeNatField, actionWriteStart, unaryFieldFirst,
            readHeadNat, beforeRightPath, List.map_append,
            List.replicate_succ, List.append_assoc, codeTape] using run.2
        | succ w => cases w with
          | zero => cases target <;> simpa [run, sourceReadStartedAt,
              matchedReadLeftAt, encodedActionPath,
              ULogBytecode.encodeNatField, actionWriteStart, unaryFieldFirst,
              readHeadNat, beforeRightPath, List.map_append,
              List.replicate_succ, List.append_assoc, codeTape] using run.2
          | succ w => cases w with
            | zero => cases target <;> simpa [run, sourceReadStartedAt,
                matchedReadLeftAt, encodedActionPath,
                ULogBytecode.encodeNatField, actionWriteStart,
                unaryFieldFirst, readHeadNat, beforeRightPath,
                List.map_append, List.replicate_succ, List.append_assoc,
                codeTape] using run.2
            | succ w => omega

/-- The delimiter transition from a restored matched source field into the
read selector consumes its unary source word exactly once. -/
theorem sourceFieldRestoredAt_read_fuel_eq
    (slot : Bool) (q : ℕ) (boundary : ULogLetter) (b : Bool)
    (base corridor suffix : List Tape) :
    (stopFree_sourceFieldRestoredAt_read slot q boundary b base corridor
      suffix).1 = q + 1 := by
  rfl

/-! ## Explicit rule-return/count subphase -/

/-- The selected-branch rule-return/count subphase has no hidden search
fuel: it crosses the returned program path once, performs one mark step,
crosses exactly one `pcDone` cell per rule, and performs one final dispatch.
This is the first explicit suffix component needed by the accepting branch. -/
theorem dynamicRuleSourceStarted_fuel_eq
    (slot : Bool) (leftTape : List Tape) (hleft : PayloadPathSafe leftTape)
    (rules : List ULogBytecode.RuleCode) (hrules : rules ≠ [])
    (input : List Bool) (outer : List Tape) (head : Tape)
    (right : List Tape) :
    (stopFree_dynamicRuleSourceStarted slot leftTape hleft rules hrules input
      outer head right).1 =
      (dynamicRuleReturnPath leftTape rules input).length + 1 + rules.length + 1 := by
  simp [stopFree_dynamicRuleSourceStarted, StopFreeValidZeroRun.append,
    List.length_replicate, Nat.add_left_comm, Nat.add_comm]

/-- Exact physical size of the returned rule corridor.  This exposes all
four pieces that later have to be charged to the copied radius: dynamic left
tape, payload prefix, encoded rules, and unary rule counter. -/
theorem dynamicRuleReturnPath_length
    (leftTape : List Tape) (rules : List ULogBytecode.RuleCode)
    (input : List Bool) :
    (dynamicRuleReturnPath leftTape rules input).length =
      leftTape.length + (payloadProgramPrefix input).length +
        (ULogBytecode.encodeRules rules).length + 1 + rules.length := by
  simp [dynamicRuleReturnPath, ruleReturnPath, List.length_reverse,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The same subphase is at most linear in any radius bounding both its
returned program corridor and number of encoded rules. -/
theorem dynamicRuleSourceStarted_fuel_le_radius
    (slot : Bool) (leftTape : List Tape) (hleft : PayloadPathSafe leftTape)
    (rules : List ULogBytecode.RuleCode) (hrules : rules ≠ [])
    (input : List Bool) (outer : List Tape) (head : Tape)
    (right : List Tape) {R : ℕ}
    (hpath : (dynamicRuleReturnPath leftTape rules input).length ≤ R)
    (hrulesBound : rules.length ≤ R) :
    (stopFree_dynamicRuleSourceStarted slot leftTape hleft rules hrules input
      outer head right).1 ≤ 2 * R + 2 := by
  rw [dynamicRuleSourceStarted_fuel_eq]
  omega

/-- Data-carrying version of the preceding numerical estimate, suitable for
direct composition with an accepting cursor first hit. -/
theorem dynamicRuleSourceStarted_bounded_radius
    (slot : Bool) (leftTape : List Tape) (hleft : PayloadPathSafe leftTape)
    (rules : List ULogBytecode.RuleCode) (hrules : rules ≠ [])
    (input : List Bool) (outer : List Tape) (head : Tape)
    (right : List Tape) {R : ℕ}
    (hpath : (dynamicRuleReturnPath leftTape rules input).length ≤ R)
    (hrulesBound : rules.length ≤ R) :
    Nonempty (QuantifiedStopFreeRun (2 * R + 2)
      (.running (.ruleSeekChoice slot)
        (beforeLeftPath (dynamicRuleReturnPath leftTape rules input) outer
          (ulogCore pcMark) (head :: right)))
      (dynamicRuleSourceStarted slot leftTape rules input outer head right)) := by
  let run := stopFree_dynamicRuleSourceStarted slot leftTape hleft rules
    hrules input outer head right
  refine ⟨
    { steps := run.1
      le_bound := dynamicRuleSourceStarted_fuel_le_radius slot leftTape hleft
        rules hrules input outer head right hpath hrulesBound
      run := run.2 }⟩

/-- A fully expanded radius charge for the deterministic selected-branch
rule-return/count segment.  This is independent of the later cursor
mismatch machinery. -/
theorem dynamicRuleSourceStarted_fuel_le_radius_expanded
    (slot : Bool) (leftTape : List Tape) (hleft : PayloadPathSafe leftTape)
    (rules : List ULogBytecode.RuleCode) (hrules : rules ≠ [])
    (input : List Bool) (outer : List Tape) (head : Tape)
    (right : List Tape) {R : ℕ}
    (hleftBound : leftTape.length ≤ R)
    (hpayloadBound : (payloadProgramPrefix input).length ≤ R)
    (hencodeBound : (ULogBytecode.encodeRules rules).length ≤ R)
    (hrulesBound : rules.length ≤ R) :
    (stopFree_dynamicRuleSourceStarted slot leftTape hleft rules hrules input
      outer head right).1 ≤ 5 * R + 3 := by
  rw [dynamicRuleSourceStarted_fuel_eq, dynamicRuleReturnPath_length]
  omega

/-- A fixed-state read scan followed by its mismatch turn has exactly one
pass per corridor cell and one turning transition. -/
theorem readHeadMismatch_fuel_eq
    (slot : Bool) (seekState : State) (hseek : seekState ≠ .cycleStart)
    (head : Tape) (path : List Tape)
    (hpass : ∀ x, x ∈ path → ∀ left y right,
      ULogBootstrapExecution.oneStep
        (ULogBootstrapExecution.Result.running seekState ⟨left, x, y :: right⟩) =
        ULogBootstrapExecution.Result.running seekState ⟨x :: left, y, right⟩)
    (hmismatch : ∀ left y right,
      ULogBootstrapExecution.oneStep
        (ULogBootstrapExecution.Result.running seekState ⟨y :: left, head, right⟩) =
        ULogBootstrapExecution.Result.running (.restoreRule slot)
          ⟨left, y, head :: right⟩)
    (left suffix : List Tape) :
    (stopFree_readHeadMismatch_of slot seekState hseek head path hpass
      hmismatch left suffix).1 = path.length + 1 := by
  simp [stopFree_readHeadMismatch_of, StopFreeValidZeroRun.append,
    Nat.add_comm]

/-- Radius form of the preceding primitive. -/
theorem readHeadMismatch_fuel_le_radius
    (slot : Bool) (seekState : State) (hseek : seekState ≠ .cycleStart)
    (head : Tape) (path : List Tape)
    (hpass : ∀ x, x ∈ path → ∀ left y right,
      ULogBootstrapExecution.oneStep
        (ULogBootstrapExecution.Result.running seekState ⟨left, x, y :: right⟩) =
        ULogBootstrapExecution.Result.running seekState ⟨x :: left, y, right⟩)
    (hmismatch : ∀ left y right,
      ULogBootstrapExecution.oneStep
        (ULogBootstrapExecution.Result.running seekState ⟨y :: left, head, right⟩) =
        ULogBootstrapExecution.Result.running (.restoreRule slot)
          ⟨left, y, head :: right⟩)
    (left suffix : List Tape) {R : ℕ} (hpath : path.length ≤ R) :
    (stopFree_readHeadMismatch_of slot seekState hseek head path hpass
      hmismatch left suffix).1 ≤ R + 1 := by
  rw [readHeadMismatch_fuel_eq]
  omega

/-- The read-zero mismatch alternative is a completely explicit linear
subphase: one dispatch followed by the scanned mismatch turn. -/
theorem sourceReadZeroMismatch_bounded
    (slot : Bool) (source : ℕ) (boundary : ULogLetter)
    (base path runtime suffix : List Tape) (actualHead : Tape)
    (hmismatch : actualHead = ulogCore payloadHeadOne ∨
      actualHead = ulogCore payloadHeadBlank)
    (hsafe : ReadCorridorSafe path) :
    Nonempty (QuantifiedStopFreeRun (path.length + 2)
      (sourceReadStartedAt slot source boundary true base
        (path ++ actualHead :: runtime) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath path.reverse
          (readMismatchBaseAt source 0 boundary base)
          (ulogCore readBoundary)
          (actualHead :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)))) := by
  have hstart : StopFreeValidZeroRun 1
      (sourceReadStartedAt slot source boundary true base
        (path ++ actualHead :: runtime) suffix)
      (.running (.readPhase .seekZero slot)
        (beforeRightPath path
          (ulogCore readBoundary :: readMismatchBaseAt source 0 boundary base)
          actualHead
          (runtime ++ List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases path <;> simp [sourceReadStartedAt, readMismatchBaseAt,
        beforeRightPath, fieldCompare_read_zero, codeTape,
        List.append_assoc]
    · cases slot <;> simp [sourceReadStartedAt,
        IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have hmismatchStep : ∀ left y right,
      ULogBootstrapExecution.oneStep
        (ULogBootstrapExecution.Result.running (.readPhase .seekZero slot)
          ⟨y :: left, actualHead, right⟩) =
        ULogBootstrapExecution.Result.running (.restoreRule slot)
          ⟨left, y, actualHead :: right⟩ := by
    intro l y rr
    rcases hmismatch with rfl | rfl
    · exact readSeekZero_one_mismatch slot l y rr
    · exact readSeekZero_blank_mismatch slot l y rr
  let tail := stopFree_readHeadMismatch_of slot
    (.readPhase .seekZero slot) (by intro h; cases h) actualHead path
    (fun x hx l y r =>
      let h := hsafe x hx
      readSeekZero_pass slot x h.1 h.2.1 h.2.2.1 h.2.2.2.1 l y r)
    hmismatchStep (readMismatchBaseAt source 0 boundary base)
    (runtime ++ List.replicate source (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  refine ⟨
    { steps := 1 + tail.1
      le_bound := ?_
      run := hstart.append tail.2 }⟩
  rw [readHeadMismatch_fuel_eq]
  omega

/-- The one-coded read mismatch has two fixed count transitions before the
same scanned mismatch turn. -/
theorem sourceReadOneMismatch_bounded
    (slot : Bool) (source : ℕ) (boundary : ULogLetter)
    (base path runtime suffix : List Tape) (actualHead : Tape)
    (hmismatch : actualHead = ulogCore payloadHeadZero ∨
      actualHead = ulogCore payloadHeadBlank)
    (hsafe : ReadCorridorSafe path) :
    Nonempty (QuantifiedStopFreeRun (path.length + 3)
      (sourceReadStartedAt slot source boundary false base
        (ulogCore codeOne :: path ++ actualHead :: runtime) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath path.reverse
          (readMismatchBaseAt source 1 boundary base)
          (ulogCore readBoundary)
          (actualHead :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)))) := by
  let counted : Result := .running (.readPhase .countOne slot)
    ⟨ulogCore codeZero :: ulogCore codeOne ::
        List.replicate source (ulogCore codeZero) ++ ulogCore boundary :: base,
        ulogCore codeOne,
      path ++ actualHead :: runtime ++ List.replicate source (ulogCore stateZero) ++
        ulogCore stateOne :: suffix⟩
  have h₀ : StopFreeValidZeroRun 1
      (sourceReadStartedAt slot source boundary false base
        (ulogCore codeOne :: path ++ actualHead :: runtime) suffix) counted := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simp [sourceReadStartedAt, fieldCompare_read_more,
        codeTape, List.append_assoc]
    · cases slot <;> simp [sourceReadStartedAt,
        IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have h₁ : StopFreeValidZeroRun 1 counted
      (.running (.readPhase .seekOne slot)
        (beforeRightPath path
          (ulogCore readBoundary :: readMismatchBaseAt source 1 boundary base)
          actualHead
          (runtime ++ List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases path <;> simp [counted, readMismatchBaseAt, beforeRightPath,
        readCountOne_done, List.append_assoc]
    · cases slot <;> simp [counted, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hmismatchStep : ∀ left y right,
      ULogBootstrapExecution.oneStep
        (ULogBootstrapExecution.Result.running (.readPhase .seekOne slot)
          ⟨y :: left, actualHead, right⟩) =
        ULogBootstrapExecution.Result.running (.restoreRule slot)
          ⟨left, y, actualHead :: right⟩ := by
    intro l y rr
    rcases hmismatch with rfl | rfl
    · exact readSeekOne_zero_mismatch slot l y rr
    · exact readSeekOne_blank_mismatch slot l y rr
  let tail := stopFree_readHeadMismatch_of slot
    (.readPhase .seekOne slot) (by intro h; cases h) actualHead path
    (fun x hx l y r =>
      let h := hsafe x hx
      readSeekOne_pass slot x h.1 h.2.1 h.2.2.1 h.2.2.2.1 l y r)
    hmismatchStep (readMismatchBaseAt source 1 boundary base)
    (runtime ++ List.replicate source (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  refine ⟨
    { steps := 2 + tail.1
      le_bound := ?_
      run := (h₀.append h₁).append tail.2 }⟩
  rw [readHeadMismatch_fuel_eq]
  omega

/-- The blank-coded read mismatch has three fixed count transitions before
the same scanned mismatch turn. -/
theorem sourceReadBlankMismatch_bounded
    (slot : Bool) (source : ℕ) (boundary : ULogLetter)
    (base path runtime suffix : List Tape) (actualHead : Tape)
    (hmismatch : actualHead = ulogCore payloadHeadZero ∨
      actualHead = ulogCore payloadHeadOne)
    (hsafe : ReadCorridorSafe path) :
    Nonempty (QuantifiedStopFreeRun (path.length + 4)
      (sourceReadStartedAt slot source boundary false base
        (ulogCore codeZero :: ulogCore codeOne :: path ++ actualHead :: runtime) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath path.reverse
          (readMismatchBaseAt source 2 boundary base)
          (ulogCore readBoundary)
          (actualHead :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)))) := by
  let countedOne : Result := .running (.readPhase .countOne slot)
    ⟨ulogCore codeZero :: ulogCore codeOne ::
        List.replicate source (ulogCore codeZero) ++ ulogCore boundary :: base,
        ulogCore codeZero,
      ulogCore codeOne :: path ++ actualHead :: runtime ++
        List.replicate source (ulogCore stateZero) ++ ulogCore stateOne :: suffix⟩
  let countedTwo : Result := .running (.readPhase .countTwo slot)
    ⟨ulogCore codeZero :: ulogCore codeZero :: ulogCore codeOne ::
        List.replicate source (ulogCore codeZero) ++ ulogCore boundary :: base,
        ulogCore codeOne,
      path ++ actualHead :: runtime ++ List.replicate source (ulogCore stateZero) ++
        ulogCore stateOne :: suffix⟩
  have h₀ : StopFreeValidZeroRun 1
      (sourceReadStartedAt slot source boundary false base
        (ulogCore codeZero :: ulogCore codeOne :: path ++ actualHead :: runtime) suffix)
      countedOne := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simp [sourceReadStartedAt, fieldCompare_read_more,
        codeTape, List.append_assoc]
    · cases slot <;> simp [sourceReadStartedAt,
        IsConcreteCycleStop, IsConcreteCycleBoundary, concreteHalted]
  have h₁ : StopFreeValidZeroRun 1 countedOne countedTwo := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simp [countedOne, readCountOne_more, List.append_assoc]
    · cases slot <;> simp [countedOne, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have h₂ : StopFreeValidZeroRun 1 countedTwo
      (.running (.readPhase .seekBlank slot)
        (beforeRightPath path
          (ulogCore readBoundary :: readMismatchBaseAt source 2 boundary base)
          actualHead
          (runtime ++ List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      cases path <;> simp [countedTwo, readMismatchBaseAt, beforeRightPath,
        readCountTwo_done, List.append_assoc]
    · cases slot <;> simp [countedTwo, IsConcreteCycleStop,
        IsConcreteCycleBoundary, concreteHalted]
  have hmismatchStep : ∀ left y right,
      ULogBootstrapExecution.oneStep
        (ULogBootstrapExecution.Result.running (.readPhase .seekBlank slot)
          ⟨y :: left, actualHead, right⟩) =
        ULogBootstrapExecution.Result.running (.restoreRule slot)
          ⟨left, y, actualHead :: right⟩ := by
    intro l y rr
    rcases hmismatch with rfl | rfl
    · exact readSeekBlank_zero_mismatch slot l y rr
    · exact readSeekBlank_one_mismatch slot l y rr
  let tail := stopFree_readHeadMismatch_of slot
    (.readPhase .seekBlank slot) (by intro h; cases h) actualHead path
    (fun x hx l y r =>
      let h := hsafe x hx
      readSeekBlank_pass slot x h.1 h.2.1 h.2.2.1 h.2.2.2.1 l y r)
    hmismatchStep (readMismatchBaseAt source 2 boundary base)
    (runtime ++ List.replicate source (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  refine ⟨
    { steps := 3 + tail.1
      le_bound := ?_
      run := ((h₀.append h₁).append h₂).append tail.2 }⟩
  rw [readHeadMismatch_fuel_eq]
  omega

/-- Uniform bounded dispatch over the six legal unequal read/actual pairs.
The three previous constructions give the literal paths; this theorem only
normalizes their common encoded input/output shapes and takes the finite
maximum `|path| + 4`. -/
theorem sourceReadMismatch_bounded
    (slot : Bool) (source read actual : ℕ)
    (hread : read < 3) (hactual : actual < 3) (hne : read ≠ actual)
    (boundary : ULogLetter) (base path runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe path) :
    Nonempty (QuantifiedStopFreeRun (path.length + 4)
      (sourceReadStartedAt slot source boundary (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          path ++ readHeadNat actual :: runtime) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath (readMismatchRestorePath source read path)
          base (ulogCore boundary)
          (readHeadNat actual :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)))) := by
  interval_cases read <;> interval_cases actual
  all_goals try omega
  · obtain ⟨h⟩ := sourceReadZeroMismatch_bounded slot source boundary
      base path runtime suffix (ulogCore payloadHeadOne) (Or.inl rfl) hsafe
    rcases h with ⟨n, hn, hrun⟩
    rw [readMismatch_beforeLeft_eq] at hrun
    exact ⟨
      { steps := n
        le_bound := by omega
        run := by simpa [ULogBytecode.encodeNatField, unaryFieldFirst,
          readHeadNat, codeTape, List.append_assoc] using hrun }⟩

  · obtain ⟨h⟩ := sourceReadZeroMismatch_bounded slot source boundary
      base path runtime suffix (ulogCore payloadHeadBlank) (Or.inr rfl) hsafe
    rcases h with ⟨n, hn, hrun⟩
    rw [readMismatch_beforeLeft_eq] at hrun
    exact ⟨
      { steps := n
        le_bound := by omega
        run := by simpa [ULogBytecode.encodeNatField, unaryFieldFirst,
          readHeadNat, codeTape, List.append_assoc] using hrun }⟩
  · obtain ⟨h⟩ := sourceReadOneMismatch_bounded slot source boundary
      base path runtime suffix (ulogCore payloadHeadZero) (Or.inl rfl) hsafe
    rcases h with ⟨n, hn, hrun⟩
    rw [readMismatch_beforeLeft_eq] at hrun
    exact ⟨
      { steps := n
        le_bound := by omega
        run := by simpa [ULogBytecode.encodeNatField, unaryFieldFirst,
          readHeadNat, codeTape, List.append_assoc] using hrun }⟩
  · obtain ⟨h⟩ := sourceReadOneMismatch_bounded slot source boundary
      base path runtime suffix (ulogCore payloadHeadBlank) (Or.inr rfl) hsafe
    rcases h with ⟨n, hn, hrun⟩
    rw [readMismatch_beforeLeft_eq] at hrun
    exact ⟨
      { steps := n
        le_bound := by omega
        run := by simpa [ULogBytecode.encodeNatField, unaryFieldFirst,
          readHeadNat, codeTape, List.append_assoc] using hrun }⟩
  · obtain ⟨h⟩ := sourceReadBlankMismatch_bounded slot source boundary
      base path runtime suffix (ulogCore payloadHeadZero) (Or.inl rfl) hsafe
    rcases h with ⟨n, hn, hrun⟩
    rw [readMismatch_beforeLeft_eq] at hrun
    exact ⟨
      { steps := n
        le_bound := by omega
        run := by simpa [ULogBytecode.encodeNatField, unaryFieldFirst,
          readHeadNat, codeTape, List.append_assoc] using hrun }⟩
  · obtain ⟨h⟩ := sourceReadBlankMismatch_bounded slot source boundary
      base path runtime suffix (ulogCore payloadHeadOne) (Or.inr rfl) hsafe
    rcases h with ⟨n, hn, hrun⟩
    rw [readMismatch_beforeLeft_eq] at hrun
    exact ⟨
      { steps := n
        le_bound := by omega
        run := by simpa [ULogBytecode.encodeNatField, unaryFieldFirst,
          readHeadNat, codeTape, List.append_assoc] using hrun }⟩

/-- Radius specialization of all legal unequal read/actual dispatches. -/
theorem sourceReadMismatch_bounded_radius
    (slot : Bool) (source read actual : ℕ)
    (hread : read < 3) (hactual : actual < 3) (hne : read ≠ actual)
    (boundary : ULogLetter) (base path runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe path) {R : ℕ} (hpath : path.length ≤ R) :
    Nonempty (QuantifiedStopFreeRun (R + 4)
      (sourceReadStartedAt slot source boundary (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          path ++ readHeadNat actual :: runtime) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath (readMismatchRestorePath source read path)
          base (ulogCore boundary)
          (readHeadNat actual :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)))) := by
  obtain ⟨run⟩ := sourceReadMismatch_bounded slot source read actual
    hread hactual hne boundary base path runtime suffix hsafe
  exact ⟨
    { steps := run.steps
      le_bound := run.le_bound.trans (by omega)
      run := run.run }⟩

/-- First half of restoration/advance: restoring a mismatch corridor is one
mapped left scan plus the boundary turn. -/
theorem restoreRuleBoundary_fuel_eq
    (slot : Bool) (path : List Tape) (hpath : MismatchRestorePathSafe path)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (outer : List Tape) (pcSide : Tape) (right : List Tape) :
    (stopFree_restoreRule_boundary slot path hpath boundary hboundary outer
      pcSide right).1 = path.length + 1 := by
  simp [stopFree_restoreRule_boundary, StopFreeValidZeroRun.append,
    Nat.add_comm]

/-- Second half starts by returning across a concrete path and one control
turn; this exact formula is independent of the subsequent rule skip. -/
theorem mismatchReturnToPc_fuel_eq
    (slot : Bool) (path : List Tape)
    (hpath : ∀ x ∈ path, x ≠ ulogCore pcMark)
    (outer : List Tape) (y : Tape) (right : List Tape) :
    (stopFree_mismatchReturnToPc slot path hpath outer y right).1 =
      path.length + 1 := by
  simp [stopFree_mismatchReturnToPc, StopFreeValidZeroRun.append,
    Nat.add_comm]

/-- One matched source-comparison round makes a right and a left pass over
the same explicit comparison corridor, with three control transitions. -/
theorem sourceCompareRound_fuel_eq
    (slot : Bool) (remaining done : ℕ) (corridor : List Tape)
    (hseek : ∀ x ∈ sourceCompareScanPath remaining corridor done,
      x ≠ ulogCore stateZero ∧ x ≠ ulogCore stateOne ∧
        x ≠ MStarConcreteAlphabet.work)
    (hreturn : ∀ x ∈ sourceCompareScanPath remaining corridor done,
      x ≠ ulogCore sourceMark ∧ x ≠ ulogCore pcMark)
    (left stateRest : List Tape) :
    (stopFree_sourceCompareRound slot remaining done corridor hseek hreturn
      left stateRest).1 =
      2 * (sourceCompareScanPath remaining corridor done).length + 3 := by
  simp [stopFree_sourceCompareRound, StopFreeValidZeroRun.append,
    List.length_reverse, Nat.two_mul, Nat.add_left_comm, Nat.add_comm]
  omega

/-- The comparison scan length is exactly its two unary fields, one separator,
and the fixed rule corridor. -/
theorem sourceCompareScanPath_length
    (remaining done : ℕ) (corridor : List Tape) :
    (sourceCompareScanPath remaining corridor done).length =
      remaining + corridor.length + 1 + done := by
  simp [sourceCompareScanPath, Nat.add_left_comm, Nat.add_comm]

/-- Radius specialization of a single source-comparison round. -/
theorem sourceCompareRound_fuel_le_radius
    (slot : Bool) (remaining done : ℕ) (corridor : List Tape)
    (hseek : ∀ x ∈ sourceCompareScanPath remaining corridor done,
      x ≠ ulogCore stateZero ∧ x ≠ ulogCore stateOne ∧
        x ≠ MStarConcreteAlphabet.work)
    (hreturn : ∀ x ∈ sourceCompareScanPath remaining corridor done,
      x ≠ ulogCore sourceMark ∧ x ≠ ulogCore pcMark)
    (left stateRest : List Tape) {R : ℕ}
    (hremaining : remaining ≤ R) (hdone : done ≤ R)
    (hcorridor : corridor.length ≤ R) :
    (stopFree_sourceCompareRound slot remaining done corridor hseek hreturn
      left stateRest).1 ≤ 6 * R + 5 := by
  rw [sourceCompareRound_fuel_eq, sourceCompareScanPath_length]
  omega

/-- A reconstructed, bounded version of the recursive matched-zero source
comparison.  Unlike the older sigma-valued helper, the statement retains its
quadratic literal fuel certificate. -/
theorem sourceCompareZeros_bounded
    (slot : Bool) (remaining done : ℕ) (corridor : List Tape)
    (hcorridor : SourceCompareCorridorSafe corridor)
    (left suffix : List Tape) :
    Nonempty (QuantifiedStopFreeRun
      (remaining * (2 * (remaining + done + corridor.length) + 3))
      (sourceCompareStart slot remaining done corridor left suffix)
      (sourceCompareAllMarked slot remaining done corridor left suffix)) := by
  induction remaining generalizing done left with
  | zero =>
      exact ⟨
        { steps := 0
          le_bound := by simp
          run :=
            { valid := .nil _
              stop_free := by intro m hm; simp at hm } }⟩
  | succ remaining ih =>
      let round := stopFree_sourceCompareRound slot remaining done corridor
        (fun x hx => sourceCompareScanPath_seek_safe hcorridor hx)
        (fun x hx => sourceCompareScanPath_return_safe hcorridor hx)
        left
        (List.replicate remaining (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)
      obtain ⟨tail⟩ := ih (done + 1) (ulogCore sourceMark :: left)
      have htail' : StopFreeValidZeroRun tail.steps
          (.running (.fieldCompare .source slot)
            (beforeRightPath (sourceCompareScanPath remaining corridor done)
              (ulogCore sourceMark :: left) (ulogCore stateMark)
              (List.replicate remaining (ulogCore stateZero) ++
                ulogCore stateOne :: suffix)))
          (sourceCompareAllMarked slot remaining (done + 1) corridor
            (ulogCore sourceMark :: left) suffix) := by
        cases remaining <;>
          simpa [sourceCompareStart, sourceCompareScanPath, beforeRightPath,
            List.replicate_succ, List.replicate_succ',
            List.append_assoc] using tail.run
      have hroundFuel : round.1 =
          2 * (sourceCompareScanPath remaining corridor done).length + 3 := by
        simpa [round] using sourceCompareRound_fuel_eq slot remaining done
          corridor
          (fun x hx => sourceCompareScanPath_seek_safe hcorridor hx)
          (fun x hx => sourceCompareScanPath_return_safe hcorridor hx)
          left
          (List.replicate remaining (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)
      refine ⟨
        { steps := round.1 + tail.steps
          le_bound := ?_
          run := by
            cases remaining <;>
              simpa [sourceCompareStart, sourceCompareScanPath,
                sourceCompareAllMarked,
                beforeRightPath, List.replicate_succ,
                List.replicate_succ', List.append_assoc,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                round.2.append htail' }⟩
      rw [hroundFuel, sourceCompareScanPath_length]
      have htailBound := tail.le_bound
      calc
        2 * (remaining + corridor.length + 1 + done) + 3 + tail.steps ≤
            2 * (remaining + corridor.length + 1 + done) + 3 +
              remaining * (2 * (remaining + (done + 1) + corridor.length) + 3) :=
          Nat.add_le_add_left htailBound _
        _ = (remaining + 1) *
            (2 * (remaining + 1 + done + corridor.length) + 3) := by
          ring

/-- Radius-specialized quadratic certificate for the complete matched-zero
source comparison. -/
theorem sourceCompareZeros_bounded_radius
    (slot : Bool) (remaining done : ℕ) (corridor : List Tape)
    (hcorridor : SourceCompareCorridorSafe corridor)
    (left suffix : List Tape) {R : ℕ}
    (hremaining : remaining ≤ R) (hdone : done ≤ R)
    (hcorridorBound : corridor.length ≤ R) :
    Nonempty (QuantifiedStopFreeRun (6 * R ^ 2 + 3 * R)
      (sourceCompareStart slot remaining done corridor left suffix)
      (sourceCompareAllMarked slot remaining done corridor left suffix)) := by
  obtain ⟨run⟩ := sourceCompareZeros_bounded slot remaining done corridor
    hcorridor left suffix
  refine ⟨{ steps := run.steps, le_bound := ?_, run := run.run }⟩
  apply run.le_bound.trans
  nlinarith

/-- Bounded common-prefix comparison for unequal unary source fields.  Each
round costs at most `6R+5`, and the recursion performs exactly at most
`min source current` rounds. -/
theorem sourceCompareCommon_bounded_radius
    (slot : Bool) (source current done : ℕ) (corridor : List Tape)
    (hcorridor : SourceCompareCorridorSafe corridor)
    (left suffix : List Tape) {R : ℕ}
    (hsource : source ≤ R) (hcurrent : current ≤ R)
    (hbudget : done + min source current ≤ R)
    (hcorridorBound : corridor.length ≤ R) :
    Nonempty (QuantifiedStopFreeRun (min source current * (6 * R + 5))
      (sourceCompareStartAgainst slot source current done corridor left suffix)
      (sourceCompareStartAgainst slot (source - current) (current - source)
        (done + min source current) corridor
        (List.replicate (min source current) (ulogCore sourceMark) ++ left)
        suffix)) := by
  induction source generalizing current done left with
  | zero =>
      exact ⟨
        { steps := 0
          le_bound := by simp
          run := by
            simpa using (show StopFreeValidZeroRun 0
              (sourceCompareStartAgainst slot 0 current done corridor left suffix)
              (sourceCompareStartAgainst slot 0 current done corridor left suffix) from
                { valid := .nil _
                  stop_free := by intro m hm; simp at hm }) }⟩
  | succ source ih =>
      cases current with
      | zero =>
          exact ⟨
            { steps := 0
              le_bound := by simp
              run := by
                simpa using (show StopFreeValidZeroRun 0
                  (sourceCompareStartAgainst slot (source + 1) 0 done
                    corridor left suffix)
                  (sourceCompareStartAgainst slot (source + 1) 0 done
                    corridor left suffix) from
                    { valid := .nil _
                      stop_free := by intro m hm; simp at hm }) }⟩
      | succ current =>
          let round := stopFree_sourceCompareRound slot source done corridor
            (fun x hx => sourceCompareScanPath_seek_safe hcorridor hx)
            (fun x hx => sourceCompareScanPath_return_safe hcorridor hx)
            left
            (List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)
          have hsource' : source ≤ R := by omega
          have hcurrent' : current ≤ R := by omega
          have hbudget' : done + 1 + min source current ≤ R := by
            omega
          obtain ⟨tail⟩ := ih current (done + 1)
            (ulogCore sourceMark :: left) hsource' hcurrent' hbudget'
          have htail' : StopFreeValidZeroRun tail.steps
              (.running (.fieldCompare .source slot)
                (beforeRightPath (sourceCompareScanPath source corridor done)
                  (ulogCore sourceMark :: left) (ulogCore stateMark)
                  (List.replicate current (ulogCore stateZero) ++
                    ulogCore stateOne :: suffix)))
              (sourceCompareStartAgainst slot (source - current)
                (current - source) (done + 1 + min source current) corridor
                (List.replicate (min source current) (ulogCore sourceMark) ++
                  ulogCore sourceMark :: left) suffix) := by
            cases source <;> cases current <;>
              simpa [sourceCompareStartAgainst, sourceCompareScanPath,
                beforeRightPath, List.replicate_succ,
                List.replicate_succ', Nat.add_comm, Nat.add_left_comm,
                List.append_assoc] using tail.run
          have hroundFuel : round.1 =
              2 * (sourceCompareScanPath source corridor done).length + 3 := by
            dsimp [round]
            exact sourceCompareRound_fuel_eq slot source done corridor
              (fun x hx => sourceCompareScanPath_seek_safe hcorridor hx)
              (fun x hx => sourceCompareScanPath_return_safe hcorridor hx)
              left
              (List.replicate current (ulogCore stateZero) ++
                ulogCore stateOne :: suffix)
          have hroundBound : round.1 ≤ 6 * R + 5 := by
            rw [hroundFuel, sourceCompareScanPath_length]
            have hdone : done ≤ R := by omega
            omega
          have hall := round.2.append htail'
          refine ⟨
            { steps := round.1 + tail.steps
              le_bound := ?_
              run := by
                simpa [Nat.succ_sub_succ_eq_sub,
                  sourceCompareStartAgainst, sourceCompareScanPath,
                  List.replicate_succ, List.replicate_succ',
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
                  List.append_assoc] using hall }⟩
          have ht := tail.le_bound
          rw [Nat.succ_min_succ]
          calc
            round.1 + tail.steps ≤ (6 * R + 5) +
                min source current * (6 * R + 5) :=
              Nat.add_le_add hroundBound ht
            _ = (min source current + 1) * (6 * R + 5) := by ring

/-- Coarser polynomial form of the common comparison, convenient for the
four-way cursor case split. -/
theorem sourceCompareCommon_bounded_radius_quadratic
    (slot : Bool) (source current done : ℕ) (corridor : List Tape)
    (hcorridor : SourceCompareCorridorSafe corridor)
    (left suffix : List Tape) {R : ℕ}
    (hsource : source ≤ R) (hcurrent : current ≤ R)
    (hbudget : done + min source current ≤ R)
    (hcorridorBound : corridor.length ≤ R) :
    Nonempty (QuantifiedStopFreeRun (6 * R ^ 2 + 5 * R)
      (sourceCompareStartAgainst slot source current done corridor left suffix)
      (sourceCompareStartAgainst slot (source - current) (current - source)
        (done + min source current) corridor
        (List.replicate (min source current) (ulogCore sourceMark) ++ left)
        suffix)) := by
  obtain ⟨run⟩ := sourceCompareCommon_bounded_radius slot source current done
    corridor hcorridor left suffix hsource hcurrent hbudget hcorridorBound
  refine ⟨{ steps := run.steps, le_bound := ?_, run := run.run }⟩
  apply run.le_bound.trans
  nlinarith [Nat.min_le_left source current]

/-- Exact tails after the common unary prefix in the two strict source-length
mismatch directions. -/
theorem sourceShortMismatch_restore_fuel_eq
    (slot : Bool) (done extra : ℕ) (corridor : List Tape)
    (hcorridor : SourceCompareCorridorSafe corridor)
    (boundary : Tape) (pcBase suffix : List Tape) :
    (stopFree_sourceShortMismatch_restore slot done extra corridor hcorridor
      boundary pcBase suffix).1 = corridor.length + done + 2 := by
  simp [stopFree_sourceShortMismatch_restore, sourceShortFinishPath,
    StopFreeValidZeroRun.append, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]
  omega

theorem sourceLongMismatch_restore_fuel_eq
    (slot : Bool) (done extra : ℕ) (corridor : List Tape)
    (hcorridor : SourceCompareCorridorSafe corridor)
    (boundary : Tape) (pcBase suffix : List Tape) :
    (stopFree_sourceLongMismatch_restore slot done extra corridor hcorridor
      boundary pcBase suffix).1 = extra + corridor.length + done + 3 := by
  simp [stopFree_sourceLongMismatch_restore, sourceLongSeekPath,
    sourceCompareScanPath, StopFreeValidZeroRun.append,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  omega

/-- Explicit lengths of the finish and restoration corridors following a
matched source comparison. -/
theorem sourceFinishPath_length (q : ℕ) (corridor : List Tape) :
    (sourceFinishPath q corridor).length = corridor.length + q := by
  simp [sourceFinishPath]

theorem sourceRestorePath_length (q : ℕ) (corridor : List Tape) :
    (sourceRestorePath q corridor).length = corridor.length + 2 * q + 1 := by
  simp [sourceRestorePath, sourceFinishPath, List.length_reverse,
    Nat.two_mul, Nat.add_left_comm, Nat.add_comm]
  omega

/-- Reconstructed bounded source-match/restore phase.  This is the shared
quadratic core used by all four rule-cursor mismatch alternatives. -/
theorem sourceMatchRestored_bounded_radius
    (slot : Bool) (q : ℕ) (corridor : List Tape)
    (hcorridor : SourceCompareCorridorSafe corridor)
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (base suffix : List Tape) {R : ℕ}
    (hq : q ≤ R) (hcorridorBound : corridor.length ≤ R) :
    Nonempty (QuantifiedStopFreeRun (6 * R ^ 2 + 8 * R + 4)
      (sourceCompareStart slot q 0 corridor (ulogCore boundary :: base) suffix)
      (sourceFieldRestoredAt slot q boundary base corridor suffix)) := by
  obtain ⟨zeros⟩ := sourceCompareZeros_bounded_radius slot q 0 corridor
    hcorridor (ulogCore boundary :: base) suffix hq (by omega) hcorridorBound
  let finishPath := sourceFinishPath q corridor
  let restorePath := sourceRestorePath q corridor
  have hstart : StopFreeValidZeroRun 1
      (sourceCompareAllMarked slot q 0 corridor
        (ulogCore boundary :: base) suffix)
      (.running (.compareFinishSource slot)
        (beforeRightPath finishPath
          (ulogCore codeOne :: List.replicate q (ulogCore sourceMark) ++
            ulogCore boundary :: base)
          (ulogCore stateOne) suffix)) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      rw [show sourceCompareAllMarked slot q 0 corridor
            (ulogCore boundary :: base) suffix =
          .running (.fieldCompare .source slot)
            ⟨List.replicate q (ulogCore sourceMark) ++
                ulogCore boundary :: base,
              ulogCore codeOne, finishPath ++ ulogCore stateOne :: suffix⟩ by
        simp [sourceCompareAllMarked, finishPath, sourceFinishPath]]
      cases he : finishPath with
      | nil => simpa [beforeRightPath, he] using
          (fieldCompare_source_one slot
            (List.replicate q (ulogCore sourceMark) ++
              ulogCore boundary :: base) (ulogCore stateOne) suffix)
      | cons x xs => simpa [beforeRightPath, he, List.append_assoc] using
          (fieldCompare_source_one slot
            (List.replicate q (ulogCore sourceMark) ++
              ulogCore boundary :: base) x
            (xs ++ ulogCore stateOne :: suffix))
    · cases slot <;>
        simp [sourceCompareAllMarked, IsConcreteCycleStop,
          IsConcreteCycleBoundary, concreteHalted]
  have hfinishScan := stopFree_rightPath_of (.compareFinishSource slot)
    (by intro h; cases h) finishPath (by
      intro x hx l y r
      unfold finishPath sourceFinishPath at hx
      rcases List.mem_append.mp hx with hc | hs
      · have h := hcorridor x hc
        exact compareFinishSource_pass slot x h.2.2.2.2.2.1 h.1
          h.2.1 h.2.2.1 l y r
      · have heq : x = ulogCore stateMark :=
          (by simpa only [List.mem_replicate] using hs :
            q ≠ 0 ∧ x = ulogCore stateMark).2
        rw [heq]
        exact compareFinishSource_mark slot l y r)
    (ulogCore codeOne :: List.replicate q (ulogCore sourceMark) ++
      ulogCore boundary :: base) (ulogCore stateOne) suffix
  have hturn : StopFreeValidZeroRun 1
      (.running (.compareFinishSource slot)
        (afterRightPath finishPath
          (ulogCore codeOne :: List.replicate q (ulogCore sourceMark) ++
            ulogCore boundary :: base) (ulogCore stateOne) suffix))
      (.running (.compareRestoreSource slot)
        (beforeLeftPath restorePath base (ulogCore boundary)
          (ulogCore stateOne :: suffix))) := by
    apply StopFreeValidZeroRun.one
    · apply validStepAt_zero_of_oneStep_running
      simpa [finishPath, restorePath, sourceRestorePath, afterRightPath,
        List.append_assoc] using
        compareFinishSource_one_over_path slot restorePath base
          (ulogCore boundary) suffix
    · cases slot <;>
        simp [IsConcreteCycleStop,
          IsConcreteCycleBoundary, concreteHalted]
  have hrestore := stopFree_leftPathMap_of (.compareRestoreSource slot)
    (by intro h; cases h) restorePath restoreSourceCell (by
      intro x hx l y r
      have hsafe := sourceRestorePath_safe q corridor hcorridor
        (by simpa [restorePath] using hx)
      exact compareRestoreSource_step slot x hsafe.1 hsafe.2.1
        hsafe.2.2.1 hsafe.2.2.2 l y r)
    base (ulogCore boundary) (ulogCore stateOne :: suffix)
  have hend : StopFreeValidZeroRun 1
      (.running (.compareRestoreSource slot)
        (afterLeftPathMap restorePath restoreSourceCell base
          (ulogCore boundary) (ulogCore stateOne :: suffix)))
      (sourceFieldRestoredAt slot q boundary base corridor suffix) := by
    have hmap : restorePath.reverse.map restoreSourceCell =
        List.replicate q (ulogCore codeZero) ++ ulogCore codeOne ::
          corridor ++ List.replicate q (ulogCore stateZero) := by
      simpa [restorePath] using sourceRestorePath_map q corridor hcorridor
    rw [show afterLeftPathMap restorePath restoreSourceCell base
          (ulogCore boundary) (ulogCore stateOne :: suffix) =
        ⟨base, ulogCore boundary,
          List.replicate q (ulogCore codeZero) ++ ulogCore codeOne ::
            corridor ++ List.replicate q (ulogCore stateZero) ++
              ulogCore stateOne :: suffix⟩ by
      simp [afterLeftPathMap, hmap, List.append_assoc]]
    apply StopFreeValidZeroRun.one
    · rcases hboundary with rfl | rfl | rfl <;> cases q <;>
        apply validStepAt_zero_of_oneStep_running <;>
        simp [List.replicate_succ, List.append_assoc,
          compareRestoreSource_boundary, compareRestoreSource_boundaryZero,
          compareRestoreSource_boundaryOne]
    · cases slot <;> cases q <;>
        simp [IsConcreteCycleStop,
          IsConcreteCycleBoundary, concreteHalted]
  refine ⟨
    { steps := zeros.steps + 1 + finishPath.length + 1 + restorePath.length + 1
      le_bound := ?_
      run := (((zeros.run.append hstart).append hfinishScan).append hturn).append
        hrestore |>.append hend }⟩
  rw [sourceFinishPath_length, sourceRestorePath_length]
  have hz := zeros.le_bound
  nlinarith

/-- Quantitative matched-source decoder, including the unary delimiter that
enters the read selector.  This removes the `Classical.choice` fuel erasure
from `stopFree_ruleCursorSourceMatch_read`. -/
theorem ruleCursorSourceMatch_read_bounded_radius
    (slot : Bool) (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead base : List Tape) (head : Tape)
    (runtime suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead head runtime))
    {R : ℕ} (hsource : r.source ≤ R)
    (hcorridorBound :
      (cursorRuleCorridor r rs programToHead head runtime).length ≤ R) :
    Nonempty (QuantifiedStopFreeRun (6 * R ^ 2 + 9 * R + 5)
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: base)
        (programToHead ++ head :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (sourceReadStartedAt slot r.source boundary
        (unaryFieldFirst r.read) base
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          codeTape r.slot :: encodedActionPath r.action.write
            r.action.target r.action.move
              (cursorMatchedMovePath rs programToHead) ++ head :: runtime)
        suffix)) := by
  let corridor := cursorRuleCorridor r rs programToHead head runtime
  obtain ⟨sourceRun⟩ := sourceMatchRestored_bounded_radius slot r.source
    corridor hcorridor boundary hboundary base suffix hsource hcorridorBound
  have hstart :
      atBitsTail (.fieldCompare .source slot)
          (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: base)
          (programToHead ++ head :: runtime ++
            List.replicate r.source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix) =
        sourceCompareStart slot r.source 0 corridor
          (ulogCore boundary :: base) suffix := by
    rw [atBitsTail_encodeRules_cons_source]
    cases r.source <;>
      simp [corridor, sourceCompareStartAgainst, sourceCompareStart,
        cursorRuleCorridor, List.append_assoc]
  have sourceRun' : StopFreeValidZeroRun sourceRun.steps
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: base)
        (programToHead ++ head :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (sourceFieldRestoredAt slot r.source boundary base corridor suffix) := by
    rw [hstart]
    exact sourceRun.run
  have hcorridorEq : corridor =
      codeTape (unaryFieldFirst r.read) ::
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          codeTape r.slot :: encodedActionPath r.action.write
            r.action.target r.action.move
              (cursorMatchedMovePath rs programToHead) ++ head :: runtime) := by
    rcases r with ⟨source, read, ruleSlot, ⟨write, target, move⟩⟩
    cases read <;> simp [corridor, cursorRuleCorridor,
      ruleContinuationCorridor, cursorMatchedMovePath, encodedActionPath,
      ULogBytecode.encodeNatField, ULogBytecode.encodeAction,
      encodeMove_eq, moveBits, unaryFieldFirst, List.replicate_succ,
      List.map_append, codeTape, List.append_assoc]
  let readRun := stopFree_sourceFieldRestoredAt_read slot r.source boundary
    (unaryFieldFirst r.read) base
    ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
      codeTape r.slot :: encodedActionPath r.action.write r.action.target
        r.action.move (cursorMatchedMovePath rs programToHead) ++ head :: runtime)
    suffix
  have hreadFuel : readRun.1 = r.source + 1 := by
    dsimp [readRun]
    exact sourceFieldRestoredAt_read_fuel_eq slot r.source boundary
      (unaryFieldFirst r.read) base
      ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
        codeTape r.slot :: encodedActionPath r.action.write r.action.target
          r.action.move (cursorMatchedMovePath rs programToHead) ++
            head :: runtime) suffix
  have readRun' : StopFreeValidZeroRun readRun.1
      (sourceFieldRestoredAt slot r.source boundary base corridor suffix)
      (sourceReadStartedAt slot r.source boundary
        (unaryFieldFirst r.read) base
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          codeTape r.slot :: encodedActionPath r.action.write
            r.action.target r.action.move
              (cursorMatchedMovePath rs programToHead) ++ head :: runtime)
        suffix) := by
    rw [hcorridorEq]
    exact readRun.2
  refine ⟨
    { steps := sourceRun.steps + readRun.1
      le_bound := ?_
      run := sourceRun'.append readRun' }⟩
  rw [hreadFuel]
  have hs := sourceRun.le_bound
  omega

/-- A matched target-zero cursor leaf now has a fully explicit quadratic
first-stop bound.  The three charged pieces are the source decoder, matched
read dispatch, and write/target-zero accepting suffix. -/
theorem ruleCursorMatchedTargetZero_firstStop_steps_le_radius
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead base runtime : List Tape) (htarget : r.action.target = 0)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs programToHead))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: runtime))
    (tail : List Tape) {R : ℕ}
    (hsource : r.source ≤ R)
    (hsourceCorridor :
      (cursorRuleCorridor r rs programToHead
        (readHeadNat r.read) runtime).length ≤ R)
    (hreadCorridor :
      (encodedActionPath r.action.write r.action.target r.action.move
        (cursorMatchedMovePath rs programToHead)).length ≤ R)
    (hactionCorridor :
      (moveBits r.action.move ++
        cursorMatchedMovePath rs programToHead).length ≤ R)
    (htargetCorridor :
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: runtime).length ≤ R) :
    (ruleCursorMatchedTargetZero_firstStop boundary hboundary r rs
      programToHead base runtime htarget hread hwrite hcorridor hreadPath
      hwritePath htargetPath tail).2.steps ≤ 6 * R ^ 2 + 14 * R + 22 := by
  let actionCorridor :=
    moveBits r.action.move ++ cursorMatchedMovePath rs programToHead
  obtain ⟨sourceRun⟩ := ruleCursorSourceMatch_read_bounded_radius r.slot
    boundary hboundary r rs programToHead base (readHeadNat r.read) runtime
    (ulogCore stateSep :: tail) hcorridor hsource hsourceCorridor
  obtain ⟨readRun⟩ := sourceReadAtValid_actionWrite_bounded_radius r.slot
    r.source r.read r.action.write r.action.target boundary r.action.move
    hread hwrite base (cursorMatchedMovePath rs programToHead) runtime
    (ulogCore stateSep :: tail) hreadPath hreadCorridor
  have hwritePath' : ActionWriteCorridorSafe
      (ulogCore codeOne :: actionCorridor) := by
    simpa [actionCorridor, htarget] using hwritePath
  let actionHit := actionWriteTargetZero_firstStop r.action.write r.source
    hwrite (readHeadNat r.read)
    (by interval_cases r.read <;> decide)
    actionCorridor runtime hwritePath' (by
      simpa [actionCorridor, List.append_assoc] using htargetPath)
    (matchedReadLeftAt r.slot r.source r.read boundary base) tail
  have haction : actionHit.2.steps ≤ 3 * R + 9 := by
    dsimp [actionHit]
    exact actionWriteTargetZero_firstStop_steps_le_radius
      r.action.write r.source hwrite (readHeadNat r.read)
      (by interval_cases r.read <;> decide)
      actionCorridor runtime hwritePath'
      (by simpa [actionCorridor, List.append_assoc] using htargetPath)
      (matchedReadLeftAt r.slot r.source r.read boundary base) tail
      hactionCorridor
      (by simpa [actionCorridor, List.append_assoc] using htargetCorridor)
  have readRun' : StopFreeValidZeroRun readRun.steps
      (sourceReadStartedAt r.slot r.source boundary
        (unaryFieldFirst r.read) base
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          codeTape r.slot :: encodedActionPath r.action.write
            r.action.target r.action.move
              (cursorMatchedMovePath rs programToHead) ++
            readHeadNat r.read :: runtime)
        (ulogCore stateSep :: tail))
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read boundary base)
        (ulogCore codeOne :: actionCorridor) (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: ulogCore stateSep :: tail)) := by
    simpa [actionCorridor, htarget] using readRun.run
  let candidate := (sourceRun.run.append readRun').appendFirstHit actionHit.2
  have heq :=
    (ruleCursorMatchedTargetZero_firstStop boundary hboundary r rs
      programToHead base runtime htarget hread hwrite hcorridor hreadPath
      hwritePath htargetPath tail).2.steps_eq candidate
  calc
    _ = candidate.steps := heq
    _ = sourceRun.steps + readRun.steps + actionHit.2.steps := rfl
    _ ≤ 6 * R ^ 2 + 14 * R + 22 := by
      have hs := sourceRun.le_bound
      have hr := readRun.le_bound
      omega

/-- Shared matched-rule prefix used by every nonterminal target/move branch.
It stops at the common `actionWriteStart` configuration, before any target
comparison or move-specific geometry. -/
theorem ruleCursorMatched_actionWrite_bounded_radius
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead base runtime : List Tape)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (cursorMatchedMovePath rs programToHead)))
    (tail : List Tape) {R : ℕ}
    (hsource : r.source ≤ R)
    (hsourceCorridor :
      (cursorRuleCorridor r rs programToHead
        (readHeadNat r.read) runtime).length ≤ R)
    (hreadCorridor :
      (encodedActionPath r.action.write r.action.target r.action.move
        (cursorMatchedMovePath rs programToHead)).length ≤ R) :
    Nonempty (QuantifiedStopFreeRun (6 * R ^ 2 + 11 * R + 13)
      (atBitsTail (.fieldCompare .source r.slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: base)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: tail))
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read boundary base)
        (List.replicate r.action.target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits r.action.move ++
            cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: tail))) := by
  obtain ⟨sourceRun⟩ := ruleCursorSourceMatch_read_bounded_radius r.slot
    boundary hboundary r rs programToHead base (readHeadNat r.read) runtime
    tail hcorridor hsource hsourceCorridor
  obtain ⟨readRun⟩ := sourceReadAtValid_actionWrite_bounded_radius r.slot
    r.source r.read r.action.write r.action.target boundary r.action.move
    hread hwrite base (cursorMatchedMovePath rs programToHead) runtime tail
    hreadPath hreadCorridor
  refine ⟨
    { steps := sourceRun.steps + readRun.steps
      le_bound := ?_
      run := sourceRun.run.append readRun.run }⟩
  have hs := sourceRun.le_bound
  have hr := readRun.le_bound
  omega

/-! ## Uniform mismatch-advance radius bound -/

/-- A complete restore/count/skip transition to the next rule has a uniform
linear physical budget.  The literal ledger is

`|restorePath| + 2*done + 2*|path| + |encodeRule r| + 5`.

The proof constructs this indexed run directly.  In particular, it does not
erase the fuel hidden in the older sigma-valued reachability helper. -/
theorem restoreMismatchAdvanceRule_bounded_radius
    (lookupSlot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe path) (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (restorePath : List Tape)
    (hrestoreSafe : MismatchRestorePathSafe restorePath)
    (mismatchRight : List Tape) (r : ULogBytecode.RuleCode)
    (next : List Bool) (hnext : next ≠ [])
    (outer : List Tape) (after : Tape) (right : List Tape)
    (hrestored : restorePath.reverse.map restoreMismatchCell ++ mismatchRight =
      (ULogBytecode.encodeRule r ++ next).map codeTape ++ after :: right)
    {R : ℕ}
    (hrestoreBound : restorePath.length ≤ R)
    (hdone : done ≤ R) (hpathBound : path.length ≤ R)
    (hruleBound : (ULogBytecode.encodeRule r).length ≤ R) :
    Nonempty (QuantifiedStopFreeRun (6 * R + 5)
      (restoreAdvanceStarted lookupSlot restorePath
        (List.replicate done (ulogCore codeZero) ++
          ulogCore pcDone :: path).reverse outer boundary mismatchRight)
      (atBits (.fieldCompare .source lookupSlot) next
        (mismatchRulePrefix r ++
          (if boundary = sourceBoundaryZero then ulogCore codeZero
            else ulogCore codeOne) :: path.reverse ++ ulogCore codeZero ::
              List.replicate done (ulogCore codeZero) ++
                ulogCore pcMark :: outer) after right)) := by
  let returnPath :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: path).reverse
  have hreturnNonempty : returnPath ≠ [] := by simp [returnPath]
  have hreturnSafe : ∀ x ∈ returnPath, x ≠ ulogCore pcMark := by
    intro x hx
    have hx' : x ∈ path ∨ x = ulogCore pcDone ∨
        (done ≠ 0 ∧ x = ulogCore codeZero) := by
      simpa [returnPath] using hx
    rcases hx' with hp | hd | hz
    · exact hpath.2 x hp
    · rw [hd]; decide
    · rw [hz.2]; decide
  cases he : returnPath with
  | nil => exact (hreturnNonempty he).elim
  | cons x xs =>
      let restore := stopFree_restoreRule_boundary lookupSlot
        restorePath hrestoreSafe boundary hboundary
        (xs ++ ulogCore pcMark :: outer) x mismatchRight
      have ha₀ : restore.1 = restorePath.length + 1 := by
        dsimp [restore]
        exact restoreRuleBoundary_fuel_eq lookupSlot restorePath hrestoreSafe
          boundary hboundary (xs ++ ulogCore pcMark :: outer) x mismatchRight
      obtain ⟨a, hrestore⟩ := restore
      have ha : a = restorePath.length + 1 := by
        exact ha₀
      have hrestored' :
          (restorePath.map restoreMismatchCell).reverse ++ mismatchRight =
            (ULogBytecode.encodeRule r ++ next).map codeTape ++
              after :: right := by
        simpa only [List.map_reverse] using hrestored
      have hrestore' : StopFreeValidZeroRun a
          (restoreAdvanceStarted lookupSlot restorePath returnPath
            outer boundary mismatchRight)
          (.running (.mismatchReturnToPc lookupSlot)
            (beforeLeftPath returnPath outer (ulogCore pcMark)
              (ulogCore boundary ::
                (ULogBytecode.encodeRule r ++ next).map codeTape ++
                  after :: right))) := by
        simpa [restoreAdvanceStarted, returnPath, he, beforeLeftPath,
          hrestored', List.append_assoc] using hrestore
      let returnRun := stopFree_mismatchReturnToPc lookupSlot
        returnPath hreturnSafe outer (ulogCore boundary)
        ((ULogBytecode.encodeRule r ++ next).map codeTape ++ after :: right)
      have hb₀ : returnRun.1 = returnPath.length + 1 := by
        dsimp [returnRun]
        exact mismatchReturnToPc_fuel_eq lookupSlot returnPath hreturnSafe
          outer (ulogCore boundary)
          ((ULogBytecode.encodeRule r ++ next).map codeTape ++ after :: right)
      obtain ⟨b, hreturn⟩ := returnRun
      have hb : b = returnPath.length + 1 := by
        exact hb₀
      have hreturn' : StopFreeValidZeroRun b
          (.running (.mismatchReturnToPc lookupSlot)
            (beforeLeftPath returnPath outer (ulogCore pcMark)
              (ulogCore boundary ::
                (ULogBytecode.encodeRule r ++ next).map codeTape ++
                  after :: right)))
          (.running (.mismatchCount lookupSlot)
            (beforeRightPath
              (List.replicate done (ulogCore codeZero) ++
                ulogCore pcDone :: path) (ulogCore pcMark :: outer)
              (ulogCore boundary)
              ((ULogBytecode.encodeRule r ++ next).map codeTape ++
                after :: right))) := by
        simpa [returnPath] using hreturn
      have hcount := mismatchCount_skipRule_exact lookupSlot done path
        hpath.1 boundary hboundary r next hnext (ulogCore pcMark :: outer)
        after right
      let total := a + b +
        (done + path.length + (ULogBytecode.encodeRule r).length + 2)
      have hall : StopFreeValidZeroRun total
          (restoreAdvanceStarted lookupSlot restorePath returnPath
            outer boundary mismatchRight)
          (atBits (.fieldCompare .source lookupSlot) next
            (mismatchRulePrefix r ++
              (if boundary = sourceBoundaryZero then ulogCore codeZero
                else ulogCore codeOne) :: path.reverse ++
                  ulogCore codeZero ::
                    List.replicate done (ulogCore codeZero) ++
                      ulogCore pcMark :: outer) after right) := by
        dsimp [total]
        exact (hrestore'.append hreturn').append hcount
      refine ⟨
        { steps := total
          le_bound := ?_
          run := by simpa [returnPath] using hall }⟩
      dsimp [total]
      have hreturnLength : returnPath.length = done + path.length + 1 := by
        simp [returnPath]
        omega
      rw [ha, hb, hreturnLength]
      omega

/-- Complete read-mismatch cursor advance.  This is the first of the four
`CursorMismatchReady` cases with all three physical phases charged to one
radius. -/
theorem ruleCursorReadMismatch_step_bounded_radius
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe (ulogCore pcDone :: path))
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (hrs : rs ≠ []) (programToHead : List Tape) (actual : ℕ)
    (hread : r.read < 3) (hactual : actual < 3)
    (hreadNe : r.read ≠ actual) (runtime outer suffix : List Tape)
    (hsourceCorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat actual) runtime))
    (hreadScan : ReadCorridorSafe (cursorReadScanPath r rs programToHead))
    (hrestoreSafe : MismatchRestorePathSafe
      (readMismatchRestorePath r.source r.read
        (cursorReadScanPath r rs programToHead)))
    (hrestoreIdentity : RestoreMismatchIdentity programToHead)
    {R : ℕ}
    (hsource : r.source ≤ R)
    (hsourceCorridorBound :
      (cursorRuleCorridor r rs programToHead
        (readHeadNat actual) runtime).length ≤ R)
    (hreadScanBound : (cursorReadScanPath r rs programToHead).length ≤ R)
    (hrestoreBound :
      (readMismatchRestorePath r.source r.read
        (cursorReadScanPath r rs programToHead)).length ≤ R)
    (hdone : done ≤ R)
    (hpathBound : (ulogCore pcDone :: path).length ≤ R)
    (hruleBound : (ULogBytecode.encodeRule r).length ≤ R) :
    Nonempty (QuantifiedStopFreeRun (6 * R ^ 2 + 16 * R + 14)
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
              ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat actual :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules rs)
        (ulogCore (nextSourceBoundary (moveSecond r.action.move)) ::
          (List.replicate (done + 1) (ulogCore codeZero) ++
            ulogCore pcDone :: advanceMismatchPath r boundary path).reverse ++
              ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat actual :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
  let pcBase :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
        ulogCore pcMark :: outer
  obtain ⟨sourceRun⟩ := ruleCursorSourceMatch_read_bounded_radius slot
    boundary hboundary r rs programToHead pcBase (readHeadNat actual) runtime
    suffix hsourceCorridor hsource hsourceCorridorBound
  obtain ⟨mismatchRun⟩ := sourceReadMismatch_bounded_radius slot r.source
    r.read actual hread hactual hreadNe boundary pcBase
    (cursorReadScanPath r rs programToHead) runtime suffix hreadScan
    hreadScanBound
  have prefixRun : StopFreeValidZeroRun
      (sourceRun.steps + mismatchRun.steps)
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: pcBase)
        (programToHead ++ readHeadNat actual :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (.running (.restoreRule slot)
        (beforeLeftPath
          (readMismatchRestorePath r.source r.read
            (cursorReadScanPath r rs programToHead))
          pcBase (ulogCore boundary)
          (readHeadNat actual :: runtime ++
            List.replicate r.source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) := by
    exact sourceRun.run.append mismatchRun.run
  have htail : programToHead ++ readHeadNat actual :: runtime ++
      List.replicate r.source (ulogCore stateZero) ++
        ulogCore stateOne :: suffix ≠ [] := by simp
  cases he : programToHead ++ readHeadNat actual :: runtime ++
      List.replicate r.source (ulogCore stateZero) ++
        ulogCore stateOne :: suffix with
  | nil => exact (htail he).elim
  | cons after right =>
      have hrestored := cursorReadMismatch_restored r rs programToHead
        runtime suffix actual hrestoreIdentity
      have hrestored' :
          (readMismatchRestorePath r.source r.read
            (cursorReadScanPath r rs programToHead)).reverse.map
              restoreMismatchCell ++
            (readHeadNat actual :: runtime ++
              List.replicate r.source (ulogCore stateZero) ++
                ulogCore stateOne :: suffix) =
          (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
            codeTape ++ after :: right := by
        have he' := congrArg
          (fun xs => (ULogBytecode.encodeRule r ++
            ULogBytecode.encodeRules rs).map codeTape ++ xs) he
        calc
          _ = (ULogBytecode.encodeRule r ++
                ULogBytecode.encodeRules rs).map codeTape ++
              (programToHead ++ readHeadNat actual :: runtime ++
                List.replicate r.source (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix) := by
            simpa [List.append_assoc] using hrestored
          _ = _ := by simpa [List.append_assoc] using he'
      obtain ⟨advanceRun⟩ := restoreMismatchAdvanceRule_bounded_radius slot
        done (ulogCore pcDone :: path) hpath boundary hboundary
        (readMismatchRestorePath r.source r.read
          (cursorReadScanPath r rs programToHead)) hrestoreSafe
        (readHeadNat actual :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)
        r (ULogBytecode.encodeRules rs) (encodeRules_ne_nil hrs)
        outer after right (by simpa only [List.append_assoc] using hrestored')
        hrestoreBound hdone hpathBound hruleBound
      have prefixRun' : StopFreeValidZeroRun
          (sourceRun.steps + mismatchRun.steps)
          (atBitsTail (.fieldCompare .source slot)
            (ULogBytecode.encodeRules (r :: rs))
            (ulogCore boundary :: pcBase) (after :: right))
          (restoreAdvanceStarted slot
            (readMismatchRestorePath r.source r.read
              (cursorReadScanPath r rs programToHead))
            (List.replicate done (ulogCore codeZero) ++
              ulogCore pcDone :: ulogCore pcDone :: path).reverse
            outer boundary
            (readHeadNat actual :: runtime ++
              List.replicate r.source (ulogCore stateZero) ++
                ulogCore stateOne :: suffix)) := by
        have hp : StopFreeValidZeroRun
            (sourceRun.steps + mismatchRun.steps)
            (atBitsTail (.fieldCompare .source slot)
              (ULogBytecode.encodeRules (r :: rs))
              (ulogCore boundary :: pcBase) (after :: right))
            (.running (.restoreRule slot)
              (beforeLeftPath
                (readMismatchRestorePath r.source r.read
                  (cursorReadScanPath r rs programToHead))
                pcBase (ulogCore boundary)
                (readHeadNat actual :: runtime ++
                  List.replicate r.source (ulogCore stateZero) ++
                    ulogCore stateOne :: suffix))) := by
          simpa only [he] using prefixRun
        have hreturn : (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse ≠ [] := by simp
        cases hret : (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse with
        | nil => exact (hreturn hret).elim
        | cons x xs =>
            simpa [pcBase, restoreAdvanceStarted, hret, beforeLeftPath,
              List.append_assoc] using hp
      have hall := prefixRun'.append advanceRun.run
      have hleft := ruleCursor_advance_left_eq done path r boundary outer
      have hall' : StopFreeValidZeroRun
          (sourceRun.steps + mismatchRun.steps + advanceRun.steps)
          (atBitsTail (.fieldCompare .source slot)
            (ULogBytecode.encodeRules (r :: rs))
            (ulogCore boundary :: pcBase) (after :: right))
          (atBits (.fieldCompare .source slot) (ULogBytecode.encodeRules rs)
            (ulogCore (nextSourceBoundary (moveSecond r.action.move)) ::
              (List.replicate (done + 1) (ulogCore codeZero) ++
                ulogCore pcDone :: advanceMismatchPath r boundary path).reverse ++
                  ulogCore pcMark :: outer) after right) := by
        simpa only [hleft] using hall
      refine ⟨
        { steps := sourceRun.steps + mismatchRun.steps + advanceRun.steps
          le_bound := ?_
          run := by
            simpa [atBitsTail, he, pcBase, List.reverse_append,
              List.append_assoc] using hall' }⟩
      have hs := sourceRun.le_bound
      have hm := mismatchRun.le_bound
      have ha := advanceRun.le_bound
      omega

/-- Complete slot-mismatch cursor advance, parallel to the read-mismatch
case but using the saved-slot restoration corridor. -/
theorem ruleCursorSlotMismatch_step_bounded_radius
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe (ulogCore pcDone :: path))
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (hslot : r.slot = !slot)
    (rs : List ULogBytecode.RuleCode) (hrs : rs ≠ [])
    (programToHead : List Tape) (hread : r.read < 3)
    (runtime outer suffix : List Tape)
    (hsourceCorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read) runtime))
    (hreadScan : ReadCorridorSafe
      (codeTape (!slot) :: encodedActionPath r.action.write
        r.action.target r.action.move (cursorMatchedMovePath rs programToHead)))
    (hrestoreSafe : MismatchRestorePathSafe
      (slotMismatchRestorePath r.source r.read))
    {R : ℕ}
    (hsource : r.source ≤ R)
    (hsourceCorridorBound :
      (cursorRuleCorridor r rs programToHead
        (readHeadNat r.read) runtime).length ≤ R)
    (hactionPathBound :
      (encodedActionPath r.action.write r.action.target r.action.move
        (cursorMatchedMovePath rs programToHead)).length ≤ R)
    (hrestoreBound : (slotMismatchRestorePath r.source r.read).length ≤ R)
    (hdone : done ≤ R)
    (hpathBound : (ulogCore pcDone :: path).length ≤ R)
    (hruleBound : (ULogBytecode.encodeRule r).length ≤ R) :
    Nonempty (QuantifiedStopFreeRun (6 * R ^ 2 + 17 * R + 18)
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
              ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules rs)
        (ulogCore (nextSourceBoundary (moveSecond r.action.move)) ::
          (List.replicate (done + 1) (ulogCore codeZero) ++
            ulogCore pcDone :: advanceMismatchPath r boundary path).reverse ++
              ulogCore pcMark :: outer)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
  let pcBase :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
        ulogCore pcMark :: outer
  obtain ⟨sourceRun⟩ := ruleCursorSourceMatch_read_bounded_radius slot
    boundary hboundary r rs programToHead pcBase (readHeadNat r.read) runtime
    suffix hsourceCorridor hsource hsourceCorridorBound
  obtain ⟨mismatchRun⟩ := sourceReadAtSlotMismatch_bounded_radius slot
    r.source r.read hread boundary pcBase
    (encodedActionPath r.action.write r.action.target r.action.move
      (cursorMatchedMovePath rs programToHead))
    runtime suffix hreadScan hactionPathBound
  have sourceRun' : StopFreeValidZeroRun sourceRun.steps
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: pcBase)
        (programToHead ++ readHeadNat r.read :: runtime ++
          List.replicate r.source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (sourceReadStartedAt slot r.source boundary
        (unaryFieldFirst r.read) pcBase
        ((ULogBytecode.encodeNatField r.read).tail.map codeTape ++
          codeTape (!slot) :: encodedActionPath r.action.write
            r.action.target r.action.move
              (cursorMatchedMovePath rs programToHead) ++
            readHeadNat r.read :: runtime) suffix) := by
    simpa [hslot] using sourceRun.run
  have prefixRun := sourceRun'.append mismatchRun.run
  have htail : programToHead ++ readHeadNat r.read :: runtime ++
      List.replicate r.source (ulogCore stateZero) ++
        ulogCore stateOne :: suffix ≠ [] := by simp
  cases he : programToHead ++ readHeadNat r.read :: runtime ++
      List.replicate r.source (ulogCore stateZero) ++
        ulogCore stateOne :: suffix with
  | nil => exact (htail he).elim
  | cons after right =>
      have hrestored := cursorSlotMismatch_restored slot r hslot rs
        programToHead runtime suffix
      have hrestored' :
          (slotMismatchRestorePath r.source r.read).reverse.map
                restoreMismatchCell ++ codeTape (!slot) ::
              encodedActionPath r.action.write r.action.target r.action.move
                (cursorMatchedMovePath rs programToHead) ++
              readHeadNat r.read :: runtime ++
                List.replicate r.source (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix =
            (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
              codeTape ++ after :: right := by
        have he' := congrArg
          (fun xs => (ULogBytecode.encodeRule r ++
            ULogBytecode.encodeRules rs).map codeTape ++ xs) he
        calc
          _ = (ULogBytecode.encodeRule r ++
                ULogBytecode.encodeRules rs).map codeTape ++
              (programToHead ++ readHeadNat r.read :: runtime ++
                List.replicate r.source (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix) := by
            simpa [List.append_assoc] using hrestored
          _ = _ := by simpa [List.append_assoc] using he'
      obtain ⟨advanceRun⟩ := restoreMismatchAdvanceRule_bounded_radius slot
        done (ulogCore pcDone :: path) hpath boundary hboundary
        (slotMismatchRestorePath r.source r.read) hrestoreSafe
        (codeTape (!slot) ::
          encodedActionPath r.action.write r.action.target r.action.move
            (cursorMatchedMovePath rs programToHead) ++
          readHeadNat r.read :: runtime ++
            List.replicate r.source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)
        r (ULogBytecode.encodeRules rs) (encodeRules_ne_nil hrs)
        outer after right (by simpa only [List.append_assoc] using hrestored')
        hrestoreBound hdone hpathBound hruleBound
      have prefixRun' : StopFreeValidZeroRun
          (sourceRun.steps + mismatchRun.steps)
          (atBitsTail (.fieldCompare .source slot)
            (ULogBytecode.encodeRules (r :: rs))
            (ulogCore boundary :: pcBase) (after :: right))
          (restoreAdvanceStarted slot
            (slotMismatchRestorePath r.source r.read)
            (List.replicate done (ulogCore codeZero) ++
              ulogCore pcDone :: ulogCore pcDone :: path).reverse
            outer boundary
            (codeTape (!slot) ::
              encodedActionPath r.action.write r.action.target r.action.move
                (cursorMatchedMovePath rs programToHead) ++
              readHeadNat r.read :: runtime ++
                List.replicate r.source (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix)) := by
        have hp : StopFreeValidZeroRun
            (sourceRun.steps + mismatchRun.steps)
            (atBitsTail (.fieldCompare .source slot)
              (ULogBytecode.encodeRules (r :: rs))
              (ulogCore boundary :: pcBase) (after :: right))
            (.running (.restoreRule slot)
              (beforeLeftPath (slotMismatchRestorePath r.source r.read)
                pcBase (ulogCore boundary)
                (codeTape (!slot) ::
                  encodedActionPath r.action.write r.action.target
                    r.action.move (cursorMatchedMovePath rs programToHead) ++
                  readHeadNat r.read :: runtime ++
                    List.replicate r.source (ulogCore stateZero) ++
                      ulogCore stateOne :: suffix))) := by
          simpa only [he] using prefixRun
        have hreturn : (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse ≠ [] := by simp
        cases hret : (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse with
        | nil => exact (hreturn hret).elim
        | cons x xs =>
            simpa [pcBase, restoreAdvanceStarted, hret, beforeLeftPath,
              List.append_assoc] using hp
      have hall := prefixRun'.append advanceRun.run
      have hleft := ruleCursor_advance_left_eq done path r boundary outer
      have hall' : StopFreeValidZeroRun
          (sourceRun.steps + mismatchRun.steps + advanceRun.steps)
          (atBitsTail (.fieldCompare .source slot)
            (ULogBytecode.encodeRules (r :: rs))
            (ulogCore boundary :: pcBase) (after :: right))
          (atBits (.fieldCompare .source slot) (ULogBytecode.encodeRules rs)
            (ulogCore (nextSourceBoundary (moveSecond r.action.move)) ::
              (List.replicate (done + 1) (ulogCore codeZero) ++
                ulogCore pcDone :: advanceMismatchPath r boundary path).reverse ++
                  ulogCore pcMark :: outer) after right) := by
        simpa only [hleft] using hall
      refine ⟨
        { steps := sourceRun.steps + mismatchRun.steps + advanceRun.steps
          le_bound := ?_
          run := by simpa [atBitsTail, he, pcBase, List.reverse_append,
            List.append_assoc] using hall' }⟩
      have hs := sourceRun.le_bound
      have hm := mismatchRun.le_bound
      have ha := advanceRun.le_bound
      omega

/-- Complete source-short mismatch cursor advance. -/
theorem ruleCursorSourceShort_step_bounded_radius
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe (ulogCore pcDone :: path))
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (hrs : rs ≠ []) (programPath : List Tape) (extra : ℕ)
    (outer suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (ruleContinuationCorridor r rs programPath))
    (hreadBoundary : ∀ x ∈ ruleContinuationCorridor r rs programPath,
      x ≠ ulogCore readBoundary)
    {R : ℕ}
    (hsource : r.source ≤ R)
    (hcurrent : r.source + extra + 1 ≤ R)
    (hcorridorBound :
      (ruleContinuationCorridor r rs programPath).length ≤ R)
    (hrestoreBound :
      (sourceShortRestorePath r.source
        (ruleContinuationCorridor r rs programPath)).length ≤ R)
    (hdone : done ≤ R)
    (hpathBound : (ulogCore pcDone :: path).length ≤ R)
    (hruleBound : (ULogBytecode.encodeRule r).length ≤ R) :
    Nonempty (QuantifiedStopFreeRun (6 * R ^ 2 + 13 * R + 12)
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
              ulogCore pcMark :: outer)
        (programPath ++
          List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules rs)
        (ulogCore (nextSourceBoundary (moveSecond r.action.move)) ::
          (List.replicate (done + 1) (ulogCore codeZero) ++
            ulogCore pcDone :: advanceMismatchPath r boundary path).reverse ++
              ulogCore pcMark :: outer)
        (programPath ++
          List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
  let corridor := ruleContinuationCorridor r rs programPath
  let pcBase :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
        ulogCore pcMark :: outer
  have hle : r.source ≤ r.source + extra + 1 := by omega
  have hmin : min r.source (r.source + extra + 1) = r.source :=
    Nat.min_eq_left hle
  obtain ⟨commonRun⟩ := sourceCompareCommon_bounded_radius_quadratic slot
    r.source (r.source + extra + 1) 0 corridor hcorridor
    (ulogCore boundary :: pcBase) suffix hsource hcurrent
    (by simpa [hmin] using hsource) hcorridorBound
  have hcommonEnd : sourceCompareStartAgainst slot
      (r.source - (r.source + extra + 1))
      (r.source + extra + 1 - r.source)
      (0 + min r.source (r.source + extra + 1)) corridor
      (List.replicate (min r.source (r.source + extra + 1))
        (ulogCore sourceMark) ++ ulogCore boundary :: pcBase) suffix =
      sourceCompareStartAgainst slot 0 (extra + 1) r.source corridor
        (List.replicate r.source (ulogCore sourceMark) ++
          ulogCore boundary :: pcBase) suffix := by
    have hsub₁ : r.source - (r.source + extra + 1) = 0 :=
      Nat.sub_eq_zero_of_le hle
    have hsub₂ : r.source + extra + 1 - r.source = extra + 1 := by omega
    simp [hsub₁, hsub₂, hmin]
  have commonRunEnd : StopFreeValidZeroRun commonRun.steps
      (sourceCompareStartAgainst slot r.source (r.source + extra + 1) 0
        corridor (ulogCore boundary :: pcBase) suffix)
      (sourceCompareStartAgainst slot 0 (extra + 1) r.source corridor
        (List.replicate r.source (ulogCore sourceMark) ++
          ulogCore boundary :: pcBase) suffix) := by
    simpa only [hcommonEnd] using commonRun.run
  have commonRun' : StopFreeValidZeroRun commonRun.steps
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: pcBase)
        (programPath ++
          List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (sourceCompareStartAgainst slot 0 (extra + 1) r.source corridor
        (List.replicate r.source (ulogCore sourceMark) ++
          ulogCore boundary :: pcBase) suffix) := by
    rw [atBitsTail_encodeRules_cons_source]
    simpa [corridor, ruleContinuationCorridor, List.append_assoc] using
      commonRunEnd
  let mismatchRun := stopFree_sourceShortMismatch_restore slot r.source
    extra corridor hcorridor (ulogCore boundary) pcBase suffix
  have hmismatchFuel : mismatchRun.1 = corridor.length + r.source + 2 := by
    dsimp [mismatchRun]
    exact sourceShortMismatch_restore_fuel_eq slot r.source extra corridor
      hcorridor (ulogCore boundary) pcBase suffix
  have prefixRun := commonRun'.append mismatchRun.2
  have htail : programPath ++
      List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
        ulogCore stateOne :: suffix ≠ [] := by simp
  cases he : programPath ++
      List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
        ulogCore stateOne :: suffix with
  | nil => exact (htail he).elim
  | cons after right =>
      have hrestored := ruleSourceShort_restored r rs programPath suffix extra
        hcorridor hreadBoundary
      have hrestored' :
          (sourceShortRestorePath r.source corridor).reverse.map
              restoreMismatchCell ++
            (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: suffix) =
          (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
            codeTape ++ after :: right := by
        have he' := congrArg
          (fun xs => (ULogBytecode.encodeRule r ++
            ULogBytecode.encodeRules rs).map codeTape ++ xs) he
        calc
          _ = (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
              codeTape ++ (programPath ++
                List.replicate (r.source + extra + 1)
                  (ulogCore stateZero) ++ ulogCore stateOne :: suffix) := by
            simpa [corridor, List.append_assoc] using hrestored
          _ = _ := by simpa [List.append_assoc] using he'
      obtain ⟨advanceRun⟩ := restoreMismatchAdvanceRule_bounded_radius slot
        done (ulogCore pcDone :: path) hpath boundary hboundary
        (sourceShortRestorePath r.source corridor)
        (sourceShortRestorePath_safe r.source corridor hcorridor)
        (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)
        r (ULogBytecode.encodeRules rs) (encodeRules_ne_nil hrs)
        outer after right (by simpa only [List.append_assoc] using hrestored')
        hrestoreBound hdone hpathBound hruleBound
      have prefixRun' : StopFreeValidZeroRun
          (commonRun.steps + mismatchRun.1)
          (atBitsTail (.fieldCompare .source slot)
            (ULogBytecode.encodeRules (r :: rs))
            (ulogCore boundary :: pcBase) (after :: right))
          (restoreAdvanceStarted slot
            (sourceShortRestorePath r.source corridor)
            (List.replicate done (ulogCore codeZero) ++
              ulogCore pcDone :: ulogCore pcDone :: path).reverse
            outer boundary
            (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)) := by
        have hp : StopFreeValidZeroRun (commonRun.steps + mismatchRun.1)
            (atBitsTail (.fieldCompare .source slot)
              (ULogBytecode.encodeRules (r :: rs))
              (ulogCore boundary :: pcBase) (after :: right))
            (.running (.restoreRule slot)
              (beforeLeftPath (sourceShortRestorePath r.source corridor)
                pcBase (ulogCore boundary)
                (ulogCore stateZero ::
                  List.replicate extra (ulogCore stateZero) ++
                    ulogCore stateOne :: suffix))) := by
          simpa only [he] using prefixRun
        have hreturn : (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse ≠ [] := by simp
        cases hret : (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse with
        | nil => exact (hreturn hret).elim
        | cons x xs =>
            simpa [pcBase, restoreAdvanceStarted, hret, beforeLeftPath,
              List.append_assoc] using hp
      have hall := prefixRun'.append advanceRun.run
      have hleft := ruleCursor_advance_left_eq done path r boundary outer
      have hall' : StopFreeValidZeroRun
          (commonRun.steps + mismatchRun.1 + advanceRun.steps)
          (atBitsTail (.fieldCompare .source slot)
            (ULogBytecode.encodeRules (r :: rs))
            (ulogCore boundary :: pcBase) (after :: right))
          (atBits (.fieldCompare .source slot) (ULogBytecode.encodeRules rs)
            (ulogCore (nextSourceBoundary (moveSecond r.action.move)) ::
              (List.replicate (done + 1) (ulogCore codeZero) ++
                ulogCore pcDone :: advanceMismatchPath r boundary path).reverse ++
                  ulogCore pcMark :: outer) after right) := by
        simpa only [hleft] using hall
      refine ⟨
        { steps := commonRun.steps + mismatchRun.1 + advanceRun.steps
          le_bound := ?_
          run := by simpa [atBitsTail, he, pcBase, List.reverse_append,
            List.append_assoc] using hall' }⟩
      rw [hmismatchFuel]
      have hc := commonRun.le_bound
      have ha := advanceRun.le_bound
      dsimp [corridor] at hc ⊢
      omega

/-- Complete source-long mismatch cursor advance. -/
theorem ruleCursorSourceLong_step_bounded_radius
    (slot : Bool) (done : ℕ) (path : List Tape)
    (hpath : MismatchAdvancePathSafe (ulogCore pcDone :: path))
    (boundary : ULogLetter)
    (hboundary : boundary = sourceBoundary ∨
      boundary = sourceBoundaryZero ∨ boundary = sourceBoundaryOne)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (hrs : rs ≠ []) (programPath : List Tape) (current extra : ℕ)
    (hsourceEq : r.source = current + extra + 1)
    (outer suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (ruleContinuationCorridor r rs programPath))
    (hreadBoundary : ∀ x ∈ ruleContinuationCorridor r rs programPath,
      x ≠ ulogCore readBoundary)
    {R : ℕ}
    (hsource : r.source ≤ R) (hcurrent : current ≤ R)
    (hcorridorBound :
      (ruleContinuationCorridor r rs programPath).length ≤ R)
    (hrestoreBound :
      (sourceLongRestorePath extra current
        (ruleContinuationCorridor r rs programPath)).length ≤ R)
    (hdone : done ≤ R)
    (hpathBound : (ulogCore pcDone :: path).length ≤ R)
    (hruleBound : (ULogBytecode.encodeRule r).length ≤ R) :
    Nonempty (QuantifiedStopFreeRun (6 * R ^ 2 + 13 * R + 12)
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs))
        (ulogCore boundary ::
          (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
              ulogCore pcMark :: outer)
        (programPath ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules rs)
        (ulogCore (nextSourceBoundary (moveSecond r.action.move)) ::
          (List.replicate (done + 1) (ulogCore codeZero) ++
            ulogCore pcDone :: advanceMismatchPath r boundary path).reverse ++
              ulogCore pcMark :: outer)
        (programPath ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))) := by
  let corridor := ruleContinuationCorridor r rs programPath
  let pcBase :=
    (List.replicate done (ulogCore codeZero) ++
      ulogCore pcDone :: ulogCore pcDone :: path).reverse ++
        ulogCore pcMark :: outer
  have hle : current ≤ current + extra + 1 := by omega
  have hmin : min r.source current = current := by
    rw [hsourceEq]
    exact Nat.min_eq_right hle
  obtain ⟨commonRun⟩ := sourceCompareCommon_bounded_radius_quadratic slot
    r.source current 0 corridor hcorridor (ulogCore boundary :: pcBase)
    suffix hsource hcurrent (by simpa [hmin] using hcurrent) hcorridorBound
  have hcommonEnd : sourceCompareStartAgainst slot
      (r.source - current) (current - r.source)
      (0 + min r.source current) corridor
      (List.replicate (min r.source current) (ulogCore sourceMark) ++
        ulogCore boundary :: pcBase) suffix =
      sourceCompareStartAgainst slot (extra + 1) 0 current corridor
        (List.replicate current (ulogCore sourceMark) ++
          ulogCore boundary :: pcBase) suffix := by
    have hge : current ≤ r.source := by omega
    have hsub₁ : r.source - current = extra + 1 := by omega
    have hsub₂ : current - r.source = 0 := Nat.sub_eq_zero_of_le hge
    simp [hsub₁, hsub₂, hmin]
  have commonRunEnd : StopFreeValidZeroRun commonRun.steps
      (sourceCompareStartAgainst slot r.source current 0 corridor
        (ulogCore boundary :: pcBase) suffix)
      (sourceCompareStartAgainst slot (extra + 1) 0 current corridor
        (List.replicate current (ulogCore sourceMark) ++
          ulogCore boundary :: pcBase) suffix) := by
    simpa only [hcommonEnd] using commonRun.run
  have commonRun' : StopFreeValidZeroRun commonRun.steps
      (atBitsTail (.fieldCompare .source slot)
        (ULogBytecode.encodeRules (r :: rs)) (ulogCore boundary :: pcBase)
        (programPath ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))
      (sourceCompareStartAgainst slot (extra + 1) 0 current corridor
        (List.replicate current (ulogCore sourceMark) ++
          ulogCore boundary :: pcBase) suffix) := by
    rw [atBitsTail_encodeRules_cons_source]
    simpa [hsourceEq, corridor, ruleContinuationCorridor,
      List.append_assoc] using commonRunEnd
  let mismatchRun := stopFree_sourceLongMismatch_restore slot current extra
    corridor hcorridor (ulogCore boundary) pcBase suffix
  have hmismatchFuel : mismatchRun.1 =
      extra + corridor.length + current + 3 := by
    dsimp [mismatchRun]
    exact sourceLongMismatch_restore_fuel_eq slot current extra corridor
      hcorridor (ulogCore boundary) pcBase suffix
  have prefixRun := commonRun'.append mismatchRun.2
  have htail : programPath ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: suffix ≠ [] := by simp
  cases he : programPath ++ List.replicate current (ulogCore stateZero) ++
      ulogCore stateOne :: suffix with
  | nil => exact (htail he).elim
  | cons after right =>
      have hrestored := ruleSourceLong_restored r rs programPath suffix
        current extra hsourceEq hcorridor hreadBoundary
      have hrestored' :
          (sourceLongRestorePath extra current corridor).reverse.map
              restoreMismatchCell ++ ulogCore stateOne :: suffix =
          (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
            codeTape ++ after :: right := by
        have he' := congrArg
          (fun xs => (ULogBytecode.encodeRule r ++
            ULogBytecode.encodeRules rs).map codeTape ++ xs) he
        calc
          _ = (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
              codeTape ++ (programPath ++
                List.replicate current (ulogCore stateZero) ++
                  ulogCore stateOne :: suffix) := by
            simpa [corridor, List.append_assoc] using hrestored
          _ = _ := by simpa [List.append_assoc] using he'
      obtain ⟨advanceRun⟩ := restoreMismatchAdvanceRule_bounded_radius slot
        done (ulogCore pcDone :: path) hpath boundary hboundary
        (sourceLongRestorePath extra current corridor)
        (sourceLongRestorePath_safe extra current corridor hcorridor)
        (ulogCore stateOne :: suffix)
        r (ULogBytecode.encodeRules rs) (encodeRules_ne_nil hrs)
        outer after right (by simpa only [List.append_assoc] using hrestored')
        hrestoreBound hdone hpathBound hruleBound
      have prefixRun' : StopFreeValidZeroRun
          (commonRun.steps + mismatchRun.1)
          (atBitsTail (.fieldCompare .source slot)
            (ULogBytecode.encodeRules (r :: rs))
            (ulogCore boundary :: pcBase) (after :: right))
          (restoreAdvanceStarted slot
            (sourceLongRestorePath extra current corridor)
            (List.replicate done (ulogCore codeZero) ++
              ulogCore pcDone :: ulogCore pcDone :: path).reverse
            outer boundary (ulogCore stateOne :: suffix)) := by
        have hp : StopFreeValidZeroRun (commonRun.steps + mismatchRun.1)
            (atBitsTail (.fieldCompare .source slot)
              (ULogBytecode.encodeRules (r :: rs))
              (ulogCore boundary :: pcBase) (after :: right))
            (.running (.restoreRule slot)
              (beforeLeftPath (sourceLongRestorePath extra current corridor)
                pcBase (ulogCore boundary) (ulogCore stateOne :: suffix))) := by
          simpa only [he] using prefixRun
        have hreturn : (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse ≠ [] := by simp
        cases hret : (List.replicate done (ulogCore codeZero) ++
            ulogCore pcDone :: ulogCore pcDone :: path).reverse with
        | nil => exact (hreturn hret).elim
        | cons x xs =>
            simpa [pcBase, restoreAdvanceStarted, hret, beforeLeftPath,
              List.append_assoc] using hp
      have hall := prefixRun'.append advanceRun.run
      have hleft := ruleCursor_advance_left_eq done path r boundary outer
      have hall' : StopFreeValidZeroRun
          (commonRun.steps + mismatchRun.1 + advanceRun.steps)
          (atBitsTail (.fieldCompare .source slot)
            (ULogBytecode.encodeRules (r :: rs))
            (ulogCore boundary :: pcBase) (after :: right))
          (atBits (.fieldCompare .source slot) (ULogBytecode.encodeRules rs)
            (ulogCore (nextSourceBoundary (moveSecond r.action.move)) ::
              (List.replicate (done + 1) (ulogCore codeZero) ++
                ulogCore pcDone :: advanceMismatchPath r boundary path).reverse ++
                  ulogCore pcMark :: outer) after right) := by
        simpa only [hleft] using hall
      refine ⟨
        { steps := commonRun.steps + mismatchRun.1 + advanceRun.steps
          le_bound := ?_
          run := by simpa [atBitsTail, he, pcBase, List.reverse_append,
            List.append_assoc] using hall' }⟩
      rw [hmismatchFuel]
      have hc := commonRun.le_bound
      have ha := advanceRun.le_bound
      dsimp [corridor] at hc ⊢
      omega



/-- A stop-free run together with a literal numerical upper bound.  It lives
in `Type` because `StopFreeValidZeroRun` itself carries non-proof execution
data; using an `And` here would incorrectly force it into `Prop`. -/
structure BoundedStopFreeRun (B : ℕ) (start finish : Result) : Type where
  steps : ℕ
  le_bound : steps ≤ B
  run : StopFreeValidZeroRun steps start finish

/-- The numerical envelope needed to instantiate all four concrete mismatch
branches from one `CursorMismatchReady` certificate. -/
structure CursorMismatchWithinRadius (R : ℕ)
    (slot : Bool) (current actual : ℕ) (c : RuleCursorData)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead runtime : List Tape)
    (ready : CursorMismatchReady slot current actual c r rs
      programToHead runtime) : Prop where
  current_le : current ≤ R
  source_le : r.source ≤ R
  done_le : c.done ≤ R
  cursor_path_le : (ulogCore pcDone :: ready.tail).length ≤ R
  rule_le : (ULogBytecode.encodeRule r).length ≤ R
  source_corridor_le :
    (cursorRuleCorridor r rs programToHead
      (readHeadNat actual) runtime).length ≤ R
  read_scan_le : (cursorReadScanPath r rs programToHead).length ≤ R
  read_restore_le :
    (readMismatchRestorePath r.source r.read
      (cursorReadScanPath r rs programToHead)).length ≤ R
  slot_action_le :
    (encodedActionPath r.action.write r.action.target r.action.move
      (cursorMatchedMovePath rs programToHead)).length ≤ R
  slot_restore_le : (slotMismatchRestorePath r.source r.read).length ≤ R
  source_short_restore_le :
    (sourceShortRestorePath r.source
      (cursorRuleCorridor r rs programToHead
        (readHeadNat actual) runtime)).length ≤ R
  source_long_restore_le : ∀ extra,
    r.source = current + extra + 1 →
      (sourceLongRestorePath extra current
        (cursorRuleCorridor r rs programToHead
          (readHeadNat actual) runtime)).length ≤ R

/-- A concrete, assumption-free local size envelope for one mismatch node.
It is intentionally additive: the next global step is to dominate this sum
by the copied physical work span. -/
def cursorMismatchLocalRadius
    (current actual : ℕ) (c : RuleCursorData)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead runtime : List Tape) (tail : List Tape) : ℕ :=
  current + actual + r.source + c.done +
    (ulogCore pcDone :: tail).length +
    (ULogBytecode.encodeRule r).length +
    (cursorRuleCorridor r rs programToHead
      (readHeadNat actual) runtime).length +
    (cursorReadScanPath r rs programToHead).length +
    (readMismatchRestorePath r.source r.read
      (cursorReadScanPath r rs programToHead)).length +
    (encodedActionPath r.action.write r.action.target r.action.move
      (cursorMatchedMovePath rs programToHead)).length +
    (slotMismatchRestorePath r.source r.read).length +
    (sourceShortRestorePath r.source
      (cursorRuleCorridor r rs programToHead
        (readHeadNat actual) runtime)).length +
    ((cursorRuleCorridor r rs programToHead
      (readHeadNat actual) runtime).length + r.source + current + 1)

/-- Every actual `CursorMismatchReady` node produces its local quantitative
envelope; no new oracle or user hypothesis is introduced here. -/
theorem cursorMismatchWithin_localRadius
    (slot : Bool) (current actual : ℕ) (c : RuleCursorData)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead runtime : List Tape)
    (ready : CursorMismatchReady slot current actual c r rs
      programToHead runtime) :
    CursorMismatchWithinRadius
      (cursorMismatchLocalRadius current actual c r rs programToHead runtime
        ready.tail)
      slot current actual c r rs programToHead runtime ready := by
  let R := cursorMismatchLocalRadius current actual c r rs programToHead
    runtime ready.tail
  have hlong (extra : ℕ) (heq : r.source = current + extra + 1) :
      (sourceLongRestorePath extra current
        (cursorRuleCorridor r rs programToHead
          (readHeadNat actual) runtime)).length ≤ R := by
    dsimp [R, cursorMismatchLocalRadius]
    simp [sourceLongRestorePath, sourceLongSeekPath,
      sourceCompareScanPath]
    omega
  refine
    { current_le := by dsimp [R, cursorMismatchLocalRadius]; omega
      source_le := by dsimp [R, cursorMismatchLocalRadius]; omega
      done_le := by dsimp [R, cursorMismatchLocalRadius]; omega
      cursor_path_le := by dsimp [R, cursorMismatchLocalRadius]; omega
      rule_le := by dsimp [R, cursorMismatchLocalRadius]; omega
      source_corridor_le := by dsimp [R, cursorMismatchLocalRadius]; omega
      read_scan_le := by dsimp [R, cursorMismatchLocalRadius]; omega
      read_restore_le := by dsimp [R, cursorMismatchLocalRadius]; omega
      slot_action_le := by dsimp [R, cursorMismatchLocalRadius]; omega
      slot_restore_le := by dsimp [R, cursorMismatchLocalRadius]; omega
      source_short_restore_le := by
        dsimp [R, cursorMismatchLocalRadius]; omega
      source_long_restore_le := hlong }

theorem CursorMismatchWithinRadius.mono
    {R S : ℕ} (hRS : R ≤ S)
    {slot : Bool} {current actual : ℕ} {c : RuleCursorData}
    {r : ULogBytecode.RuleCode} {rs : List ULogBytecode.RuleCode}
    {programToHead runtime : List Tape}
    {ready : CursorMismatchReady slot current actual c r rs
      programToHead runtime}
    (h : CursorMismatchWithinRadius R slot current actual c r rs
      programToHead runtime ready) :
    CursorMismatchWithinRadius S slot current actual c r rs
      programToHead runtime ready := by
  exact
    { current_le := h.current_le.trans hRS
      source_le := h.source_le.trans hRS
      done_le := h.done_le.trans hRS
      cursor_path_le := h.cursor_path_le.trans hRS
      rule_le := h.rule_le.trans hRS
      source_corridor_le := h.source_corridor_le.trans hRS
      read_scan_le := h.read_scan_le.trans hRS
      read_restore_le := h.read_restore_le.trans hRS
      slot_action_le := h.slot_action_le.trans hRS
      slot_restore_le := h.slot_restore_le.trans hRS
      source_short_restore_le := h.source_short_restore_le.trans hRS
      source_long_restore_le := fun extra heq =>
        (h.source_long_restore_le extra heq).trans hRS }

theorem mismatchRulePrefix_length_eq_encodeRule
    (r : ULogBytecode.RuleCode) :
    (mismatchRulePrefix r).length = (ULogBytecode.encodeRule r).length := by
  rcases r with ⟨source, read, ruleSlot, ⟨write, target, move⟩⟩
  cases move <;>
    simp [mismatchRulePrefix, ULogBytecode.encodeRule,
      ULogBytecode.encodeAction, ULogBytecode.encodeMove,
      ULogBytecode.encodeNatField, List.append_assoc] <;> omega

theorem skippedRuleSegment_length_eq_encodeRule
    (boundary : ULogLetter) (r : ULogBytecode.RuleCode) :
    (skippedRuleSegment boundary r).length =
      (ULogBytecode.encodeRule r).length := by
  have hpos : 0 < (ULogBytecode.encodeRule r).length :=
    List.length_pos_of_ne_nil (ULogBootstrapExecution.encodeRule_ne_nil r)
  simp [skippedRuleSegment, mismatchRulePrefix_length_eq_encodeRule,
    ULogBootstrapExecution.encodeRule_ne_nil]
  omega

theorem mismatchHistory_length_eq_encodeRules
    (boundary : ULogLetter) (rules : List ULogBytecode.RuleCode) :
    (mismatchHistory boundary rules).length =
      (ULogBytecode.encodeRules rules).length := by
  induction rules generalizing boundary with
  | nil => simp [mismatchHistory, ULogBytecode.encodeRules]
  | cons r rs ih =>
      simp [mismatchHistory, ULogBytecode.encodeRules,
        skippedRuleSegment_length_eq_encodeRule, ih, List.length_append]

theorem canonicalRuleCursor_path_length
    (passed remaining : List ULogBytecode.RuleCode) :
    (canonicalRuleCursor passed remaining).path.length =
      (remaining.length - 1) +
        (ULogBytecode.encodeRules passed).length := by
  simp [canonicalRuleCursor, mismatchHistory_length_eq_encodeRules]

/-- One canonical cursor node is controlled by a fixed multiple of the
literal program/tape data of the enclosing semantic frame. -/
theorem canonicalCursorMismatch_localRadius_le
    (slot : Bool) (current actual : ℕ)
    (passed : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (remaining : List ULogBytecode.RuleCode) (hremaining : remaining ≠ [])
    (programToHead runtime : List Tape)
    (ready : CursorMismatchReady slot current actual
      (canonicalRuleCursor passed (r :: remaining)) r remaining
      programToHead runtime) :
    cursorMismatchLocalRadius current actual
        (canonicalRuleCursor passed (r :: remaining)) r remaining
        programToHead runtime ready.tail ≤
      32 * ((ULogBytecode.encodeRules (passed ++ r :: remaining)).length +
        (passed ++ r :: remaining).length + programToHead.length +
          runtime.length + current + actual + 1) := by
  have hpath := canonicalRuleCursor_path_cons passed r remaining hremaining
  have htail : ready.tail = (canonicalRuleCursor passed remaining).path := by
    have heq := ready.path_eq
    rw [hpath] at heq
    exact (List.cons.inj heq |>.2).symm
  have henc :
      (ULogBytecode.encodeRules (passed ++ r :: remaining)).length =
        (ULogBytecode.encodeRules passed).length +
          (ULogBytecode.encodeRule r).length +
            (ULogBytecode.encodeRules remaining).length := by
    simp [encodeRules_append, ULogBytecode.encodeRules]
    omega
  have hlist : (passed ++ r :: remaining).length =
      passed.length + 1 + remaining.length := by
    simp
    omega
  rw [htail]
  rw [henc, hlist]
  simp [cursorMismatchLocalRadius, cursorRuleCorridor,
    ruleContinuationCorridor, cursorReadScanPath, encodedActionPath,
    cursorMatchedMovePath, readMismatchRestorePath, slotMismatchRestorePath,
    sourceShortRestorePath, sourceShortFinishPath, canonicalRuleCursor,
    mismatchHistory_length_eq_encodeRules, mismatchRulePrefix_length_eq_encodeRule,
    ULogBytecode.encodeRule,
    ULogBytecode.encodeAction, ULogBytecode.encodeMove,
    ULogBytecode.encodeNatField, moveBits, List.length_append,
    List.length_reverse, List.length_map]
  omega

theorem canonicalCursorMismatchWithin_budget
    (slot : Bool) (current actual : ℕ)
    (passed : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (remaining : List ULogBytecode.RuleCode) (hremaining : remaining ≠ [])
    (programToHead runtime : List Tape)
    (ready : CursorMismatchReady slot current actual
      (canonicalRuleCursor passed (r :: remaining)) r remaining
      programToHead runtime) :
    CursorMismatchWithinRadius
      (32 * ((ULogBytecode.encodeRules (passed ++ r :: remaining)).length +
        (passed ++ r :: remaining).length + programToHead.length +
          runtime.length + current + actual + 1))
      slot current actual (canonicalRuleCursor passed (r :: remaining)) r
        remaining programToHead runtime ready := by
  exact (cursorMismatchWithin_localRadius slot current actual
    (canonicalRuleCursor passed (r :: remaining)) r remaining
    programToHead runtime ready).mono
      (canonicalCursorMismatch_localRadius_le slot current actual passed r
        remaining hremaining programToHead runtime ready)

/-- Uniform bounded form matching the constructor of `MismatchPrefixTrace`.
It is a new quantitative obligation; no finite-state counting is used. -/
def CursorMismatchHeadStepAtMost (B : ℕ) : Prop :=
  ∀ (slot : Bool) (current actual : ℕ) (c : RuleCursorData)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead runtime outer suffix : List Tape)
    (ready : CursorMismatchReady slot current actual c r (rs)
      programToHead runtime),
    Nonempty (BoundedStopFreeRun B
      (ruleCursorResult slot current actual c (r :: rs)
        programToHead runtime outer suffix)
      (ruleCursorResult slot current actual
        (advanceRuleCursor c r ready.tail) rs
        programToHead runtime outer suffix))

/-- All four mismatch alternatives fit the single budget
`6R² + 17R + 18` at one physical cursor node. -/
theorem cursorMismatchReady_step_bounded_radius
    (R : ℕ) (slot : Bool) (current actual : ℕ)
    (c : RuleCursorData) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode)
    (programToHead runtime outer suffix : List Tape)
    (ready : CursorMismatchReady slot current actual c r rs
      programToHead runtime)
    (bounds : CursorMismatchWithinRadius R slot current actual c r rs
      programToHead runtime ready) :
    Nonempty (BoundedStopFreeRun (6 * R ^ 2 + 17 * R + 18)
      (ruleCursorResult slot current actual c (r :: rs)
        programToHead runtime outer suffix)
      (ruleCursorResult slot current actual
        (advanceRuleCursor c r ready.tail) rs
        programToHead runtime outer suffix)) := by
  by_cases hsourceEq : r.source = current
  · by_cases hreadEq : r.read = actual
    · have hslotNe : r.slot ≠ slot := by
        intro hs
        exact ready.mismatch ⟨hsourceEq, hreadEq, hs⟩
      have hslot : r.slot = !slot := by
        cases hr : r.slot <;> cases hs : slot <;> simp_all
      obtain ⟨run⟩ := ruleCursorSlotMismatch_step_bounded_radius slot c.done
        ready.tail ready.path_safe c.boundary ready.boundary_valid r hslot rs
        ready.remaining_ne programToHead ready.read_valid runtime outer suffix
        (by simpa [hreadEq] using ready.source_corridor)
        (by simpa [hslot] using ready.slot_scan)
        (by simpa [hsourceEq, hreadEq] using ready.slot_restore)
        bounds.source_le
        (by simpa [hreadEq] using bounds.source_corridor_le)
        (by simpa using bounds.slot_action_le)
        (by simpa [hsourceEq, hreadEq] using bounds.slot_restore_le)
        bounds.done_le bounds.cursor_path_le bounds.rule_le
      exact ⟨
        { steps := run.steps
          le_bound := run.le_bound
          run := by simpa [ruleCursorResult, ruleCursorBase,
            advanceRuleCursor, ready.path_eq, hsourceEq, hreadEq,
            List.append_assoc] using run.run }⟩
    · obtain ⟨run⟩ := ruleCursorReadMismatch_step_bounded_radius slot
        c.done ready.tail ready.path_safe c.boundary ready.boundary_valid r rs
        ready.remaining_ne programToHead actual ready.read_valid
        ready.actual_valid hreadEq runtime outer suffix ready.source_corridor
        ready.read_scan ready.read_restore ready.program_restore
        bounds.source_le bounds.source_corridor_le bounds.read_scan_le
        bounds.read_restore_le bounds.done_le bounds.cursor_path_le
        bounds.rule_le
      exact ⟨
        { steps := run.steps
          le_bound := run.le_bound.trans (by omega)
          run := by simpa [ruleCursorResult, ruleCursorBase,
            advanceRuleCursor, ready.path_eq, hsourceEq,
            List.append_assoc] using run.run }⟩
  · by_cases hlt : r.source < current
    · obtain ⟨extra, hcurrentEq⟩ : ∃ extra,
          current = r.source + extra + 1 :=
        ⟨current - r.source - 1, by omega⟩
      obtain ⟨run⟩ := ruleCursorSourceShort_step_bounded_radius slot c.done
        ready.tail ready.path_safe c.boundary ready.boundary_valid r rs
        ready.remaining_ne
        (programToHead ++ readHeadNat actual :: runtime) extra outer suffix
        (by simpa [cursorRuleCorridor, List.append_assoc] using
          ready.source_corridor)
        (by simpa [cursorRuleCorridor, List.append_assoc] using
          ready.read_boundary_free)
        bounds.source_le (by simpa [hcurrentEq] using bounds.current_le)
        (by simpa [cursorRuleCorridor, List.append_assoc] using
          bounds.source_corridor_le)
        (by simpa [cursorRuleCorridor, List.append_assoc] using
          bounds.source_short_restore_le)
        bounds.done_le bounds.cursor_path_le bounds.rule_le
      exact ⟨
        { steps := run.steps
          le_bound := run.le_bound.trans (by omega)
          run := by simpa [ruleCursorResult, ruleCursorBase,
            advanceRuleCursor, ready.path_eq, hcurrentEq,
            List.append_assoc] using run.run }⟩
    · have hcurLt : current < r.source := by omega
      obtain ⟨extra, hrsource⟩ : ∃ extra,
          r.source = current + extra + 1 :=
        ⟨r.source - current - 1, by omega⟩
      obtain ⟨run⟩ := ruleCursorSourceLong_step_bounded_radius slot c.done
        ready.tail ready.path_safe c.boundary ready.boundary_valid r rs
        ready.remaining_ne
        (programToHead ++ readHeadNat actual :: runtime) current extra
        hrsource outer suffix
        (by simpa [cursorRuleCorridor, List.append_assoc] using
          ready.source_corridor)
        (by simpa [cursorRuleCorridor, List.append_assoc] using
          ready.read_boundary_free)
        bounds.source_le bounds.current_le
        (by simpa [cursorRuleCorridor, List.append_assoc] using
          bounds.source_corridor_le)
        (by simpa [cursorRuleCorridor, List.append_assoc] using
          bounds.source_long_restore_le extra hrsource)
        bounds.done_le bounds.cursor_path_le bounds.rule_le
      exact ⟨
        { steps := run.steps
          le_bound := run.le_bound.trans (by omega)
          run := by simpa [ruleCursorResult, ruleCursorBase,
            advanceRuleCursor, ready.path_eq, List.append_assoc] using
              run.run }⟩

/-- Uniform-function wrapper retained for consumers that already have a
global radius certificate. -/
theorem cursorMismatchHeadStepAtMost_of_radius
    (R : ℕ)
    (resources : ∀ (slot : Bool) (current actual : ℕ)
      (c : RuleCursorData) (r : ULogBytecode.RuleCode)
      (rs : List ULogBytecode.RuleCode)
      (programToHead runtime : List Tape)
      (ready : CursorMismatchReady slot current actual c r rs
        programToHead runtime),
      CursorMismatchWithinRadius R slot current actual c r rs
        programToHead runtime ready) :
    CursorMismatchHeadStepAtMost (6 * R ^ 2 + 17 * R + 18) := by
  intro slot current actual c r rs programToHead runtime outer suffix ready
  exact cursorMismatchReady_step_bounded_radius R slot current actual c r rs
    programToHead runtime outer suffix ready
    (resources slot current actual c r rs programToHead runtime ready)

/-- A certified mismatch prefix with `s` skipped rules costs at most `s * B`
once each concrete cursor advance has the uniform `B` budget.  This is the
literal fold missing from the old existential mismatch interface. -/
theorem mismatchPrefix_stopFree_atMost
    (B : ℕ) (stepBound : CursorMismatchHeadStepAtMost B)
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    {start final : RuleCursorData}
    {skip rest : List ULogBytecode.RuleCode}
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      start skip rest final) :
    Nonempty (BoundedStopFreeRun (skip.length * B)
      (ruleCursorResult slot current actual start (skip ++ rest)
        programToHead runtime outer suffix)
      (ruleCursorResult slot current actual final rest
        programToHead runtime outer suffix)) := by
  induction trace with
  | nil c rest =>
      exact ⟨
        { steps := 0
          le_bound := by simp
          run :=
            { valid := .nil _
              stop_free := by intro m hm; simp at hm } }⟩
  | cons c r skip rest final ready next ih =>
      obtain ⟨⟨a, ha, hstep⟩⟩ := stepBound slot current actual c r (skip ++ rest)
        programToHead runtime outer suffix ready
      obtain ⟨⟨b, hb, htail⟩⟩ := ih
      refine ⟨
        { steps := a + b
          le_bound := ?_
          run := hstep.append htail }⟩
      calc
        a + b ≤ B + skip.length * B := Nat.add_le_add ha hb
        _ = (skip.length + 1) * B := by
          rw [Nat.add_mul]
          omega

/-- Trace-indexed quantitative envelope.  Unlike the global function-valued
interface, this records bounds only for the physical nodes that actually
occur in one certified mismatch trace. -/
inductive MismatchPrefixWithinRadius
    (R : ℕ) (slot : Bool) (current actual : ℕ)
    (programToHead runtime : List Tape) :
    ∀ {start final : RuleCursorData}
      {skip rest : List ULogBytecode.RuleCode},
      MismatchPrefixTrace slot current actual programToHead runtime
        start skip rest final → Prop
  | nil (c : RuleCursorData) (rest : List ULogBytecode.RuleCode) :
      MismatchPrefixWithinRadius R slot current actual programToHead runtime
        (.nil c rest)
  | cons (c : RuleCursorData) (r : ULogBytecode.RuleCode)
      (skip rest : List ULogBytecode.RuleCode) (final : RuleCursorData)
      (ready : CursorMismatchReady slot current actual c r (skip ++ rest)
        programToHead runtime)
      (next : MismatchPrefixTrace slot current actual programToHead runtime
        (advanceRuleCursor c r ready.tail) skip rest final)
      (headBound : CursorMismatchWithinRadius R slot current actual c r
        (skip ++ rest) programToHead runtime ready)
      (tailBound : MismatchPrefixWithinRadius R slot current actual
        programToHead runtime next) :
      MismatchPrefixWithinRadius R slot current actual programToHead runtime
        (.cons c r skip rest final ready next)

/-- The physical trace-indexed fold; this is the form used by the canonical
lookup certificate and avoids quantifying over unrealizable cursor nodes. -/
theorem mismatchPrefix_stopFree_atMost_traceRadius
    (R : ℕ) (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    {start final : RuleCursorData}
    {skip rest : List ULogBytecode.RuleCode}
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      start skip rest final)
    (radius : MismatchPrefixWithinRadius R slot current actual
      programToHead runtime trace) :
    Nonempty (BoundedStopFreeRun
      (skip.length * (6 * R ^ 2 + 17 * R + 18))
      (ruleCursorResult slot current actual start (skip ++ rest)
        programToHead runtime outer suffix)
      (ruleCursorResult slot current actual final rest
        programToHead runtime outer suffix)) := by
  induction radius with
  | nil c rest =>
      exact ⟨
        { steps := 0
          le_bound := by simp
          run :=
            { valid := .nil _
              stop_free := by intro m hm; simp at hm } }⟩
  | cons c r skip rest final ready next headBound tailBound ih =>
      obtain ⟨headRun⟩ := cursorMismatchReady_step_bounded_radius R slot
        current actual c r (skip ++ rest) programToHead runtime outer suffix
        ready headBound
      obtain ⟨tailRun⟩ := ih
      refine ⟨
        { steps := headRun.steps + tailRun.steps
          le_bound := ?_
          run := headRun.run.append tailRun.run }⟩
      calc
        headRun.steps + tailRun.steps ≤
            (6 * R ^ 2 + 17 * R + 18) +
              skip.length * (6 * R ^ 2 + 17 * R + 18) :=
          Nat.add_le_add headRun.le_bound tailRun.le_bound
        _ = (skip.length + 1) * (6 * R ^ 2 + 17 * R + 18) := by ring

def canonicalMismatchBudget
    (current actual : ℕ) (passed skip rest : List ULogBytecode.RuleCode)
    (programToHead runtime : List Tape) : ℕ :=
  32 * ((ULogBytecode.encodeRules (passed ++ skip ++ rest)).length +
    (passed ++ skip ++ rest).length + programToHead.length +
      runtime.length + current + actual + 1)

/-- The active (non-outer) physical span charged by one semantic frame's
rule cursor.  It is exactly the canonical mismatch budget after automatic
lookup decomposes the program into skipped, matching, and remaining rules. -/
def semanticFrameCursorRadius
    (input : List Bool) (frame : SemanticCycleFrame input suffix) : ℕ :=
  32 * ((ULogBytecode.encodeRules frame.config.program).length +
    frame.config.program.length + (payloadProgramPrefix input).length +
      frame.config.leftRev.length + frame.config.right.length +
        frame.clockZeros + 1 + frame.runtime.length + frame.config.state +
          frame.config.focus + 1)

theorem canonicalMismatchBudget_eq_frameCursorRadius
    {input : List Bool} (frame : SemanticCycleFrame input suffix)
    (skip : List ULogBytecode.RuleCode) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode)
    (heq : frame.config.program = skip ++ r :: rs) :
    canonicalMismatchBudget frame.config.state frame.config.focus [] skip
        (r :: rs)
        (cursorDynamicProgramToHead input
          (frame.config.leftRev.map payloadNat))
        (clockCellsAfter (frame.config.right.map payloadNat)
          frame.clockZeros frame.runtime) =
      semanticFrameCursorRadius input frame := by
  simp [canonicalMismatchBudget, semanticFrameCursorRadius,
    cursorDynamicProgramToHead, clockCellsAfter, heq,
    List.append_assoc]
  omega

/-- Quantitative physical data exported by an actual semantic frame.  This
is a constructed envelope, not an additional semantic oracle. -/
structure CopiedFrameSizeEnvelope
    {input : List Bool} (frame : SemanticCycleFrame input suffix)
    (R : ℕ) : Prop where
  cursor_radius_le : semanticFrameCursorRadius input frame ≤ R
  right_le : frame.config.right.length ≤ R
  clock_le : frame.clockZeros ≤ R
  rules_le : frame.config.program.length ≤ R
  dynamic_path_le :
    (dynamicRuleReturnPath (frame.config.leftRev.map payloadNat)
      frame.config.program input).length ≤ R

/-- Every concrete semantic frame generates its own literal size envelope.
The later copied-workspace theorem only has to dominate this one scalar. -/
theorem semanticFrame_has_sizeEnvelope
    {input : List Bool} (frame : SemanticCycleFrame input suffix) :
    CopiedFrameSizeEnvelope frame (semanticFrameCursorRadius input frame) := by
  have hbase :
      (ULogBytecode.encodeRules frame.config.program).length +
        frame.config.program.length + (payloadProgramPrefix input).length +
          frame.config.leftRev.length + frame.config.right.length +
            frame.clockZeros + 1 + frame.runtime.length +
              frame.config.state + frame.config.focus + 1 ≤
        semanticFrameCursorRadius input frame := by
    dsimp [semanticFrameCursorRadius]
    omega
  refine
    { cursor_radius_le := Nat.le_refl _
      right_le := by omega
      clock_le := by omega
      rules_le := by omega
      dynamic_path_le := ?_ }
  rw [dynamicRuleReturnPath_length]
  simp only [List.length_map]
  omega

theorem payloadProgramPrefix_length_le (input : List Bool) :
    (payloadProgramPrefix input).length ≤ input.length + 1 := by
  cases input <;> simp [payloadProgramPrefix]

theorem linear_frame_size_le_exponential_radius (m : ℕ) :
    32 * (m + 6) ≤ 2 ^ (8 * (m + 1)) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      have hscale : 32 * (m + 1 + 6) ≤ 256 * (32 * (m + 6)) := by
        omega
      calc
        32 * (m + 1 + 6) ≤ 256 * (32 * (m + 6)) := hscale
        _ ≤ 256 * 2 ^ (8 * (m + 1)) := Nat.mul_le_mul_left 256 ih
        _ = 2 ^ (8 * (m + 1 + 1)) := by ring_nf

/-- The actual bootstrap constructor's cursor radius is paid by the copier's
exponential work radius. -/
theorem bootstrapSemanticFrame_cursorRadius_le_copiedCoreRadius
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (capacity : ℕ) (outerTail : List Tape)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    semanticFrameCursorRadius input
        (bootstrapSemanticFrame rules input padding capacity outerTail) ≤
      PakOuterULogBridge.copiedCoreRadius x := by
  have hpayload := payloadProgramPrefix_length_le input
  have hwordLen : x.length =
      (ULogBytecode.encodeProgram rules).length +
        2 * input.length + padding.length + 1 := by
    rw [hword]
    simp [ULogBytecode.length_encodePayload]
    omega
  have hprogramLen : (ULogBytecode.encodeProgram rules).length =
      rules.length + 1 + (ULogBytecode.encodeRules rules).length := by
    simp [ULogBytecode.encodeProgram]
  have hlinear : semanticFrameCursorRadius input
      (bootstrapSemanticFrame rules input padding capacity outerTail) ≤
      32 * (x.length + 6) := by
    cases input with
    | nil =>
        simp [semanticFrameCursorRadius, bootstrapSemanticFrame,
          ULogSemantics.startFrom, ULogSemantics.initialTape,
          ULogSemantics.startCode, ULogSemantics.blankCode,
          payloadProgramPrefix] at hpayload hwordLen ⊢
        omega
    | cons b bs =>
        cases b <;>
          simp [semanticFrameCursorRadius, bootstrapSemanticFrame,
            ULogSemantics.startFrom, ULogSemantics.initialTape,
            ULogSemantics.startCode, ULogSemantics.bitCode,
            payloadProgramPrefix] at hpayload hwordLen ⊢ <;>
          omega
  calc
    _ ≤ 32 * (x.length + 6) := hlinear
    _ ≤ 2 ^ (8 * (x.length + 1)) :=
      linear_frame_size_le_exponential_radius x.length
    _ = PakOuterULogBridge.copiedCoreRadius x := rfl

/-- A history measure whose only dynamic contribution is the represented
semantic tape span and clock reframe; state/focus are paid separately from
the selected rule width. -/
def semanticFrameGlobalMeasure
    (input : List Bool) (frame : SemanticCycleFrame input suffix) : ℕ :=
  3 * (ULogBytecode.encodeRules frame.config.program).length +
    frame.config.program.length + (payloadProgramPrefix input).length +
      frame.config.leftRev.length + frame.config.right.length +
        frame.clockZeros + frame.runtime.length + 5

theorem encodeRule_length_le_encodeRules_of_mem
    {r : ULogBytecode.RuleCode} {rules : List ULogBytecode.RuleCode}
    (hr : r ∈ rules) :
    (ULogBytecode.encodeRule r).length ≤
      (ULogBytecode.encodeRules rules).length := by
  induction rules with
  | nil => simp at hr
  | cons s ss ih =>
      rcases List.mem_cons.mp hr with rfl | hr
      · simp [ULogBytecode.encodeRules]
      · have h := ih hr
        simp [ULogBytecode.encodeRules]
        omega

theorem applyAction_tapeSpan_le
    (c : ULogSemantics.Config) (a : ULogBytecode.ActionCode) :
    (ULogSemantics.applyAction c a).leftRev.length +
        (ULogSemantics.applyAction c a).right.length ≤
      c.leftRev.length + c.right.length + 1 := by
  cases hm : a.move with
  | stay => simp [ULogSemantics.applyAction, hm]
  | right => cases hr : c.right <;>
      simp [ULogSemantics.applyAction, hm, hr] <;> omega
  | left => cases hl : c.leftRev <;>
      simp [ULogSemantics.applyAction, hm, hl] <;> omega

/-- One reframe step increases the history measure by at most one. -/
theorem semanticFrameGlobalMeasure_reframeNext_le
    {input : List Bool} (frame : SemanticCycleFrame input suffix)
    (action : ULogBytecode.ActionCode)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime)) :
    semanticFrameGlobalMeasure input (frame.reframeNext action reframe) ≤
      semanticFrameGlobalMeasure input frame + 1 := by
  have htape := applyAction_tapeSpan_le frame.config action
  have hclockLen := congrArg List.length reframe.eq_before
  simp [clockCellsBefore, clockCellsAfter] at hclockLen
  simp [semanticFrameGlobalMeasure, SemanticCycleFrame.reframeNext,
    applyAction_program_eq]
  omega

/-- At any actual nonhalting selected rule, the local cursor radius is paid
by the history measure. -/
theorem semanticFrameCursorRadius_le_globalMeasure
    {input : List Bool} (frame : SemanticCycleFrame input suffix)
    (slot : Bool) (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (hfocus : frame.config.focus < 3) :
    semanticFrameCursorRadius input frame ≤
      32 * semanticFrameGlobalMeasure input frame := by
  obtain ⟨r, hr, hsource, hread, hslot, haction⟩ :=
    ULogBytecode.lookupRule_some_mem hlookup
  have hrule := encodeRule_length_le_encodeRules_of_mem hr
  have hsourceRule : r.source ≤ (ULogBytecode.encodeRule r).length := by
    rcases r with ⟨source, read, ruleSlot, ⟨write, target, move⟩⟩
    cases move <;>
      simp [ULogBytecode.encodeRule, ULogBytecode.encodeAction,
        ULogBytecode.encodeMove, ULogBytecode.encodeNatField] <;>
      omega
  have hstate : frame.config.state ≤
      (ULogBytecode.encodeRules frame.config.program).length := by
    calc
      frame.config.state = r.source := hsource.symm
      _ ≤ (ULogBytecode.encodeRule r).length := hsourceRule
      _ ≤ (ULogBytecode.encodeRules frame.config.program).length := hrule
  simp [semanticFrameCursorRadius, semanticFrameGlobalMeasure]
  omega

/-- A trace-indexed global envelope tied to the copier radius.  `elapsed`
counts semantic cycles already consumed. -/
structure GlobalCopiedEnvelope
    (x : ConcretePakSide.Word) {input : List Bool}
    (frame : SemanticCycleFrame input suffix) (elapsed : ℕ) : Prop where
  measure_le : semanticFrameGlobalMeasure input frame ≤
    PakOuterULogBridge.copiedCoreRadius x + elapsed
  elapsed_le : elapsed ≤ PakOuterULogBridge.copiedCoreRadius x

theorem bootstrapSemanticFrame_globalMeasure_le_copiedCoreRadius
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (capacity : ℕ) (outerTail : List Tape)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    semanticFrameGlobalMeasure input
        (bootstrapSemanticFrame rules input padding capacity outerTail) ≤
      PakOuterULogBridge.copiedCoreRadius x := by
  have hpayload := payloadProgramPrefix_length_le input
  have hwordLen : x.length =
      (ULogBytecode.encodeProgram rules).length +
        2 * input.length + padding.length + 1 := by
    rw [hword]
    simp [ULogBytecode.length_encodePayload]
    omega
  have hprogramLen : (ULogBytecode.encodeProgram rules).length =
      rules.length + 1 + (ULogBytecode.encodeRules rules).length := by
    simp [ULogBytecode.encodeProgram]
  have hmeasure : semanticFrameGlobalMeasure input
      (bootstrapSemanticFrame rules input padding capacity outerTail) ≤
      3 * (x.length + 6) := by
    cases input with
    | nil =>
        simp [semanticFrameGlobalMeasure, bootstrapSemanticFrame,
          ULogSemantics.startFrom, ULogSemantics.initialTape,
          payloadProgramPrefix] at hpayload hwordLen ⊢
        omega
    | cons b bs =>
        cases b <;>
          simp [semanticFrameGlobalMeasure, bootstrapSemanticFrame,
            ULogSemantics.startFrom, ULogSemantics.initialTape,
            payloadProgramPrefix] at hpayload hwordLen ⊢ <;>
          omega
  calc
    _ ≤ 3 * (x.length + 6) := hmeasure
    _ ≤ 32 * (x.length + 6) := by omega
    _ ≤ PakOuterULogBridge.copiedCoreRadius x :=
      linear_frame_size_le_exponential_radius x.length

theorem bootstrapSemanticFrame_globalEnvelope
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (capacity : ℕ) (outerTail : List Tape)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding) :
    GlobalCopiedEnvelope x
      (bootstrapSemanticFrame rules input padding capacity outerTail) 0 :=
  { measure_le := by
      simpa using bootstrapSemanticFrame_globalMeasure_le_copiedCoreRadius
        x rules input padding capacity outerTail hword
    elapsed_le := by omega }

/-- One semantic reframe advances the global envelope by one elapsed cycle. -/
theorem GlobalCopiedEnvelope.next
    {x : ConcretePakSide.Word} {input : List Bool}
    {frame : SemanticCycleFrame input suffix} {elapsed : ℕ}
    (h : GlobalCopiedEnvelope x frame elapsed)
    (action : ULogBytecode.ActionCode)
    (reframe : ClockReframe
      ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
      (clockCellsAfter
        ((ULogSemantics.applyAction frame.config action).right.map payloadNat)
        frame.clockZeros frame.runtime))
    (helapsed : elapsed + 1 ≤ PakOuterULogBridge.copiedCoreRadius x) :
    GlobalCopiedEnvelope x (frame.reframeNext action reframe) (elapsed + 1) :=
  { measure_le := by
      have hstep := semanticFrameGlobalMeasure_reframeNext_le frame action reframe
      have hm := h.measure_le
      omega
    elapsed_le := helapsed }

/-- Every selected cycle in a globally enveloped trace has local cursor
radius at most `64` times the copied radius. -/
theorem GlobalCopiedEnvelope.cursorRadius_le
    {x : ConcretePakSide.Word} {input : List Bool}
    {frame : SemanticCycleFrame input suffix} {elapsed : ℕ}
    (h : GlobalCopiedEnvelope x frame elapsed)
    (slot : Bool) (action : ULogBytecode.ActionCode)
    (hlookup : ULogBytecode.lookupRule frame.config.program frame.config.state
      frame.config.focus slot = some action)
    (hfocus : frame.config.focus < 3) :
    semanticFrameCursorRadius input frame ≤
      64 * PakOuterULogBridge.copiedCoreRadius x := by
  have hc := semanticFrameCursorRadius_le_globalMeasure frame slot action
    hlookup hfocus
  have hm := h.measure_le
  have he := h.elapsed_le
  calc
    semanticFrameCursorRadius input frame ≤
        32 * semanticFrameGlobalMeasure input frame := hc
    _ ≤ 32 * (PakOuterULogBridge.copiedCoreRadius x + elapsed) :=
      Nat.mul_le_mul_left 32 hm
    _ ≤ 64 * PakOuterULogBridge.copiedCoreRadius x := by omega

theorem accepting_microFuel_scaled_lt_pow_nine
    {R : ℕ} (hR : 256 ≤ R) :
    6 * (64 * R) ^ 3 + 23 * (64 * R) ^ 2 + 38 * (64 * R) + 28 <
      R ^ 9 := by
  let Q := 64 * R
  have hQ : 256 ≤ Q := by dsimp [Q]; omega
  have hQ2 : 256 ^ 2 ≤ Q ^ 2 := Nat.pow_le_pow_left hQ 2
  have hQ3 : 256 ^ 3 ≤ Q ^ 3 := Nat.pow_le_pow_left hQ 3
  have hpoly : 6 * Q ^ 3 + 23 * Q ^ 2 + 38 * Q + 28 <
      7 * Q ^ 3 := by
    nlinarith [hQ2, hQ3]
  have hR6 : 256 ^ 6 ≤ R ^ 6 := Nat.pow_le_pow_left hR 6
  have hcoef : 1835008 < R ^ 6 := by
    have : 1835008 < 256 ^ 6 := by norm_num
    exact this.trans_le hR6
  have hRpos : 0 < R ^ 3 := pow_pos (by omega) _
  calc
    6 * (64 * R) ^ 3 + 23 * (64 * R) ^ 2 + 38 * (64 * R) + 28 =
        6 * Q ^ 3 + 23 * Q ^ 2 + 38 * Q + 28 := by rfl
    _ < 7 * Q ^ 3 := hpoly
    _ = 1835008 * R ^ 3 := by dsimp [Q]; ring
    _ < R ^ 6 * R ^ 3 := Nat.mul_lt_mul_of_pos_right hcoef hRpos
    _ = R ^ 9 := by ring

structure MatchedTargetZeroWithinRadius (R : ℕ)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead runtime : List Tape) : Prop where
  source_le : r.source ≤ R
  source_corridor_le :
    (cursorRuleCorridor r rs programToHead
      (readHeadNat r.read) runtime).length ≤ R
  read_corridor_le :
    (encodedActionPath r.action.write r.action.target r.action.move
      (cursorMatchedMovePath rs programToHead)).length ≤ R
  action_corridor_le :
    (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead).length ≤ R
  target_corridor_le :
    (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
      writeHeadNat r.action.write :: runtime).length ≤ R

theorem matchedTargetZeroWithin_canonicalBudget
    (current actual : ℕ) (passed skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (programToHead runtime : List Tape) :
    MatchedTargetZeroWithinRadius
      (canonicalMismatchBudget current actual passed skip (r :: rs)
        programToHead runtime)
      r rs programToHead runtime := by
  have henc :
      (ULogBytecode.encodeRules (passed ++ skip ++ r :: rs)).length =
        (ULogBytecode.encodeRules passed).length +
          (ULogBytecode.encodeRules skip).length +
            (ULogBytecode.encodeRule r).length +
              (ULogBytecode.encodeRules rs).length := by
    simp [encodeRules_append, ULogBytecode.encodeRules]
    omega
  have hlist : (passed ++ skip ++ r :: rs).length =
      passed.length + skip.length + 1 + rs.length := by
    simp
    omega
  rw [show canonicalMismatchBudget current actual passed skip (r :: rs)
        programToHead runtime =
      32 * ((ULogBytecode.encodeRules (passed ++ skip ++ r :: rs)).length +
        (passed ++ skip ++ r :: rs).length + programToHead.length +
          runtime.length + current + actual + 1) by
    rfl, henc, hlist]
  rcases r with ⟨source, read, ruleSlot, ⟨write, target, move⟩⟩
  cases move <;>
    refine
      { source_le := by
          simp [ULogBytecode.encodeRule, ULogBytecode.encodeAction,
            ULogBytecode.encodeMove, ULogBytecode.encodeNatField]; omega
        source_corridor_le := by
          simp [cursorRuleCorridor, ruleContinuationCorridor,
            cursorMatchedMovePath, encodedActionPath,
            ULogBytecode.encodeRule, ULogBytecode.encodeAction,
            ULogBytecode.encodeMove, ULogBytecode.encodeNatField,
            moveBits]; omega
        read_corridor_le := by
          simp [cursorMatchedMovePath, encodedActionPath,
            ULogBytecode.encodeRule, ULogBytecode.encodeAction,
            ULogBytecode.encodeMove, ULogBytecode.encodeNatField,
            moveBits]; omega
        action_corridor_le := by
          simp [cursorMatchedMovePath, moveBits,
            ULogBytecode.encodeRule, ULogBytecode.encodeAction,
            ULogBytecode.encodeMove, ULogBytecode.encodeNatField]; omega
        target_corridor_le := by
          simp [cursorMatchedMovePath, moveBits,
            ULogBytecode.encodeRule, ULogBytecode.encodeAction,
            ULogBytecode.encodeMove, ULogBytecode.encodeNatField,
            writeHeadNat]; omega }

/-- Direct quantitative fold over the automatic certificate list.  This is
the canonical physical form: no proof-index transport and no global oracle
over unrealizable cursor states is required. -/
theorem mismatchCertificateList_stopFree_atMost_budget
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    {skip rest : List ULogBytecode.RuleCode}
    (certs : MismatchCertificateList slot current actual programToHead runtime
      skip rest)
    (hrest : rest ≠ []) (passed : List ULogBytecode.RuleCode) :
    let R := canonicalMismatchBudget current actual passed skip rest
      programToHead runtime
    Nonempty (BoundedStopFreeRun
      (skip.length * (6 * R ^ 2 + 17 * R + 18))
      (ruleCursorResult slot current actual
        (canonicalRuleCursor passed (skip ++ rest)) (skip ++ rest)
        programToHead runtime outer suffix)
      (ruleCursorResult slot current actual
        (canonicalRuleCursor (passed ++ skip) rest) rest
        programToHead runtime outer suffix)) := by
  induction certs generalizing passed with
  | nil rest =>
      exact ⟨
        { steps := 0
          le_bound := by simp
          run := by simpa using (show StopFreeValidZeroRun 0
            (ruleCursorResult slot current actual
              (canonicalRuleCursor passed rest) rest
              programToHead runtime outer suffix)
            (ruleCursorResult slot current actual
              (canonicalRuleCursor passed rest) rest
              programToHead runtime outer suffix) from
              { valid := .nil _
                stop_free := by intro m hm; simp at hm }) }⟩
  | cons r skip rest head tail ih =>
      let R := canonicalMismatchBudget current actual passed (r :: skip) rest
        programToHead runtime
      have hremaining : skip ++ rest ≠ [] := by
        intro h
        have : rest = [] := by
          simpa using congrArg (List.drop skip.length) h
        exact hrest this
      let c := canonicalRuleCursor passed (r :: (skip ++ rest))
      let tailPath := (canonicalRuleCursor passed (skip ++ rest)).path
      have hpath : c.path = ulogCore pcDone :: tailPath :=
        canonicalRuleCursor_path_cons passed r (skip ++ rest) hremaining
      let ready : CursorMismatchReady slot current actual c r
          (skip ++ rest) programToHead runtime :=
        { tail := tailPath
          path_eq := hpath
          path_safe := by
            rw [← hpath]
            exact canonicalRuleCursor_path_safe passed
              (r :: (skip ++ rest))
          boundary_valid :=
            boundaryAfter_valid sourceBoundary (Or.inl rfl) passed
          remaining_ne := hremaining
          mismatch := head.mismatch
          actual_valid := head.actual_valid
          read_valid := head.read_valid
          source_corridor := head.source_corridor
          read_boundary_free := head.read_boundary_free
          read_scan := head.read_scan
          read_restore := head.read_restore
          slot_scan := head.slot_scan
          slot_restore := head.slot_restore
          program_restore := head.program_restore }
      have headRadius₀ := canonicalCursorMismatchWithin_budget slot current
        actual passed r (skip ++ rest) hremaining programToHead runtime ready
      have headRadius : CursorMismatchWithinRadius R slot current actual c r
          (skip ++ rest) programToHead runtime ready := by
        have hbudget :
            32 * ((ULogBytecode.encodeRules
                (passed ++ r :: (skip ++ rest))).length +
              (passed ++ r :: (skip ++ rest)).length +
                programToHead.length + runtime.length + current + actual + 1) =
              R := by
          simp [R, canonicalMismatchBudget, encodeRules_append,
            List.append_assoc]
        simpa only [hbudget] using headRadius₀
      obtain ⟨headRun⟩ := cursorMismatchReady_step_bounded_radius R slot
        current actual c r (skip ++ rest) programToHead runtime outer suffix
        ready headRadius
      obtain ⟨tailRun⟩ := ih hrest (passed ++ [r])
      have hbudgetTail : canonicalMismatchBudget current actual
          (passed ++ [r]) skip rest programToHead runtime = R := by
        simp [R, canonicalMismatchBudget, encodeRules_append,
          List.append_assoc]
      have hstep : advanceRuleCursor c r tailPath =
          canonicalRuleCursor (passed ++ [r]) (skip ++ rest) :=
        advance_canonicalRuleCursor passed r (skip ++ rest)
      have tailRun' : BoundedStopFreeRun
          (skip.length * (6 * R ^ 2 + 17 * R + 18))
          (ruleCursorResult slot current actual
            (advanceRuleCursor c r tailPath) (skip ++ rest)
            programToHead runtime outer suffix)
          (ruleCursorResult slot current actual
            (canonicalRuleCursor (passed ++ (r :: skip)) rest) rest
            programToHead runtime outer suffix) := by
        simpa [hbudgetTail, hstep, List.append_assoc] using tailRun
      refine ⟨
        { steps := headRun.steps + tailRun'.steps
          le_bound := ?_
          run := by
            simpa [R, c, tailPath, List.append_assoc] using
              headRun.run.append tailRun'.run }⟩
      calc
        headRun.steps + tailRun'.steps ≤
            (6 * R ^ 2 + 17 * R + 18) +
              skip.length * (6 * R ^ 2 + 17 * R + 18) :=
          Nat.add_le_add headRun.le_bound tailRun'.le_bound
        _ = (r :: skip).length * (6 * R ^ 2 + 17 * R + 18) := by
          simp
          ring

/-- Fully automatic canonical accepting cursor suffix: the scan certificate
itself now supplies the common size envelope for all mismatching rules and
for the first matching rule. -/
theorem mismatchCertificateList_matchedTargetZero_bounded
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (certs : MismatchCertificateList slot current actual programToHead runtime
      skip (r :: rs))
    (hmatch : RuleMatchesCursor slot current actual r)
    (htarget : r.action.target = 0)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (hboundary : (canonicalRuleCursor skip (r :: rs)).boundary =
        sourceBoundary ∨
      (canonicalRuleCursor skip (r :: rs)).boundary = sourceBoundaryZero ∨
      (canonicalRuleCursor skip (r :: rs)).boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs programToHead))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: runtime)) :
    let R := canonicalMismatchBudget current actual [] skip (r :: rs)
      programToHead runtime
    ∃ (z : MStarParserExecution.Zipper Tape),
      ∃ hit : FirstValidZeroHit IsConcreteCycleStop
        (ruleCursorResult slot current actual
          (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
          programToHead runtime outer (ulogCore stateSep :: suffix))
        (.accepted z),
        hit.steps ≤ 6 * R ^ 3 + 23 * R ^ 2 + 32 * R + 22 := by
  let R := canonicalMismatchBudget current actual [] skip (r :: rs)
    programToHead runtime
  obtain ⟨prefixRun⟩ := mismatchCertificateList_stopFree_atMost_budget slot
    current actual programToHead runtime outer (ulogCore stateSep :: suffix)
    certs (by simp) []
  have prefixRun' : BoundedStopFreeRun
      (skip.length * (6 * R ^ 2 + 17 * R + 18))
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        programToHead runtime outer (ulogCore stateSep :: suffix))
      (ruleCursorResult slot current actual
        (canonicalRuleCursor skip (r :: rs)) (r :: rs)
        programToHead runtime outer (ulogCore stateSep :: suffix)) := by
    simpa [R, canonicalRuleCursor_initial] using prefixRun
  let final := canonicalRuleCursor skip (r :: rs)
  let matchedResult := ruleCursorMatchedTargetZero_firstStop final.boundary
    hboundary r rs programToHead
    ((List.replicate final.done (ulogCore codeZero) ++
      ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: outer)
    runtime htarget hread hwrite hcorridor hreadPath hwritePath htargetPath
    suffix
  have matchedBounds := matchedTargetZeroWithin_canonicalBudget current actual
    [] skip r rs programToHead runtime
  have hmatchedDirect₀ : matchedResult.2.steps ≤
      6 * R ^ 2 + 14 * R + 22 := by
    dsimp [matchedResult, final]
    exact ruleCursorMatchedTargetZero_firstStop_steps_le_radius
      (canonicalRuleCursor skip (r :: rs)).boundary hboundary r rs
      programToHead
      ((List.replicate (canonicalRuleCursor skip (r :: rs)).done
          (ulogCore codeZero) ++
        ulogCore pcDone :: (canonicalRuleCursor skip (r :: rs)).path).reverse ++
          ulogCore pcMark :: outer)
      runtime htarget hread hwrite hcorridor hreadPath hwritePath htargetPath
      suffix matchedBounds.source_le matchedBounds.source_corridor_le
      matchedBounds.read_corridor_le matchedBounds.action_corridor_le
      matchedBounds.target_corridor_le
  obtain ⟨z, matched⟩ := matchedResult
  rcases hmatch with ⟨hsourceEq, hreadEq, hslotEq⟩
  have matched' : FirstValidZeroHit IsConcreteCycleStop
      (ruleCursorResult slot current actual final (r :: rs)
        programToHead runtime outer (ulogCore stateSep :: suffix))
      (.accepted z) := by
    simpa [final, ruleCursorResult, ruleCursorBase, hsourceEq, hreadEq,
      hslotEq, List.append_assoc] using matched
  have hmatched : matched'.steps ≤ 6 * R ^ 2 + 14 * R + 22 := by
    have hstart :
        ruleCursorResult slot current actual final (r :: rs)
            programToHead runtime outer (ulogCore stateSep :: suffix) =
          atBitsTail (.fieldCompare .source r.slot)
            (ULogBytecode.encodeRules (r :: rs))
            (ulogCore final.boundary ::
              (List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: outer)
            (programToHead ++ readHeadNat r.read :: runtime ++
              List.replicate r.source (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep :: suffix) := by
      simp [ruleCursorResult, ruleCursorBase, hsourceEq, hreadEq, hslotEq,
        List.append_assoc]
    have hsteps := FirstValidZeroHit.steps_eq_of_start_eq hstart matched'
      matched
    exact hsteps ▸ hmatchedDirect₀
  let hit := prefixRun'.run.appendFirstHit matched'
  refine ⟨z, hit, ?_⟩
  change prefixRun'.steps + matched'.steps ≤
    6 * R ^ 3 + 23 * R ^ 2 + 32 * R + 22
  have hskip : skip.length ≤ R := by
    dsimp [R, canonicalMismatchBudget]
    simp
    omega
  have hp := prefixRun'.le_bound.trans
    (Nat.mul_le_mul_right (6 * R ^ 2 + 17 * R + 18) hskip)
  calc
    prefixRun'.steps + matched'.steps ≤
        R * (6 * R ^ 2 + 17 * R + 18) +
          (6 * R ^ 2 + 14 * R + 22) := Nat.add_le_add hp hmatched
    _ = 6 * R ^ 3 + 23 * R ^ 2 + 32 * R + 22 := by ring

/-- Common canonical prefix for all nonterminal branches, ending immediately
before the target/move-specific suffix. -/
theorem mismatchCertificateList_matchedActionWrite_bounded
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer tail : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (certs : MismatchCertificateList slot current actual programToHead runtime
      skip (r :: rs))
    (hmatch : RuleMatchesCursor slot current actual r)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (hboundary : (canonicalRuleCursor skip (r :: rs)).boundary =
        sourceBoundary ∨
      (canonicalRuleCursor skip (r :: rs)).boundary = sourceBoundaryZero ∨
      (canonicalRuleCursor skip (r :: rs)).boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move (cursorMatchedMovePath rs programToHead))) :
    let R := canonicalMismatchBudget current actual [] skip (r :: rs)
      programToHead runtime
    Nonempty (BoundedStopFreeRun
      (6 * R ^ 3 + 23 * R ^ 2 + 29 * R + 13)
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        programToHead runtime outer tail)
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read
          (canonicalRuleCursor skip (r :: rs)).boundary
          ((List.replicate (canonicalRuleCursor skip (r :: rs)).done
              (ulogCore codeZero) ++
            ulogCore pcDone :: (canonicalRuleCursor skip (r :: rs)).path).reverse ++
              ulogCore pcMark :: outer))
        (List.replicate r.action.target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits r.action.move ++
            cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: tail))) := by
  let R := canonicalMismatchBudget current actual [] skip (r :: rs)
    programToHead runtime
  obtain ⟨prefixRun⟩ := mismatchCertificateList_stopFree_atMost_budget slot
    current actual programToHead runtime outer tail certs (by simp) []
  have prefixRun' : BoundedStopFreeRun
      (skip.length * (6 * R ^ 2 + 17 * R + 18))
      (ruleCursorResult slot current actual
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        programToHead runtime outer tail)
      (ruleCursorResult slot current actual
        (canonicalRuleCursor skip (r :: rs)) (r :: rs)
        programToHead runtime outer tail) := by
    simpa [R, canonicalRuleCursor_initial] using prefixRun
  let final := canonicalRuleCursor skip (r :: rs)
  have matchedBounds := matchedTargetZeroWithin_canonicalBudget current actual
    [] skip r rs programToHead runtime
  obtain ⟨matchedRun⟩ := ruleCursorMatched_actionWrite_bounded_radius
    final.boundary hboundary r rs programToHead
    ((List.replicate final.done (ulogCore codeZero) ++
      ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: outer)
    runtime hread hwrite hcorridor hreadPath tail matchedBounds.source_le
    matchedBounds.source_corridor_le matchedBounds.read_corridor_le
  rcases hmatch with ⟨hsourceEq, hreadEq, hslotEq⟩
  have matchedRun' : StopFreeValidZeroRun matchedRun.steps
      (ruleCursorResult slot current actual final (r :: rs)
        programToHead runtime outer tail)
      (actionWriteStart r.action.write
        (matchedReadLeftAt r.slot r.source r.read final.boundary
          ((List.replicate final.done (ulogCore codeZero) ++
            ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: outer))
        (List.replicate r.action.target (ulogCore codeZero) ++
          ulogCore codeOne :: moveBits r.action.move ++
            cursorMatchedMovePath rs programToHead)
        (readHeadNat r.read)
        (runtime ++ List.replicate r.source (ulogCore stateZero) ++
          ulogCore stateOne :: tail)) := by
    simpa [ruleCursorResult, ruleCursorBase, hsourceEq, hreadEq, hslotEq,
      List.append_assoc] using matchedRun.run
  refine ⟨
    { steps := prefixRun'.steps + matchedRun.steps
      le_bound := ?_
      run := by simpa [final] using prefixRun'.run.append matchedRun' }⟩
  have hskip : skip.length ≤ R := by
    dsimp [R, canonicalMismatchBudget]
    simp
    omega
  have hp := prefixRun'.le_bound.trans
    (Nat.mul_le_mul_right (6 * R ^ 2 + 17 * R + 18) hskip)
  have hm := matchedRun.le_bound
  calc
    prefixRun'.steps + matchedRun.steps ≤
        R * (6 * R ^ 2 + 17 * R + 18) +
          (6 * R ^ 2 + 11 * R + 13) := Nat.add_le_add hp hm
    _ = 6 * R ^ 3 + 23 * R ^ 2 + 29 * R + 13 := by ring

/-- The canonical accepting refinement automatically satisfies the complete
raw-cycle polynomial bound at the concrete frame radius. -/
theorem exactAcceptingCycleRefinement_microFuel_le_frameRadius
    {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (slot : Bool)
    (next : ULogSemantics.Config) (ready : FrameReady frame)
    (hstep : ULogSemantics.stepSlot slot frame.config = some next)
    (haccept : ULogSemantics.accepting next = true) :
    let R := semanticFrameCursorRadius input frame
    let cycle :=
      (exactAcceptingCycleRefinement frame slot ready next hstep haccept).exact_cycle
    cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps ≤
      6 * R ^ 3 + 23 * R ^ 2 + 38 * R + 28 := by
  let R := semanticFrameCursorRadius input frame
  let cycle :=
    (exactAcceptingCycleRefinement frame slot ready next hstep haccept).exact_cycle
  have frameSize := semanticFrame_has_sizeEnvelope frame
  rcases ULogSemantics.stepSlot_some_rule hstep with
    ⟨_, action, hlookup, haction⟩
  have hacceptAction : ULogSemantics.accepting
      (ULogSemantics.applyAction frame.config action) = true := by
    simpa [haction] using haccept
  have htarget : action.target = 0 :=
    (accepting_applyAction_iff_target_zero frame.config action).mp hacceptAction
  have hp := cursorDynamicProgramToHead_passive input frame.config.leftRev
  have hclock := clockCellsAfter_passive frame.config.right frame.clockZeros
    frame.runtime ready.runtime_passive
  obtain ⟨skip, r, rs, heq, certs, rscan, hmatch, hactionRule⟩ :=
    automatic_lookup_some slot frame.config.state frame.config.focus
      ready.focus_lt_three
      (cursorDynamicProgramToHead input
        (frame.config.leftRev.map payloadNat))
      (clockCellsAfter (frame.config.right.map payloadNat)
        frame.clockZeros frame.runtime)
      hp hclock frame.config.program ready.reads_lt_three action hlookup
  have htargetRule : r.action.target = 0 := by
    rw [hactionRule]
    exact htarget
  have hwrite : r.action.write < 3 := ready.writes_lt_three r (by
    rw [heq]
    simp)
  have hboundary := boundaryAfter_valid sourceBoundary (Or.inl rfl) skip
  let programToHead := cursorDynamicProgramToHead input
    (frame.config.leftRev.map payloadNat)
  let cursorRuntime := clockCellsAfter
    (frame.config.right.map payloadNat) frame.clockZeros frame.runtime
  let cursorTail :=
    List.replicate (frame.capacity - frame.config.state)
      MStarConcreteAlphabet.work ++ suffix
  obtain ⟨z, cursorHit, hcursorCanonical⟩ :=
    mismatchCertificateList_matchedTargetZero_bounded slot
      frame.config.state frame.config.focus programToHead cursorRuntime
      frame.outer cursorTail skip r rs certs hmatch htargetRule
      rscan.read_valid hwrite hboundary
      (by simpa [programToHead, cursorRuntime, hmatch.2.1] using
        rscan.source_corridor)
      (matchedReadPath_safe r.slot r rs programToHead (by
        simpa [programToHead] using hp))
      (by simpa [htargetRule, programToHead] using
        (matchedWritePath_safe r rs programToHead (by
          simpa [programToHead] using hp)))
      (matchedTargetPath_safe r hwrite rs programToHead cursorRuntime
        (by simpa [programToHead] using hp)
        (by simpa [cursorRuntime] using hclock))
  have hbudgetEq : canonicalMismatchBudget frame.config.state
      frame.config.focus [] skip (r :: rs) programToHead cursorRuntime = R := by
    dsimp [programToHead, cursorRuntime, R]
    exact canonicalMismatchBudget_eq_frameCursorRadius frame skip r rs heq
  have hcursor : cursorHit.steps ≤
      6 * R ^ 3 + 23 * R ^ 2 + 32 * R + 22 := by
    simpa only [hbudgetEq] using hcursorCanonical
  let choiceLeft := dynamicRuleReturnPath
    (frame.config.leftRev.map payloadNat) (skip ++ r :: rs) input ++
      ulogCore pcMark :: frame.outer
  let choiceRight := cursorRuntime ++
    List.replicate frame.config.state (ulogCore stateZero) ++
      ulogCore stateOne :: ulogCore stateSep :: cursorTail
  have hhead : choiceHead (readHeadNat frame.config.focus) = true := by
    have hfocus := ready.focus_lt_three
    interval_cases frame.config.focus <;> decide
  have canonicalChoice := clockDecrementCells_firstChoice
    (readHeadNat frame.config.focus) hhead frame.clockZeros
    (frame.config.right.map payloadNat)
    (payloadNatList_safe frame.config.right) choiceLeft
    (frame.runtime ++
      List.replicate frame.config.state (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep :: cursorTail)
  have canonicalChoice' : FirstValidZeroHit IsConcreteChoice frame.encode
      (.running .chooseSlot
        ⟨choiceLeft, readHeadNat frame.config.focus, choiceRight⟩) := by
    simpa [SemanticCycleFrame.encode, semanticCycleEncoding,
      stateWorkspace, clockCellsBefore, cursorRuntime, cursorTail, heq,
      choiceLeft, choiceRight, clockCellsAfter,
      List.append_assoc] using canonicalChoice
  have hchoiceEq : cycle.choice =
      .running .chooseSlot
        ⟨choiceLeft, readHeadNat frame.config.focus, choiceRight⟩ :=
    cycle.choicePrefix.finish_unique canonicalChoice'
  have hselectedStart :
      oneStepAt (ULogBytecode.slotIndex slot)
        (.running .chooseSlot
          ⟨choiceLeft, readHeadNat frame.config.focus, choiceRight⟩) =
      .running (.ruleSeekChoice slot)
        (beforeLeftPath
          (dynamicRuleReturnPath (frame.config.leftRev.map payloadNat)
            (skip ++ r :: rs) input)
          frame.outer (ulogCore pcMark)
          (readHeadNat frame.config.focus :: choiceRight)) := by
    have hpne := dynamicRuleReturnPath_ne_nil
      (frame.config.leftRev.map payloadNat) (skip ++ r :: rs) input
    cases hePath : dynamicRuleReturnPath
        (frame.config.leftRev.map payloadNat) (skip ++ r :: rs) input with
    | nil => exact (hpne hePath).elim
    | cons x xs =>
        cases slot with
        | false =>
            simpa [choiceLeft, beforeLeftPath, hePath,
              ULogBytecode.slotIndex, List.append_assoc] using
              oneStepAt_chooseSlot_zero (readHeadNat frame.config.focus)
                hhead (xs ++ ulogCore pcMark :: frame.outer) x choiceRight
        | true =>
            simpa [choiceLeft, beforeLeftPath, hePath,
              ULogBytecode.slotIndex, List.append_assoc] using
              oneStepAt_chooseSlot_one (readHeadNat frame.config.focus)
                hhead (xs ++ ulogCore pcMark :: frame.outer) x choiceRight
  have hbranchEq : cycle.branch =
      .running (.ruleSeekChoice slot)
        (beforeLeftPath
          (dynamicRuleReturnPath (frame.config.leftRev.map payloadNat)
            (skip ++ r :: rs) input)
          frame.outer (ulogCore pcMark)
          (readHeadNat frame.config.focus :: choiceRight)) := by
    have hs := validStepAt_some_eq_oneStepAt cycle.selected
    rw [hchoiceEq, hselectedStart] at hs
    exact hs.symm
  have hdynamicPath :
      (dynamicRuleReturnPath (frame.config.leftRev.map payloadNat)
        (skip ++ r :: rs) input).length ≤ R := by
    simpa [R, heq] using frameSize.dynamic_path_le
  have hrules : (skip ++ r :: rs).length ≤ R := by
    simpa [R, heq] using frameSize.rules_le
  obtain ⟨dynamicRun⟩ := dynamicRuleSourceStarted_bounded_radius slot
    (frame.config.leftRev.map payloadNat)
    (payloadNatList_safe frame.config.leftRev) (skip ++ r :: rs) (by simp)
    input frame.outer (readHeadNat frame.config.focus) choiceRight
    hdynamicPath hrules
  have dynamicRun' : QuantifiedStopFreeRun (2 * R + 2) cycle.branch
      (ruleCursorResult slot frame.config.state frame.config.focus
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        programToHead cursorRuntime frame.outer
        (ulogCore stateSep :: cursorTail)) := by
    refine
      { steps := dynamicRun.steps
        le_bound := dynamicRun.le_bound
        run := ?_ }
    have hend := dynamicRuleSourceStarted_eq_cursorResult slot
        frame.config.state frame.config.focus
        (frame.config.leftRev.map payloadNat) input skip r rs cursorRuntime
        frame.outer (ulogCore stateSep :: cursorTail)
    have hend' : dynamicRuleSourceStarted slot
        (frame.config.leftRev.map payloadNat) (skip ++ r :: rs) input
        frame.outer (readHeadNat frame.config.focus) choiceRight =
      ruleCursorResult slot frame.config.state frame.config.focus
        (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
        programToHead cursorRuntime frame.outer
        (ulogCore stateSep :: cursorTail) := by
      simpa [programToHead, choiceRight, cursorTail, cursorRuntime,
        List.append_assoc] using hend
    have dynEnd : StopFreeValidZeroRun dynamicRun.steps
        (.running (.ruleSeekChoice slot)
          (beforeLeftPath
            (dynamicRuleReturnPath (frame.config.leftRev.map payloadNat)
              (skip ++ r :: rs) input)
            frame.outer (ulogCore pcMark)
            (readHeadNat frame.config.focus :: choiceRight)))
        (ruleCursorResult slot frame.config.state frame.config.focus
          (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
          programToHead cursorRuntime frame.outer
          (ulogCore stateSep :: cursorTail)) := by
      exact hend' ▸ dynamicRun.run
    rw [hbranchEq]
    exact dynEnd
  have hchoice : cycle.choicePrefix.steps ≤ 4 * R + 3 := by
    apply exactConcreteCycle_frame_choicePrefix_le_radius frame cycle
      ready.focus_lt_three
    · exact frameSize.right_le
    · exact frameSize.clock_le
  let fullHit := dynamicRun'.run.appendFirstHit cursorHit
  have hsuffix : cycle.cycleSuffix.steps = fullHit.steps :=
    cycle.cycleSuffix.steps_eq fullHit
  change cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps ≤
    6 * R ^ 3 + 23 * R ^ 2 + 38 * R + 28
  rw [hsuffix]
  change cycle.choicePrefix.steps + 1 +
    (dynamicRun'.steps + cursorHit.steps) ≤
      6 * R ^ 3 + 23 * R ^ 2 + 38 * R + 28
  have hd := dynamicRun'.le_bound
  calc
    cycle.choicePrefix.steps + 1 +
        (dynamicRun'.steps + cursorHit.steps) ≤
      (4 * R + 3) + 1 +
        ((2 * R + 2) +
          (6 * R ^ 3 + 23 * R ^ 2 + 32 * R + 22)) := by omega
    _ = 6 * R ^ 3 + 23 * R ^ 2 + 38 * R + 28 := by ring

/-- Global copied-radius form for every accepting semantic cycle along an
elapsed-indexed reframe history. -/
theorem exactAcceptingCycleRefinement_microFuel_lt_copiedPowNine
    {x : ConcretePakSide.Word} {input : List Bool} {suffix : List Tape}
    (frame : SemanticCycleFrame input suffix) (elapsed : ℕ)
    (global : GlobalCopiedEnvelope x frame elapsed)
    (slot : Bool) (next : ULogSemantics.Config) (ready : FrameReady frame)
    (hstep : ULogSemantics.stepSlot slot frame.config = some next)
    (haccept : ULogSemantics.accepting next = true) :
    let cycle :=
      (exactAcceptingCycleRefinement frame slot ready next hstep haccept).exact_cycle
    cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps <
      (PakOuterULogBridge.copiedCoreRadius x) ^ 9 := by
  let L := semanticFrameCursorRadius input frame
  let W := PakOuterULogBridge.copiedCoreRadius x
  let cycle :=
    (exactAcceptingCycleRefinement frame slot ready next hstep haccept).exact_cycle
  rcases ULogSemantics.stepSlot_some_rule hstep with
    ⟨_, action, hlookup, _⟩
  have hL : L ≤ 64 * W := by
    dsimp [L, W]
    exact global.cursorRadius_le slot action hlookup ready.focus_lt_three
  have hcycle := exactAcceptingCycleRefinement_microFuel_le_frameRadius
    frame slot next ready hstep haccept
  have hmono :
      6 * L ^ 3 + 23 * L ^ 2 + 38 * L + 28 ≤
        6 * (64 * W) ^ 3 + 23 * (64 * W) ^ 2 + 38 * (64 * W) + 28 := by
    gcongr
  have hW : 256 ≤ W := by
    dsimp [W]
    exact PakOuterULogBridge.copiedCoreRadius_ge_256 x
  have hstrict := accepting_microFuel_scaled_lt_pow_nine hW
  change cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps < W ^ 9
  exact (hcycle.trans hmono).trans_lt hstrict

/-- Radius-instantiated mismatch-prefix fold.  Every skipped rule is charged
the same verified four-way cursor budget. -/
theorem mismatchPrefix_stopFree_atMost_radius
    (R : ℕ)
    (resources : ∀ (slot : Bool) (current actual : ℕ)
      (c : RuleCursorData) (r : ULogBytecode.RuleCode)
      (rs : List ULogBytecode.RuleCode)
      (programToHead runtime : List Tape)
      (ready : CursorMismatchReady slot current actual c r rs
        programToHead runtime),
      CursorMismatchWithinRadius R slot current actual c r rs
        programToHead runtime ready)
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    {start final : RuleCursorData}
    {skip rest : List ULogBytecode.RuleCode}
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      start skip rest final) :
    Nonempty (BoundedStopFreeRun
      (skip.length * (6 * R ^ 2 + 17 * R + 18))
      (ruleCursorResult slot current actual start (skip ++ rest)
        programToHead runtime outer suffix)
      (ruleCursorResult slot current actual final rest
        programToHead runtime outer suffix)) := by
  exact mismatchPrefix_stopFree_atMost (6 * R ^ 2 + 17 * R + 18)
    (cursorMismatchHeadStepAtMost_of_radius R resources)
    slot current actual programToHead runtime outer suffix trace

/-- A bounded mismatch prefix followed by its first matching target-zero rule
forms one exact accepting first hit.  This is the complete cursor suffix of
the canonical accepting cycle. -/
theorem mismatchPrefix_matchedTargetZero_firstStop_bounded_radius
    (R : ℕ)
    (resources : ∀ (slot : Bool) (current actual : ℕ)
      (c : RuleCursorData) (r : ULogBytecode.RuleCode)
      (rs : List ULogBytecode.RuleCode)
      (programToHead runtime : List Tape)
      (ready : CursorMismatchReady slot current actual c r rs
        programToHead runtime),
      CursorMismatchWithinRadius R slot current actual c r rs
        programToHead runtime ready)
    (slot : Bool) (current actual : ℕ)
    (programToHead runtime outer suffix : List Tape)
    (skip : List ULogBytecode.RuleCode)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (final : RuleCursorData)
    (trace : MismatchPrefixTrace slot current actual programToHead runtime
      (initialRuleCursor (skip ++ r :: rs)) skip (r :: rs) final)
    (hmatch : RuleMatchesCursor slot current actual r)
    (htarget : r.action.target = 0)
    (hread : r.read < 3) (hwrite : r.action.write < 3)
    (hboundary : final.boundary = sourceBoundary ∨
      final.boundary = sourceBoundaryZero ∨
        final.boundary = sourceBoundaryOne)
    (hcorridor : SourceCompareCorridorSafe
      (cursorRuleCorridor r rs programToHead
        (readHeadNat r.read) runtime))
    (hreadPath : ReadCorridorSafe
      (codeTape r.slot :: encodedActionPath r.action.write
        r.action.target r.action.move
          (cursorMatchedMovePath rs programToHead)))
    (hwritePath : ActionWriteCorridorSafe
      (List.replicate r.action.target (ulogCore codeZero) ++
        ulogCore codeOne :: moveBits r.action.move ++
          cursorMatchedMovePath rs programToHead))
    (htargetPath : TargetRewriteCorridorSafe
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: runtime))
    (hskip : skip.length ≤ R)
    (hsource : r.source ≤ R)
    (hsourceCorridor :
      (cursorRuleCorridor r rs programToHead
        (readHeadNat r.read) runtime).length ≤ R)
    (hreadCorridor :
      (encodedActionPath r.action.write r.action.target r.action.move
        (cursorMatchedMovePath rs programToHead)).length ≤ R)
    (hactionCorridor :
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead).length ≤ R)
    (htargetCorridor :
      (moveBits r.action.move ++ cursorMatchedMovePath rs programToHead ++
        writeHeadNat r.action.write :: runtime).length ≤ R) :
    ∃ (z : MStarParserExecution.Zipper Tape),
      ∃ hit : FirstValidZeroHit IsConcreteCycleStop
        (ruleCursorResult slot current actual
          (initialRuleCursor (skip ++ r :: rs)) (skip ++ r :: rs)
          programToHead runtime outer (ulogCore stateSep :: suffix))
        (.accepted z),
        hit.steps ≤ 6 * R ^ 3 + 23 * R ^ 2 + 32 * R + 22 := by
  obtain ⟨prefixRun⟩ := mismatchPrefix_stopFree_atMost_radius R resources
    slot current actual programToHead runtime outer
    (ulogCore stateSep :: suffix) trace
  let matchedResult := ruleCursorMatchedTargetZero_firstStop
    final.boundary hboundary r rs programToHead
    ((List.replicate final.done (ulogCore codeZero) ++
      ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: outer)
    runtime htarget hread hwrite hcorridor hreadPath hwritePath htargetPath
    suffix
  have hmatchedDirect₀ : matchedResult.2.steps ≤
      6 * R ^ 2 + 14 * R + 22 := by
    dsimp [matchedResult]
    exact ruleCursorMatchedTargetZero_firstStop_steps_le_radius
      final.boundary hboundary r rs programToHead
      ((List.replicate final.done (ulogCore codeZero) ++
        ulogCore pcDone :: final.path).reverse ++ ulogCore pcMark :: outer)
      runtime htarget hread hwrite hcorridor hreadPath hwritePath htargetPath
      suffix hsource hsourceCorridor hreadCorridor hactionCorridor
      htargetCorridor
  obtain ⟨z, matched⟩ := matchedResult
  rcases hmatch with ⟨hsourceEq, hreadEq, hslotEq⟩
  have matched' : FirstValidZeroHit IsConcreteCycleStop
      (ruleCursorResult slot current actual final (r :: rs)
        programToHead runtime outer (ulogCore stateSep :: suffix))
      (.accepted z) := by
    simpa [ruleCursorResult, ruleCursorBase, hsourceEq, hreadEq, hslotEq,
      List.append_assoc] using matched
  have hmatchedDirect : matched.steps ≤ 6 * R ^ 2 + 14 * R + 22 :=
    hmatchedDirect₀
  have hmatchedBound : matched'.steps ≤ 6 * R ^ 2 + 14 * R + 22 := by
    have hstart :
        ruleCursorResult slot current actual final (r :: rs)
            programToHead runtime outer (ulogCore stateSep :: suffix) =
          atBitsTail (.fieldCompare .source r.slot)
            (ULogBytecode.encodeRules (r :: rs))
            (ulogCore final.boundary ::
              (List.replicate final.done (ulogCore codeZero) ++
                ulogCore pcDone :: final.path).reverse ++
                  ulogCore pcMark :: outer)
            (programToHead ++ readHeadNat r.read :: runtime ++
              List.replicate r.source (ulogCore stateZero) ++
                ulogCore stateOne :: ulogCore stateSep :: suffix) := by
      simp [ruleCursorResult, ruleCursorBase, hsourceEq, hreadEq, hslotEq,
        List.append_assoc]
    have hsteps := FirstValidZeroHit.steps_eq_of_start_eq hstart matched'
      matched
    exact hsteps ▸ hmatchedDirect
  let hit := prefixRun.run.appendFirstHit matched'
  refine ⟨z, hit, ?_⟩
  have hp := prefixRun.le_bound
  have hm := hmatchedBound
  have hmul : skip.length * (6 * R ^ 2 + 17 * R + 18) ≤
      R * (6 * R ^ 2 + 17 * R + 18) :=
    Nat.mul_le_mul_right _ hskip
  have := hp.trans hmul
  change prefixRun.steps + matched'.steps ≤
    6 * R ^ 3 + 23 * R ^ 2 + 32 * R + 22
  calc
    prefixRun.steps + matched'.steps ≤
        R * (6 * R ^ 2 + 17 * R + 18) +
          (6 * R ^ 2 + 14 * R + 22) := Nat.add_le_add this hm
    _ = 6 * R ^ 3 + 23 * R ^ 2 + 32 * R + 22 := by ring

/-- Final whole-cycle arithmetic interface.  Once the selected-arrow suffix
is instantiated by the dynamic return (`2R+2`) followed by the bounded
cursor accepting hit above, the stored exact cycle has a literal cubic raw
microstep bound. -/
theorem exactConcreteCycle_accepting_microFuel_le_radius
    {slot : Bool} {start finish cursorStart : Result}
    (cycle : ExactConcreteCycle slot start finish)
    {R : ℕ}
    (hchoice : cycle.choicePrefix.steps ≤ 4 * R + 3)
    (dynamic : QuantifiedStopFreeRun (2 * R + 2)
      cycle.branch cursorStart)
    {z : MStarParserExecution.Zipper Tape}
    (cursorHit : FirstValidZeroHit IsConcreteCycleStop cursorStart
      (.accepted z))
    (hcursor : cursorHit.steps ≤
      6 * R ^ 3 + 23 * R ^ 2 + 32 * R + 22) :
    cycle.choicePrefix.steps + 1 + cycle.cycleSuffix.steps ≤
      6 * R ^ 3 + 23 * R ^ 2 + 38 * R + 28 := by
  let fullHit := dynamic.run.appendFirstHit cursorHit
  have hsuffix : cycle.cycleSuffix.steps = fullHit.steps :=
    cycle.cycleSuffix.steps_eq fullHit
  rw [hsuffix]
  change cycle.choicePrefix.steps + 1 +
    (dynamic.steps + cursorHit.steps) ≤
      6 * R ^ 3 + 23 * R ^ 2 + 38 * R + 28
  have hd := dynamic.le_bound
  calc
    cycle.choicePrefix.steps + 1 + (dynamic.steps + cursorHit.steps) ≤
        (4 * R + 3) + 1 +
          ((2 * R + 2) +
            (6 * R ^ 3 + 23 * R ^ 2 + 32 * R + 22)) := by omega
    _ = 6 * R ^ 3 + 23 * R ^ 2 + 38 * R + 28 := by ring

/-- The explicit cubic accepting-cycle budget fits comfortably under the
copier's advertised ninth-power envelope. -/
theorem accepting_microFuel_polynomial_lt_pow_nine
    {R : ℕ} (hR : 256 ≤ R) :
    6 * R ^ 3 + 23 * R ^ 2 + 38 * R + 28 < R ^ 9 := by
  have hpos : 0 < R := by omega
  have hR2 : 256 ^ 2 ≤ R ^ 2 := Nat.pow_le_pow_left hR 2
  have hR3 : 256 ^ 3 ≤ R ^ 3 := Nat.pow_le_pow_left hR 3
  have hpoly : 6 * R ^ 3 + 23 * R ^ 2 + 38 * R + 28 < 7 * R ^ 3 := by
    nlinarith [hR2, hR3]
  have hseven : 7 * R ^ 3 < R ^ 9 := by
    calc
      7 * R ^ 3 < R ^ 3 * R ^ 3 := by
        have : 7 < R ^ 3 := by nlinarith [hR3]
        nlinarith [Nat.zero_le (R ^ 3)]
      _ ≤ R ^ 3 * R ^ 6 := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_right (by omega) (by omega)
      _ = R ^ 9 := by ring
  exact hpoly.trans hseven

end PakFixedPolyomino.PakULogCycleResourceBound
