import PakFixedPolyomino.ULogRuleMismatchReconstruction

/-! Both source-length mismatches advance from the first rule to the next. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem remainingPcPath_safe (remaining : ℕ) :
    MismatchAdvancePathSafe
      (List.replicate remaining (ulogCore pcDone)) := by
  constructor
  · intro x hx
    have heq : x = ulogCore pcDone :=
      (by simpa only [List.mem_replicate] using hx :
        remaining ≠ 0 ∧ x = ulogCore pcDone).2
    rw [heq]
    native_decide
  · intro x hx
    have heq : x = ulogCore pcDone :=
      (by simpa only [List.mem_replicate] using hx :
        remaining ≠ 0 ∧ x = ulogCore pcDone).2
    rw [heq]
    native_decide

theorem reaches_dynamicSourceShort_advance
    (slot : Bool) (leftTape : List Tape) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (hrs : rs ≠ [])
    (input : List Bool) (extra : ℕ) (left : List Tape) (head : Tape)
    (runtime suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (dynamicFirstRuleCorridor r rs input leftTape head runtime))
    (hreadBoundary : ∀ x ∈
      dynamicFirstRuleCorridor r rs input leftTape head runtime,
        x ≠ ulogCore readBoundary)
    (after : Tape) (right : List Tape)
    (hafter : (payloadProgramPrefix input).reverse ++ leftTape.reverse ++
        head :: runtime ++
          List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix = after :: right) :
    Reaches
      (dynamicRuleSourceStarted slot leftTape (r :: rs) input left head
        (runtime ++
          List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (atBits (.fieldCompare .source slot) (ULogBytecode.encodeRules rs)
        (mismatchRulePrefix r ++ ulogCore codeOne ::
          (List.replicate rs.length (ulogCore pcDone)).reverse ++
            ulogCore codeZero :: ulogCore pcMark :: left)
        after right) := by
  have hrestore := reaches_dynamicRuleSourceShort_restore slot leftTape r rs
    input extra left head runtime suffix hcorridor
  have hrestored := dynamicSourceShort_restored r rs input leftTape head
    runtime suffix extra hcorridor hreadBoundary
  have hrestored' :
      (sourceShortRestorePath r.source
        (dynamicFirstRuleCorridor r rs input leftTape head runtime)).reverse.map
          restoreMismatchCell ++
        ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
          ulogCore stateOne :: suffix =
      (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
        codeTape ++ after :: right := by
    rw [hrestored]
    have hafter' := congrArg
      (fun xs =>
        (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
          codeTape ++ xs) hafter
    simpa [List.append_assoc] using hafter'
  have hrestored'' :
      (sourceShortRestorePath r.source
        (dynamicFirstRuleCorridor r rs input leftTape head runtime)).reverse.map
          restoreMismatchCell ++
        (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
          ulogCore stateOne :: suffix) =
      (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
        codeTape ++ after :: right := by
    simpa [List.append_assoc] using hrestored'
  have hadvance := reaches_restoreMismatchAdvanceRule slot 0
    (List.replicate rs.length (ulogCore pcDone))
    (remainingPcPath_safe rs.length) sourceBoundary (Or.inl rfl)
    (sourceShortRestorePath r.source
      (dynamicFirstRuleCorridor r rs input leftTape head runtime))
    (by
      intro x hx
      unfold sourceShortRestorePath at hx
      rcases List.mem_append.mp hx with hp | hs
      · have hp' : x ∈ sourceShortFinishPath r.source
            (dynamicFirstRuleCorridor r rs input leftTape head runtime) := by
          simpa using hp
        unfold sourceShortFinishPath at hp'
        rcases List.mem_append.mp hp' with hc | hm
        · have h := hcorridor x hc
          exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
            h.2.2.2.2.2.2.2.2, h.2.2.2.2.1⟩
        · have heq : x = ulogCore stateMark :=
            (by simpa only [List.mem_replicate] using hm :
              r.source ≠ 0 ∧ x = ulogCore stateMark).2
          rw [heq]
          native_decide
      · simp only [List.mem_cons, List.mem_replicate] at hs
        rcases hs with rfl | hs
        · native_decide
        · rw [hs.2]
          native_decide)
    (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
    r (ULogBytecode.encodeRules rs) (encodeRules_ne_nil hrs)
    left after right hrestored''
  have hrestore' : Reaches
      (dynamicRuleSourceStarted slot leftTape (r :: rs) input left head
        (runtime ++
          List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
      (restoreAdvanceStarted slot
        (sourceShortRestorePath r.source
          (dynamicFirstRuleCorridor r rs input leftTape head runtime))
        (ulogCore pcDone ::
          List.replicate rs.length (ulogCore pcDone)).reverse
        left sourceBoundary
        (ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
          ulogCore stateOne :: suffix)) := by
    simpa [restoreAdvanceStarted, List.replicate_succ,
      List.append_assoc] using hrestore
  have hall := reaches_trans hrestore' hadvance
  have hboundaryNe : sourceBoundary ≠ sourceBoundaryZero := by native_decide
  simpa [hboundaryNe, List.append_assoc] using hall

theorem sourceLongRestorePath_safe (remaining done : ℕ)
    (corridor : List Tape) (hcorridor : SourceCompareCorridorSafe corridor) :
    MismatchRestorePathSafe
      (sourceLongRestorePath remaining done corridor) := by
  intro x hx
  unfold sourceLongRestorePath at hx
  rcases List.mem_append.mp hx with hp | hs
  · have hp' : x ∈ sourceLongSeekPath remaining done corridor := by
      simpa using hp
    unfold sourceLongSeekPath sourceCompareScanPath at hp'
    rcases List.mem_append.mp hp' with hpre | hm
    · rcases List.mem_append.mp hpre with hz | honeCorridor
      · have heq : x = ulogCore codeZero :=
          (by simpa only [List.mem_replicate] using hz :
            remaining ≠ 0 ∧ x = ulogCore codeZero).2
        rw [heq]
        decide
      · rcases List.mem_cons.mp honeCorridor with rfl | hc
        · decide
        · have h := hcorridor x hc
          exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
            h.2.2.2.2.2.2.2.2, h.2.2.2.2.1⟩
    · have heq : x = ulogCore stateMark :=
        (by simpa only [List.mem_replicate] using hm :
          done ≠ 0 ∧ x = ulogCore stateMark).2
      rw [heq]
      decide
  · simp only [List.mem_cons, List.mem_replicate] at hs
    rcases hs with rfl | hs
    · decide
    · rw [hs.2]
      decide

theorem reaches_dynamicSourceLong_advance
    (slot : Bool) (leftTape : List Tape) (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (hrs : rs ≠ [])
    (input : List Bool) (current extra : ℕ)
    (hsource : r.source = current + extra + 1)
    (left : List Tape) (head : Tape) (runtime suffix : List Tape)
    (hcorridor : SourceCompareCorridorSafe
      (dynamicFirstRuleCorridor r rs input leftTape head runtime))
    (hreadBoundary : ∀ x ∈
      dynamicFirstRuleCorridor r rs input leftTape head runtime,
        x ≠ ulogCore readBoundary)
    (after : Tape) (right : List Tape)
    (hafter : (payloadProgramPrefix input).reverse ++ leftTape.reverse ++
        head :: runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix = after :: right) :
    Reaches
      (dynamicRuleSourceStarted slot leftTape (r :: rs) input left head
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))
      (atBits (.fieldCompare .source slot) (ULogBytecode.encodeRules rs)
        (mismatchRulePrefix r ++ ulogCore codeOne ::
          (List.replicate rs.length (ulogCore pcDone)).reverse ++
            ulogCore codeZero :: ulogCore pcMark :: left)
        after right) := by
  have hrestore := reaches_dynamicRuleSourceLong_restore slot leftTape r rs
    input current extra hsource left head runtime suffix hcorridor
  have hrestored := dynamicSourceLong_restored r rs input leftTape head
    runtime suffix current extra hsource hcorridor hreadBoundary
  have hrestored' :
      (sourceLongRestorePath extra current
        (dynamicFirstRuleCorridor r rs input leftTape head runtime)).reverse.map
          restoreMismatchCell ++ ulogCore stateOne :: suffix =
      (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
        codeTape ++ after :: right := by
    rw [hrestored]
    have hafter' := congrArg
      (fun xs =>
        (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
          codeTape ++ xs) hafter
    simpa [List.append_assoc] using hafter'
  have hadvance := reaches_restoreMismatchAdvanceRule slot 0
    (List.replicate rs.length (ulogCore pcDone))
    (remainingPcPath_safe rs.length) sourceBoundary (Or.inl rfl)
    (sourceLongRestorePath extra current
      (dynamicFirstRuleCorridor r rs input leftTape head runtime))
    (sourceLongRestorePath_safe extra current
      (dynamicFirstRuleCorridor r rs input leftTape head runtime) hcorridor)
    (ulogCore stateOne :: suffix)
    r (ULogBytecode.encodeRules rs) (encodeRules_ne_nil hrs)
    left after right hrestored'
  have hrestore' : Reaches
      (dynamicRuleSourceStarted slot leftTape (r :: rs) input left head
        (runtime ++ List.replicate current (ulogCore stateZero) ++
          ulogCore stateOne :: suffix))
      (restoreAdvanceStarted slot
        (sourceLongRestorePath extra current
          (dynamicFirstRuleCorridor r rs input leftTape head runtime))
        (ulogCore pcDone ::
          List.replicate rs.length (ulogCore pcDone)).reverse
        left sourceBoundary (ulogCore stateOne :: suffix)) := by
    simpa [restoreAdvanceStarted, List.replicate_succ,
      List.append_assoc] using hrestore
  have hall := reaches_trans hrestore' hadvance
  have hboundaryNe : sourceBoundary ≠ sourceBoundaryZero := by native_decide
  simpa [hboundaryNe, List.append_assoc] using hall

end PakFixedPolyomino.ULogBootstrapExecution
