import PakFixedPolyomino.ULogRuleSourceMismatch

/-! Reconstruction of the exact bytecode/runtime suffix after source mismatch. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem dynamicFirstRuleCorridor_readBoundary_free
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (leftTape : List Tape) (head : Tape)
    (runtime : List Tape)
    (hleft : ∀ x ∈ leftTape, x ≠ ulogCore readBoundary)
    (hhead : head ≠ ulogCore readBoundary)
    (hruntime : ∀ x ∈ runtime, x ≠ ulogCore readBoundary) :
    ∀ x ∈ dynamicFirstRuleCorridor r rs input leftTape head runtime,
      x ≠ ulogCore readBoundary := by
  intro x hx
  unfold dynamicFirstRuleCorridor at hx
  rcases List.mem_append.mp hx with hp | ht
  · rcases List.mem_append.mp hp with hcodePayload | hl
    · rcases List.mem_append.mp hcodePayload with hc | hpayload
      · rcases List.mem_map.mp hc with ⟨b, -, rfl⟩
        cases b <;> native_decide
      · have hm : x ∈ payloadProgramPrefix input := by
          simpa using hpayload
        rcases payloadProgramPrefix_mem hm with rfl | rfl | rfl | rfl <;>
          native_decide
    · exact hleft x (by simpa using hl)
  · rcases List.mem_cons.mp ht with rfl | hr
    · exact hhead
    · exact hruntime x hr

theorem dynamicSourceShort_restored
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (leftTape : List Tape) (head : Tape)
    (runtime suffix : List Tape) (extra : ℕ)
    (hcorridor : SourceCompareCorridorSafe
      (dynamicFirstRuleCorridor r rs input leftTape head runtime))
    (hreadBoundary : ∀ x ∈
      dynamicFirstRuleCorridor r rs input leftTape head runtime,
        x ≠ ulogCore readBoundary) :
    (sourceShortRestorePath r.source
        (dynamicFirstRuleCorridor r rs input leftTape head runtime)).reverse.map
          restoreMismatchCell ++
        ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
          ulogCore stateOne :: suffix =
      (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
          codeTape ++
        (payloadProgramPrefix input).reverse ++ leftTape.reverse ++
          head :: runtime ++
            List.replicate (r.source + extra + 1) (ulogCore stateZero) ++
              ulogCore stateOne :: suffix := by
  rw [sourceShortRestorePath_map r.source extra
    (dynamicFirstRuleCorridor r rs input leftTape head runtime)
    hcorridor hreadBoundary suffix]
  rcases r with ⟨source, read, slot, ⟨write, target, move⟩⟩
  simp [dynamicFirstRuleCorridor, ULogBytecode.encodeRule,
    ULogBytecode.encodeAction, ULogBytecode.encodeNatField, codeTape,
    List.map_append, List.append_assoc]

theorem dynamicSourceLong_restored
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (input : List Bool) (leftTape : List Tape) (head : Tape)
    (runtime suffix : List Tape) (current extra : ℕ)
    (hsource : r.source = current + extra + 1)
    (hcorridor : SourceCompareCorridorSafe
      (dynamicFirstRuleCorridor r rs input leftTape head runtime))
    (hreadBoundary : ∀ x ∈
      dynamicFirstRuleCorridor r rs input leftTape head runtime,
        x ≠ ulogCore readBoundary) :
    (sourceLongRestorePath extra current
        (dynamicFirstRuleCorridor r rs input leftTape head runtime)).reverse.map
          restoreMismatchCell ++ ulogCore stateOne :: suffix =
      (ULogBytecode.encodeRule r ++ ULogBytecode.encodeRules rs).map
          codeTape ++
        (payloadProgramPrefix input).reverse ++ leftTape.reverse ++
          head :: runtime ++ List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: suffix := by
  rw [sourceLongRestorePath_map extra current
    (dynamicFirstRuleCorridor r rs input leftTape head runtime)
    hcorridor hreadBoundary suffix]
  rcases r with ⟨source, read, slot, ⟨write, target, move⟩⟩
  change source = current + extra + 1 at hsource
  subst source
  simp [dynamicFirstRuleCorridor, ULogBytecode.encodeRule,
    ULogBytecode.encodeAction, ULogBytecode.encodeNatField, codeTape,
    List.map_append, List.append_assoc,
    Nat.add_assoc]

end PakFixedPolyomino.ULogBootstrapExecution
