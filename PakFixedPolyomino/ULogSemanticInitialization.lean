import PakFixedPolyomino.ULogConcreteMachine
import PakFixedPolyomino.ULogAutomaticCoupledStep

/-! Full bootstrap initialization lands exactly in the semantic cycle encoding. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

@[simp] theorem payloadNat_bitCode (b : Bool) :
    payloadNat (ULogSemantics.bitCode b) = payloadTape b := by
  cases b <;> native_decide

theorem initializedRuntime_eq_semanticCycleEncoding
    (n : ℕ) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (source tail : List Tape) :
    initializedRuntime padding input
        (programMarkedLeft rules
          (List.replicate n MStarConcreteAlphabet.work ++ source)) tail =
      semanticCycleEncoding input
        (clockCellsBefore
          ((ULogSemantics.startFrom rules input).right.map payloadNat)
          padding.length [ulogCore clockSep])
        2 (List.replicate n MStarConcreteAlphabet.work ++ source) tail
        (ULogSemantics.startFrom rules input) := by
  cases input with
  | nil =>
      simp [initializedRuntime, semanticCycleEncoding,
        ULogSemantics.startFrom, ULogSemantics.initialTape,
        ULogSemantics.startCode, ULogSemantics.blankCode,
        dynamicRuleReturnPath, ruleReturnPath, payloadProgramPrefix,
        programMarkedLeft, clockCellsBefore, runtimeSuffix,
        stateWorkspace, readHeadNat, payloadNat, codeTape,
        List.append_assoc]
  | cons b bs =>
      have hz : payloadTape false =
          unheadTape (ulogCore payloadHeadZero) := by native_decide
      have ho : payloadTape true =
          unheadTape (ulogCore payloadHeadOne) := by native_decide
      have hn₀ : payloadNat 0 = ulogCore dataZero := by native_decide
      have hn₁ : payloadNat 1 = ulogCore dataOne := by native_decide
      cases b <;>
        simp [initializedRuntime, semanticCycleEncoding,
          ULogSemantics.startFrom, ULogSemantics.initialTape,
          ULogSemantics.startCode, ULogSemantics.bitCode,
          dynamicRuleReturnPath, ruleReturnPath, payloadProgramPrefix,
          programMarkedLeft, clockCellsBefore, runtimeSuffix,
          stateWorkspace, readHeadNat, payloadTape, codeTape,
          List.map_map, hz, ho, hn₀, hn₁, List.append_assoc]

theorem reaches_bootstrap_semanticStart
    (n : ℕ) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (source tail : List Tape) :
    Reaches
      (.running .start
        ⟨source, MStarConcreteAlphabet.work,
          List.replicate n MStarConcreteAlphabet.work ++
            (ULogBytecode.encodeProgram rules ++
              ULogBytecode.encodePayload input padding).map bitTape ++
                MStarConcreteAlphabet.work ::
                  payloadRuntimeWorkspace input tail⟩)
      (semanticCycleEncoding input
        (clockCellsBefore
          ((ULogSemantics.startFrom rules input).right.map payloadNat)
          padding.length [ulogCore clockSep])
        2 (List.replicate n MStarConcreteAlphabet.work ++ source) tail
        (ULogSemantics.startFrom rules input)) := by
  rw [← initializedRuntime_eq_semanticCycleEncoding]
  exact reaches_bootstrap_runtimeInitialized n rules input padding source tail

theorem initializedRuntime_eq_semanticCycleEncoding_capacity
    (n capacity : ℕ)
    (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (source tail : List Tape) :
    initializedRuntime padding input
        (programMarkedLeft rules
          (List.replicate n MStarConcreteAlphabet.work ++ source))
        (List.replicate (capacity - 2) MStarConcreteAlphabet.work ++ tail) =
      semanticCycleEncoding input
        (clockCellsBefore
          ((ULogSemantics.startFrom rules input).right.map payloadNat)
          padding.length [ulogCore clockSep])
        capacity (List.replicate n MStarConcreteAlphabet.work ++ source) tail
        (ULogSemantics.startFrom rules input) := by
  rw [initializedRuntime_eq_semanticCycleEncoding n rules input padding
    source (List.replicate (capacity - 2) MStarConcreteAlphabet.work ++ tail)]
  have hsub : capacity - 2 = capacity - ULogSemantics.startCode := by
    simp [ULogSemantics.startCode]
  simp [semanticCycleEncoding, stateWorkspace, ULogSemantics.startFrom,
    ULogSemantics.startCode, hsub, List.append_assoc]

theorem reaches_bootstrap_semanticStart_capacity
    (n capacity : ℕ)
    (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (source tail : List Tape) :
    Reaches
      (.running .start
        ⟨source, MStarConcreteAlphabet.work,
          List.replicate n MStarConcreteAlphabet.work ++
            (ULogBytecode.encodeProgram rules ++
              ULogBytecode.encodePayload input padding).map bitTape ++
                MStarConcreteAlphabet.work ::
                  payloadRuntimeWorkspace input
                    (List.replicate (capacity - 2)
                      MStarConcreteAlphabet.work ++ tail)⟩)
      (semanticCycleEncoding input
        (clockCellsBefore
          ((ULogSemantics.startFrom rules input).right.map payloadNat)
          padding.length [ulogCore clockSep])
        capacity (List.replicate n MStarConcreteAlphabet.work ++ source) tail
        (ULogSemantics.startFrom rules input)) := by
  rw [← initializedRuntime_eq_semanticCycleEncoding_capacity n capacity
    rules input padding source tail]
  exact reaches_bootstrap_runtimeInitialized n rules input padding source
    (List.replicate (capacity - 2) MStarConcreteAlphabet.work ++ tail)

end PakFixedPolyomino.ULogBootstrapExecution
