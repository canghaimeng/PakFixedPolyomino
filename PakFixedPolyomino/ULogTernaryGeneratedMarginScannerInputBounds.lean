import PakFixedPolyomino.ULogEncodedRuleSize
import PakFixedPolyomino.ULogTernaryGeneratedMarginScannerPhysicalFuel

/-! Bounds from the actual generated input and its highest-state guard rule.
No state-size or source-capacity certificate is supplied. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginScannerInputBounds
noncomputable section
open ULogCompiler ULogBytecode
open ULogTernaryGeneratedMarginScanner (input states program scannerStates)
open ULogTernaryGeneratedMarginScannerPhysicalFuel
open StandardNondeterministicMachine (Machine)
variable {ns nt : Nat}

theorem states_le_input_length (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    states M p ≤ (input M p x).length := by
  let left := ULogTernaryGeneratedMarginLoop.states nt p
  let right := scannerStates M
  let q : Fin (states M p) := ⟨left + right, by
    unfold states ULogFiniteTapeGuardedStageComposition.stateCount
    omega⟩
  let action : BoundedAction (states M p) 3 :=
    ⟨2, ULogFiniteTapeGuardedStageComposition.rightState
      (⟨2, ULogTernaryGeneratedMarginScanner.scanner_states_ge M⟩ : Fin right), .stay⟩
  have occupied : (program M p).rule q (2 : Fin 3) false = some action := by
    simp [program, ULogFiniteTapeGuardedStageComposition.program,
      ULogFiniteTapeGuardedStageComposition.rightState, q, left, right, action] <;> rfl
  have code := ULogEncodedRuleSize.occupied_source_le_compiled_program_length
    (program M p) q (2 : Fin 3) false action occupied
  have length := ULogPayloadClockBitWrapper.length_wrap (program M p)
    (StandardBitCountedPolynomialPayload.payload
      (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x)
  change (input M p x).length = _ at length
  have qsize : q.val + 1 = states M p := by
    unfold q left right states ULogFiniteTapeGuardedStageComposition.stateCount
    rfl
  rw [qsize] at code
  omega

theorem source_width_le_input_length (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) : ULogTernaryGeneratedHeadedSourceExpansion.width nt p x ≤
      (input M p x).length := by
  have clock := clock_width_le_input_length M p x
  change 2 * (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x +
    (ULogTernaryGuardedPumpDelimiterInput.source
      (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p) x).length + 1) + 1 ≤
      (input M p x).length at clock
  omega

theorem reserve_le_radius (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    ULogTernaryGeneratedMarginSourceClock.reserve nt p x ≤
      PakOuterULogBridge.copiedCoreRadius (input M p x) := by
  have width := source_width_le_input_length M p x
  unfold ULogTernaryGeneratedMarginSourceClock.reserve PakOuterULogBridge.copiedCoreRadius
    MStarParserCopySpec.timeExponent
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)

theorem source_cutoff_le_radius (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) :
    2 ^ p.eval x.length ≤ PakOuterULogBridge.copiedCoreRadius (input M p x) := by
  have source := ULogTernaryGeneratedWindowBudget.width_lower nt p x
  have width := source_width_le_input_length M p x
  change ULogTernaryGeneratedWindowBudget.width nt p x ≤ (input M p x).length at width
  unfold PakOuterULogBridge.copiedCoreRadius MStarParserCopySpec.timeExponent
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)

theorem input_length_le_radius (y : ConcretePakSide.Word) :
    y.length ≤ PakOuterULogBridge.copiedCoreRadius y := by
  exact (ULogTernaryGeneratedSourceExpansion.self_le_pow_two y.length).trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by
      unfold MStarParserCopySpec.timeExponent
      omega))

end
end PakFixedPolyomino.ULogTernaryGeneratedMarginScannerInputBounds
