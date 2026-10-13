import PakFixedPolyomino.ULogTernaryGeneratedMarginEntryClock

/-! Closed compact entry scope, ending before the repeated balanced margins.
Every reserve/counter/forward condition is derived internally for the actual
bit input. Physical growth/ALLcapacity and scanner micro-time remain open. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginEntryChecked
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogTernaryGeneratedMarginEntry

theorem generated_margin_entry_spec {nt : Nat} (hnt : 0 < nt)
    (codes : Fin 3 → Fin nt) (blank : Fin nt) (p : Polynomial Nat) :
    StandardBitTime.PolyBitTime (input hnt codes blank p) ∧
    (∀ x : List Bool,
      let k := ULogTernaryGeneratedHeadedSourceExpansion.width nt p x
      let d := ULogTernaryGuardedPumpDelimiterInput.depth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)
      let c := ULogTernaryGuardedPumpDelimiterInput.seedWidth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)
      semanticRun (ULogSemantics.start (input hnt codes blank p x))
        (List.replicate (compactDeadline nt p x) false) =
          some (liftConfig (compactProgram hnt codes blank p) (compactFinal codes blank p x)) ∧
      (compactFinal codes blank p x).leftRev = ULogTernaryGeneratedHeadedSourceReturn.retained k d c x ∧
      (compactFinal codes blank p x).focus = 2 ∧
      (compactFinal codes blank p x).right =
        ULogTernaryRetainedCounterPump.cells (correctedBits codes blank x) ++
          2 :: (List.replicate (ULogTernaryMarginReserveBudget.after nt (2 ^ k) x.length) 0 ++ [2]) ∧
      compactDeadline nt p x ≤ 2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x ∧
      (∀ T, ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input hnt codes blank p x)) =
        if compactDeadline nt p x ≤ T then 1 else 0) ∧
      (∀ w hf out, run (compactProgram hnt codes blank p) 2 w 0 (compactInitial nt p x) = some (hf, out) →
        w = List.replicate w.length false ∧ w.length ≤ compactDeadline nt p x)) := by
  refine ⟨input_polyBitTime hnt codes blank p, ?_⟩
  intro x
  dsimp only
  have ht := final_tape codes blank
    (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x)
    (ULogTernaryGuardedPumpDelimiterInput.depth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)) x
    (compact_pool_fits nt p x)
  refine ⟨compact_semantic_run hnt codes blank p x, ht.1, ht.2.1, ht.2.2,
    ULogTernaryGeneratedMarginEntryClock.deadline_le_clock nt p x,
    compact_cutoff_counts hnt codes blank p x, ?_⟩
  intro w hf out hw
  exact ⟨successful_zipper_is_false (2 : Fin 3) _ (program_falseOnly hnt codes blank _ _) hw,
    successful_zipper_length_le (2 : Fin 3) _ (program_falseOnly hnt codes blank _ _)
      (compactDeadline nt p x) 0 (compactInitial nt p x) (compactFinal codes blank p x)
      (ULogTernaryGeneratedHeadedSourceReturn.finalHead nt
        (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x)
        (ULogTernaryGuardedPumpDelimiterInput.depth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
        (ULogTernaryGuardedPumpDelimiterInput.seedWidth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)) x)
      (compact_actual_run hnt codes blank p x) (final_accepts codes blank _ _ _ x) hw⟩

end PakFixedPolyomino.ULogTernaryGeneratedMarginEntryChecked
