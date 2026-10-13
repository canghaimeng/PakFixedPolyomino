import PakFixedPolyomino.ULogTernaryGeneratedHeadedReturnClock

/-! Closed compact source-return scope. Generic reserve conditions are
internally discharged for every input of the actual bit transducer. This
local theorem does not execute the margins or the final source scanner. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedHeadedReturnChecked
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open ULogTernaryGeneratedHeadedSourceReturn

theorem generated_headed_return_spec {nt : Nat} (hnt : 0 < nt)
    (codes : Fin 3 → Fin nt) (p : Polynomial Nat) :
    StandardBitTime.PolyBitTime (input hnt codes p) ∧
    (∀ x : List Bool,
      let k := ULogTernaryGeneratedHeadedSourceExpansion.width nt p x
      let d := ULogTernaryGuardedPumpDelimiterInput.depth
        (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)
      let c := ULogTernaryGuardedPumpDelimiterInput.seedWidth
        (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)
      semanticRun (ULogSemantics.start (input hnt codes p x))
        (List.replicate (compactDeadline nt p x) false) =
          some (liftConfig (compactProgram hnt codes p) (compactFinal codes p x)) ∧
      (compactFinal codes p x).leftRev =
        ULogTernaryCountedSourceDelimiter.ones x.length ++
          2 :: ULogTernaryGuardedPumpDelimiter.under k d c x ∧
      (compactFinal codes p x).focus = 2 ∧
      (compactFinal codes p x).right =
        ULogTernaryRetainedCounterPump.cells (sourceBits codes x) ++ 2 :: pool nt k x ∧
      compactDeadline nt p x ≤ 2 ^ ULogTernaryGeneratedHeadedSourceExpansion.clockWidth nt p x ∧
      (∀ T, ULogSemantics.machine.acceptingPaths T (ULogSemantics.start (input hnt codes p x)) =
        if compactDeadline nt p x ≤ T then 1 else 0) ∧
      (∀ w hf out,
        run (compactProgram hnt codes p) 2 w 0 (compactInitial nt p x) = some (hf, out) →
          w = List.replicate w.length false ∧ w.length ≤ compactDeadline nt p x ∧
            cellCount out ≤ ULogTernaryGuardedPumpDelimiterSpace.peak k d c x)) := by
  refine ⟨input_polyBitTime hnt codes p, ?_⟩
  intro x
  dsimp only
  have ht := final_tape codes
    (ULogTernaryGeneratedHeadedSourceExpansion.width nt p x)
    (ULogTernaryGuardedPumpDelimiterInput.depth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
    (ULogTernaryGuardedPumpDelimiterInput.seedWidth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)) x
  exact ⟨compact_actual_run hnt codes p x, ht.1, ht.2.1, ht.2.2,
    ULogTernaryGeneratedHeadedReturnClock.deadline_le_clock nt p x,
    compact_cutoff_counts hnt codes p x,
    fun _ _ _ h => every_raw hnt codes _ _ _
      (ULogTernaryGuardedPumpDelimiterInput.seed_positive _) x
      (ULogTernaryGeneratedHeadedSourceExpansion.compact_reserve_fits nt p x) h⟩

end PakFixedPolyomino.ULogTernaryGeneratedHeadedReturnChecked
