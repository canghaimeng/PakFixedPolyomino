import PakFixedPolyomino.ULogRuleCursorMatchedAction

/-! All six unequal read/head pairs at an arbitrary rule cursor. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def readMismatchBaseAt (source read : ℕ) (boundary : ULogLetter)
    (base : List Tape) : List Tape :=
    List.replicate read (ulogCore codeZero) ++ ulogCore codeOne ::
    List.replicate source (ulogCore codeZero) ++
      ulogCore boundary :: base

theorem reaches_sourceReadAtZero_mismatch (slot : Bool) (source : ℕ)
    (boundary : ULogLetter) (base path runtime suffix : List Tape)
    (actualHead : Tape)
    (hmismatch : actualHead = ulogCore payloadHeadOne ∨
      actualHead = ulogCore payloadHeadBlank)
    (hsafe : ReadCorridorSafe path) :
    Reaches
      (sourceReadStartedAt slot source boundary true base
        (path ++ actualHead :: runtime) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath path.reverse
          (readMismatchBaseAt source 0 boundary base)
          (ulogCore readBoundary)
          (actualHead :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) := by
  have h₀ : Reaches
      (sourceReadStartedAt slot source boundary true base
        (path ++ actualHead :: runtime) suffix)
      (.running (.readPhase .seekZero slot)
        (beforeRightPath path
          (ulogCore readBoundary :: readMismatchBaseAt source 0 boundary base)
          actualHead
          (runtime ++ List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
    apply reaches_step
    cases path <;>
      simp [sourceReadStartedAt, readMismatchBaseAt, beforeRightPath,
        fieldCompare_read_zero, codeTape, List.append_assoc]
  have h₁ := reaches_readHeadMismatch_of slot (.readPhase .seekZero slot)
    actualHead path
    (fun x hx l y r =>
      let h := hsafe x hx
      readSeekZero_pass slot x h.1 h.2.1 h.2.2.1 h.2.2.2.1 l y r)
    (by
      rcases hmismatch with rfl | rfl
      · exact readSeekZero_one_mismatch slot
      · exact readSeekZero_blank_mismatch slot)
    (readMismatchBaseAt source 0 boundary base)
    (runtime ++ List.replicate source (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  exact reaches_trans h₀ h₁

theorem reaches_sourceReadAtOne_mismatch (slot : Bool) (source : ℕ)
    (boundary : ULogLetter) (base path runtime suffix : List Tape)
    (actualHead : Tape)
    (hmismatch : actualHead = ulogCore payloadHeadZero ∨
      actualHead = ulogCore payloadHeadBlank)
    (hsafe : ReadCorridorSafe path) :
    Reaches
      (sourceReadStartedAt slot source boundary false base
        (ulogCore codeOne :: path ++ actualHead :: runtime) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath path.reverse
          (readMismatchBaseAt source 1 boundary base)
          (ulogCore readBoundary)
          (actualHead :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) := by
  have h₀ : Reaches
      (sourceReadStartedAt slot source boundary false base
        (ulogCore codeOne :: path ++ actualHead :: runtime) suffix)
      (.running (.readPhase .seekOne slot)
        (beforeRightPath path
          (ulogCore readBoundary :: readMismatchBaseAt source 1 boundary base)
          actualHead
          (runtime ++ List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
    refine ⟨2, ?_⟩
    cases path <;>
      simp [run, sourceReadStartedAt, readMismatchBaseAt, beforeRightPath,
        fieldCompare_read_more, readCountOne_done, codeTape,
        List.append_assoc]
  have h₁ := reaches_readHeadMismatch_of slot (.readPhase .seekOne slot)
    actualHead path
    (fun x hx l y r =>
      let h := hsafe x hx
      readSeekOne_pass slot x h.1 h.2.1 h.2.2.1 h.2.2.2.1 l y r)
    (by
      rcases hmismatch with rfl | rfl
      · exact readSeekOne_zero_mismatch slot
      · exact readSeekOne_blank_mismatch slot)
    (readMismatchBaseAt source 1 boundary base)
    (runtime ++ List.replicate source (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  exact reaches_trans h₀ h₁

theorem reaches_sourceReadAtBlank_mismatch (slot : Bool) (source : ℕ)
    (boundary : ULogLetter) (base path runtime suffix : List Tape)
    (actualHead : Tape)
    (hmismatch : actualHead = ulogCore payloadHeadZero ∨
      actualHead = ulogCore payloadHeadOne)
    (hsafe : ReadCorridorSafe path) :
    Reaches
      (sourceReadStartedAt slot source boundary false base
        (ulogCore codeZero :: ulogCore codeOne ::
          path ++ actualHead :: runtime) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath path.reverse
          (readMismatchBaseAt source 2 boundary base)
          (ulogCore readBoundary)
          (actualHead :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) := by
  have h₀ : Reaches
      (sourceReadStartedAt slot source boundary false base
        (ulogCore codeZero :: ulogCore codeOne ::
          path ++ actualHead :: runtime) suffix)
      (.running (.readPhase .seekBlank slot)
        (beforeRightPath path
          (ulogCore readBoundary :: readMismatchBaseAt source 2 boundary base)
          actualHead
          (runtime ++ List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
    refine ⟨3, ?_⟩
    cases path <;>
      simp [run, sourceReadStartedAt, readMismatchBaseAt, beforeRightPath,
        fieldCompare_read_more, readCountOne_more, readCountTwo_done,
        codeTape, List.append_assoc]
  have h₁ := reaches_readHeadMismatch_of slot (.readPhase .seekBlank slot)
    actualHead path
    (fun x hx l y r =>
      let h := hsafe x hx
      readSeekBlank_pass slot x h.1 h.2.1 h.2.2.1 h.2.2.2.1 l y r)
    (by
      rcases hmismatch with rfl | rfl
      · exact readSeekBlank_zero_mismatch slot
      · exact readSeekBlank_one_mismatch slot)
    (readMismatchBaseAt source 2 boundary base)
    (runtime ++ List.replicate source (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  exact reaches_trans h₀ h₁

theorem reaches_sourceReadAt_mismatch (slot : Bool) (source read actual : ℕ)
    (hread : read < 3) (hactual : actual < 3) (hne : read ≠ actual)
    (boundary : ULogLetter) (base path runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe path) :
    Reaches
      (sourceReadStartedAt slot source boundary (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          path ++ readHeadNat actual :: runtime) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath path.reverse
          (readMismatchBaseAt source read boundary base)
          (ulogCore readBoundary)
          (readHeadNat actual :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) := by
  interval_cases read <;> interval_cases actual
  all_goals try omega
  · simpa [ULogBytecode.encodeNatField, unaryFieldFirst, readHeadNat,
      codeTape, List.append_assoc] using
      reaches_sourceReadAtZero_mismatch slot source boundary base path runtime
        suffix (ulogCore payloadHeadOne) (Or.inl rfl) hsafe
  · simpa [ULogBytecode.encodeNatField, unaryFieldFirst, readHeadNat,
      codeTape, List.append_assoc] using
      reaches_sourceReadAtZero_mismatch slot source boundary base path runtime
        suffix (ulogCore payloadHeadBlank) (Or.inr rfl) hsafe
  · simpa [ULogBytecode.encodeNatField, unaryFieldFirst, readHeadNat,
      codeTape, List.append_assoc] using
      reaches_sourceReadAtOne_mismatch slot source boundary base path runtime
        suffix (ulogCore payloadHeadZero) (Or.inl rfl) hsafe
  · simpa [ULogBytecode.encodeNatField, unaryFieldFirst, readHeadNat,
      codeTape, List.append_assoc] using
      reaches_sourceReadAtOne_mismatch slot source boundary base path runtime
        suffix (ulogCore payloadHeadBlank) (Or.inr rfl) hsafe
  · simpa [ULogBytecode.encodeNatField, unaryFieldFirst, readHeadNat,
      codeTape, List.append_assoc] using
      reaches_sourceReadAtBlank_mismatch slot source boundary base path runtime
        suffix (ulogCore payloadHeadZero) (Or.inl rfl) hsafe
  · simpa [ULogBytecode.encodeNatField, unaryFieldFirst, readHeadNat,
      codeTape, List.append_assoc] using
      reaches_sourceReadAtBlank_mismatch slot source boundary base path runtime
        suffix (ulogCore payloadHeadOne) (Or.inr rfl) hsafe

end PakFixedPolyomino.ULogBootstrapExecution
