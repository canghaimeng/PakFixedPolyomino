import PakFixedPolyomino.ULogCursorReadMismatch

/-! All valid-read opposite-slot mismatch exits at an arbitrary cursor. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem reaches_sourceReadAtZero_slotMismatch (slot : Bool) (source : ℕ)
    (boundary : ULogLetter) (base actionPath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe (codeTape (!slot) :: actionPath)) :
    Reaches
      (sourceReadStartedAt slot source boundary true base
        (codeTape (!slot) :: actionPath ++
          ulogCore payloadHeadZero :: runtime) suffix)
      (.running (.restoreRule slot)
        ⟨readMismatchBaseAt source 0 boundary base, ulogCore codeOne,
          codeTape (!slot) :: actionPath ++
            ulogCore payloadHeadZero :: runtime ++
              List.replicate source (ulogCore stateZero) ++
                ulogCore stateOne :: suffix⟩) := by
  have h₀ := reaches_readZero_match slot
    (codeTape (!slot) :: actionPath) hsafe
    (ulogCore codeOne :: List.replicate source (ulogCore codeZero) ++
      ulogCore boundary :: base)
    (runtime ++ List.replicate source (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  have h₁ : Reaches
      (.running (.fieldCompare .slot slot)
        (beforeRightPath (codeTape (!slot) :: actionPath)
          (ulogCore codeOne :: ulogCore codeOne ::
            List.replicate source (ulogCore codeZero) ++
              ulogCore boundary :: base)
          (ulogCore payloadHeadZero)
          (runtime ++ List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)))
      (.running (.restoreRule slot)
        ⟨readMismatchBaseAt source 0 boundary base, ulogCore codeOne,
          codeTape (!slot) :: actionPath ++
            ulogCore payloadHeadZero :: runtime ++
              List.replicate source (ulogCore stateZero) ++
                ulogCore stateOne :: suffix⟩) := by
    apply reaches_step
    simpa [beforeRightPath, readMismatchBaseAt, List.append_assoc] using
      (fieldCompare_slot_mismatch slot
        (readMismatchBaseAt source 0 boundary base) (ulogCore codeOne)
        (actionPath ++ ulogCore payloadHeadZero :: runtime ++
          List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
  have h₀' : Reaches
      (sourceReadStartedAt slot source boundary true base
        (codeTape (!slot) :: actionPath ++
          ulogCore payloadHeadZero :: runtime) suffix)
      (.running (.fieldCompare .slot slot)
        (beforeRightPath (codeTape (!slot) :: actionPath)
          (ulogCore codeOne :: ulogCore codeOne ::
            List.replicate source (ulogCore codeZero) ++
              ulogCore boundary :: base)
          (ulogCore payloadHeadZero)
          (runtime ++ List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
    simpa [sourceReadStartedAt, codeTape, List.append_assoc] using h₀
  exact reaches_trans h₀' h₁

theorem reaches_sourceReadAtOne_slotMismatch (slot : Bool) (source : ℕ)
    (boundary : ULogLetter) (base actionPath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe (codeTape (!slot) :: actionPath)) :
    Reaches
      (sourceReadStartedAt slot source boundary false base
        (ulogCore codeOne :: codeTape (!slot) :: actionPath ++
          ulogCore payloadHeadOne :: runtime) suffix)
      (.running (.restoreRule slot)
        ⟨readMismatchBaseAt source 1 boundary base, ulogCore codeOne,
          codeTape (!slot) :: actionPath ++
            ulogCore payloadHeadOne :: runtime ++
              List.replicate source (ulogCore stateZero) ++
                ulogCore stateOne :: suffix⟩) := by
  have h₀ := reaches_readOne_match slot
    (codeTape (!slot) :: actionPath) hsafe
    (ulogCore codeOne :: List.replicate source (ulogCore codeZero) ++
      ulogCore boundary :: base)
    (runtime ++ List.replicate source (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  have h₁ : Reaches
      (.running (.fieldCompare .slot slot)
        (beforeRightPath (codeTape (!slot) :: actionPath)
          (ulogCore codeOne :: ulogCore codeZero :: ulogCore codeOne ::
            List.replicate source (ulogCore codeZero) ++
              ulogCore boundary :: base)
          (ulogCore payloadHeadOne)
          (runtime ++ List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)))
      (.running (.restoreRule slot)
        ⟨readMismatchBaseAt source 1 boundary base, ulogCore codeOne,
          codeTape (!slot) :: actionPath ++
            ulogCore payloadHeadOne :: runtime ++
              List.replicate source (ulogCore stateZero) ++
                ulogCore stateOne :: suffix⟩) := by
    apply reaches_step
    simpa [beforeRightPath, readMismatchBaseAt, List.append_assoc] using
      (fieldCompare_slot_mismatch slot
        (readMismatchBaseAt source 1 boundary base) (ulogCore codeOne)
        (actionPath ++ ulogCore payloadHeadOne :: runtime ++
          List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
  have h₀' : Reaches
      (sourceReadStartedAt slot source boundary false base
        (ulogCore codeOne :: codeTape (!slot) :: actionPath ++
          ulogCore payloadHeadOne :: runtime) suffix)
      (.running (.fieldCompare .slot slot)
        (beforeRightPath (codeTape (!slot) :: actionPath)
          (ulogCore codeOne :: ulogCore codeZero :: ulogCore codeOne ::
            List.replicate source (ulogCore codeZero) ++
              ulogCore boundary :: base)
          (ulogCore payloadHeadOne)
          (runtime ++ List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
    simpa [sourceReadStartedAt, codeTape, List.append_assoc] using h₀
  exact reaches_trans h₀' h₁

theorem reaches_sourceReadAtBlank_slotMismatch (slot : Bool) (source : ℕ)
    (boundary : ULogLetter) (base actionPath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe (codeTape (!slot) :: actionPath)) :
    Reaches
      (sourceReadStartedAt slot source boundary false base
        (ulogCore codeZero :: ulogCore codeOne :: codeTape (!slot) ::
          actionPath ++ ulogCore payloadHeadBlank :: runtime) suffix)
      (.running (.restoreRule slot)
        ⟨readMismatchBaseAt source 2 boundary base, ulogCore codeOne,
          codeTape (!slot) :: actionPath ++
            ulogCore payloadHeadBlank :: runtime ++
              List.replicate source (ulogCore stateZero) ++
                ulogCore stateOne :: suffix⟩) := by
  have h₀ := reaches_readBlank_match slot
    (codeTape (!slot) :: actionPath) hsafe
    (ulogCore codeOne :: List.replicate source (ulogCore codeZero) ++
      ulogCore boundary :: base)
    (runtime ++ List.replicate source (ulogCore stateZero) ++
      ulogCore stateOne :: suffix)
  have h₁ : Reaches
      (.running (.fieldCompare .slot slot)
        (beforeRightPath (codeTape (!slot) :: actionPath)
          (ulogCore codeOne :: ulogCore codeZero :: ulogCore codeZero ::
            ulogCore codeOne :: List.replicate source (ulogCore codeZero) ++
              ulogCore boundary :: base)
          (ulogCore payloadHeadBlank)
          (runtime ++ List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix)))
      (.running (.restoreRule slot)
        ⟨readMismatchBaseAt source 2 boundary base, ulogCore codeOne,
          codeTape (!slot) :: actionPath ++
            ulogCore payloadHeadBlank :: runtime ++
              List.replicate source (ulogCore stateZero) ++
                ulogCore stateOne :: suffix⟩) := by
    apply reaches_step
    simpa [beforeRightPath, readMismatchBaseAt, List.append_assoc] using
      (fieldCompare_slot_mismatch slot
        (readMismatchBaseAt source 2 boundary base) (ulogCore codeOne)
        (actionPath ++ ulogCore payloadHeadBlank :: runtime ++
          List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))
  have h₀' : Reaches
      (sourceReadStartedAt slot source boundary false base
        (ulogCore codeZero :: ulogCore codeOne :: codeTape (!slot) ::
          actionPath ++ ulogCore payloadHeadBlank :: runtime) suffix)
      (.running (.fieldCompare .slot slot)
        (beforeRightPath (codeTape (!slot) :: actionPath)
          (ulogCore codeOne :: ulogCore codeZero :: ulogCore codeZero ::
            ulogCore codeOne :: List.replicate source (ulogCore codeZero) ++
              ulogCore boundary :: base)
          (ulogCore payloadHeadBlank)
          (runtime ++ List.replicate source (ulogCore stateZero) ++
            ulogCore stateOne :: suffix))) := by
    simpa [sourceReadStartedAt, codeTape, List.append_assoc] using h₀
  exact reaches_trans h₀' h₁

theorem reaches_sourceReadAt_slotMismatch (slot : Bool)
    (source read : ℕ) (hread : read < 3) (boundary : ULogLetter)
    (base actionPath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe (codeTape (!slot) :: actionPath)) :
    Reaches
      (sourceReadStartedAt slot source boundary (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape (!slot) :: actionPath ++ readHeadNat read :: runtime)
        suffix)
      (.running (.restoreRule slot)
        ⟨readMismatchBaseAt source read boundary base, ulogCore codeOne,
          codeTape (!slot) :: actionPath ++ readHeadNat read :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix⟩) := by
  interval_cases read
  · simpa [ULogBytecode.encodeNatField, unaryFieldFirst, readHeadNat,
      codeTape, List.append_assoc] using
      reaches_sourceReadAtZero_slotMismatch slot source boundary base
        actionPath runtime suffix hsafe
  · simpa [ULogBytecode.encodeNatField, unaryFieldFirst, readHeadNat,
      codeTape, List.append_assoc] using
      reaches_sourceReadAtOne_slotMismatch slot source boundary base
        actionPath runtime suffix hsafe
  · simpa [ULogBytecode.encodeNatField, unaryFieldFirst, readHeadNat,
      codeTape, List.append_assoc] using
      reaches_sourceReadAtBlank_slotMismatch slot source boundary base
        actionPath runtime suffix hsafe

end PakFixedPolyomino.ULogBootstrapExecution
