import PakFixedPolyomino.ULogReadSlotRestoration

/-! Normalize read/slot mismatch exits back to the current source boundary. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem readMismatch_beforeLeft_eq (source read : ℕ)
    (boundary : ULogLetter) (scanPath base right : List Tape) :
    beforeLeftPath scanPath.reverse
        (readMismatchBaseAt source read boundary base)
        (ulogCore readBoundary) right =
      beforeLeftPath (readMismatchRestorePath source read scanPath)
        base (ulogCore boundary) right := by
  cases hr : scanPath.reverse with
  | nil =>
      have he : scanPath = [] := by
        simpa using congrArg List.reverse hr
      subst scanPath
      cases read <;> cases source <;>
        simp [beforeLeftPath, readMismatchBaseAt, readMismatchRestorePath,
          List.replicate_succ, List.append_assoc]
  | cons x xs =>
      cases read <;> cases source <;>
        simp [beforeLeftPath, readMismatchBaseAt, readMismatchRestorePath,
          hr, List.replicate_succ, List.append_assoc]

theorem slotMismatch_beforeLeft_eq (source read : ℕ)
    (boundary : ULogLetter) (base right : List Tape) :
    ⟨readMismatchBaseAt source read boundary base, ulogCore codeOne, right⟩ =
      beforeLeftPath (slotMismatchRestorePath source read)
        base (ulogCore boundary) right := by
  cases read <;> cases source <;>
    simp [beforeLeftPath, readMismatchBaseAt, slotMismatchRestorePath,
      List.replicate_succ, List.append_assoc]

theorem reaches_sourceReadAtMismatch_boundary
    (slot : Bool) (source read actual : ℕ)
    (hread : read < 3) (hactual : actual < 3) (hne : read ≠ actual)
    (boundary : ULogLetter) (base scanPath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe scanPath) :
    Reaches
      (sourceReadStartedAt slot source boundary (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          scanPath ++ readHeadNat actual :: runtime) suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath (readMismatchRestorePath source read scanPath)
          base (ulogCore boundary)
          (readHeadNat actual :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) := by
  have h := reaches_sourceReadAt_mismatch slot source read actual hread hactual
    hne boundary base scanPath runtime suffix hsafe
  rw [readMismatch_beforeLeft_eq] at h
  exact h

theorem reaches_sourceReadAtSlotMismatch_boundary
    (slot : Bool) (source read : ℕ) (hread : read < 3)
    (boundary : ULogLetter) (base actionPath runtime suffix : List Tape)
    (hsafe : ReadCorridorSafe (codeTape (!slot) :: actionPath)) :
    Reaches
      (sourceReadStartedAt slot source boundary (unaryFieldFirst read) base
        ((ULogBytecode.encodeNatField read).tail.map codeTape ++
          codeTape (!slot) :: actionPath ++ readHeadNat read :: runtime)
        suffix)
      (.running (.restoreRule slot)
        (beforeLeftPath (slotMismatchRestorePath source read)
          base (ulogCore boundary)
          (codeTape (!slot) :: actionPath ++ readHeadNat read :: runtime ++
            List.replicate source (ulogCore stateZero) ++
              ulogCore stateOne :: suffix))) := by
  have h := reaches_sourceReadAt_slotMismatch slot source read hread boundary
    base actionPath runtime suffix hsafe
  rw [slotMismatch_beforeLeft_eq] at h
  exact h

end PakFixedPolyomino.ULogBootstrapExecution
