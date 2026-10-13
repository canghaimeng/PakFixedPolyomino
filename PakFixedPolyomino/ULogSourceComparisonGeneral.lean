import PakFixedPolyomino.ULogBoundaryBranchedCycle

/-! Source-field comparison for independent encoded and runtime lengths. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def sourceCompareStartAgainst (slot : Bool) (source current done : ℕ)
    (corridor left suffix : List Tape) : Result :=
  match source with
  | 0 => .running (.fieldCompare .source slot)
      ⟨left, ulogCore codeOne,
        corridor ++ List.replicate done (ulogCore stateMark) ++
          List.replicate current (ulogCore stateZero) ++
            ulogCore stateOne :: suffix⟩
  | s + 1 => .running (.fieldCompare .source slot)
      ⟨left, ulogCore codeZero,
        sourceCompareScanPath s corridor done ++
          match current with
          | 0 => ulogCore stateOne :: suffix
          | c + 1 => ulogCore stateZero ::
              List.replicate c (ulogCore stateZero) ++
                ulogCore stateOne :: suffix⟩

theorem reaches_sourceCompareCommon (slot : Bool) (source current done : ℕ)
    (corridor : List Tape) (hcorridor : SourceCompareCorridorSafe corridor)
    (left suffix : List Tape) :
    Reaches
      (sourceCompareStartAgainst slot source current done corridor left suffix)
      (sourceCompareStartAgainst slot (source - current) (current - source)
        (done + min source current) corridor
        (List.replicate (min source current) (ulogCore sourceMark) ++ left)
        suffix) := by
  induction source generalizing current done left with
  | zero =>
      simp [sourceCompareStartAgainst]
      exact reaches_refl _
  | succ source ih =>
      cases current with
      | zero =>
          simp [sourceCompareStartAgainst]
          exact reaches_refl _
      | succ current =>
          have hround := reaches_sourceCompareRound slot source done corridor
            (fun x hx => sourceCompareScanPath_seek_safe hcorridor hx)
            (fun x hx => sourceCompareScanPath_return_safe hcorridor hx)
            left
            (List.replicate current (ulogCore stateZero) ++
              ulogCore stateOne :: suffix)
          have htail := ih current (done + 1)
            (ulogCore sourceMark :: left)
          have hround' : Reaches
              (sourceCompareStartAgainst slot (source + 1) (current + 1)
                done corridor left suffix)
              (sourceCompareStartAgainst slot source current (done + 1)
                corridor (ulogCore sourceMark :: left) suffix) := by
            cases source <;> cases current <;>
              simpa [sourceCompareStartAgainst, sourceCompareScanPath,
                beforeRightPath, List.replicate_succ,
                List.replicate_succ', Nat.add_comm, Nat.add_left_comm,
                List.append_assoc] using hround
          have hall := reaches_trans hround' htail
          simpa [Nat.succ_sub_succ_eq_sub,
            List.replicate_succ, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm, List.append_assoc] using hall

end PakFixedPolyomino.ULogBootstrapExecution
