import PakFixedPolyomino.ULogSourceMismatchExecution

/-! Exact tape reconstruction after both source-length mismatch exits. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem restoreMismatchCell_corridor
    {corridor : List Tape} (hsource : SourceCompareCorridorSafe corridor)
    (hread : ∀ x ∈ corridor, x ≠ ulogCore readBoundary) :
    corridor.map restoreMismatchCell = corridor := by
  induction corridor with
  | nil => rfl
  | cons x xs ih =>
      have hs := hsource x (by simp)
      have hr := hread x (by simp)
      have hsourceTail : SourceCompareCorridorSafe xs := by
        intro y hy
        exact hsource y (by simp [hy])
      have hreadTail : ∀ y ∈ xs, y ≠ ulogCore readBoundary := by
        intro y hy
        exact hread y (by simp [hy])
      simp [restoreMismatchCell, hs.2.2.2.1, hs.2.2.2.2.2.1,
        hr, ih hsourceTail hreadTail]

theorem sourceShortRestorePath_map (done extra : ℕ)
    (corridor : List Tape) (hsource : SourceCompareCorridorSafe corridor)
    (hread : ∀ x ∈ corridor, x ≠ ulogCore readBoundary)
    (suffix : List Tape) :
    (sourceShortRestorePath done corridor).reverse.map restoreMismatchCell ++
        ulogCore stateZero :: List.replicate extra (ulogCore stateZero) ++
          ulogCore stateOne :: suffix =
      List.replicate done (ulogCore codeZero) ++ ulogCore codeOne ::
        corridor ++ List.replicate (done + extra + 1) (ulogCore stateZero) ++
          ulogCore stateOne :: suffix := by
  have hstateSource : ulogCore sourceMark ≠ ulogCore stateMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have hreadSource : ulogCore sourceMark ≠ ulogCore readBoundary :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have honeState : ulogCore codeOne ≠ ulogCore stateMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have honeSource : ulogCore codeOne ≠ ulogCore sourceMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have honeRead : ulogCore codeOne ≠ ulogCore readBoundary :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have hmarkSource : ulogCore stateMark ≠ ulogCore sourceMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have hmarkRead : ulogCore stateMark ≠ ulogCore readBoundary :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  simp [sourceShortRestorePath, sourceShortFinishPath,
    List.reverse_append, List.map_append, List.map_reverse,
    restoreMismatchCell, hstateSource, hreadSource, honeState, honeSource,
    honeRead, hmarkSource, hmarkRead,
    restoreMismatchCell_corridor hsource hread,
    ← List.replicate_add, List.replicate_succ, List.append_assoc]

theorem sourceLongRestorePath_map (remaining done : ℕ)
    (corridor : List Tape) (hsource : SourceCompareCorridorSafe corridor)
    (hread : ∀ x ∈ corridor, x ≠ ulogCore readBoundary)
    (suffix : List Tape) :
    (sourceLongRestorePath remaining done corridor).reverse.map
          restoreMismatchCell ++ ulogCore stateOne :: suffix =
      List.replicate (done + remaining + 1) (ulogCore codeZero) ++
        ulogCore codeOne :: corridor ++
          List.replicate done (ulogCore stateZero) ++
            ulogCore stateOne :: suffix := by
  have hstateSource : ulogCore sourceMark ≠ ulogCore stateMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have hreadSource : ulogCore sourceMark ≠ ulogCore readBoundary :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have hmarkSource : ulogCore stateMark ≠ ulogCore sourceMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have hmarkRead : ulogCore stateMark ≠ ulogCore readBoundary :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have hzeroState : ulogCore codeZero ≠ ulogCore stateMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have hzeroSource : ulogCore codeZero ≠ ulogCore sourceMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have hzeroRead : ulogCore codeZero ≠ ulogCore readBoundary :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have honeState : ulogCore codeOne ≠ ulogCore stateMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have honeSource : ulogCore codeOne ≠ ulogCore sourceMark :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  have honeRead : ulogCore codeOne ≠ ulogCore readBoundary :=
    ULogTapeDecoding.ulog_symbol_ne (by decide)
  simp [sourceLongRestorePath, sourceLongSeekPath, sourceCompareScanPath,
    List.reverse_append, List.map_append, List.map_reverse,
    restoreMismatchCell, hstateSource, hreadSource, hmarkSource, hmarkRead,
    hzeroState, hzeroSource, hzeroRead, honeState, honeSource, honeRead,
    restoreMismatchCell_corridor hsource hread,
    ← List.replicate_add, List.replicate_succ, List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [show remaining + (done + 1) = 1 + done + remaining by omega]
  rw [List.replicate_add, List.replicate_add]
  simp only [List.replicate_one, List.singleton_append, List.cons_append,
    List.nil_append, List.append_assoc]

end PakFixedPolyomino.ULogBootstrapExecution
