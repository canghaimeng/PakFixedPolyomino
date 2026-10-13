import PakFixedPolyomino.PakScannerKernelRawInvariantFacts
import PakFixedPolyomino.PakScannerKernelTerminalFacts

/-! Original ALL scanner paths: positive phases, raw-state and adjacent rank
invariants, using the six-clause kernel facts. -/
namespace PakFixedPolyomino.PakScannerPathRawStandard
open MStarParserTailSoundness

theorem scannerPath_phase_ne_bot_of_pos {n : ℕ}
    (P : PakScannerBaselineAutomaton.ScannerPath n)
    (j : Fin (n + 1)) (hj : 0 < j.1) : (P.states j).phase ≠ .bot := by
  let i : Fin n := ⟨j.1 - 1, by omega⟩
  have htarget : P.states ⟨i.1 + 1, by omega⟩ = P.states j := by
    apply congrArg P.states
    apply Fin.ext
    dsimp [i]
    omega
  intro hbot
  apply PakScannerKernelTerminalFacts.no_clause_to_bot
    (P.states ⟨i.1, Nat.lt_succ_of_lt i.2⟩) (P.states j) (n.testBit i.1)
    hbot
  rw [← htarget]
  exact P.legal i

theorem scannerPath_state_succ_rawState {n : ℕ}
    (P : PakScannerBaselineAutomaton.ScannerPath n) :
    ∀ (k : ℕ) (hk : k + 1 ≤ n),
      ScannerRawStateOK (P.states ⟨k + 1, by omega⟩) := by
  intro k
  induction k with
  | zero =>
      intro hk
      apply (PakScannerKernelRawInvariantFacts.legalScan_from_bottom_rawState
        (P.states ⟨1, by omega⟩) (n.testBit 0) ?_).1
      rw [← P.bottom]
      simpa using P.legal ⟨0, by omega⟩
  | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      let jpos : Fin (n + 1) := ⟨k + 1, by have := hk; omega⟩
      have hjpos : 0 < jpos.1 := by simp [jpos]
      exact (PakScannerKernelRawInvariantFacts.legalScan_preserves_rawState_and_rank
        (P.states ⟨k + 1, by omega⟩) (P.states ⟨k + 2, by omega⟩)
        (n.testBit (k + 1)) hprev
        (scannerPath_phase_ne_bot_of_pos P jpos hjpos)
        (by simpa using P.legal ⟨k + 1, by omega⟩)).1

theorem scannerPath_rank_mono_adjacent_of_pos {n : ℕ}
    (P : PakScannerBaselineAutomaton.ScannerPath n)
    (j : Fin n) (hj : 0 < j.1) :
    scannerBufferRank
        (P.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩).centre ≤
      scannerBufferRank (P.states ⟨j.1 + 1, by omega⟩).centre := by
  have hok := scannerPath_state_succ_rawState P (j.1 - 1) (by omega)
  have hstate : P.states ⟨j.1 - 1 + 1, by omega⟩ =
      P.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩ := by
    apply congrArg P.states
    apply Fin.ext
    change j.1 - 1 + 1 = j.1
    omega
  rw [hstate] at hok
  exact (PakScannerKernelRawInvariantFacts.legalScan_preserves_rawState_and_rank
    (P.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
    (P.states ⟨j.1 + 1, by omega⟩) (n.testBit j.1) hok
    (scannerPath_phase_ne_bot_of_pos P _ hj) (P.legal j)).2

end PakFixedPolyomino.PakScannerPathRawStandard
