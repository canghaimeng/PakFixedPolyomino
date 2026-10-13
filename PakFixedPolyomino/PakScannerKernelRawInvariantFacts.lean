import PakFixedPolyomino.PakScannerRawShape

/-! Structural proofs on the original raw-state/rank/stage predicates and
the unchanged six scanner clauses. No path subset or compiler-trust table
enumeration is used. -/
namespace PakFixedPolyomino.PakScannerKernelRawInvariantFacts
open ConcretePakScanner MStarParserTailSoundness PakScannerRawShape
set_option maxHeartbeats 4000000

theorem legalScan_from_bottom_rawState (t : State) (b : Bool)
    (h : LegalScan PakCouplingGenerated.scannerBottom t b) :
    ScannerRawStateOK t ∧ scannerBufferRank t.centre = 0 := by
  obtain ⟨clause, hc⟩ := h
  rcases t with ⟨tp, tl, tc, ta, tm⟩
  cases b <;> cases clause <;>
    simp_all [LegalClause, Shift, PakCouplingGenerated.scannerBottom,
      headBuffer, ScannerRawStateOK, scannerRawStateOKB, scannerBufferRank]

theorem legalScan_preserves_rawState_and_rank (s t : State) (b : Bool)
    (hs : ScannerRawStateOK s) (hn : s.phase ≠ .bot) (h : LegalScan s t b) :
    ScannerRawStateOK t ∧ scannerBufferRank s.centre ≤ scannerBufferRank t.centre := by
  obtain ⟨clause, hc⟩ := h
  rcases s with ⟨sp, sl, sc, sa, sm⟩
  rcases t with ⟨tp, tl, tc, ta, tm⟩
  cases sc <;> cases sm <;> cases tm <;> cases b <;> cases clause <;>
    simp_all [LegalClause, Shift, newMid, modeOut, headBuffer,
      ScannerRawStateOK, scannerRawStateOKB, scannerBufferRank]

theorem bottom_edge_stage_core (t : State) (b : Bool)
    (h : LegalScan PakCouplingGenerated.scannerBottom t b) :
    bufferStage t.centre = .core := by
  have hr := (legalScan_from_bottom_rawState t b h).2
  cases hcentre : t.centre <;> simp_all [scannerBufferRank, bufferStage]

theorem legal_edge_stage_step (s t : State) (b : Bool)
    (hs : ScannerRawStateOK s) (hn : s.phase ≠ .bot) (h : LegalScan s t b) :
    stageStep (bufferStage s.centre) t.centre = some (bufferStage t.centre) := by
  obtain ⟨clause, hc⟩ := h
  rcases s with ⟨sp, sl, sc, sa, sm⟩
  rcases t with ⟨tp, tl, tc, ta, tm⟩
  cases sc <;> cases sm <;> cases tm <;> cases b <;> cases clause <;>
    simp_all [LegalClause, Shift, newMid, modeOut, headBuffer,
      ScannerRawStateOK, scannerRawStateOKB, scannerBufferRank,
      bufferStage, stageStep]

end PakFixedPolyomino.PakScannerKernelRawInvariantFacts
