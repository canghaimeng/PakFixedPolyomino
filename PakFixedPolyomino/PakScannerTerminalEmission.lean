import PakFixedPolyomino.PakScannerTerminal

/-! Readout of the terminal scanner as one concrete tape row. -/

namespace PakFixedPolyomino.PakScannerTerminalEmission

open ConcretePakScanner PakScannerPath PakScannerTerminal

variable {MachineState Tape : Type*}

def stateTapeCell
    (B : PakCouplingGenerated.MachineBoundaryData MachineState Tape)
    (bits : List Bool) (hbits : 0 < bits.length) (terminal : ℕ)
    (z : Int) : TableauCell MachineState Tape :=
  if z < 0 then .plain B.hash
  else PakCouplingGenerated.bufferCell B
    (terminalScannerState bits hbits terminal z.toNat).centre

def stateTapeWindow
    (B : PakCouplingGenerated.MachineBoundaryData MachineState Tape)
    (bits : List Bool) (hbits : 0 < bits.length) (terminal : ℕ)
    (j : Fin (bits.length + 2)) :
    CellTriple (TableauCell MachineState Tape) :=
  { minus := stateTapeCell B bits hbits terminal ((j.1 : Int) - 1)
    center := stateTapeCell B bits hbits terminal j.1
    plus := stateTapeCell B bits hbits terminal ((j.1 : Int) + 1) }

theorem stateTapeCell_eq_terminalScannerTapeCell
    (B : PakCouplingGenerated.MachineBoundaryData MachineState Tape)
    (bits : List Bool) (hbits : 0 < bits.length)
    (terminal : ℕ) (hterminal : 0 < terminal)
    (hbound : terminal < bits.length) (z : Int) :
    stateTapeCell B bits hbits terminal z =
      terminalScannerTapeCell B bits terminal z := by
  cases z with
  | negSucc k =>
      simp [stateTapeCell, terminalScannerTapeCell]
  | ofNat k =>
      cases k with
      | zero =>
          simp [stateTapeCell, terminalScannerTapeCell,
            terminalScannerState, PakCouplingGenerated.scannerBottom,
            PakCouplingGenerated.bufferCell]
      | succ k =>
          have hk_nonneg : ¬((k : Int) < 0) := by omega
          have hks_nonneg : ¬((k : Int) + 1 < 0) := by omega
          by_cases hk : k < terminal
          · have hkle : k + 1 ≤ terminal := by omega
            have hkbits : k < bits.length := by omega
            simp [stateTapeCell, terminalScannerTapeCell,
              terminalScannerState, terminalTailState, terminalTopState,
              terminalDataCell, midState, hkle, hk, hkbits,
              hk_nonneg, hks_nonneg]
          · by_cases hkeq : k = terminal
            · have hnextle : terminal + 1 ≤ bits.length := by omega
              have hnextnot : ¬ terminal + 1 ≤ terminal := by omega
              have ht_nonneg : ¬((terminal : Int) < 0) := by omega
              have hts_nonneg : ¬((terminal : Int) + 1 < 0) := by omega
              simp [stateTapeCell, terminalScannerTapeCell,
                terminalScannerState, terminalTailState, terminalTopState,
                terminalDataCell, midState, hkeq, hnextle, hnextnot,
                hbound, hk_nonneg, hks_nonneg, ht_nonneg, hts_nonneg]
            · have hgt : terminal < k := by omega
              by_cases hkbits : k < bits.length
              · have hnextle : k + 1 ≤ bits.length := by omega
                have hnextnot : ¬ k + 1 ≤ terminal := by omega
                simp [stateTapeCell, terminalScannerTapeCell,
                  terminalScannerState, terminalTailState, terminalTopState,
                  terminalDataCell, midState, hk, hkeq, hgt, hkbits,
                  hnextle, hnextnot, hk_nonneg, hks_nonneg]
              · have hnextnot : ¬ k + 1 ≤ bits.length := by omega
                by_cases hktop : k = bits.length
                · have hnot : ¬ bits.length < terminal := by omega
                  have hlen_nonneg : ¬((bits.length : Int) + 1 < 0) := by omega
                  simp [stateTapeCell, terminalScannerTapeCell,
                    terminalScannerState, terminalTailState, terminalTopState,
                    terminalDataCell, midState, hk, hkeq, hgt, hkbits,
                    hnextnot, hktop, hk_nonneg, hks_nonneg,
                    hnot, hlen_nonneg, PakCouplingGenerated.bufferCell]
                · simp [stateTapeCell, terminalScannerTapeCell,
                    terminalScannerState, terminalTailState, terminalTopState,
                    terminalDataCell, midState, hk, hkeq, hgt, hkbits,
                    hnextnot, hktop, hk_nonneg, hks_nonneg,
                    ConcretePakScanner.topNorth,
                    PakCouplingGenerated.bufferCell]

theorem state_left_eq_previous_center
    (bits : List Bool) (hbits : 0 < bits.length)
    (terminal : ℕ) (hterminal : 0 < terminal)
    (hbound : terminal < bits.length)
    (j : Fin (bits.length + 2)) (hj : 0 < j.1) :
    (terminalScannerState bits hbits terminal j.1).left =
      (terminalScannerState bits hbits terminal (j.1 - 1)).centre := by
  let jm : Fin (bits.length + 2) := ⟨j.1 - 1, by omega⟩
  rcases terminalScannerColumn_legal bits hbits terminal hterminal hbound false jm with
    ⟨s, t, hcol, hlegal⟩
  have hpair :
      (terminalScannerState bits hbits terminal jm.1,
        terminalScannerState bits hbits terminal (jm.1 + 1)) = (s, t) := by
    exact Option.some.inj (by simpa [terminalScannerColumn] using hcol)
  have hs : terminalScannerState bits hbits terminal jm.1 = s := by
    simpa using congrArg Prod.fst hpair
  have ht : terminalScannerState bits hbits terminal (jm.1 + 1) = t := by
    simpa using congrArg Prod.snd hpair
  have hshift := legalScan_shift hlegal
  unfold Shift at hshift
  rw [← hs, ← ht] at hshift
  have hnext : jm.1 + 1 = j.1 := by
    dsimp [jm]
    omega
  simpa [jm, hnext] using hshift

theorem terminalScannerColumn_emits_stateTapeWindow
    (B : PakCouplingGenerated.MachineBoundaryData MachineState Tape)
    (bits : List Bool) (hbits : 0 < bits.length)
    (terminal : ℕ) (hterminal : 0 < terminal)
    (hbound : terminal < bits.length)
    (j : Fin (bits.length + 2)) :
    PakCouplingGenerated.emittedWindow B
        (terminalScannerState bits hbits terminal j.1)
        (terminalScannerState bits hbits terminal (j.1 + 1)) =
      stateTapeWindow B bits hbits terminal j := by
  apply CellTriple.ext
  · by_cases hj : j.1 = 0
    · simp [stateTapeWindow, stateTapeCell, terminalScannerState,
        PakCouplingGenerated.emittedWindow, PakCouplingGenerated.bufferCell,
        PakCouplingGenerated.scannerBottom, hj]
    · have hjpos : 0 < j.1 := Nat.pos_of_ne_zero hj
      have hleft := state_left_eq_previous_center bits hbits terminal
        hterminal hbound j hjpos
      change PakCouplingGenerated.bufferCell B
          (terminalScannerState bits hbits terminal j.1).left = _
      rw [hleft]
      simp [stateTapeWindow, stateTapeCell, hjpos, hj]
  · have hnonneg : ¬((j.1 : Int) < 0) := by omega
    simp [stateTapeWindow, stateTapeCell,
      PakCouplingGenerated.emittedWindow, hnonneg]
  · have hnonneg : ¬((j.1 : Int) + 1 < 0) := by omega
    simp [stateTapeWindow, stateTapeCell,
      PakCouplingGenerated.emittedWindow, hnonneg]

theorem stateTapeWindow_eq_terminalScannerTapeWindow
    (B : PakCouplingGenerated.MachineBoundaryData MachineState Tape)
    (bits : List Bool) (hbits : 0 < bits.length)
    (terminal : ℕ) (hterminal : 0 < terminal)
    (hbound : terminal < bits.length)
    (j : Fin (bits.length + 2)) :
    stateTapeWindow B bits hbits terminal j =
      terminalScannerTapeWindow B bits terminal j := by
  apply CellTriple.ext
  · change stateTapeCell B bits hbits terminal ((j.1 : Int) - 1) =
      terminalScannerTapeCell B bits terminal ((j.1 : Int) - 1)
    exact stateTapeCell_eq_terminalScannerTapeCell B bits hbits terminal
      hterminal hbound _
  · change stateTapeCell B bits hbits terminal j.1 =
      terminalScannerTapeCell B bits terminal j.1
    exact stateTapeCell_eq_terminalScannerTapeCell B bits hbits terminal
      hterminal hbound _
  · change stateTapeCell B bits hbits terminal ((j.1 : Int) + 1) =
      terminalScannerTapeCell B bits terminal ((j.1 : Int) + 1)
    exact stateTapeCell_eq_terminalScannerTapeCell B bits hbits terminal
      hterminal hbound _

theorem terminalScannerColumn_emits_terminalTapeWindow
    (B : PakCouplingGenerated.MachineBoundaryData MachineState Tape)
    (bits : List Bool) (hbits : 0 < bits.length)
    (terminal : ℕ) (hterminal : 0 < terminal)
    (hbound : terminal < bits.length)
    (j : Fin (bits.length + 2)) :
    PakCouplingGenerated.emittedWindow B
        (terminalScannerState bits hbits terminal j.1)
        (terminalScannerState bits hbits terminal (j.1 + 1)) =
      terminalScannerTapeWindow B bits terminal j := by
  rw [terminalScannerColumn_emits_stateTapeWindow B bits hbits terminal
    hterminal hbound j]
  exact stateTapeWindow_eq_terminalScannerTapeWindow B bits hbits terminal
    hterminal hbound j

end PakFixedPolyomino.PakScannerTerminalEmission
