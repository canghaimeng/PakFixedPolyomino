import PakFixedPolyomino.PakGeneralCapacityFullFrameForward
import PakFixedPolyomino.PakScannerTerminalEmission
import PakFixedPolyomino.PakSideScannerRow

/-!
# Literal initial row at an arbitrary scanner capacity

The finite row below is deliberately written in the same physical list form
read from a slot-one frame: encoded input, two fixed entry work cells, the
actual free-work capacity, one `rightEnd`, and the residual hash tail.
-/

namespace PakFixedPolyomino.PakGeneralCapacityInitialWindow

open FiniteOneTapeProgram FiniteOneTapeSemantics
open PakGeneralCapacityFullFrameForward
open PakSlotOneScannerMultiplicity
open MStarConcreteAlphabet MStarOuterProgram MStarParserExecution
open MStarCopierMicrocode

abbrev FixedTape := PakEncodedStart.Fixed.Tape
abbrev FixedState := PakEncodedStart.Fixed.State
abbrev MStarConfig := PakEncodedStart.MStarConfig

def capacityHashTailLength (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) : ℕ :=
  (PakSideScanner.sideScannerBits x).length -
    (capacityTerminalIndex x c + 1)

def capacityInitialCells (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) : List FixedTape :=
  inputCells zero one work (ConcretePakSide.encodedWord x) ++
    [Tape.core work, Tape.core work] ++
      List.replicate c.1 (Tape.core work) ++
        [rightEnd] ++ List.replicate (capacityHashTailLength x c) Tape.hash

theorem capacityInitialCells_prefix_length (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) :
    (inputCells zero one work (ConcretePakSide.encodedWord x) ++
      [Tape.core work, Tape.core work] ++
      List.replicate c.1 (Tape.core work)).length =
      capacityTerminalIndex x c := by
  simp [capacityTerminalIndex, inputCells]
  omega

theorem capacityInitialCells_length (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) :
    (capacityInitialCells x c).length =
      (PakSideScanner.sideScannerBits x).length := by
  have hterm : capacityTerminalIndex x c + 1 ≤
      (PakSideScanner.sideScannerBits x).length :=
    Nat.succ_le_of_lt (capacityTerminalIndex_lt x c)
  let pre := inputCells zero one work (ConcretePakSide.encodedWord x) ++
    [Tape.core work, Tape.core work] ++
      List.replicate c.1 (Tape.core work)
  have hpre : pre.length = capacityTerminalIndex x c := by
    simpa [pre] using capacityInitialCells_prefix_length x c
  change (pre ++ [rightEnd] ++
    List.replicate (capacityHashTailLength x c) Tape.hash).length = _
  simp [hpre, capacityHashTailLength]
  have hcancel := Nat.sub_add_cancel hterm
  omega

private def capacityInitialPrefix (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) : List FixedTape :=
  inputCells zero one work (ConcretePakSide.encodedWord x) ++
    [Tape.core work, Tape.core work] ++
      List.replicate c.1 (Tape.core work)

private theorem capacityInitialPrefix_length (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) :
    (capacityInitialPrefix x c).length = capacityTerminalIndex x c := by
  simpa [capacityInitialPrefix] using capacityInitialCells_prefix_length x c

private theorem capacityInitialCells_decomp (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) :
    capacityInitialCells x c = capacityInitialPrefix x c ++
      rightEnd :: List.replicate (capacityHashTailLength x c) Tape.hash := by
  simp [capacityInitialCells, capacityInitialPrefix, List.append_assoc]

private theorem workTail_getD (k q : ℕ) (hq : q < k + 2) :
    ([Tape.core work, Tape.core work] ++
      List.replicate k (Tape.core work) : List FixedTape).getD q Tape.hash =
        Tape.core work := by
  cases q with
  | zero => simp
  | succ q =>
      cases q with
      | zero => simp
      | succ q =>
          have hqk : q < k := by omega
          change (List.replicate k (Tape.core work)).getD q Tape.hash = _
          exact List.getD_replicate (Tape.core work) hqk

theorem capacityInitialCells_getD_encoded (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) (p : ℕ)
    (hp : p < (ConcretePakSide.encodedWord x).length) :
    (capacityInitialCells x c).getD p Tape.hash =
      bitCell zero one ((PakSideScanner.sideScannerBits x).getD p false) := by
  unfold capacityInitialCells
  simp only [List.append_assoc]
  rw [List.getD_append _ _ _ _]
  · exact PakSideScannerRow.parserCells_getD_encoded x p hp
  · have hinput : (inputCells zero one work
        (ConcretePakSide.encodedWord x)).length =
          (ConcretePakSide.encodedWord x).length + 1 := by
        simp [inputCells]
    omega

theorem capacityInitialCells_getD_work (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) (p : ℕ)
    (hlow : (ConcretePakSide.encodedWord x).length ≤ p)
    (hhigh : p < capacityTerminalIndex x c) :
    (capacityInitialCells x c).getD p Tape.hash = Tape.core work := by
  rw [capacityInitialCells_decomp]
  rw [List.getD_append _ _ _ _]
  unfold capacityInitialPrefix
  simp only [List.append_assoc]
  · by_cases hp : p < (inputCells zero one work
        (ConcretePakSide.encodedWord x)).length
    · have hinput : (inputCells zero one work
          (ConcretePakSide.encodedWord x)).length =
          (ConcretePakSide.encodedWord x).length + 1 := by
        simp [inputCells]
      have hpEq : p = (ConcretePakSide.encodedWord x).length := by omega
      subst p
      rw [List.getD_append _ _ _ _]
      exact PakSideScannerRow.parserCells_getD_encoded_end x
      simp [inputCells]
    · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hp)]
      have hinput : (inputCells zero one work
          (ConcretePakSide.encodedWord x)).length =
          (ConcretePakSide.encodedWord x).length + 1 := by
        simp [inputCells]
      have hq : p - (inputCells zero one work
          (ConcretePakSide.encodedWord x)).length < c.1 + 2 := by
        have hpre : (inputCells zero one work
            (ConcretePakSide.encodedWord x)).length + (c.1 + 2) =
            capacityTerminalIndex x c := by
          simp [capacityTerminalIndex, inputCells]
          omega
        omega
      exact workTail_getD c.1 _ hq
  · rw [capacityInitialPrefix_length]
    exact hhigh

theorem capacityInitialCells_getD_rightEnd (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) :
    (capacityInitialCells x c).getD (capacityTerminalIndex x c) Tape.hash =
      rightEnd := by
  rw [capacityInitialCells_decomp]
  rw [List.getD_append_right _ _ _ _]
  · simp [capacityInitialPrefix_length]
  · rw [capacityInitialPrefix_length]

theorem capacityInitialCells_getD_after_rightEnd (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) (p : ℕ)
    (hlow : capacityTerminalIndex x c < p)
    (hhigh : p < (PakSideScanner.sideScannerBits x).length) :
    (capacityInitialCells x c).getD p Tape.hash = Tape.hash := by
  rw [capacityInitialCells_decomp]
  rw [List.getD_append_right _ _ _ _]
  · rw [capacityInitialPrefix_length]
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (Nat.sub_pos_of_lt hlow))
    rw [hq, List.getD_cons_succ]
    simp
  · rw [capacityInitialPrefix_length]
    exact Nat.le_of_lt hlow

def capacityInitialCell (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) (p : ℕ) :
    TableauCell FixedState FixedTape :=
  if p = 0 then
    .head (.start : FixedState) ((capacityInitialCells x c).getD p Tape.hash)
  else .plain ((capacityInitialCells x c).getD p Tape.hash)

private theorem capacityCells_head_zero (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) :
    (capacityInitialCells x c).getD 0 Tape.hash = Tape.core zero := by
  unfold capacityInitialCells
  simp only [List.append_assoc]
  rw [List.getD_append _ _ _ _]
  · exact PakEncodedStart.parserCells_head_zero x
  · simp [inputCells]

theorem terminalDataCell_eq_capacityInitialCell (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) (p : ℕ)
    (hp : p < (PakSideScanner.sideScannerBits x).length) :
    PakCouplingGenerated.bufferCell MStarULogAssembly.boundaryData
        (PakScannerTerminal.terminalDataCell
          (PakSideScanner.sideScannerBits x) (capacityTerminalIndex x c) p) =
      capacityInitialCell x c p := by
  have htermPos := capacityTerminalIndex_pos x c
  have hencTerm : (ConcretePakSide.encodedWord x).length <
      capacityTerminalIndex x c := by
    unfold capacityTerminalIndex
    omega
  by_cases hp0 : p = 0
  · subst p
    rw [PakScannerTerminal.terminalDataCell_lt _ _ _ htermPos]
    rw [PakSideScannerRow.sideDataCell_zero]
    unfold capacityInitialCell
    rw [if_pos rfl, capacityCells_head_zero]
    simp [PakCouplingGenerated.bufferCell, MStarULogAssembly.boundaryData,
      MStarOuterProgram.boundaryData, MStarULogAssembly.data,
      MStarCopierMicrocode.attach]
  · by_cases henc : p < (ConcretePakSide.encodedWord x).length
    · rw [PakScannerTerminal.terminalDataCell_lt _ _ _
        (henc.trans hencTerm)]
      rw [PakSideScannerRow.sideDataCell_encoded x p
        (Nat.pos_of_ne_zero hp0) henc]
      unfold capacityInitialCell
      rw [if_neg hp0, capacityInitialCells_getD_encoded x c p henc]
      cases hb : (PakSideScanner.sideScannerBits x).getD p false <;>
        simp [hb, MStarParserExecution.bitCell,
          PakCouplingGenerated.bufferCell, MStarULogAssembly.boundaryData,
          MStarOuterProgram.boundaryData, MStarULogAssembly.data,
          MStarCopierMicrocode.attach]
    · have hlow : (ConcretePakSide.encodedWord x).length ≤ p :=
        Nat.le_of_not_gt henc
      by_cases hbefore : p < capacityTerminalIndex x c
      · rw [PakScannerTerminal.terminalDataCell_lt _ _ _ hbefore]
        rw [PakSideScannerRow.sideDataCell_work x p hlow hp]
        unfold capacityInitialCell
        rw [if_neg hp0, capacityInitialCells_getD_work x c p hlow hbefore]
        simp [PakCouplingGenerated.bufferCell, MStarULogAssembly.boundaryData,
          MStarOuterProgram.boundaryData, MStarULogAssembly.data,
          MStarCopierMicrocode.attach]
      · by_cases heq : p = capacityTerminalIndex x c
        · subst p
          rw [PakScannerTerminal.terminalDataCell_eq]
          unfold capacityInitialCell
          rw [if_neg (Nat.ne_of_gt htermPos),
            capacityInitialCells_getD_rightEnd]
          simp [PakCouplingGenerated.bufferCell, MStarULogAssembly.boundaryData,
            MStarOuterProgram.boundaryData, MStarCopierMicrocode.rightEnd,
            MStarULogAssembly.data, MStarCopierMicrocode.attach]
        · have hafter : capacityTerminalIndex x c < p := by omega
          rw [PakScannerTerminal.terminalDataCell_gt _ _ _ hafter]
          unfold capacityInitialCell
          rw [if_neg hp0,
            capacityInitialCells_getD_after_rightEnd x c p hafter hp]
          simp [PakCouplingGenerated.bufferCell, MStarULogAssembly.boundaryData,
            MStarOuterProgram.boundaryData, MStarULogAssembly.data,
            MStarCopierMicrocode.attach]

def capacityInitialTableauCell (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) (z : Int) : TableauCell FixedState FixedTape :=
  if z ≤ 0 then .plain Tape.hash
  else capacityInitialCell x c (Int.toNat (z - 1))

theorem terminalScannerTapeCell_eq_capacityInitialTableauCell
    (x : ConcretePakSide.Word) (c : ScannerCapacity x) (z : Int) :
    PakScannerTerminal.terminalScannerTapeCell MStarULogAssembly.boundaryData
        (PakSideScanner.sideScannerBits x) (capacityTerminalIndex x c) z =
      capacityInitialTableauCell x c z := by
  unfold PakScannerTerminal.terminalScannerTapeCell capacityInitialTableauCell
  by_cases hz : z ≤ 0
  · simp [hz, MStarULogAssembly.boundaryData,
      MStarOuterProgram.boundaryData]
  · rw [if_neg hz, if_neg hz]
    by_cases hp : Int.toNat (z - 1) <
        (PakSideScanner.sideScannerBits x).length
    · rw [if_pos hp]
      exact terminalDataCell_eq_capacityInitialCell x c _ hp
    · rw [if_neg hp]
      have hp0 : Int.toNat (z - 1) ≠ 0 := by
        intro hzero
        rw [hzero] at hp
        exact hp (PakSideScanner.sideScannerBits_pos x)
      unfold capacityInitialCell
      rw [if_neg hp0]
      have hget : (capacityInitialCells x c).getD
          (Int.toNat (z - 1)) Tape.hash = Tape.hash := by
        apply List.getD_eq_default
        rw [capacityInitialCells_length]
        exact Nat.le_of_not_gt hp
      rw [hget]
      simp [MStarULogAssembly.boundaryData, MStarOuterProgram.boundaryData]

def capacityInitialWindow (x : ConcretePakSide.Word)
    (c : ScannerCapacity x)
    (j : Fin ((PakSideScanner.sideScannerBits x).length + 2)) :
    CellTriple (TableauCell FixedState FixedTape) :=
  { minus := capacityInitialTableauCell x c ((j.1 : Int) - 1)
    center := capacityInitialTableauCell x c j.1
    plus := capacityInitialTableauCell x c ((j.1 : Int) + 1) }

theorem terminalScannerTapeWindow_eq_capacityInitialWindow
    (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (j : Fin ((PakSideScanner.sideScannerBits x).length + 2)) :
    PakScannerTerminal.terminalScannerTapeWindow
        MStarULogAssembly.boundaryData (PakSideScanner.sideScannerBits x)
        (capacityTerminalIndex x c) j = capacityInitialWindow x c j := by
  unfold PakScannerTerminal.terminalScannerTapeWindow capacityInitialWindow
  apply CellTriple.ext
  · change PakScannerTerminal.terminalScannerTapeCell
        MStarULogAssembly.boundaryData (PakSideScanner.sideScannerBits x)
        (capacityTerminalIndex x c) ((j.1 : Int) - 1) = _
    exact terminalScannerTapeCell_eq_capacityInitialTableauCell x c _
  · change PakScannerTerminal.terminalScannerTapeCell
        MStarULogAssembly.boundaryData (PakSideScanner.sideScannerBits x)
        (capacityTerminalIndex x c) (j.1 : Int) = _
    exact terminalScannerTapeCell_eq_capacityInitialTableauCell x c _
  · change PakScannerTerminal.terminalScannerTapeCell
        MStarULogAssembly.boundaryData (PakSideScanner.sideScannerBits x)
        (capacityTerminalIndex x c) ((j.1 : Int) + 1) = _
    exact terminalScannerTapeCell_eq_capacityInitialTableauCell x c _

/-- The arbitrary-capacity terminal scanner emits the literal physical row,
not merely a row with the same scalar capacity. -/
theorem capacityScannerColumn_emits_capacityInitialWindow
    (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (j : Fin ((PakSideScanner.sideScannerBits x).length + 2)) :
    PakCouplingGenerated.emittedWindow MStarULogAssembly.boundaryData
        (PakScannerTerminal.terminalScannerState
          (PakSideScanner.sideScannerBits x)
          (PakSideScanner.sideScannerBits_pos x)
          (capacityTerminalIndex x c) j.1)
        (PakScannerTerminal.terminalScannerState
          (PakSideScanner.sideScannerBits x)
          (PakSideScanner.sideScannerBits_pos x)
          (capacityTerminalIndex x c) (j.1 + 1)) =
      capacityInitialWindow x c j := by
  rw [PakScannerTerminalEmission.terminalScannerColumn_emits_terminalTapeWindow
    MStarULogAssembly.boundaryData (PakSideScanner.sideScannerBits x)
    (PakSideScanner.sideScannerBits_pos x)
    (capacityTerminalIndex x c) (capacityTerminalIndex_pos x c)
    (capacityTerminalIndex_lt x c) j]
  exact terminalScannerTapeWindow_eq_capacityInitialWindow x c j

def capacityInitialTape (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) (z : Int) : FixedTape :=
  if 1 ≤ z then
    (capacityInitialCells x c).getD (Int.toNat (z - 1)) Tape.hash
  else Tape.hash

theorem capacityInitialTape_left_hash (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) {z : Int} (hz : z < 1) :
    capacityInitialTape x c z = Tape.hash := by
  simp [capacityInitialTape, not_le_of_gt hz]

theorem capacityInitialCells_head_zero (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) :
    (capacityInitialCells x c).getD 0 Tape.hash = Tape.core zero := by
  unfold capacityInitialCells
  simp only [List.append_assoc]
  rw [List.getD_append _ _ _ _]
  · exact PakEncodedStart.parserCells_head_zero x
  · simp [inputCells]

theorem capacityInitialTape_head_zero (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) :
    capacityInitialTape x c 1 = Tape.core zero := by
  change (capacityInitialCells x c).getD 0 Tape.hash = Tape.core zero
  exact capacityInitialCells_head_zero x c

theorem update_capacityInitialTape (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) :
    Function.update (capacityInitialTape x c) 1 (Tape.core zero) =
      capacityInitialTape x c := by
  funext z
  by_cases hz : z = 1
  · subst z
    simpa [Function.update] using (capacityInitialTape_head_zero x c).symm
  · have hzne : (1 : Int) ≠ z := Ne.symm hz
    simp [Function.update, hz, hzne]

def capacityEncodedStartConfig (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) : MStarConfig :=
  { state := .start
    head := 1
    tape := capacityInitialTape x c }

def capacityEncodedParserConfig (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) : MStarConfig :=
  { state := .parser MStarULogAssembly.data.parserStart
    head := 1
    tape := capacityInitialTape x c }

theorem capacityEncodedStart_slotOne_step (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) :
    FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable (capacityEncodedStartConfig x c)
      PakEncodedStart.startOneArrow = some (capacityEncodedParserConfig x c) := by
  simp [FiniteOneTapeSemantics.step, FiniteOneTapeProgram.transition,
    FiniteOneTapeSemantics.writtenTape, PakEncodedStart.actionOf_startOneArrow,
    capacityEncodedStartConfig, capacityEncodedParserConfig,
    capacityInitialTape_head_zero, update_capacityInitialTape,
    PakEncodedStart.parserStartAction, MStarOuterProgram.movable,
    FiniteOneTapeSemantics.moveHead]

theorem capacityInitialTape_hash_outside (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) (z : Int)
    (hz : z < 0 ∨ ((PakSideScanner.sideScannerBits x).length + 2 : Int) ≤ z) :
    capacityInitialTape x c z = Tape.hash := by
  cases z with
  | negSucc k =>
      unfold capacityInitialTape
      rw [if_neg (by omega)]
  | ofNat k =>
      cases k with
      | zero => simp [capacityInitialTape]
      | succ k =>
          have hhigh : ((PakSideScanner.sideScannerBits x).length : Int) + 2 ≤
              (k + 1 : ℕ) := hz.resolve_left
            (not_lt_of_ge (Int.natCast_nonneg (k + 1)))
          have hk : (PakSideScanner.sideScannerBits x).length + 2 ≤ k + 1 := by
            have hcast : (((PakSideScanner.sideScannerBits x).length + 2 : ℕ) : Int) ≤
                ((k + 1 : ℕ) : Int) := by simpa using hhigh
            exact Int.ofNat_le.mp hcast
          unfold capacityInitialTape
          have hkone : (1 : Int) ≤ Int.ofNat (k + 1) :=
            Int.ofNat_le.mpr (Nat.succ_le_succ (Nat.zero_le k))
          rw [if_pos hkone]
          have hsub : (Int.ofNat (k + 1) - 1).toNat = k := by simp
          rw [hsub]
          apply List.getD_eq_default
          rw [capacityInitialCells_length]
          omega

theorem capacityInitialTableauCell_eq_configCell (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) (z : Int) :
    capacityInitialTableauCell x c z =
      if z = (capacityEncodedStartConfig x c).head then
        .head (capacityEncodedStartConfig x c).state
          ((capacityEncodedStartConfig x c).tape z)
      else .plain ((capacityEncodedStartConfig x c).tape z) := by
  change capacityInitialTableauCell x c z =
    if z = 1 then
      .head (.start : FixedState) (capacityInitialTape x c z)
    else .plain (capacityInitialTape x c z)
  by_cases hz : z ≤ 0
  · have hnotOne : z ≠ 1 := by omega
    unfold capacityInitialTableauCell capacityInitialTape
    rw [if_pos hz, if_neg hnotOne, if_neg (by omega)]
  · have hzpos : 1 ≤ z := by omega
    by_cases hone : z = 1
    · subst z
      simp [capacityInitialTableauCell, capacityInitialCell,
        capacityInitialTape, capacityInitialCells_head_zero]
    · have hzsub : 0 ≤ z - 1 := by omega
      have hp0 : (z - 1).toNat ≠ 0 := by
        intro hzero
        have hcast := Int.toNat_of_nonneg hzsub
        rw [hzero] at hcast
        omega
      unfold capacityInitialTableauCell capacityInitialTape
      rw [if_neg hz, if_neg hone, if_pos hzpos]
      unfold capacityInitialCell
      rw [if_neg hp0]

def capacityStartWindowedStep (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) :
    PakMStarCouplingCorrectness.WindowedMStarStep
      ((PakSideScanner.sideScannerBits x).length + 2) where
  before := capacityEncodedStartConfig x c
  after := capacityEncodedParserConfig x c
  arrow := PakEncodedStart.startOneArrow
  executes := capacityEncodedStart_slotOne_step x c
  origin := 0
  width_ge_three := by
    have hbits := PakSideScanner.sideScannerBits_pos x
    omega
  head_index := ⟨1, by
    have hbits := PakSideScanner.sideScannerBits_pos x
    omega⟩
  head_eq := by simp [capacityEncodedStartConfig]
  head_interior_left := by
    change 0 < 1
    omega
  head_interior_right := by
    have hbits := PakSideScanner.sideScannerBits_pos x
    change 1 + 1 < (PakSideScanner.sideScannerBits x).length + 2
    omega
  before_hash_outside := by
    intro z hz
    apply capacityInitialTape_hash_outside x c z
    simpa [capacityEncodedStartConfig] using hz
  after_hash_outside := by
    intro z hz
    apply capacityInitialTape_hash_outside x c z
    simpa [capacityEncodedParserConfig] using hz

theorem capacityStartWindowedStep_cell (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) (z : Int) :
    (capacityStartWindowedStep x c).cell (capacityEncodedStartConfig x c) z =
      capacityInitialTableauCell x c z := by
  unfold PakMStarCouplingCorrectness.WindowedMStarStep.cell
  exact (capacityInitialTableauCell_eq_configCell x c z).symm

theorem capacityStartWindowedStep_oldStrip (x : ConcretePakSide.Word)
    (c : ScannerCapacity x)
    (j : Fin ((PakSideScanner.sideScannerBits x).length + 2)) :
    (capacityStartWindowedStep x c).oldStrip j = capacityInitialWindow x c j := by
  unfold PakMStarCouplingCorrectness.WindowedMStarStep.oldStrip
    PakMStarCouplingCorrectness.WindowedMStarStep.triple
    PakMStarCouplingCorrectness.WindowedMStarStep.position capacityInitialWindow
  apply CellTriple.ext
  · simpa only [capacityStartWindowedStep, zero_add] using
      capacityStartWindowedStep_cell x c ((j.1 : Int) - 1)
  · simpa only [capacityStartWindowedStep, zero_add] using
      capacityStartWindowedStep_cell x c (j.1 : Int)
  · simpa only [capacityStartWindowedStep, zero_add] using
      capacityStartWindowedStep_cell x c ((j.1 : Int) + 1)

theorem capacityScanner_emits_startOldStrip (x : ConcretePakSide.Word)
    (c : ScannerCapacity x)
    (j : Fin ((PakSideScanner.sideScannerBits x).length + 2)) :
    PakCouplingGenerated.emittedWindow MStarULogAssembly.boundaryData
        (PakScannerTerminal.terminalScannerState
          (PakSideScanner.sideScannerBits x)
          (PakSideScanner.sideScannerBits_pos x)
          (capacityTerminalIndex x c) j.1)
        (PakScannerTerminal.terminalScannerState
          (PakSideScanner.sideScannerBits x)
          (PakSideScanner.sideScannerBits_pos x)
          (capacityTerminalIndex x c) (j.1 + 1)) =
      (capacityStartWindowedStep x c).oldStrip j := by
  rw [capacityScannerColumn_emits_capacityInitialWindow,
    capacityStartWindowedStep_oldStrip]

end PakFixedPolyomino.PakGeneralCapacityInitialWindow
