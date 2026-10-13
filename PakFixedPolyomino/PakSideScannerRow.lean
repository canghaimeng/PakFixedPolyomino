import PakFixedPolyomino.PakSideScanner
import PakFixedPolyomino.PakScannerTerminalEmission

/-! Exact tape-row identification for the terminal side scanner. -/

namespace PakFixedPolyomino.PakSideScannerRow

open ConcretePakSide

abbrev FixedTape := PakEncodedStart.Fixed.Tape

def groupExtraWorkCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | groups + 1, n => 510 * n + groupExtraWorkCount groups (256 * n)

private theorem cons_three_replicates {A : Type*} (a : A)
    (p q r : ℕ) (tail : List A) :
    a :: (List.replicate p a ++
      (List.replicate q a ++ (List.replicate r a ++ tail))) =
      List.replicate (1 + p + q + r) a ++ tail := by
  rw [show 1 + p + q + r = 1 + (p + (q + r)) by omega,
    List.replicate_add, List.replicate_add, List.replicate_add]
  simp only [List.replicate_one, List.singleton_append]
  congr 1
  rw [← List.append_assoc (List.replicate q a) (List.replicate r a) tail,
    ← List.append_assoc (List.replicate p a)
      (List.replicate q a ++ List.replicate r a) tail]
  rfl

theorem eightRoundReserve_eq_replicate (n : ℕ) (tail : List FixedTape) :
    MStarCopierExecution.eightRoundReserve n tail =
      List.replicate (510 * n) (.core MStarConcreteAlphabet.work) ++ tail := by
  simp [MStarCopierExecution.eightRoundReserve, ← List.replicate_add,
    List.append_assoc]
  congr 2
  omega

theorem groupExtraReserve_eq_replicate (groups n : ℕ)
    (tail : List FixedTape) :
    MStarCopierExecution.groupExtraReserve groups n tail =
      List.replicate (groupExtraWorkCount groups n)
        (.core MStarConcreteAlphabet.work) ++ tail := by
  induction groups generalizing n with
  | zero => rfl
  | succ groups ih =>
      simp only [MStarCopierExecution.groupExtraReserve, groupExtraWorkCount]
      rw [ih, eightRoundReserve_eq_replicate]
      rw [List.replicate_add, List.append_assoc]

def copierWorkCount (m : ℕ) : ℕ :=
  1 + 510 + groupExtraWorkCount m 256 + (m + 1)

set_option maxRecDepth 100000 in
theorem copierReserve_eq_work_rightEnd (m : ℕ) :
    MStarCopierExecution.copierReserve m [] =
      List.replicate (copierWorkCount m) (.core MStarConcreteAlphabet.work) ++
        [MStarCopierMicrocode.rightEnd] := by
  unfold MStarCopierExecution.copierReserve
    MStarCopierExecution.copierRoundReserve copierWorkCount
  rw [eightRoundReserve_eq_replicate, groupExtraReserve_eq_replicate]
  change .core MStarConcreteAlphabet.work ::
      (List.replicate 510 (.core MStarConcreteAlphabet.work) ++
        (List.replicate (groupExtraWorkCount m 256)
          (.core MStarConcreteAlphabet.work) ++
          (List.replicate (m + 1) (.core MStarConcreteAlphabet.work) ++
            [MStarCopierMicrocode.rightEnd]))) =
    List.replicate (1 + 510 + groupExtraWorkCount m 256 + (m + 1))
        (.core MStarConcreteAlphabet.work) ++ [MStarCopierMicrocode.rightEnd]
  exact cons_three_replicates _ 510 (groupExtraWorkCount m 256) (m + 1) _

def parserCopierWorkCount (x : Word) : ℕ := 2 + copierWorkCount x.length

theorem parserCopierReserve_eq_work_rightEnd (x : Word) :
    MStarCopierExecution.parserCopierReserve x =
      List.replicate (parserCopierWorkCount x)
          (.core MStarConcreteAlphabet.work) ++
        [MStarCopierMicrocode.rightEnd] := by
  unfold MStarCopierExecution.parserCopierReserve parserCopierWorkCount
  rw [copierReserve_eq_work_rightEnd]
  rw [show 2 + copierWorkCount x.length =
    Nat.succ (Nat.succ (copierWorkCount x.length)) by omega]
  simp [List.replicate_succ]

@[simp] theorem parserCopierReserve_length_shape (x : Word) :
    (MStarCopierExecution.parserCopierReserve x).length =
      parserCopierWorkCount x + 1 := by
  rw [parserCopierReserve_eq_work_rightEnd]
  simp

theorem parserCopierReserve_getD_before_rightEnd (x : Word) (k : ℕ)
    (hk : k < parserCopierWorkCount x) :
    (MStarCopierExecution.parserCopierReserve x).getD k .hash =
      .core MStarConcreteAlphabet.work := by
  rw [parserCopierReserve_eq_work_rightEnd]
  rw [List.getD_append _ _ _ _ (by simpa using hk)]
  simp [hk]

theorem parserCopierReserve_getD_rightEnd (x : Word) :
    (MStarCopierExecution.parserCopierReserve x).getD
        (parserCopierWorkCount x) .hash = MStarCopierMicrocode.rightEnd := by
  rw [parserCopierReserve_eq_work_rightEnd]
  rw [List.getD_append_right]
  · simp
  · simp

theorem scannerTerminalIndex_eq (x : Word) :
    PakSideScanner.scannerTerminalIndex x =
      (PakEncodedStart.parserCells x).length + parserCopierWorkCount x := by
  unfold PakSideScanner.scannerTerminalIndex
  rw [parserCopierReserve_length_shape]
  omega

theorem parserCellsWithCopierReserve_shape (x : Word) :
    PakSideScanner.parserCellsWithCopierReserve x =
      PakEncodedStart.parserCells x ++
        List.replicate (parserCopierWorkCount x)
          (.core MStarConcreteAlphabet.work) ++
        MStarCopierMicrocode.rightEnd :: PakSideScanner.sideCopierHashTail x := by
  unfold PakSideScanner.parserCellsWithCopierReserve
  rw [parserCopierReserve_eq_work_rightEnd]
  simp [List.append_assoc]

theorem sideScannerBits_drop_eq_false_replicate (x : Word) (j : ℕ)
    (hj : (encodedWord x).length ≤ j) :
    (PakSideScanner.sideScannerBits x).drop j =
      List.replicate ((PakSideScanner.sideScannerBits x).length - j) false := by
  apply List.eq_replicate_iff.mpr
  constructor
  · simp
  · intro b hb
    rcases List.mem_iff_getElem.mp hb with ⟨i, hi, hget⟩
    have hidx : j + i < (PakSideScanner.sideScannerBits x).length := by
      simp only [List.length_drop] at hi
      omega
    have hbside : (PakSideScanner.sideScannerBits x).getD (j + i) false = b := by
      rw [List.getD_eq_getElem _ _ hidx]
      calc
        (PakSideScanner.sideScannerBits x)[j + i] =
            ((PakSideScanner.sideScannerBits x).drop j)[i] :=
          List.getElem_drop.symm
        _ = b := hget
    have hword : (encodedWord x).reverse.getD (j + i) false = false := by
      apply List.getD_eq_default
      simp only [List.length_reverse]
      omega
    calc
      b = (PakSideScanner.sideScannerBits x).getD (j + i) false := hbside.symm
      _ = (encodedWord x).reverse.getD (j + i) false :=
        PakSideScanner.sideScannerBits_getD_encodedWord x (j + i) hidx
      _ = false := hword

theorem sideSuffixMode_high (x : Word) (j : ℕ)
    (hj : (encodedWord x).length ≤ j) :
    PakScannerPath.suffixMode (PakSideScanner.sideScannerBits x) j =
      ConcretePakScanner.Mode.high := by
  unfold PakScannerPath.suffixMode
  rw [sideScannerBits_drop_eq_false_replicate x j hj]
  have hfold : ∀ n : ℕ,
      (List.replicate n false).foldr
        (fun b m => ConcretePakScanner.modeOut b m)
        .high = .high := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [List.replicate_succ, List.foldr]
        rw [ih]
        rfl
  exact hfold _

/-- The final bit belonging to the self-delimiting encoded word is its
leading sentinel, hence is true in the scanner's little-endian order. -/
theorem sideScannerBits_last_encoded_true (x : Word) :
    (PakSideScanner.sideScannerBits x).getD ((encodedWord x).length - 1) false =
      true := by
  let L := (encodedWord x).length
  have hL : 0 < L := by simp [L]
  have hsideLen : L ≤ (PakSideScanner.sideScannerBits x).length := by
    have hp := PakSideScanner.parserCells_le_sideScannerBits_length x
    rw [PakSideScanner.parserCells_length] at hp
    dsimp [L]
    rw [encodedWord_length]
    omega
  have hidx : L - 1 < (PakSideScanner.sideScannerBits x).length := by omega
  rw [PakSideScanner.sideScannerBits_getD_encodedWord x (L - 1) hidx]
  rw [List.getD_reverse (i := L - 1) (by simp [L])]
  have hz : L - 1 - (L - 1) = 0 := by omega
  rw [hz]
  simp [L, encodedWord]

theorem sideSuffixMode_binary_before_encoded_end (x : Word) (j : ℕ)
    (hj : j < (encodedWord x).length) :
    PakScannerPath.suffixMode (PakSideScanner.sideScannerBits x) j =
      ConcretePakScanner.Mode.binary := by
  apply PakScannerPath.suffixMode_binary_of_true_mem
  let L := (encodedWord x).length
  have hL : 0 < L := by simp [L, encodedWord]
  have hsideLen : L ≤ (PakSideScanner.sideScannerBits x).length := by
    have hp := PakSideScanner.parserCells_le_sideScannerBits_length x
    rw [PakSideScanner.parserCells_length] at hp
    dsimp [L]
    rw [encodedWord_length]
    omega
  have hlastSide : (PakSideScanner.sideScannerBits x).getD (L - 1) false =
      true := by simpa [L] using sideScannerBits_last_encoded_true x
  apply List.mem_iff_getElem.mpr
  let i := L - 1 - j
  have hi : i < ((PakSideScanner.sideScannerBits x).drop j).length := by
    simp only [List.length_drop]
    dsimp [i]
    omega
  refine ⟨i, hi, ?_⟩
  have hsum : j + i = L - 1 := by
    dsimp [i]
    omega
  have hidx : j + i < (PakSideScanner.sideScannerBits x).length := by omega
  have hgetD : (PakSideScanner.sideScannerBits x).getD (j + i) false = true := by
    simpa only [hsum] using hlastSide
  calc
    ((PakSideScanner.sideScannerBits x).drop j)[i] =
        (PakSideScanner.sideScannerBits x)[j + i] := List.getElem_drop
    _ = (PakSideScanner.sideScannerBits x).getD (j + i) false :=
      (List.getD_eq_getElem _ _ hidx).symm
    _ = true := hgetD

/-- Inside the encoded word, every non-head scanner output is the literal
zero/one buffer cell for that bit.  The final sentinel is handled separately
because the suffix above it has already returned to high mode. -/
theorem sideDataCell_encoded (x : Word) (p : ℕ)
    (hp0 : 0 < p) (hp : p < (encodedWord x).length) :
    PakScannerPath.dataCell (PakSideScanner.sideScannerBits x) p =
      if (PakSideScanner.sideScannerBits x).getD p false then
        ConcretePakScanner.Buffer.one else ConcretePakScanner.Buffer.zero := by
  cases p with
  | zero => omega
  | succ k =>
      by_cases hlast : k + 1 = (encodedWord x).length - 1
      · have hbit : (PakSideScanner.sideScannerBits x).getD (k + 1) false =
            true := by
          simpa only [hlast] using sideScannerBits_last_encoded_true x
        have hmode := PakScannerPath.suffixMode_ne_tail
          (PakSideScanner.sideScannerBits x) (k + 2)
        unfold PakScannerPath.dataCell
        rw [hbit]
        cases hm : PakScannerPath.suffixMode
            (PakSideScanner.sideScannerBits x) (k + 2) <;>
          simp_all [ConcretePakScanner.newMid]
      · have hnext : k + 2 < (encodedWord x).length := by omega
        have hmode := sideSuffixMode_binary_before_encoded_end x (k + 2) hnext
        unfold PakScannerPath.dataCell
        change ConcretePakScanner.newMid
            ((PakSideScanner.sideScannerBits x).getD (k + 1) false)
            (PakScannerPath.suffixMode
              (PakSideScanner.sideScannerBits x) (k + 2)) = _
        rw [hmode]
        cases (PakSideScanner.sideScannerBits x).getD (k + 1) false <;> rfl

/-- All scanner positions after the encoded word but before the explicit
copier endpoint emit literal work cells. -/
theorem sideDataCell_work (x : Word) (p : ℕ)
    (hp : (encodedWord x).length ≤ p)
    (hbound : p < (PakSideScanner.sideScannerBits x).length) :
    PakScannerPath.dataCell (PakSideScanner.sideScannerBits x) p =
      ConcretePakScanner.Buffer.work := by
  cases p with
  | zero => simp [encodedWord] at hp
  | succ k =>
      have hbit : (PakSideScanner.sideScannerBits x).getD (k + 1) false =
          false := by
        rw [PakSideScanner.sideScannerBits_getD_encodedWord x (k + 1) hbound]
        apply List.getD_eq_default
        simp only [List.length_reverse]
        omega
      have hmode := sideSuffixMode_high x (k + 2) (by omega)
      unfold PakScannerPath.dataCell
      change ConcretePakScanner.newMid
          ((PakSideScanner.sideScannerBits x).getD (k + 1) false)
          (PakScannerPath.suffixMode
            (PakSideScanner.sideScannerBits x) (k + 2)) = _
      rw [hbit, hmode]
      rfl

theorem sideScannerBits_zero_false (x : Word) :
    (PakSideScanner.sideScannerBits x).getD 0 false = false := by
  have hbound := PakSideScanner.sideScannerBits_pos x
  rw [PakSideScanner.sideScannerBits_getD_encodedWord x 0 hbound]
  rw [List.getD_reverse (i := 0) (by simp [encodedWord])]
  simp only [Nat.sub_zero]
  rcases encodedWord_has_long_zero_suffix x with ⟨pre, henc⟩
  have hpad : 0 < paddingLength x.length := by simp [paddingLength]
  rw [henc]
  have hprele : pre.length ≤
      (pre ++ List.replicate (paddingLength x.length) false).length - 1 := by
    simp only [List.length_append, List.length_replicate]
    omega
  rw [List.getD_append_right _ _ _ _ hprele]
  apply List.getD_replicate
  simp only [List.length_append, List.length_replicate]
  omega

theorem sideDataCell_zero (x : Word) :
    PakScannerPath.dataCell (PakSideScanner.sideScannerBits x) 0 =
      ConcretePakScanner.Buffer.headZero := by
  unfold PakScannerPath.dataCell
  change ConcretePakScanner.headBuffer
    ((PakSideScanner.sideScannerBits x).getD 0 false) = _
  rw [sideScannerBits_zero_false]
  rfl

/-- On every encoded-word position, the parser tape reads the same bit as the
terminal scanner. -/
theorem parserCells_getD_encoded (x : Word) (p : ℕ)
    (hp : p < (encodedWord x).length) :
    (PakEncodedStart.parserCells x).getD p .hash =
      MStarParserExecution.bitCell MStarConcreteAlphabet.zero
        MStarConcreteAlphabet.one
        ((PakSideScanner.sideScannerBits x).getD p false) := by
  have hrev : p < (encodedWord x).reverse.length := by simpa using hp
  unfold PakEncodedStart.parserCells MStarParserExecution.inputCells
  rw [List.getD_eq_getElem _ _ (by
    simpa only [List.length_append, List.length_map, List.length_reverse,
      List.length_singleton] using Nat.lt_succ_of_lt hp)]
  rw [List.getElem_append_left (by simpa using hrev)]
  rw [List.getElem_map]
  have hside := PakSideScanner.sideScannerBits_getD_encodedWord x p
    (by
      have hle := PakSideScanner.parserCells_le_sideScannerBits_length x
      have hencParser : (encodedWord x).length ≤
          (PakEncodedStart.parserCells x).length := by
        rw [PakSideScanner.parserCells_length, encodedWord_length]
        omega
      exact Nat.lt_of_lt_of_le hp (hencParser.trans hle))
  rw [hside, List.getD_eq_getElem _ _ hrev]

theorem parserCells_getD_encoded_end (x : Word) :
    (PakEncodedStart.parserCells x).getD (encodedWord x).length .hash =
      .core MStarConcreteAlphabet.work := by
  unfold PakEncodedStart.parserCells MStarParserExecution.inputCells
  rw [List.getD_append_right]
  · simp
  · simp

theorem parserCellsWithCopierReserve_getD_prefix (x : Word) (p : ℕ)
    (hp : p < (PakEncodedStart.parserCells x).length) :
    (PakSideScanner.parserCellsWithCopierReserve x).getD p .hash =
      (PakEncodedStart.parserCells x).getD p .hash := by
  unfold PakSideScanner.parserCellsWithCopierReserve
  simpa only [List.append_assoc] using
    (List.getD_append (PakEncodedStart.parserCells x)
      (MStarCopierExecution.parserCopierReserve x ++
        PakSideScanner.sideCopierHashTail x) .hash p hp)

/-- From the parser's final work lookahead through the copier slack, every
cell strictly before the explicit endpoint is literal work. -/
theorem parserCellsWithCopierReserve_getD_work (x : Word) (p : ℕ)
    (hlow : (encodedWord x).length ≤ p)
    (hhigh : p < PakSideScanner.scannerTerminalIndex x) :
    (PakSideScanner.parserCellsWithCopierReserve x).getD p .hash =
      .core MStarConcreteAlphabet.work := by
  by_cases hp : p < (PakEncodedStart.parserCells x).length
  · rw [parserCellsWithCopierReserve_getD_prefix x p hp]
    have hlen : (PakEncodedStart.parserCells x).length =
        (encodedWord x).length + 1 := by
      rw [PakSideScanner.parserCells_length, encodedWord_length]
    have heq : p = (encodedWord x).length := by omega
    rw [heq]
    exact parserCells_getD_encoded_end x
  · rw [parserCellsWithCopierReserve_shape]
    rw [List.append_assoc]
    rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hp)]
    rw [List.getD_append]
    · apply List.getD_replicate
      unfold PakSideScanner.scannerTerminalIndex at hhigh
      rw [parserCopierReserve_length_shape] at hhigh
      omega
    · unfold PakSideScanner.scannerTerminalIndex at hhigh
      rw [parserCopierReserve_length_shape] at hhigh
      simp only [List.length_replicate]
      omega

theorem parserCellsWithCopierReserve_getD_rightEnd (x : Word) :
    (PakSideScanner.parserCellsWithCopierReserve x).getD
        (PakSideScanner.scannerTerminalIndex x) .hash =
      MStarCopierMicrocode.rightEnd := by
  rw [parserCellsWithCopierReserve_shape, scannerTerminalIndex_eq]
  rw [List.append_assoc]
  rw [List.getD_append_right]
  · rw [List.getD_append_right]
    · simp
    · simp
  · omega

theorem parserCellsWithCopierReserve_getD_after_rightEnd (x : Word) (p : ℕ)
    (hlow : PakSideScanner.scannerTerminalIndex x < p)
    (hhigh : p < (PakSideScanner.sideScannerBits x).length) :
    (PakSideScanner.parserCellsWithCopierReserve x).getD p .hash = .hash := by
  rw [parserCellsWithCopierReserve_shape]
  have hterminal := scannerTerminalIndex_eq x
  have hleft :
      (PakEncodedStart.parserCells x ++
        List.replicate (parserCopierWorkCount x)
          (MStarOuterProgram.Tape.core MStarConcreteAlphabet.work :
            FixedTape)).length ≤ p := by
    simp only [List.length_append, List.length_replicate]
    omega
  rw [List.getD_append_right _ _ _ _ hleft]
  have hpos : 0 < p -
      (PakEncodedStart.parserCells x ++
        List.replicate (parserCopierWorkCount x)
          (MStarOuterProgram.Tape.core MStarConcreteAlphabet.work :
            FixedTape)).length := by
    simp only [List.length_append, List.length_replicate]
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  rw [hk, List.getD_cons_succ]
  simp [PakSideScanner.sideCopierHashTail]

theorem parserCellsWithCopierReserve_getD_zero (x : Word) :
    (PakSideScanner.parserCellsWithCopierReserve x).getD 0 .hash =
      .core MStarConcreteAlphabet.zero := by
  rw [parserCellsWithCopierReserve_getD_prefix]
  · rw [parserCells_getD_encoded]
    · rw [sideScannerBits_zero_false]
      rfl
    · simp [encodedWord]
  · rw [PakSideScanner.parserCells_length]
    omega

def sideInitialCell (x : Word) (p : ℕ) :
    TableauCell PakEncodedStart.Fixed.State FixedTape :=
  if p = 0 then
    .head (.start : PakEncodedStart.Fixed.State)
      ((PakSideScanner.parserCellsWithCopierReserve x).getD p .hash)
  else
    .plain ((PakSideScanner.parserCellsWithCopierReserve x).getD p .hash)

/-- The finite terminal scanner emits exactly the marked parser/copier input
row, including the work slack, explicit `rightEnd`, and hash tail. -/
theorem terminalDataCell_eq_sideInitialCell (x : Word) (p : ℕ)
    (hp : p < (PakSideScanner.sideScannerBits x).length) :
    PakCouplingGenerated.bufferCell MStarULogAssembly.boundaryData
        (PakScannerTerminal.terminalDataCell
          (PakSideScanner.sideScannerBits x)
          (PakSideScanner.scannerTerminalIndex x) p) =
      sideInitialCell x p := by
  have hencTerm : (encodedWord x).length <
      PakSideScanner.scannerTerminalIndex x := by
    rw [scannerTerminalIndex_eq, PakSideScanner.parserCells_length,
      encodedWord_length]
    omega
  by_cases hp0 : p = 0
  · subst p
    rw [PakScannerTerminal.terminalDataCell_lt _ _ _
      (PakSideScanner.scannerTerminalIndex_pos x)]
    rw [sideDataCell_zero]
    unfold sideInitialCell
    rw [if_pos rfl, parserCellsWithCopierReserve_getD_zero]
    simp [sideInitialCell, PakCouplingGenerated.bufferCell,
      MStarULogAssembly.boundaryData, MStarOuterProgram.boundaryData,
      MStarULogAssembly.data, MStarCopierMicrocode.attach]
  · by_cases henc : p < (encodedWord x).length
    · rw [PakScannerTerminal.terminalDataCell_lt _ _ _
        (henc.trans hencTerm)]
      rw [sideDataCell_encoded x p (Nat.pos_of_ne_zero hp0) henc]
      unfold sideInitialCell
      rw [if_neg hp0]
      rw [parserCellsWithCopierReserve_getD_prefix]
      · rw [parserCells_getD_encoded x p henc]
        cases hb : (PakSideScanner.sideScannerBits x).getD p false <;>
          simp [hb, MStarParserExecution.bitCell,
            PakCouplingGenerated.bufferCell, MStarULogAssembly.boundaryData,
            MStarOuterProgram.boundaryData, MStarULogAssembly.data,
            MStarCopierMicrocode.attach]
      · have hsucc := Nat.lt_succ_of_lt henc
        simpa only [PakSideScanner.parserCells_length, encodedWord_length,
          show 74 * x.length + 75 + 1 = 74 * x.length + 76 by omega]
          using hsucc
    · have hlow : (encodedWord x).length ≤ p := Nat.le_of_not_gt henc
      by_cases hbefore : p < PakSideScanner.scannerTerminalIndex x
      · rw [PakScannerTerminal.terminalDataCell_lt _ _ _ hbefore]
        rw [sideDataCell_work x p hlow hp]
        unfold sideInitialCell
        rw [if_neg hp0, parserCellsWithCopierReserve_getD_work x p hlow hbefore]
        simp [PakCouplingGenerated.bufferCell, MStarULogAssembly.boundaryData,
          MStarOuterProgram.boundaryData, MStarULogAssembly.data,
          MStarCopierMicrocode.attach]
      · by_cases heq : p = PakSideScanner.scannerTerminalIndex x
        · subst p
          rw [PakScannerTerminal.terminalDataCell_eq]
          unfold sideInitialCell
          rw [if_neg (Nat.ne_of_gt (PakSideScanner.scannerTerminalIndex_pos x))]
          rw [parserCellsWithCopierReserve_getD_rightEnd]
          simp [PakCouplingGenerated.bufferCell, MStarULogAssembly.boundaryData,
            MStarOuterProgram.boundaryData, MStarCopierMicrocode.rightEnd,
            MStarULogAssembly.data, MStarCopierMicrocode.attach]
        · have hafter : PakSideScanner.scannerTerminalIndex x < p := by omega
          rw [PakScannerTerminal.terminalDataCell_gt _ _ _ hafter]
          unfold sideInitialCell
          rw [if_neg hp0,
            parserCellsWithCopierReserve_getD_after_rightEnd x p hafter hp]
          simp [PakCouplingGenerated.bufferCell, MStarULogAssembly.boundaryData,
            MStarOuterProgram.boundaryData, MStarULogAssembly.data,
            MStarCopierMicrocode.attach]

def sideInitialTableauCell (x : Word) (z : Int) :
    TableauCell PakEncodedStart.Fixed.State FixedTape :=
  if z ≤ 0 then .plain .hash
  else sideInitialCell x (Int.toNat (z - 1))

theorem terminalScannerTapeCell_eq_sideInitialTableauCell (x : Word) (z : Int) :
    PakScannerTerminal.terminalScannerTapeCell MStarULogAssembly.boundaryData
        (PakSideScanner.sideScannerBits x)
        (PakSideScanner.scannerTerminalIndex x) z =
      sideInitialTableauCell x z := by
  unfold PakScannerTerminal.terminalScannerTapeCell sideInitialTableauCell
  by_cases hz : z ≤ 0
  · simp [hz, MStarULogAssembly.boundaryData,
      MStarOuterProgram.boundaryData]
  · rw [if_neg hz, if_neg hz]
    by_cases hp : Int.toNat (z - 1) <
        (PakSideScanner.sideScannerBits x).length
    · rw [if_pos hp]
      exact terminalDataCell_eq_sideInitialCell x _ hp
    · rw [if_neg hp]
      have hbits := PakSideScanner.sideScannerBits_pos x
      have hp0 : Int.toNat (z - 1) ≠ 0 := by omega
      unfold sideInitialCell
      rw [if_neg hp0]
      have hget : (PakSideScanner.parserCellsWithCopierReserve x).getD
          (Int.toNat (z - 1)) .hash = .hash := by
        apply List.getD_eq_default
        rw [PakSideScanner.parserCellsWithCopierReserve_length]
        exact Nat.le_of_not_gt hp
      rw [hget]
      simp [MStarULogAssembly.boundaryData, MStarOuterProgram.boundaryData]

def sideInitialWindow (x : Word)
    (j : Fin ((PakSideScanner.sideScannerBits x).length + 2)) :
    CellTriple (TableauCell PakEncodedStart.Fixed.State FixedTape) :=
  { minus := sideInitialTableauCell x ((j.1 : Int) - 1)
    center := sideInitialTableauCell x j.1
    plus := sideInitialTableauCell x ((j.1 : Int) + 1) }

theorem terminalScannerTapeWindow_eq_sideInitialWindow (x : Word)
    (j : Fin ((PakSideScanner.sideScannerBits x).length + 2)) :
    PakScannerTerminal.terminalScannerTapeWindow
        MStarULogAssembly.boundaryData (PakSideScanner.sideScannerBits x)
        (PakSideScanner.scannerTerminalIndex x) j =
      sideInitialWindow x j := by
  unfold PakScannerTerminal.terminalScannerTapeWindow sideInitialWindow
  apply CellTriple.ext
  · change PakScannerTerminal.terminalScannerTapeCell
        MStarULogAssembly.boundaryData (PakSideScanner.sideScannerBits x)
        (PakSideScanner.scannerTerminalIndex x) ((j.1 : Int) - 1) = _
    exact terminalScannerTapeCell_eq_sideInitialTableauCell x _
  · change PakScannerTerminal.terminalScannerTapeCell
        MStarULogAssembly.boundaryData (PakSideScanner.sideScannerBits x)
        (PakSideScanner.scannerTerminalIndex x) (j.1 : Int) = _
    exact terminalScannerTapeCell_eq_sideInitialTableauCell x _
  · change PakScannerTerminal.terminalScannerTapeCell
        MStarULogAssembly.boundaryData (PakSideScanner.sideScannerBits x)
        (PakSideScanner.scannerTerminalIndex x) ((j.1 : Int) + 1) = _
    exact terminalScannerTapeCell_eq_sideInitialTableauCell x _

/-- Cellwise coupling endpoint: every edge of the general terminal scanner
emits the radius-one window of the actual parser/copier start row. -/
theorem terminalScannerColumn_emits_sideInitialWindow (x : Word)
    (j : Fin ((PakSideScanner.sideScannerBits x).length + 2)) :
    PakCouplingGenerated.emittedWindow MStarULogAssembly.boundaryData
        (PakScannerTerminal.terminalScannerState
          (PakSideScanner.sideScannerBits x)
          (PakSideScanner.sideScannerBits_pos x)
          (PakSideScanner.scannerTerminalIndex x) j.1)
        (PakScannerTerminal.terminalScannerState
          (PakSideScanner.sideScannerBits x)
          (PakSideScanner.sideScannerBits_pos x)
          (PakSideScanner.scannerTerminalIndex x) (j.1 + 1)) =
      sideInitialWindow x j := by
  rw [PakScannerTerminalEmission.terminalScannerColumn_emits_terminalTapeWindow
    MStarULogAssembly.boundaryData (PakSideScanner.sideScannerBits x)
    (PakSideScanner.sideScannerBits_pos x)
    (PakSideScanner.scannerTerminalIndex x)
    (PakSideScanner.scannerTerminalIndex_pos x)
    (PakSideScanner.scannerTerminalIndex_lt x) j]
  exact terminalScannerTapeWindow_eq_sideInitialWindow x j

/-- The actual infinite tape underlying the finite scanner row. -/
def sideInputTape (x : Word) (z : Int) : FixedTape :=
  if 1 ≤ z then
    (PakSideScanner.parserCellsWithCopierReserve x).getD
      (Int.toNat (z - 1)) .hash
  else .hash

theorem sideInputTape_one (x : Word) :
    sideInputTape x 1 = .core MStarConcreteAlphabet.zero := by
  unfold sideInputTape
  rw [if_pos (by omega)]
  change (PakSideScanner.parserCellsWithCopierReserve x).getD 0 .hash = _
  exact parserCellsWithCopierReserve_getD_zero x

theorem update_sideInputTape (x : Word) :
    Function.update (sideInputTape x) 1 (.core MStarConcreteAlphabet.zero) =
      sideInputTape x := by
  funext z
  by_cases hz : z = 1
  · subst z
    simpa [Function.update] using (sideInputTape_one x).symm
  · have hzne : (1 : Int) ≠ z := Ne.symm hz
    simp [Function.update, hz, hzne]

def sideEncodedStartConfig (x : Word) : PakEncodedStart.MStarConfig :=
  { state := .start
    head := 1
    tape := sideInputTape x }

def sideEncodedParserConfig (x : Word) : PakEncodedStart.MStarConfig :=
  { state := .parser MStarULogAssembly.data.parserStart
    head := 1
    tape := sideInputTape x }

theorem sideEncodedStart_slotOne_step (x : Word) :
    FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable (sideEncodedStartConfig x)
      PakEncodedStart.startOneArrow = some (sideEncodedParserConfig x) := by
  simp [FiniteOneTapeSemantics.step, FiniteOneTapeProgram.transition,
    FiniteOneTapeSemantics.writtenTape, PakEncodedStart.actionOf_startOneArrow,
    sideEncodedStartConfig, sideEncodedParserConfig, sideInputTape_one,
    update_sideInputTape, PakEncodedStart.parserStartAction,
    MStarOuterProgram.movable, FiniteOneTapeSemantics.moveHead]

theorem sideInputTape_hash_outside (x : Word) (z : Int)
    (hz : z < 0 ∨
      ((PakSideScanner.sideScannerBits x).length + 2 : Int) ≤ z) :
    sideInputTape x z = .hash := by
  cases z with
  | negSucc k =>
      unfold sideInputTape
      rw [if_neg (by omega)]
  | ofNat k =>
      cases k with
      | zero => simp [sideInputTape]
      | succ k =>
          have hhigh : ((PakSideScanner.sideScannerBits x).length : Int) + 2 ≤
              (k + 1 : ℕ) := hz.resolve_left
                (not_lt_of_ge (Int.natCast_nonneg (k + 1)))
          have hk : (PakSideScanner.sideScannerBits x).length + 2 ≤ k + 1 := by
            have hcast : (((PakSideScanner.sideScannerBits x).length + 2 : ℕ) : Int) ≤
                ((k + 1 : ℕ) : Int) := by simpa using hhigh
            exact Int.ofNat_le.mp hcast
          unfold sideInputTape
          have hkone : (1 : Int) ≤ Int.ofNat (k + 1) :=
            Int.ofNat_le.mpr (Nat.succ_le_succ (Nat.zero_le k))
          rw [if_pos hkone]
          have hsub : (Int.ofNat (k + 1) - 1).toNat = k := by simp
          rw [hsub]
          apply List.getD_eq_default
          rw [PakSideScanner.parserCellsWithCopierReserve_length]
          omega

theorem sideInitialTableauCell_eq_configCell (x : Word) (z : Int) :
    sideInitialTableauCell x z =
      if z = (sideEncodedStartConfig x).head then
        .head (sideEncodedStartConfig x).state
          ((sideEncodedStartConfig x).tape z)
      else .plain ((sideEncodedStartConfig x).tape z) := by
  change sideInitialTableauCell x z =
    if z = 1 then
      .head (.start : PakEncodedStart.Fixed.State) (sideInputTape x z)
    else .plain (sideInputTape x z)
  by_cases hz : z ≤ 0
  · have hnotOne : z ≠ 1 := by omega
    unfold sideInitialTableauCell sideInputTape
    rw [if_pos hz, if_neg hnotOne, if_neg (by omega)]
  · have hzpos : 1 ≤ z := by omega
    by_cases hone : z = 1
    · subst z
      simp [sideInitialTableauCell, sideInitialCell, sideEncodedStartConfig,
        sideInputTape]
    · have hzsub : 0 ≤ z - 1 := by omega
      have hp0 : (z - 1).toNat ≠ 0 := by
        intro hzero
        have hcast := Int.toNat_of_nonneg hzsub
        rw [hzero] at hcast
        omega
      unfold sideInitialTableauCell sideInputTape
      rw [if_neg hz, if_neg hone, if_pos hzpos]
      unfold sideInitialCell
      rw [if_neg hp0]

def sideStartWindowedStep (x : Word) :
    PakMStarCouplingCorrectness.WindowedMStarStep
      ((PakSideScanner.sideScannerBits x).length + 2) where
  before := sideEncodedStartConfig x
  after := sideEncodedParserConfig x
  arrow := PakEncodedStart.startOneArrow
  executes := sideEncodedStart_slotOne_step x
  origin := 0
  width_ge_three := by
    have hbits := PakSideScanner.sideScannerBits_pos x
    omega
  head_index := ⟨1, by
    have hbits := PakSideScanner.sideScannerBits_pos x
    omega⟩
  head_eq := by simp [sideEncodedStartConfig]
  head_interior_left := by
    change 0 < 1
    omega
  head_interior_right := by
    have hbits := PakSideScanner.sideScannerBits_pos x
    change 1 + 1 < (PakSideScanner.sideScannerBits x).length + 2
    omega
  before_hash_outside := by
    intro z hz
    apply sideInputTape_hash_outside x z
    simpa [sideEncodedStartConfig] using hz
  after_hash_outside := by
    intro z hz
    apply sideInputTape_hash_outside x z
    simpa [sideEncodedParserConfig] using hz

theorem sideStartWindowedStep_cell (x : Word) (z : Int) :
    (sideStartWindowedStep x).cell (sideEncodedStartConfig x) z =
      sideInitialTableauCell x z := by
  unfold PakMStarCouplingCorrectness.WindowedMStarStep.cell
  exact (sideInitialTableauCell_eq_configCell x z).symm

theorem sideStartWindowedStep_oldStrip (x : Word)
    (j : Fin ((PakSideScanner.sideScannerBits x).length + 2)) :
    (sideStartWindowedStep x).oldStrip j = sideInitialWindow x j := by
  unfold PakMStarCouplingCorrectness.WindowedMStarStep.oldStrip
    PakMStarCouplingCorrectness.WindowedMStarStep.triple
    PakMStarCouplingCorrectness.WindowedMStarStep.position sideInitialWindow
  apply CellTriple.ext
  · simpa only [sideStartWindowedStep, zero_add] using
      sideStartWindowedStep_cell x ((j.1 : Int) - 1)
  · simpa only [sideStartWindowedStep, zero_add] using
      sideStartWindowedStep_cell x (j.1 : Int)
  · simpa only [sideStartWindowedStep, zero_add] using
      sideStartWindowedStep_cell x ((j.1 : Int) + 1)

theorem sideScanner_emits_startOldStrip (x : Word)
    (j : Fin ((PakSideScanner.sideScannerBits x).length + 2)) :
    PakCouplingGenerated.emittedWindow MStarULogAssembly.boundaryData
        (PakScannerTerminal.terminalScannerState
          (PakSideScanner.sideScannerBits x)
          (PakSideScanner.sideScannerBits_pos x)
          (PakSideScanner.scannerTerminalIndex x) j.1)
        (PakScannerTerminal.terminalScannerState
          (PakSideScanner.sideScannerBits x)
          (PakSideScanner.sideScannerBits_pos x)
          (PakSideScanner.scannerTerminalIndex x) (j.1 + 1)) =
      (sideStartWindowedStep x).oldStrip j := by
  rw [terminalScannerColumn_emits_sideInitialWindow,
    sideStartWindowedStep_oldStrip]

end PakFixedPolyomino.PakSideScannerRow
