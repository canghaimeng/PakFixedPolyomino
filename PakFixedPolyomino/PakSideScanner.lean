import PakFixedPolyomino.PakScannerPath
import PakFixedPolyomino.PakScannerTerminal
import PakFixedPolyomino.MStarCopierExecution
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# The scanner column at the encoded side value

The generic scanner path is specialized here to the first `n - 2` binary
digits of `n = sideValue x`.  The remaining two ripple bits are the accepted
omitted high zero bits used by the pre-top and cap edges.
-/

namespace PakFixedPolyomino.PakSideScanner

open ConcretePakSide

theorem littleDigits_shape (x : Word) :
    littleDigits x =
      List.replicate (paddingLength x.length) 0 ++
        (1 :: (List.replicate x.length 0 ++
          (1 :: (x.reverse.map Bool.toNat ++ [1])))) := by
  simp [littleDigits, encodedWord, List.reverse_append, List.map_append,
    List.map_reverse, List.append_assoc]

theorem littleDigits_padding_one (x : Word) :
    (littleDigits x).getD (paddingLength x.length) 0 = 1 := by
  rw [littleDigits_shape]
  rw [List.getD_append_right
    (List.replicate (paddingLength x.length) 0) _ 0
    (paddingLength x.length) (by simp)]
  simp

theorem sideValue_padding_testBit (x : Word) :
    (sideValue x).testBit (paddingLength x.length) = true := by
  rw [PakSideRipple.sideValue_testBit]
  unfold PakSideRipple.sideDigit
  rw [littleDigits_padding_one]
  rfl

theorem sideValue_ge_five (x : Word) : 5 ≤ sideValue x := by
  have hbit := Nat.ge_two_pow_of_testBit (sideValue_padding_testBit x)
  calc
    5 ≤ 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (paddingLength x.length) :=
      Nat.pow_le_pow_right (by decide) (by simp [paddingLength])
    _ ≤ sideValue x := hbit

theorem sideValue_pos (x : Word) : 0 < sideValue x := by
  have h := sideValue_ge_five x
  omega

private theorem parser_length_le_two_pow (m : ℕ) :
    74 * m + 78 ≤ 2 ^ (m + 7) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      calc
        74 * (m + 1) + 78 ≤ 2 * (74 * m + 78) := by omega
        _ ≤ 2 * 2 ^ (m + 7) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ ((m + 1) + 7) := by
          rw [show (m + 1) + 7 = (m + 7) + 1 by omega, pow_succ]
          ring

theorem parserCells_length (x : Word) :
    (PakEncodedStart.parserCells x).length = 74 * x.length + 76 := by
  unfold PakEncodedStart.parserCells
  simp [MStarParserExecution.inputCells, encodedWord_length]

/-- The low `n - 2` ripple bits, listed in the scanner's bottom-to-top
order.  Above the significant encoded word these are exactly the work-emitting
high zeros. -/
def sideScannerBits (x : Word) : List Bool :=
  List.ofFn fun j : Fin (sideValue x - 2) => (sideValue x).testBit j

theorem sideScannerBits_length (x : Word) :
    (sideScannerBits x).length = sideValue x - 2 := by
  simp [sideScannerBits]

theorem sideScannerBits_pos (x : Word) :
    0 < (sideScannerBits x).length := by
  rw [sideScannerBits_length]
  have h := sideValue_ge_five x
  omega

/-- The encoded side leaves at least two cells more than the parser input;
the remaining cells are precisely the high-zero work reserve emitted by the
scanner. -/
theorem parserCells_le_sideScannerBits_length (x : Word) :
    (PakEncodedStart.parserCells x).length ≤ (sideScannerBits x).length := by
  rw [parserCells_length, sideScannerBits_length]
  have hpow := Nat.ge_two_pow_of_testBit (sideValue_padding_testBit x)
  have hsmall : 74 * x.length + 78 ≤
      2 ^ (paddingLength x.length) := by
    calc
      74 * x.length + 78 ≤ 2 ^ (x.length + 7) :=
        parser_length_le_two_pow x.length
      _ ≤ 2 ^ (paddingLength x.length) :=
        Nat.pow_le_pow_right (by decide) (by
          simp [paddingLength]
          omega)
  have hside : 74 * x.length + 78 ≤ sideValue x := hsmall.trans hpow
  omega

private theorem length_eightRoundReserve (n : ℕ)
    (tail : List PakEncodedStart.Fixed.Tape) :
    (MStarCopierExecution.eightRoundReserve n tail).length =
      510 * n + tail.length := by
  simp [MStarCopierExecution.eightRoundReserve]
  omega

private theorem length_groupExtraReserve (groups n : ℕ)
    (tail : List PakEncodedStart.Fixed.Tape) :
    (MStarCopierExecution.groupExtraReserve groups n tail).length =
      tail.length + 510 * n *
        (if groups = 0 then 0 else (256 ^ groups - 1) / 255) := by
  induction groups generalizing n with
  | zero => simp [MStarCopierExecution.groupExtraReserve]
  | succ groups ih =>
      rw [MStarCopierExecution.groupExtraReserve,
        length_eightRoundReserve, ih]
      by_cases hgroups : groups = 0
      · subst groups
        norm_num
        omega
      · have hpow : 256 ^ (groups + 1) = 256 ^ groups * 256 := by
          rw [pow_succ]
        simp only [Nat.succ_ne_zero, ↓reduceIte, hgroups, hpow]
        have hdiv : (256 ^ groups * 256 - 1) / 255 =
            256 ^ groups + (256 ^ groups - 1) / 255 := by
          omega
        have hdvd : 255 ∣ 256 ^ groups - 1 := by
          simpa using Nat.sub_dvd_pow_sub_pow 256 1 groups
        have hmul : ((256 ^ groups - 1) / 255) * 255 =
            256 ^ groups - 1 := Nat.div_mul_cancel hdvd
        have hgeom : 1 + 256 * ((256 ^ groups - 1) / 255) =
            256 ^ groups + (256 ^ groups - 1) / 255 := by
          calc
            1 + 256 * ((256 ^ groups - 1) / 255) =
                (1 + ((256 ^ groups - 1) / 255) * 255) +
                  ((256 ^ groups - 1) / 255) := by ring
            _ = 256 ^ groups + (256 ^ groups - 1) / 255 := by
              rw [hmul]
              have hp : 0 < 256 ^ groups := pow_pos (by decide) _
              omega
        calc
          510 * n +
                (tail.length + 510 * (256 * n) *
                  ((256 ^ groups - 1) / 255)) =
              tail.length + 510 * n *
                (1 + 256 * ((256 ^ groups - 1) / 255)) := by ring
          _ = tail.length + 510 * n *
                (256 ^ groups + (256 ^ groups - 1) / 255) := by rw [hgeom]
          _ = tail.length + 510 * n *
                ((256 ^ (groups + 1) - 1) / 255) := by rw [hpow, hdiv]

private theorem length_parserCopierReserve (x : Word) :
    (MStarCopierExecution.parserCopierReserve x).length =
      x.length + 515 +
        510 * 256 * ((256 ^ x.length - 1) / 255) := by
  unfold MStarCopierExecution.parserCopierReserve
    MStarCopierExecution.copierReserve
    MStarCopierExecution.copierRoundReserve
  simp [length_eightRoundReserve, length_groupExtraReserve]
  by_cases hx : x = []
  · subst x
    norm_num
  · simp [hx]
    ring

private theorem linear_reserve_bound (m : ℕ) :
    m + 515 ≤ 2 ^ (m + 10) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      calc
        m + 1 + 515 ≤ 2 * (m + 515) := by omega
        _ ≤ 2 * 2 ^ (m + 10) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (m + 1 + 10) := by
          rw [show m + 1 + 10 = (m + 10) + 1 by omega, pow_succ]
          ring

private theorem parserCopierReserve_length_bound (x : Word) :
    (MStarCopierExecution.parserCopierReserve x).length ≤
      2 ^ (8 * x.length + 19) := by
  rw [length_parserCopierReserve]
  have hdiv : (256 ^ x.length - 1) / 255 ≤ 256 ^ x.length :=
    (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hterm :
      510 * 256 * ((256 ^ x.length - 1) / 255) ≤
        2 ^ (8 * x.length + 18) := by
    calc
      510 * 256 * ((256 ^ x.length - 1) / 255) ≤
          510 * 256 * 256 ^ x.length :=
        Nat.mul_le_mul_left _ hdiv
      _ ≤ 2 ^ 18 * 256 ^ x.length := by norm_num
      _ = 2 ^ (8 * x.length + 18) := by
        rw [show 256 = 2 ^ 8 by norm_num, ← pow_mul]
        rw [← pow_add]
        congr 1
        omega
  have hlin0 := linear_reserve_bound x.length
  have hlin : x.length + 515 ≤ 2 ^ (8 * x.length + 18) := by
    exact hlin0.trans (Nat.pow_le_pow_right (by decide) (by omega))
  calc
    x.length + 515 +
        510 * 256 * ((256 ^ x.length - 1) / 255) ≤
        2 ^ (8 * x.length + 18) + 2 ^ (8 * x.length + 18) :=
      Nat.add_le_add hlin hterm
    _ = 2 ^ (8 * x.length + 19) := by
      rw [show 8 * x.length + 19 = (8 * x.length + 18) + 1 by omega,
        pow_succ]
      ring

theorem parserCopierReserve_le_sideScannerBits_sub (x : Word) :
    (MStarCopierExecution.parserCopierReserve x).length ≤
      (sideScannerBits x).length - (PakEncodedStart.parserCells x).length := by
  rw [sideScannerBits_length, parserCells_length]
  have hpow := Nat.ge_two_pow_of_testBit (sideValue_padding_testBit x)
  have hp : 74 * x.length + 78 ≤ 2 ^ (8 * x.length + 20) := by
    calc
      74 * x.length + 78 ≤ 2 ^ (x.length + 7) :=
        parser_length_le_two_pow x.length
      _ ≤ 2 ^ (8 * x.length + 20) := by
        exact Nat.pow_le_pow_right (by decide) (by omega)
  have hc := parserCopierReserve_length_bound x
  have hsum : 74 * x.length + 78 +
      (MStarCopierExecution.parserCopierReserve x).length ≤
      2 ^ (8 * x.length + 21) := by
    calc
      74 * x.length + 78 +
          (MStarCopierExecution.parserCopierReserve x).length ≤
          2 ^ (8 * x.length + 20) + 2 ^ (8 * x.length + 20) :=
        Nat.add_le_add hp (hc.trans (Nat.pow_le_pow_right (by decide) (by omega)))
      _ = 2 ^ (8 * x.length + 21) := by
        rw [show 8 * x.length + 21 = (8 * x.length + 20) + 1 by omega,
          pow_succ]
        ring
  have hexp : 8 * x.length + 21 ≤ paddingLength x.length := by
    simp [paddingLength]
    omega
  have hbig : 2 ^ (8 * x.length + 21) ≤ 2 ^ (paddingLength x.length) :=
    Nat.pow_le_pow_right (by decide) hexp
  have htotal := hsum.trans (hbig.trans hpow)
  omega

def sideCopierHashTail (x : Word) : List PakEncodedStart.Fixed.Tape :=
  List.replicate
    ((sideScannerBits x).length - (PakEncodedStart.parserCells x).length -
      (MStarCopierExecution.parserCopierReserve x).length)
    .hash

def parserCellsWithCopierReserve (x : Word) :
    List PakEncodedStart.Fixed.Tape :=
  PakEncodedStart.parserCells x ++
    MStarCopierExecution.parserCopierReserve x ++ sideCopierHashTail x

theorem parserCellsWithCopierReserve_length (x : Word) :
    (parserCellsWithCopierReserve x).length = (sideScannerBits x).length := by
  unfold parserCellsWithCopierReserve sideCopierHashTail
  rw [List.length_append, List.length_append, List.length_replicate]
  have h := parserCopierReserve_le_sideScannerBits_sub x
  have hp := parserCells_le_sideScannerBits_length x
  have hb := sideScannerBits_pos x
  omega

/-- The high-zero portion of the side scanner is reserved as literal work
cells.  Its length is nonnegative by the preceding side bound. -/
def workReserve (x : Word) : List PakEncodedStart.Fixed.Tape :=
  List.replicate
    ((sideScannerBits x).length - (PakEncodedStart.parserCells x).length)
    (.core MStarConcreteAlphabet.work)

def parserCellsWithReserve (x : Word) : List PakEncodedStart.Fixed.Tape :=
  PakEncodedStart.parserCells x ++ workReserve x

theorem parserCellsWithReserve_length (x : Word) :
    (parserCellsWithReserve x).length = (sideScannerBits x).length := by
  unfold parserCellsWithReserve workReserve
  rw [List.length_append, List.length_replicate]
  have h := parserCells_le_sideScannerBits_length x
  omega

/-- The existing executable parser trace remains valid with exactly the
side-derived work reserve appended on its right.  This stops at `copyReady`:
the present copier reserve additionally contains `rightEnd = scratch 2`,
which a pure-work scanner tail does not yet initialize. -/
theorem parser_reaches_sideWorkReserve (x : Word) :
    MStarParserExecution.Reaches MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work
      (MStarParserExecution.extendResultRight
        (MStarParserExecution.initial MStarConcreteAlphabet.zero
          MStarConcreteAlphabet.one MStarConcreteAlphabet.work (encodedWord x))
        (workReserve x))
      (.copyReady (MStarParserExecution.extendRight
        (MStarConcreteAlphabet.finalZipper x.reverse) (workReserve x))) :=
  MStarConcreteAlphabet.reaches_parser_encodedWord_with_tail x (workReserve x)

/-- The parser reaches the exact side row whose suffix begins with the
    checked parser/copier reserve and ends in inert hashes.  The hash tail is
    outside the finite copier segment; the copier's `rightEnd` occurs at the
    end of its own reserve. -/
theorem parser_reaches_sideCopierReserve (x : Word) :
    MStarParserExecution.Reaches MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work
      (MStarParserExecution.extendResultRight
        (MStarParserExecution.initial MStarConcreteAlphabet.zero
          MStarConcreteAlphabet.one MStarConcreteAlphabet.work (encodedWord x))
        (MStarCopierExecution.parserCopierReserve x ++ sideCopierHashTail x))
      (.copyReady (MStarParserExecution.extendRight
        (MStarConcreteAlphabet.finalZipper x.reverse)
        (MStarCopierExecution.parserCopierReserve x ++ sideCopierHashTail x))) :=
  MStarConcreteAlphabet.reaches_parser_encodedWord_with_tail x _

def sideCopierSeedZipper (x : Word) :
    MStarParserExecution.Zipper PakEncodedStart.Fixed.Tape :=
  ⟨.markL :: MStarCopierExecution.groupSource x.reverse 0 x.length
      (MStarConcreteAlphabet.pairingPad x.length),
    .core MStarConcreteAlphabet.work,
    .core MStarConcreteAlphabet.work ::
      MStarCopierExecution.copierReserve x.length [] ++
        sideCopierHashTail x⟩

theorem sideCopier_enters (x : Word) :
    MStarCopierMicrocode.step (UState := Unit) ()
        (.inl MStarParserMicrocode.copyStart)
        (MStarParserExecution.extendRight
          (MStarConcreteAlphabet.finalZipper x.reverse)
          (MStarCopierExecution.parserCopierReserve x ++
            sideCopierHashTail x)).focus =
      some (MStarCopierMicrocode.copyGo .markL .seedCell .right) ∧
    MStarParserExecution.applyAction
        (MStarParserExecution.extendRight
          (MStarConcreteAlphabet.finalZipper x.reverse)
          (MStarCopierExecution.parserCopierReserve x ++
            sideCopierHashTail x))
        (MStarCopierMicrocode.copyGo (UState := Unit)
          .markL .seedCell .right) =
      some (sideCopierSeedZipper x) := by
  constructor
  · simp [MStarParserExecution.extendRight,
      MStarConcreteAlphabet.finalZipper,
      MStarCopierMicrocode.step]
  · simp [sideCopierSeedZipper, MStarParserExecution.extendRight,
      MStarParserExecution.applyAction,
      MStarConcreteAlphabet.finalZipper, MStarCopierMicrocode.copyGo,
      MStarCopierExecution.parserCopierReserve,
      MStarCopierExecution.copierReserve,
      MStarCopierExecution.groupSource,
      MStarCopierExecution.groupPrefix, List.append_assoc]

private theorem eightRoundReserve_append (n : ℕ)
    (base tail : List PakEncodedStart.Fixed.Tape) :
    MStarCopierExecution.eightRoundReserve n (base ++ tail) =
      MStarCopierExecution.eightRoundReserve n base ++ tail := by
  simp [MStarCopierExecution.eightRoundReserve, List.append_assoc]

private theorem groupExtraReserve_append (groups n : ℕ)
    (base tail : List PakEncodedStart.Fixed.Tape) :
    MStarCopierExecution.groupExtraReserve groups n (base ++ tail) =
      MStarCopierExecution.groupExtraReserve groups n base ++ tail := by
  induction groups generalizing n with
  | zero => rfl
  | succ groups ih =>
      simp only [MStarCopierExecution.groupExtraReserve]
      rw [ih, eightRoundReserve_append]

private theorem copierReserve_append_external (m : ℕ)
    (tail : List PakEncodedStart.Fixed.Tape) :
    MStarCopierExecution.copierReserve m tail =
      MStarCopierExecution.copierReserve m [] ++ tail := by
  unfold MStarCopierExecution.copierReserve
    MStarCopierExecution.copierRoundReserve
  apply congrArg (fun xs : List PakEncodedStart.Fixed.Tape =>
    .core MStarConcreteAlphabet.work :: xs)
  rw [show List.replicate (m + 1)
        (.core MStarConcreteAlphabet.work) ++
          MStarCopierMicrocode.rightEnd :: tail =
      (List.replicate (m + 1) (.core MStarConcreteAlphabet.work) ++
        [MStarCopierMicrocode.rightEnd]) ++ tail by simp [List.append_assoc]]
  rw [groupExtraReserve_append, eightRoundReserve_append]
  rfl

theorem side_parser_then_copier (x : Word) :
    MStarParserExecution.Reaches MStarConcreteAlphabet.zero
        MStarConcreteAlphabet.one MStarConcreteAlphabet.work
        (MStarParserExecution.extendResultRight
          (MStarParserExecution.initial MStarConcreteAlphabet.zero
            MStarConcreteAlphabet.one MStarConcreteAlphabet.work
            (ConcretePakSide.encodedWord x))
          (MStarCopierExecution.parserCopierReserve x ++
            sideCopierHashTail x))
        (.copyReady (MStarParserExecution.extendRight
          (MStarConcreteAlphabet.finalZipper x.reverse)
          (MStarCopierExecution.parserCopierReserve x ++
            sideCopierHashTail x))) ∧
      MStarParserExecution.applyAction
        (MStarParserExecution.extendRight
          (MStarConcreteAlphabet.finalZipper x.reverse)
          (MStarCopierExecution.parserCopierReserve x ++
            sideCopierHashTail x))
        (MStarCopierMicrocode.copyGo (UState := Unit)
          .markL .seedCell .right) =
        some (sideCopierSeedZipper x) ∧
      ∃ z : MStarParserExecution.Zipper PakEncodedStart.Fixed.Tape,
        MStarCopierExecution.Reaches
          (.running .seedCell (sideCopierSeedZipper x)) (.groupReady z) ∧
        .markL :: z.focus :: z.right =
          MStarParserCopySpec.copiedWorkspace
            MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
            MStarConcreteAlphabet.work x ++ sideCopierHashTail x := by
  refine ⟨parser_reaches_sideCopierReserve x, ?_, ?_⟩
  · exact (sideCopier_enters x).2
  · let tail := sideCopierHashTail x
    let n := MStarCopierExecution.iteratedGroupWidth x.length 256
    let z : MStarParserExecution.Zipper PakEncodedStart.Fixed.Tape :=
      ⟨(.markL :: (MStarCopierExecution.doneReturnPrefix x.length).reverse) ++
          MStarParserMicrocode.sepLen ::
            (List.replicate x.length MStarParserMicrocode.lenDone ++
              MStarParserMicrocode.sepPad ::
                MStarConcreteAlphabet.pairingPad x.length),
        .core MStarConcreteAlphabet.work,
        List.replicate n (.core MStarConcreteAlphabet.work) ++
          x.map MStarCopierExecution.coreBit ++
            List.replicate (n + 1) (.core MStarConcreteAlphabet.work) ++
              .markR :: tail⟩
    have h := MStarCopierExecution.reaches_copier_complete x
      (MStarConcreteAlphabet.pairingPad x.length) tail
    dsimp only at h
    rw [copierReserve_append_external] at h
    refine ⟨z, ?_, ?_⟩
    · simpa [z, n, sideCopierSeedZipper,
      MStarCopierExecution.groupSource,
      MStarCopierExecution.groupPrefix, List.append_assoc] using h
    · have hseg := MStarCopierExecution.copier_marked_segment_eq x
      dsimp only at hseg
      dsimp [z]
      calc
        .markL :: .core MStarConcreteAlphabet.work ::
            (List.replicate n (.core MStarConcreteAlphabet.work) ++
              x.map MStarCopierExecution.coreBit ++
                List.replicate (n + 1) (.core MStarConcreteAlphabet.work) ++
                  .markR :: tail) =
            (.markL :: .core MStarConcreteAlphabet.work ::
              (List.replicate n (.core MStarConcreteAlphabet.work) ++
                x.map MStarCopierExecution.coreBit ++
                  List.replicate (n + 1) (.core MStarConcreteAlphabet.work) ++
                    [.markR])) ++ tail := by simp [List.append_assoc]
        _ = MStarParserCopySpec.copiedWorkspace
              MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
              MStarConcreteAlphabet.work x ++ tail := by rw [hseg]

def scannerTerminalIndex (x : Word) : ℕ :=
  (PakEncodedStart.parserCells x).length +
      (MStarCopierExecution.parserCopierReserve x).length - 1

private theorem parserCopierReserve_pos (x : Word) :
    0 < (MStarCopierExecution.parserCopierReserve x).length := by
  rw [length_parserCopierReserve]
  omega

theorem scannerTerminalIndex_pos (x : Word) : 0 < scannerTerminalIndex x := by
  unfold scannerTerminalIndex
  rw [parserCells_length]
  have h := parserCopierReserve_pos x
  omega

theorem scannerTerminalIndex_lt (x : Word) :
    scannerTerminalIndex x < (sideScannerBits x).length := by
  unfold scannerTerminalIndex
  have h := parserCopierReserve_le_sideScannerBits_sub x
  have hp := parserCells_le_sideScannerBits_length x
  have hb := sideScannerBits_pos x
  have hr := parserCopierReserve_pos x
  omega

theorem scannerTerminalIndex_succ (x : Word) :
    scannerTerminalIndex x + 1 =
      (PakEncodedStart.parserCells x).length +
        (MStarCopierExecution.parserCopierReserve x).length := by
  unfold scannerTerminalIndex
  have h := parserCopierReserve_pos x
  omega

theorem scannerTerminal_rightEnd (x : Word) :
    PakScannerTerminal.terminalDataCell (sideScannerBits x)
      (scannerTerminalIndex x) (scannerTerminalIndex x) =
      ConcretePakScanner.Buffer.rightEnd :=
  PakScannerTerminal.terminalDataCell_eq _ _

theorem scannerTerminal_after_hash (x : Word) (k : ℕ)
    (hk : scannerTerminalIndex x < k) :
    PakScannerTerminal.terminalDataCell (sideScannerBits x)
      (scannerTerminalIndex x) k = ConcretePakScanner.Buffer.hash :=
  PakScannerTerminal.terminalDataCell_gt _ _ _ hk

theorem sideScannerHeight (x : Word) :
    (sideScannerBits x).length + 2 = sideValue x := by
  rw [sideScannerBits_length]
  have h := sideValue_ge_five x
  omega

def sideScannerTilingWithCopierReserve (x : Word) :
    OpenWangTiling (scannerTile (S := ConcretePakScanner.State))
      (sideValue x) (sideValue x) := by
  have hbits := sideScannerBits_pos x
  have hheight := sideScannerHeight x
  have hterm := scannerTerminalIndex_pos x
  have hbound := scannerTerminalIndex_lt x
  simpa only [hheight] using
    (PakScannerTerminal.terminalScannerTiling (sideValue x)
      (sideValue_pos x) (sideScannerBits x) hbits
      (scannerTerminalIndex x) hterm hbound)

theorem sideScannerBits_getD (x : Word) (k : ℕ)
    (hk : k < sideValue x - 2) :
    (sideScannerBits x).getD k false = (sideValue x).testBit k := by
  let i : Fin (sideScannerBits x).length :=
    ⟨k, by simpa [sideScannerBits] using hk⟩
  rw [List.getD_eq_get (sideScannerBits x) false i]
  simp [sideScannerBits, i, List.get_ofFn]

/-- Below the two omitted high bits, the side scanner reads the encoded word
in precisely the parser's little-endian order, with false padding afterwards. -/
theorem sideScannerBits_getD_encodedWord (x : Word) (k : ℕ)
    (hk : k < (sideScannerBits x).length) :
    (sideScannerBits x).getD k false =
      (encodedWord x).reverse.getD k false := by
  have hk' : k < sideValue x - 2 := by
    simpa [sideScannerBits_length] using hk
  rw [sideScannerBits_getD x k hk', PakSideRipple.sideValue_testBit]
  unfold PakSideRipple.sideDigit littleDigits
  change decide (((encodedWord x).reverse.map Bool.toNat).getD k
    (Bool.toNat false) = 1) = (encodedWord x).reverse.getD k false
  rw [List.getD_map]
  cases h : (encodedWord x).reverse.getD k false <;> rfl

/-- Every scanner edge receives exactly the corresponding binary ripple bit.
The last two cases are the two omitted high zeros of `sideValue x`. -/
theorem sideScannerBit_eq_testBit (x : Word)
    (j : Fin ((sideScannerBits x).length + 2)) :
    PakScannerPath.scannerBit (sideScannerBits x) false false j =
      (sideValue x).testBit j.1 := by
  have hlen := sideScannerBits_length x
  have hfive := sideValue_ge_five x
  by_cases hlow : j.1 < (sideScannerBits x).length
  · unfold PakScannerPath.scannerBit
    rw [if_pos hlow]
    exact sideScannerBits_getD x j.1 (by simpa [hlen] using hlow)
  · have hcase : j.1 = (sideScannerBits x).length ∨
      j.1 = (sideScannerBits x).length + 1 := by omega
    rcases hcase with hpre | htop
    · unfold PakScannerPath.scannerBit
      rw [if_neg hlow, if_pos hpre, hpre, hlen]
      exact (omitted_bit_sub_two hfive).symm
    · unfold PakScannerPath.scannerBit
      have hnotpre : j.1 ≠ (sideScannerBits x).length := by omega
      rw [if_neg hlow, if_neg hnotpre]
      rw [htop, hlen]
      have hidx : sideValue x - 2 + 1 = sideValue x - 1 := by omega
      rw [hidx]
      exact (omitted_bit_sub_one hfive).symm

theorem sideScannerTerminalBit_eq_testBit (x : Word)
    (j : Fin ((sideScannerBits x).length + 2)) :
    (if j.1 < scannerTerminalIndex x then
        PakScannerPath.scannerBit (sideScannerBits x) false false j
     else if j.1 = scannerTerminalIndex x then false
     else if j.1 < (sideScannerBits x).length then false
     else if j.1 = (sideScannerBits x).length then false else false) =
      (sideValue x).testBit j.1 := by
  by_cases hterm : j.1 < scannerTerminalIndex x
  · simp [hterm, sideScannerBit_eq_testBit]
  · have hparser : (PakEncodedStart.parserCells x).length ≤ j.1 := by
      have hreserve := parserCopierReserve_pos x
      have hnon : scannerTerminalIndex x ≤ j.1 := by omega
      have hprefix : (PakEncodedStart.parserCells x).length ≤
          scannerTerminalIndex x := by
        unfold scannerTerminalIndex
        omega
      exact hprefix.trans hnon
    have henc : j.1 ≥ (ConcretePakSide.encodedWord x).length := by
      have hpLen := parserCells_length x
      have heLen := encodedWord_length x
      omega
    have hword : (encodedWord x).reverse.getD j.1 false = false := by
      apply List.getD_eq_default
      simpa only [List.length_reverse] using henc
    have hside : (sideValue x).testBit j.1 = false := by
      rw [PakSideRipple.sideValue_testBit]
      unfold PakSideRipple.sideDigit ConcretePakSide.littleDigits
      change decide (((encodedWord x).reverse.map Bool.toNat).getD j.1
        (Bool.toNat false) = 1) = false
      rw [List.getD_map]
      rw [hword]
      rfl
    simp [hterm, hside]

/-- The actual square east-scanner tiling at side `sideValue x`. -/
def sideScannerTiling (x : Word) :
    OpenWangTiling (scannerTile (S := ConcretePakScanner.State))
      (sideValue x) (sideValue x) := by
  exact sideScannerTilingWithCopierReserve x

end PakFixedPolyomino.PakSideScanner
