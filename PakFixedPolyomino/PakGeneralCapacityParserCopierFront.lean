import PakFixedPolyomino.PakGeneralCapacityInitialWindow
import PakFixedPolyomino.PakOuterParserNumericSuffix
import PakFixedPolyomino.PakCopierReserveLowerBound
import PakFixedPolyomino.PakSlotOneParserDecode

/-!
# Finite parser/copier front at an actual scanner capacity

This file has no outer-machine claim.  It transports the explicit finite
parser trace across the literal tail emitted by an arbitrary terminal scanner,
then identifies the one `copyStart` action with the raw copier seed.
-/

namespace PakFixedPolyomino.PakGeneralCapacityParserCopierFront

open MStarConcreteAlphabet MStarOuterProgram MStarParserExecution
open MStarCopierMicrocode
open PakGeneralCapacityInitialWindow
open PakSlotOneScannerMultiplicity

abbrev CoreTape := MStarULogAssembly.CoreTape
abbrev Result := MStarParserExecution.Result CoreTape
abbrev Zipper := MStarParserExecution.Zipper (MStarOuterProgram.Tape CoreTape)

def capacityHashTail (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) : List (MStarOuterProgram.Tape CoreTape) :=
  List.replicate (capacityHashTailLength x c) .hash

def capacityParserTail (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) : List (MStarOuterProgram.Tape CoreTape) :=
  [.core work, .core work] ++
    List.replicate c.1 (.core work) ++
      rightEnd :: capacityHashTail x c

def capacityParserInitialResult (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) : Result :=
  MStarParserExecution.extendResultRight
    (MStarParserExecution.initial zero one work (ConcretePakSide.encodedWord x))
    (capacityParserTail x c)

theorem capacityInitialCells_eq_parserInput_append_tail
    (x : ConcretePakSide.Word) (c : ScannerCapacity x) :
    capacityInitialCells x c =
      inputCells zero one work (ConcretePakSide.encodedWord x) ++
        capacityParserTail x c := by
  simp [capacityInitialCells, capacityParserTail, capacityHashTail,
    List.append_assoc]

theorem run_capacityParserInitial_explicitFuel
    (x : ConcretePakSide.Word) (c : ScannerCapacity x) :
    MStarParserExecution.run zero one work
      (PakOuterParserNumericSuffix.parserExplicitFuel x)
      (capacityParserInitialResult x c) =
      .copyReady (MStarParserExecution.extendRight
        (MStarConcreteAlphabet.finalZipper x.reverse) (capacityParserTail x c)) := by
  apply MStarParserExecution.run_extendResultRight_to_copyReady
  exact PakOuterParserNumericSuffix.run_parser_encodedWord_explicitFuel x

theorem reaches_capacityParser_copyReady
    (x : ConcretePakSide.Word) (c : ScannerCapacity x) :
    MStarParserExecution.Reaches zero one work (capacityParserInitialResult x c)
      (.copyReady (MStarParserExecution.extendRight
        (MStarConcreteAlphabet.finalZipper x.reverse) (capacityParserTail x c))) := by
  exact ⟨PakOuterParserNumericSuffix.parserExplicitFuel x,
    run_capacityParserInitial_explicitFuel x c⟩

abbrev capacityCopierJunk (x : ConcretePakSide.Word) :
    List (MStarOuterProgram.Tape CoreTape) :=
  pairingPad x.length

def capacityRawCopierSeedZipper (x : ConcretePakSide.Word)
    (c : ScannerCapacity x) : Zipper :=
  ⟨.markL :: MStarCopierExecution.groupSource x.reverse 0 x.length
      (capacityCopierJunk x),
    .core work,
    .core work :: List.replicate c.1 (.core work) ++
      rightEnd :: capacityHashTail x c⟩

theorem rawCopierSeed_eq_capacityRawCopierSeedZipper
    (x : ConcretePakSide.Word) (c : ScannerCapacity x) :
    PakCopierReserveLowerBound.rawCopierSeed x c.1
      (capacityCopierJunk x) (capacityHashTail x c) =
      .running .seedCell (capacityRawCopierSeedZipper x c) := by
  rfl

theorem capacityCopyStart_enters_seed
    (x : ConcretePakSide.Word) (c : ScannerCapacity x) :
    MStarCopierMicrocode.step (UState := Unit) ()
        (.inl MStarParserMicrocode.copyStart)
        (MStarParserExecution.extendRight
          (MStarConcreteAlphabet.finalZipper x.reverse)
          (capacityParserTail x c)).focus =
        some (MStarCopierMicrocode.copyGo .markL .seedCell .right) ∧
    MStarParserExecution.applyAction
        (MStarParserExecution.extendRight
          (MStarConcreteAlphabet.finalZipper x.reverse)
          (capacityParserTail x c))
        (MStarCopierMicrocode.copyGo (UState := Unit)
          .markL .seedCell .right) =
      some (capacityRawCopierSeedZipper x c) := by
  constructor
  · simp [capacityParserTail, MStarParserExecution.extendRight,
      MStarConcreteAlphabet.finalZipper, MStarCopierMicrocode.step]
  · unfold capacityRawCopierSeedZipper capacityCopierJunk
    simp [capacityParserTail, capacityHashTail,
      MStarParserExecution.extendRight, MStarConcreteAlphabet.finalZipper,
      MStarParserExecution.applyAction, MStarCopierMicrocode.copyGo,
      MStarCopierExecution.groupSource, MStarCopierExecution.groupPrefix,
      List.append_assoc]

theorem reaches_capacityCopier_generalCapacity
    (x : ConcretePakSide.Word) (c : ScannerCapacity x)
    (hmin : PakCopierReserveLowerBound.minimumSuccessfulWorkCount x.length ≤ c.1) :
    MStarCopierExecution.Reaches
      (PakCopierReserveLowerBound.rawCopierSeed x c.1
        (capacityCopierJunk x) (capacityHashTail x c))
      (.groupReady (PakCopierReserveLowerBound.rawGeneralCapacityGroupZipper x
        (PakCopierReserveLowerBound.actualFinalCapacity x.length c.1)
        (capacityCopierJunk x) (capacityHashTail x c))) := by
  exact PakCopierReserveLowerBound.reaches_rawCopier_generalCapacity_of_minimum
    x c.1 (capacityCopierJunk x) (capacityHashTail x c) hmin

end PakFixedPolyomino.PakGeneralCapacityParserCopierFront
