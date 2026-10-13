import PakFixedPolyomino.PakSideRipple
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Literal slot-one entry for an encoded instance

This is the outer-machine endpoint of the parser input row.  It turns the
same `inputCells (encodedWord x)` used by the scanner into an actual
`FiniteOneTapeSemantics.Config`, and verifies the compulsory slot-one entry
from `start` into the concrete parser control.
-/

namespace PakFixedPolyomino.PakEncodedStart

open FiniteOneTapeProgram FiniteOneTapeSemantics
open PakCanonicalFullTrack

namespace Fixed

abbrev State := PakMStarCouplingCorrectness.Fixed.State
abbrev Tape := PakMStarCouplingCorrectness.Fixed.Tape
abbrev Arrow := PakMStarCouplingCorrectness.Fixed.Arrow

end Fixed

abbrev MStarConfig := PakMStarCouplingCorrectness.MStarConfig

def parserCells (x : ConcretePakSide.Word) : List Fixed.Tape :=
  MStarParserExecution.inputCells MStarConcreteAlphabet.zero
    MStarConcreteAlphabet.one MStarConcreteAlphabet.work
    (ConcretePakSide.encodedWord x)

/-- The scanner origin is a left hash at coordinate zero; the first parser
cell is at coordinate one, and all positions outside the finite row are hash. -/
def parserInputTape (x : ConcretePakSide.Word) (z : Int) : Fixed.Tape :=
  if 1 ≤ z then
    (parserCells x).getD (Int.toNat (z - 1)) .hash
  else .hash

theorem parserCells_head_zero (x : ConcretePakSide.Word) :
    (parserCells x).getD 0 .hash = .core MStarConcreteAlphabet.zero := by
  unfold parserCells
  rw [MStarParserExecution.inputCells_encodedWord]
  have hp : ConcretePakSide.paddingLength x.length =
      ConcretePakSide.paddingLength x.length - 1 + 1 := by
    simp [ConcretePakSide.paddingLength]
  rw [hp, List.replicate_succ]
  rfl

theorem parserInputTape_head_zero (x : ConcretePakSide.Word) :
    parserInputTape x 1 = .core MStarConcreteAlphabet.zero := by
  change (parserCells x).getD 0 .hash = .core MStarConcreteAlphabet.zero
  exact parserCells_head_zero x

theorem parserInputTape_left_hash (x : ConcretePakSide.Word) {z : Int}
    (hz : z < 1) : parserInputTape x z = .hash := by
  simp [parserInputTape, not_le_of_gt hz]

def encodedStartConfig (x : ConcretePakSide.Word) : MStarConfig :=
  { state := .start
    head := 1
    tape := parserInputTape x }

def encodedParserConfig (x : ConcretePakSide.Word) : MStarConfig :=
  { state := .parser MStarULogAssembly.data.parserStart
    head := 1
    tape := parserInputTape x }

def parserStartAction : Action Fixed.State Fixed.Tape :=
  { write := .core MStarConcreteAlphabet.zero
    target := .parser MStarULogAssembly.data.parserStart
    move := .stay }

theorem start_one_rule :
    MStarULogAssembly.program.rule .start
      (.core MStarConcreteAlphabet.zero) 1 = some parserStartAction := by
  simpa [parserStartAction] using
    (MStarOuterProgram.start_slot_one MStarULogAssembly.data initial_zero_letter)

def startOneArrow : Fixed.Arrow :=
  ⟨((.start, .core MStarConcreteAlphabet.zero), (1 : Fin 2)), by
    simp [start_one_rule]⟩

theorem actionOf_startOneArrow :
    actionOf MStarULogAssembly.program startOneArrow = parserStartAction := by
  apply actionOf_eq_of_rule_eq
  simpa [startOneArrow] using start_one_rule

@[simp] theorem startOneArrow_source : startOneArrow.1.1.1 = (.start : Fixed.State) := rfl

@[simp] theorem startOneArrow_read : startOneArrow.1.1.2 =
    (.core MStarConcreteAlphabet.zero : Fixed.Tape) := rfl

theorem update_parserInputTape (x : ConcretePakSide.Word) :
    Function.update (parserInputTape x) 1 (.core MStarConcreteAlphabet.zero) =
      parserInputTape x := by
  funext z
  by_cases hz : z = 1
  · subst z
    simpa [Function.update] using (parserInputTape_head_zero x).symm
  · have hzne : (1 : Int) ≠ z := Ne.symm hz
    simp [Function.update, hz, hzne]

/-- The actual outer program takes the encoded start configuration through
slot one into its parser state, preserving the concrete input tape. -/
theorem encodedStart_slotOne_step (x : ConcretePakSide.Word) :
    FiniteOneTapeSemantics.step MStarULogAssembly.program MStarOuterProgram.movable
      (encodedStartConfig x) startOneArrow = some (encodedParserConfig x) := by
  simp [FiniteOneTapeSemantics.step, transition, writtenTape,
    actionOf_startOneArrow, encodedStartConfig, encodedParserConfig,
    parserInputTape_head_zero, update_parserInputTape, parserStartAction,
    MStarOuterProgram.movable, FiniteOneTapeSemantics.moveHead]

end PakFixedPolyomino.PakEncodedStart
