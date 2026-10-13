import PakFixedPolyomino.MStarConcreteAlphabet
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Exact allocation of the 53 core letters

The parser reserves core indices `0,1,2`.  This module gives the remaining
fifty indices a separate finite type and an explicit equivalence, so the
future `U_log` table cannot accidentally alias a parser letter or exceed the
accepted 53-core-letter budget.
-/

namespace PakFixedPolyomino.ULogAlphabet

open MStarConcreteAlphabet

abbrev ParserCoreLetter := Fin 3
abbrev ULogLetter := Fin 50

/-- Literal `3 + 50 = 53` split of the core alphabet. -/
def coreSplit : ParserCoreLetter ⊕ ULogLetter ≃ CoreTape :=
  finSumFinEquiv

def parserCore (i : ParserCoreLetter) : CoreTape := coreSplit (.inl i)
def ulogCore (i : ULogLetter) : CoreTape := coreSplit (.inr i)

@[simp] theorem parserCore_val (i : ParserCoreLetter) :
    (parserCore i).1 = i.1 := by
  change (finSumFinEquiv (Sum.inl i) : Fin (3 + 50)).1 = i.1
  rw [finSumFinEquiv_apply_left]
  rfl

@[simp] theorem ulogCore_val (i : ULogLetter) :
    (ulogCore i).1 = 3 + i.1 := by
  change (finSumFinEquiv (Sum.inr i) : Fin (3 + 50)).1 = 3 + i.1
  rw [finSumFinEquiv_apply_right]
  rfl

theorem parserCore_injective : Function.Injective parserCore := by
  exact coreSplit.injective.comp Sum.inl_injective

theorem ulogCore_injective : Function.Injective ulogCore := by
  exact coreSplit.injective.comp Sum.inr_injective

theorem parserCore_ne_ulogCore (i : ParserCoreLetter) (j : ULogLetter) :
    parserCore i ≠ ulogCore j := by
  intro h
  have := coreSplit.injective h
  cases this

@[simp] theorem parserCore_zero : parserCore 0 = zero := by
  apply Fin.ext
  simp [zero]
@[simp] theorem parserCore_one : parserCore 1 = one := by
  apply Fin.ext
  simp [one]
@[simp] theorem parserCore_work : parserCore 2 = work := by
  apply Fin.ext
  simp [work]

@[simp] theorem zero_ne_ulogCore (i : ULogLetter) : zero ≠ ulogCore i := by
  simpa [← parserCore_zero] using parserCore_ne_ulogCore (0 : ParserCoreLetter) i

@[simp] theorem one_ne_ulogCore (i : ULogLetter) : one ≠ ulogCore i := by
  simpa [← parserCore_one] using parserCore_ne_ulogCore (1 : ParserCoreLetter) i

@[simp] theorem work_ne_ulogCore (i : ULogLetter) : work ≠ ulogCore i := by
  simpa [← parserCore_work] using parserCore_ne_ulogCore (2 : ParserCoreLetter) i

theorem core_eq_parser_or_ulog (a : CoreTape) :
    (∃ i : ParserCoreLetter, a = parserCore i) ∨
      ∃ i : ULogLetter, a = ulogCore i := by
  rcases coreSplit.surjective a with ⟨i, rfl⟩
  cases i with
  | inl i => exact Or.inl ⟨i, rfl⟩
  | inr i => exact Or.inr ⟨i, rfl⟩

theorem core_eq_zero_one_work_or_ulog (a : CoreTape) :
    a = zero ∨ a = one ∨ a = work ∨
      ∃ i : ULogLetter, a = ulogCore i := by
  rcases core_eq_parser_or_ulog a with ⟨i, rfl⟩ | h
  · fin_cases i <;> simp
  · exact Or.inr (Or.inr (Or.inr h))

@[simp] theorem card_parserCoreLetter : Fintype.card ParserCoreLetter = 3 := by
  simp

@[simp] theorem card_ulogLetter : Fintype.card ULogLetter = 50 := by
  simp

/- The named symbols below are the scratch vocabulary of the universal
bytecode interpreter.  They are indices in the checked fifty-letter block;
additional indices remain available for the final literal transition table. -/

def codeZero : ULogLetter := 0
def codeOne : ULogLetter := 1
def codeSep : ULogLetter := 2
def codeEnd : ULogLetter := 3
def pcMark : ULogLetter := 4
def pcDone : ULogLetter := 5
def dataZero : ULogLetter := 6
def dataOne : ULogLetter := 7
def dataSep : ULogLetter := 8
def dataEnd : ULogLetter := 9
def headLeft : ULogLetter := 10
def headHere : ULogLetter := 11
def headRight : ULogLetter := 12
def stateZero : ULogLetter := 13
def stateOne : ULogLetter := 14
def stateSep : ULogLetter := 15
def clockZero : ULogLetter := 16
def clockOne : ULogLetter := 17
def clockSep : ULogLetter := 18
def branchZero : ULogLetter := 19
def branchOne : ULogLetter := 20
def returnMark : ULogLetter := 21
def payloadStartZero : ULogLetter := 22
def payloadStartOne : ULogLetter := 23
def payloadStartDone : ULogLetter := 24
def payloadEnd : ULogLetter := 25
def payloadDone : ULogLetter := 26
def payloadHeadZero : ULogLetter := 27
def payloadHeadOne : ULogLetter := 28
def payloadHeadBlank : ULogLetter := 29
def sourceBoundary : ULogLetter := 30
def sourceMark : ULogLetter := 31
def stateMark : ULogLetter := 32
def sourceBoundaryZero : ULogLetter := 33
def sourceBoundaryOne : ULogLetter := 34
def readBoundary : ULogLetter := 35
def actionBoundary : ULogLetter := 36
def targetMark : ULogLetter := 37
def targetBoundary : ULogLetter := 38
def stateShrinkBoundary : ULogLetter := 39
def payloadBlank : ULogLetter := 40

theorem named_symbols_pairwise :
    List.Pairwise (· ≠ ·)
      [codeZero, codeOne, codeSep, codeEnd, pcMark, pcDone,
        dataZero, dataOne, dataSep, dataEnd, headLeft, headHere, headRight,
        stateZero, stateOne, stateSep, clockZero, clockOne, clockSep,
        branchZero, branchOne, returnMark, payloadStartZero,
        payloadStartOne, payloadStartDone, payloadEnd, payloadDone,
        payloadHeadZero, payloadHeadOne, payloadHeadBlank,
        sourceBoundary, sourceMark, stateMark,
        sourceBoundaryZero, sourceBoundaryOne, readBoundary,
        actionBoundary, targetMark, targetBoundary, stateShrinkBoundary,
        payloadBlank] := by
  native_decide

end PakFixedPolyomino.ULogAlphabet
