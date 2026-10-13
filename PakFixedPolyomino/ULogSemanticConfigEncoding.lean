import PakFixedPolyomino.ULogDynamicCursorRightBoundaryAtLeast

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

def payloadNat (n : ℕ) : Tape := unheadTape (readHeadNat n)

@[simp] theorem writeHeadNat_eq_readHeadNat (n : ℕ) :
    writeHeadNat n = readHeadNat n := by
  cases n with
  | zero => rfl
  | succ n => cases n <;> rfl

@[simp] theorem unhead_writeHeadNat (n : ℕ) :
    unheadTape (writeHeadNat n) = payloadNat n := by
  rw [writeHeadNat_eq_readHeadNat]
  rfl

@[simp] theorem headTapeOfCell_payloadNat (n : ℕ) :
    headTapeOfCell (payloadNat n) = readHeadNat n := by
  cases n with
  | zero => decide
  | succ n =>
      cases n with
      | zero => decide
      | succ n => simp [payloadNat, readHeadNat]; decide

theorem payloadNat_safe (n : ℕ) : PayloadCell (payloadNat n) := by
  cases n with
  | zero => left; decide
  | succ n =>
      cases n with
      | zero => right; left; decide
      | succ n => right; right; simp [payloadNat, readHeadNat]; decide

theorem payloadNatList_safe (xs : List ℕ) :
    PayloadPathSafe (xs.map payloadNat) := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨n, -, rfl⟩
  exact payloadNat_safe n

def stateWorkspace (capacity state : ℕ) (suffix : List Tape) : List Tape :=
  List.replicate state (ulogCore stateZero) ++
    ulogCore stateOne :: ulogCore stateSep ::
      List.replicate (capacity - state) MStarConcreteAlphabet.work ++ suffix

def semanticCycleEncoding (input : List Bool) (clockCells : List Tape)
    (capacity : ℕ) (outer suffix : List Tape)
    (c : ULogSemantics.Config) : Result :=
  .running .cycleStart
    ⟨dynamicRuleReturnPath (c.leftRev.map payloadNat) c.program input ++
        ulogCore pcMark :: outer,
      readHeadNat c.focus,
      clockCells ++ stateWorkspace capacity c.state suffix⟩

theorem stateWorkspace_atMost
    (capacity source target extra : ℕ)
    (hsource : source = target + extra) (hcap : source ≤ capacity)
    (suffix : List Tape) :
    List.replicate target (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep ::
          List.replicate extra MStarConcreteAlphabet.work ++
            List.replicate (capacity - source) MStarConcreteAlphabet.work ++
              suffix =
      stateWorkspace capacity target suffix := by
  have hsum : extra + (capacity - source) = capacity - target := by omega
  simp [stateWorkspace, List.append_assoc, hsum]

theorem stateWorkspace_atLeast
    (capacity source target growth : ℕ)
    (htarget : target = source + growth) (hcap : target ≤ capacity)
    (suffix : List Tape) :
    List.replicate source (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep ::
          List.replicate (capacity - source) MStarConcreteAlphabet.work ++
            suffix =
      List.replicate source (ulogCore stateZero) ++
        ulogCore stateOne :: ulogCore stateSep ::
          List.replicate growth MStarConcreteAlphabet.work ++
            List.replicate (capacity - target) MStarConcreteAlphabet.work ++
              suffix := by
  have hsum : capacity - source = growth + (capacity - target) := by omega
  rw [hsum, List.replicate_add]
  simp [List.append_assoc]

end PakFixedPolyomino.ULogBootstrapExecution
