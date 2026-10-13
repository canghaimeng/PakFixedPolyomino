import PakFixedPolyomino.ULogMultiCycleRefinement

/-! Exact semantic accepting-path count as labelled slot words. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

def acceptingSlotWords : ℕ → ULogSemantics.Config → List (List Bool)
  | 0, c =>
      if ULogSemantics.halted c then
        if ULogSemantics.accepting c then [[]] else []
      else []
  | t + 1, c =>
      if ULogSemantics.halted c then
        if ULogSemantics.accepting c then [[]] else []
      else
        [false, true].flatMap fun slot =>
          match ULogSemantics.stepSlot slot c with
          | none => []
          | some c' => (acceptingSlotWords t c').map (slot :: ·)

theorem length_acceptingSlotWords (t : ℕ)
    (c : ULogSemantics.Config) :
    (acceptingSlotWords t c).length =
      ULogSemantics.machine.acceptingPaths t c := by
  induction t generalizing c with
  | zero =>
      by_cases hh : ULogSemantics.halted c = true <;>
        by_cases ha : ULogSemantics.accepting c = true <;>
          simp [acceptingSlotWords,
            BinaryNondeterministicMachine.acceptingPaths,
            ULogSemantics.machine, hh, ha]
  | succ t ih =>
      by_cases hh : ULogSemantics.halted c = true
      · by_cases ha : ULogSemantics.accepting c = true <;>
          simp [acceptingSlotWords,
            BinaryNondeterministicMachine.acceptingPaths,
            ULogSemantics.machine, hh, ha]
      · have hhf : ULogSemantics.halted c = false := by
          cases h : ULogSemantics.halted c <;> simp_all
        cases hfalse : ULogSemantics.stepSlot false c with
        | none =>
            cases htrue : ULogSemantics.stepSlot true c with
            | none =>
                simp [acceptingSlotWords,
                  BinaryNondeterministicMachine.acceptingPaths,
                  ULogSemantics.machine, ULogSemantics.next, hhf,
                  hfalse, htrue]
            | some c₁ =>
                simp [acceptingSlotWords,
                  BinaryNondeterministicMachine.acceptingPaths,
                  ULogSemantics.machine, ULogSemantics.next, hhf,
                  hfalse, htrue, ih]
        | some c₀ =>
            cases htrue : ULogSemantics.stepSlot true c with
            | none =>
                simp [acceptingSlotWords,
                  BinaryNondeterministicMachine.acceptingPaths,
                  ULogSemantics.machine, ULogSemantics.next, hhf,
                  hfalse, htrue, ih]
            | some c₁ =>
                simp [acceptingSlotWords,
                  BinaryNondeterministicMachine.acceptingPaths,
                  ULogSemantics.machine, ULogSemantics.next, hhf,
                  hfalse, htrue, ih]

theorem acceptingSlotWords_length_le (t : ℕ)
    (c : ULogSemantics.Config) :
    (acceptingSlotWords t c).length ≤ 2 ^ t := by
  rw [length_acceptingSlotWords]
  exact ULogSemantics.machine.acceptingPaths_le_two_pow t c

end PakFixedPolyomino.ULogBootstrapExecution
