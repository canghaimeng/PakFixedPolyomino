import PakFixedPolyomino.ULogCounterPump

/-! A fixed source-retaining pump table. Its binary input is k zeros,
a one-bit separator, then arbitrary source bits. The actual entry scans
only the k zeros and replaces the separator by delimiter3. The remaining
append/counter table is unchanged and never returns to entry2. Separate
operational proofs must construct the initializer and full retained run. -/

namespace PakFixedPolyomino.ULogRetainedCounterPump

open ULogCompiler ULogFiniteTapeZipperRun
open FiniteOneTapeSemantics (moveHead)

def program : BoundedProgram 9 4 where
  rule := fun q read slot =>
    if slot then none else
      if q = 2 then
        if read = 0 then some { write := 0, target := 2, move := .right }
        else if read = 1 then some { write := 3, target := 8, move := .left }
        else none
      else ULogCounterPump.program.rule q read false

theorem rule_true (q : Fin 9) (read : Fin 4) : program.rule q read true = none := rfl

theorem rule_off_entry (q : Fin 9) (read : Fin 4) (slot : Bool) (hq : q ≠ 2) :
    program.rule q read slot = ULogCounterPump.program.rule q read slot := by
  cases slot <;> simp [program, hq, ULogCounterPump.rule_true]

theorem old_target_off_entry (q : Fin 9) (read : Fin 4) (slot : Bool)
    (hq : q ≠ 2) (a : BoundedAction 9 4)
    (ha : ULogCounterPump.program.rule q read slot = some a) : a.target ≠ 2 := by
  cases slot with
  | true => simp [ULogCounterPump.rule_true] at ha
  | false =>
    have hqv : q.val ≠ 2 := fun h => hq (Fin.ext h)
    simp only [ULogCounterPump.program, Bool.false_eq_true, ↓reduceIte,
      ULogCounterPump.action, hqv] at ha
    split_ifs at ha <;> cases ha <;> simp

theorem applyBounded_state (z : BoundedConfig 9 4) (a : BoundedAction 9 4) :
    (applyBounded (2 : Fin 4) z a).state = a.target := by
  cases hm : a.move <;> cases hl : z.leftRev <;> cases hr : z.right <;>
    simp [applyBounded, hm, hl, hr]

theorem run_off_entry (slots : List Bool) (head : Int) (z : BoundedConfig 9 4)
    (hq : z.state ≠ 2) :
    run program 2 slots head z = run ULogCounterPump.program 2 slots head z := by
  induction slots generalizing head z with
  | nil => rfl
  | cons slot rest ih =>
    simp only [run, rule_off_entry z.state z.focus slot hq]
    cases boundedHalted z with
    | true => rfl
    | false =>
      cases ha : ULogCounterPump.program.rule z.state z.focus slot with
      | none => rfl
      | some a =>
        have ht := old_target_off_entry z.state z.focus slot hq a ha
        exact ih (moveHead a.move head) (applyBounded (2 : Fin 4) z a)
          (by rwa [applyBounded_state])

def sourceInput (k : Nat) (source : List Bool) : List Bool :=
  List.replicate k false ++ true :: source

def input (k : Nat) (source : List Bool) : List Bool := encodeInstance program (sourceInput k source)

end PakFixedPolyomino.ULogRetainedCounterPump
