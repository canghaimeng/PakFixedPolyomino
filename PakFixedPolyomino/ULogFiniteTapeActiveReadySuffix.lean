import PakFixedPolyomino.ULogFiniteTapeDeterministicFrameReadiness

/-! An actual resourceRun prefix identifies the precise remaining active
readiness certificate. The prefix updates real capacity/outer resources;
no uniform per-tick consumption or next-cycle reserve is assumed. -/

namespace PakFixedPolyomino.ULogFiniteTapeActiveReadySuffix

open ULogCompiler ULogFiniteTapeDeterministicFrameReadiness
open ULogFiniteTapePhysicalResourceLedger ULogBootstrapExecution
open FiniteOneTapeSemantics (moveHead)

variable {ns : Nat}

theorem head_ready {p : BoundedProgram ns 3} {slot : Bool} {rest : List Bool}
    {head : Int} {z : BoundedConfig ns 3} {C : Nat} {outer : List ULogProgram.Tape}
    (h : ActiveReadyRun p (slot :: rest) head z C outer) :
    NonClockFrameReady (liftConfig p z) C outer := by
  cases h with
  | cons _ _ ready _ => exact ready

theorem suffix_of_resource_run (p : BoundedProgram ns 3) (u v : List Bool)
    (head hf : Int) (z zf : BoundedConfig ns 3) (C Cf : Nat)
    (outer outerf : List ULogProgram.Tape)
    (active : ActiveReadyRun p (u ++ v) head z C outer)
    (pref : resourceRun p 2 u head z C outer = some (hf, zf, Cf, outerf)) :
    ActiveReadyRun p v hf zf Cf outerf := by
  induction u generalizing head z C outer with
  | nil =>
      simp only [resourceRun, Option.some.injEq, Prod.mk.injEq] at pref
      rcases pref with ⟨rfl, rfl, rfl, rfl⟩
      simpa using active
  | cons slot rest ih =>
      change ActiveReadyRun p (slot :: (rest ++ v)) head z C outer at active
      cases active with
      | @cons _ _ _ _ a _ _ halt rule _ tail =>
          have pref' : resourceRun p 2 rest (moveHead a.move head) (applyBounded 2 z a)
              (semanticCapacityAfter (liftConfig p z) (actionCode a) C)
              (semanticOuterAfter (liftConfig p z) (actionCode a) outer) = some (hf, zf, Cf, outerf) := by
            simpa only [resourceRun, halt, Bool.false_eq_true, ↓reduceIte, rule] using pref
          exact ih _ _ _ _ tail pref'

end PakFixedPolyomino.ULogFiniteTapeActiveReadySuffix
