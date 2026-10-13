import PakFixedPolyomino.ULogFiniteTapeNondeterministicMicroInverse

/-! Derive the nondeterministic physical inverse's reachable-node premise
from ordinary all-word spatial bounds. Selected accepting words also obtain
literal first-hit traces. These are transparent generic intermediates;
concrete source bounds and physical time/full-frame counts remain separate. -/

namespace PakFixedPolyomino.ULogFiniteTapeNondeterministicResourceBridge
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open ULogFiniteTapePhysicalResourceLedger ULogFiniteTapeBoundedGrowthReadiness
open ULogFiniteTapeNondeterministicMicroInverse
open ULogFiniteTapeDeterministicFrameReadiness ULogBootstrapExecution
open ULogAlphabet ULogProgram ULogConcreteSlotMicroExpansion
open MStarParserExecution (Zipper)
open FiniteOneTapeSemantics (moveHead)

variable {ns : Nat}

theorem resource_run_forget (p : BoundedProgram ns 3) (w : List Bool)
    (head hf : Int) (z out : BoundedConfig ns 3) (C Cf : Nat) (outer outerf : List Tape)
    (path : resourceRun p 2 w head z C outer = some (hf, out, Cf, outerf)) :
    ULogFiniteTapeZipperRun.run p 2 w head z = some (hf, out) := by
  induction w generalizing head z C outer with
  | nil =>
    simp only [resourceRun, Option.some.injEq, Prod.mk.injEq] at path
    rcases path with ⟨rfl, rfl, _, _⟩
    rfl
  | cons slot rest ih =>
    cases halt : boundedHalted z with
    | true => simp [resourceRun, halt] at path
    | false =>
      cases rule : p.rule z.state z.focus slot with
      | none => simp [resourceRun, halt, rule] at path
      | some a =>
        have last := ih (moveHead a.move head) (applyBounded 2 z a) _ _ (by
          simpa only [resourceRun, halt, Bool.false_eq_true, ↓reduceIte, rule] using path)
        simpa only [ULogFiniteTapeZipperRun.run, halt, Bool.false_eq_true, ↓reduceIte, rule] using last

theorem reachable_ready_of_growth (p : BoundedProgram ns 3) (hp : compile p ≠ [])
    (head : Int) (z : BoundedConfig ns 3) (L R C : Nat) (tail : List Tape)
    (bounds : AllGrowthBounded p head z L R) (hc : R + (ns - 1) ≤ C) :
    AllReachableReady p head z C (List.replicate L MStarConcreteAlphabet.work ++ tail) := by
  intro w hf out Cf outerf path halt
  have word := resource_run_forget p w head hf z out C Cf _ outerf path
  obtain ⟨lg, rg, _, _, computed, ready⟩ := every_reachable_resource_ready
    p hp head z L R bounds w hf out word halt C tail hc
  have eq := Option.some.inj (path.symm.trans computed)
  have capacity := congrArg (fun v : Int × BoundedConfig ns 3 × Nat × List Tape => v.2.2.1) eq
  have outer := congrArg (fun v : Int × BoundedConfig ns 3 × Nat × List Tape => v.2.2.2) eq
  dsimp only at capacity outer
  rw [capacity, outer]
  exact ready

theorem every_run_active (p : BoundedProgram ns 3) (w : List Bool)
    (head hf : Int) (z out : BoundedConfig ns 3) (C : Nat) (outer : List Tape)
    (reachable : AllReachableReady p head z C outer)
    (path : ULogFiniteTapeZipperRun.run p 2 w head z = some (hf, out)) :
    ActiveReadyRun p w head z C outer := by
  induction w generalizing head z C outer with
  | nil => exact .nil _ _ _ _
  | cons slot rest ih =>
    cases halt : boundedHalted z with
    | true => simp [ULogFiniteTapeZipperRun.run, halt] at path
    | false =>
      cases rule : p.rule z.state z.focus slot with
      | none => simp [ULogFiniteTapeZipperRun.run, halt, rule] at path
      | some a =>
        apply ActiveReadyRun.cons halt rule (reachable [] head z C outer rfl halt)
        apply ih _ _ _ _ (child_reachable_ready p head z C outer reachable slot a halt rule)
        simpa only [ULogFiniteTapeZipperRun.run, halt, Bool.false_eq_true, ↓reduceIte, rule] using path

theorem bounded_growth_nd_physical_spec {input : List Bool} {suffix : List Tape}
    (p : BoundedProgram ns 3) (hp : compile p ≠ []) (B : Nat)
    (head : Int) (z : BoundedConfig ns 3) (L R C : Nat) (tail : List Tape)
    (bounds : AllGrowthBounded p head z L R) (lengths : AllRunLengthBound p head z B)
    (hc : R + (ns - 1) ≤ C) (halt : boundedHalted z = false)
    (frame : SemanticCycleFrame input suffix)
    (hconfig : frame.config = liftConfig p z) (hcapacity : frame.capacity = C)
    (houter : frame.outer = List.replicate L MStarConcreteAlphabet.work ++ tail)
    (runtime : PassivePath frame.runtime) (budget : Nat)
    (clock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some budget) (slack : B < budget) :
    (∀ labels tape, ConcreteMicroPath frame.encode labels (.accepted tape) →
      ∃ w hf out, ULogFiniteTapeZipperRun.run p 2 w head z = some (hf, out) ∧
        out.state.val = 0 ∧ SlotMicroExpansion frame.encode w labels (.accepted tape)) ∧
    (∀ w hf out, ULogFiniteTapeZipperRun.run p 2 w head z = some (hf, out) →
      out.state.val = 0 → ExactConcreteAcceptingSlotTrace frame.encode w) := by
  have reachable := reachable_ready_of_growth p hp head z L R C tail bounds hc
  constructor
  · intro labels tape raw
    exact every_accepting_micro_path_reflects p B head z C _ reachable lengths halt frame
      hconfig hcapacity houter runtime budget clock slack labels tape raw
  · intro w hf out path accept
    exact ULogFiniteTapeActiveExactTrace.accepting_run_exact p w head hf z out C _
      (every_run_active p w head hf z out C _ reachable path) path accept halt frame
      hconfig hcapacity houter runtime budget clock (by have h := lengths w hf out path; omega)

end PakFixedPolyomino.ULogFiniteTapeNondeterministicResourceBridge
