import PakFixedPolyomino.ULogSourceObliviousAcceptedCycles

/-! # Checked scope of all-raw multi-cycle counts and physical resources

The finite horizon is a number of whole scanner cycles. Nothing here assumes
a canonical raw image, an intermediate endpoint, or boundary safety.
Arbitrary physical stopping lengths, source halting, clock/capacity invariance
and full square-frame counts remain separate operational obligations.
-/

namespace PakFixedPolyomino.ULogSourceObliviousMultiCycleAcceptance

open ULogCompiler ULogSourceObliviousWindow ULogSourceObliviousScanProgram
open ULogSourceObliviousUpdateExecution ULogSourceObliviousInitialWindowExecution
open ULogSourceObliviousCycleTraces ULogSourceObliviousLogicalRuns
open ULogSourceObliviousAcceptedCycles ULogSourceObliviousWindowFootprint

theorem all_raw_multicycle_counts_and_resources {ns nt : ℕ}
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (exterior : Int → Phys) (n : ℕ) (q accept : Fin ns) (w : LogicalWindow nt) :
    Nonempty (LogicalWords p n q w ≃ RawCycles p hnt blank exterior n q w) ∧
    Finite (LogicalWords p n q w) ∧ Finite (RawCycles p hnt blank exterior n q w) ∧
    Nat.card (RawCycles p hnt blank exterior n q w) =
      Nat.card (LogicalWords p n q w) ∧
    Nonempty (AcceptedLogicalWords p n q accept w ≃
      AcceptedRawCycles p hnt blank exterior n q accept w) ∧
    Finite (AcceptedLogicalWords p n q accept w) ∧
    Finite (AcceptedRawCycles p hnt blank exterior n q accept w) ∧
    Nat.card (AcceptedRawCycles p hnt blank exterior n q accept w) =
      Nat.card (AcceptedLogicalWords p n q accept w) ∧
    (∀ raw : RawCycles p hnt blank exterior n q w,
      PrefixInInterval p hnt blank 0 (windowWidth w + 1 : Int) raw.1
        (initialWindowConfig q w exterior)) := by
  refine ⟨⟨logicalRawEquiv p hnt blank exterior n q w⟩, inferInstance,
    inferInstance, raw_count_eq_logical_count p hnt blank exterior n q w,
    ⟨acceptedEquiv p hnt blank exterior n q accept w⟩, inferInstance,
    inferInstance, accepting_count_eq p hnt blank exterior n q accept w, ?_⟩
  intro raw
  obtain ⟨out, hrun, hleft⟩ := raw.2.2
  obtain ⟨t, hword, _⟩ := raw_trace_inverse p hnt blank exterior n q w raw.1
    out hrun raw.2.1 hleft
  rw [hword]
  exact arrows_footprint p hnt blank exterior n q w t

end PakFixedPolyomino.ULogSourceObliviousMultiCycleAcceptance
