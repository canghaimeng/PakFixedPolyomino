import PakFixedPolyomino.ULogSourceObliviousCycleInverse

/-! # Exact acceptance scope for unrestricted completed scanner cycles

The raw domain retains only length, actual execution and an atLeft final
state. Boundary safety is derived internally by the operational overflow
proofs; the bijection preserves occupied literal source slots.
This does not supply source halt wrappers, clocks, capacity invariance or a
count of full physical frames.
-/

namespace PakFixedPolyomino.ULogSourceObliviousCompletedCycle

open FiniteOneTapeSemantics ULogCompiler
open ULogSourceObliviousWindow ULogSourceObliviousScanProgram
open ULogSourceObliviousScanExecution
open ULogSourceObliviousUpdateExecution
open ULogSourceObliviousInitialWindowExecution ULogSourceObliviousCycleExecution
open ULogSourceObliviousCycleInverse
open ULogSourceOneHotMacroEquiv (SourceChoice)

theorem unrestricted_completed_cycle_exact {ns nt : ℕ}
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys) :
    (∀ (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt),
      run (program p hnt blank) (fun _ => true) raw
        (initialWindowConfig q w exterior) = some out →
      raw.length = 4 * windowWidth w + 6 →
      (∃ r, out.state = State.atLeft r) →
      ∃ (choice : SourceChoice p q (w.cells.get w.head))
        (next : LogicalWindow nt)
        (hsafe : w.applyAction? choice.action = some next),
        raw = cycleArrows p hnt blank q w choice next hsafe exterior ∧
          out = initialWindowConfig choice.action.target next exterior) ∧
    Nonempty (SafeSourceChoice p q w ≃
      RawCompletedCycle p hnt blank q w exterior) := by
  exact ⟨unrestricted_cycle_inverse p hnt blank q w exterior,
    ⟨completedCycleEquiv p hnt blank q w exterior⟩⟩

end PakFixedPolyomino.ULogSourceObliviousCompletedCycle
