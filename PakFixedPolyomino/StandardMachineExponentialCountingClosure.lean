import PakFixedPolyomino.StandardNondeterministicMachine

/-! An internally proved operational clock can be enlarged to one exponential
polynomial cutoff without adding transitions to any accepting path. -/
namespace PakFixedPolyomino.StandardMachineExponentialCountingClosure
open StandardNondeterministicMachine
variable {ns nt nb : Nat}

theorem sharpEXP_of_operational_counts (M : Machine ns nt nb)
    (f : List Bool → Nat) (bound : Nat → Nat)
    (htime : ∀ raw, RunsAtMost M raw (bound raw.length))
    (hcount : ∀ raw, f raw=acceptingCount M raw (bound raw.length))
    (henvelope : ∃ e : Polynomial Nat, ∀ n, bound n≤2^e.eval n) : SharpEXP f := by
  obtain ⟨e,he⟩ := henvelope
  refine ⟨ns,nt,nb,M,e,?_⟩
  intro raw
  refine ⟨fun slots out hr => (htime raw slots out hr).trans (he raw.length),?_⟩
  exact (hcount raw).trans
    (acceptingCount_eq_of_bounds M raw (bound raw.length) (bound raw.length)
      (2^e.eval raw.length) (htime raw) (le_refl _) (he raw.length))

theorem sharpEXP_of_all_leaf_card (M : Machine ns nt nb)
    (f : List Bool → Nat) (bound : Nat → Nat)
    (htime : ∀ raw, RunsAtMost M raw (bound raw.length))
    (hcount : ∀ raw, f raw=Nat.card (AcceptingLeaf M raw))
    (henvelope : ∃ e : Polynomial Nat, ∀ n, bound n≤2^e.eval n) : SharpEXP f := by
  apply sharpEXP_of_operational_counts M f bound htime _ henvelope
  intro raw
  exact (hcount raw).trans
    ((Nat.card_congr (acceptingLeavesEquiv M raw (bound raw.length) (htime raw)).symm).trans
      Nat.card_eq_fintype_card)

end PakFixedPolyomino.StandardMachineExponentialCountingClosure
