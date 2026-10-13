import PakFixedPolyomino.StandardMachineAlphabetRelabel

/-! Literal slot words and their counts survive injective alphabet relabeling.
Every raw accepted word is covered; no additional image predicate is used. -/
namespace PakFixedPolyomino.StandardMachineAlphabetLeafTransport
open StandardNondeterministicMachine StandardMachineAlphabetRelabel
variable {ns nt mt nb : Nat}

def leafEquiv (M : Machine ns nt nb) (E : AlphabetMap nt mt) (raw : List Bool) :
    AcceptingLeaf (machine M E) raw ≃ AcceptingLeaf M raw where
  toFun w := ⟨w.val,(accepted_iff M E raw w.val).mp w.property⟩
  invFun w := ⟨w.val,(accepted_iff M E raw w.val).mpr w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def codeEquiv (M : Machine ns nt nb) (E : AlphabetMap nt mt) (raw : List Bool) (bound : Nat) :
    AcceptingCode (machine M E) raw bound ≃ AcceptingCode M raw bound where
  toFun w := ⟨w.val,(accepted_iff M E raw w.val.toList).mp w.property⟩
  invFun w := ⟨w.val,(accepted_iff M E raw w.val.toList).mpr w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem leafCard_eq (M : Machine ns nt nb) (E : AlphabetMap nt mt) (raw : List Bool) :
    Nat.card (AcceptingLeaf (machine M E) raw)=Nat.card (AcceptingLeaf M raw) :=
  Nat.card_congr (leafEquiv M E raw)

theorem acceptingCount_eq (M : Machine ns nt nb) (E : AlphabetMap nt mt) (raw : List Bool) (bound : Nat) :
    acceptingCount (machine M E) raw bound=acceptingCount M raw bound :=
  Fintype.card_congr (codeEquiv M E raw bound)

theorem runsAtMost (M : Machine ns nt nb) (E : AlphabetMap nt mt) (raw : List Bool)
    (bound : Nat) (h : RunsAtMost M raw bound) : RunsAtMost (machine M E) raw bound := by
  intro slots out hr
  obtain ⟨source,hs,_⟩ := (all_raw_run_inverse M E raw slots out).mp hr
  exact h slots source hs

end PakFixedPolyomino.StandardMachineAlphabetLeafTransport
