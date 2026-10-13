import PakFixedPolyomino.StandardBitInitializedFlagLoop

/-! The same finite physical initialized loop with arbitrary numerical frame
and iteration bounds in ORIGINAL raw length. This supports exponential grid
allocation for ordinary membership without pretending its output is short.
Bounds here are pure loop premises of a generic intermediate compiler; every
tape transition, flag strip, whole clean tape and handoff is proved internally.
Concrete membership still must supply the initialization/body/iteration data. -/
namespace PakFixedPolyomino.StandardBitInitializedFunctionBoundLoop
open StandardNondeterministicMachine StandardBitTime
open StandardBitMachineComposition (compose compose_exact encodeConfigB)
open StandardBitFlagLoop (Eval eval_run cycleBound)
open StandardBitFlagLoopCycle (machine startConfig finalConfig initial_eq final_output)
variable {nsI ntI ns nt : Nat}

def totalBound (pI p : Polynomial Nat) (lengthBound iterations : Nat → Nat) (n : Nat) : Nat :=
  pI.eval n+1+iterations n*cycleBound (fun a => p.eval a) (lengthBound n)

theorem computes (I : DeterministicMachine nsI ntI) (M : DeterministicMachine ns nt)
    (init f g : List Bool → List Bool) (pI p : Polynomial Nat)
    (lengthBound iterations : Nat → Nat)
    (hI : ComputesWithin I init (fun a => pI.eval a))
    (hM : ComputesWithin M f (fun a => p.eval a))
    (hiteration : ∀ raw, ∃ k,
      Eval f (lengthBound raw.length) (init raw) (g raw) k ∧
      k ≤ iterations raw.length) :
    ComputesWithin (compose I (machine M)) g (totalBound pI p lengthBound iterations) := by
  intro raw
  obtain ⟨a,outI,ha,hrI,hoI⟩ := hI raw
  obtain ⟨k,hk,hbound⟩ := hiteration raw
  obtain ⟨b,hb,hrM⟩ := eval_run M f _ hM _
    (fun _ h => StandardBitTimeComposition.eval_mono p h) hk
  have hrM' : run (machine M) (ticks b) (initial (machine M) (init raw))=
      some (finalConfig M (g raw)) := by
    rw [initial_eq]
    exact hrM
  have hc := compose_exact I (machine M) init (fun _ => g raw) raw a b
    outI (finalConfig M (g raw)) hrI hoI hrM' (final_output M (g raw))
  exact ⟨a+1+b,encodeConfigB (nsA:=nsI) (ntA:=ntI) (machine M)
    (finalConfig M (g raw)),Nat.add_le_add (Nat.add_le_add_right ha 1)
    (hb.trans (Nat.mul_le_mul_right _ hbound)),hc.1,hc.2⟩

theorem compiled (init f g : List Bool → List Bool)
    (hI : PolyBitTime init) (hM : PolyBitTime f)
    (lengthBound iterations : Nat → Nat)
    (hiteration : ∀ raw, ∃ k,
      Eval f (lengthBound raw.length) (init raw) (g raw) k ∧
      k ≤ iterations raw.length) :
    ∃ ns nt, ∃ M : DeterministicMachine ns nt, ∃ pI p : Polynomial Nat,
      ComputesWithin M g (totalBound pI p lengthBound iterations) := by
  obtain ⟨nsI,ntI,I,pI,hI⟩ := hI
  obtain ⟨ns,nt,M,p,hM⟩ := hM
  exact ⟨nsI+(ns+25)+2,ntI+(nt+7)+3,compose I (machine M),pI,p,
    computes I M init f g pI p lengthBound iterations hI hM hiteration⟩

end PakFixedPolyomino.StandardBitInitializedFunctionBoundLoop
