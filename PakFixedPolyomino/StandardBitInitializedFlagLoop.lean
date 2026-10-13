import PakFixedPolyomino.StandardBitFlagLoop
import PakFixedPolyomino.StandardBitMachineComposition

/-! Physical initialization followed by a bounded flag loop. The pure
iteration bounds are measured in the ORIGINAL raw input length. The loop
machine need not have polynomial runtime on arbitrary uninitialized frames.
The combined ordinary machine nevertheless computes on every raw word.
-/
namespace PakFixedPolyomino.StandardBitInitializedFlagLoop
open StandardNondeterministicMachine StandardBitTime
open StandardBitMachineComposition (compose compose_exact encodeConfigB)
open StandardBitFlagLoop (Eval loopBound loopBound_eval eval_run cycleBound)
open StandardBitFlagLoopCycle (machine startConfig finalConfig initial_eq final_output)
variable {nsI ntI ns nt : Nat}

noncomputable def totalBound (pI p lengthBound iterations : Polynomial Nat) : Polynomial Nat :=
  pI + 1 + loopBound p lengthBound iterations

theorem totalBound_eval (pI p lengthBound iterations : Polynomial Nat) (n : Nat) :
    (totalBound pI p lengthBound iterations).eval n =
      pI.eval n + 1 + iterations.eval n * cycleBound (fun a => p.eval a) (lengthBound.eval n) := by
  simp only [totalBound,Polynomial.eval_add,Polynomial.eval_one,loopBound_eval]

/-- All tape executions, handoffs and their costs are derived internally.
The only iteration premise is the pure semantics of the initialized input. -/
theorem computes (I : DeterministicMachine nsI ntI) (M : DeterministicMachine ns nt)
    (init f g : List Bool → List Bool) (pI p lengthBound iterations : Polynomial Nat)
    (hI : ComputesWithin I init (fun a => pI.eval a))
    (hM : ComputesWithin M f (fun a => p.eval a))
    (hiteration : ∀ raw, ∃ k,
      Eval f (lengthBound.eval raw.length) (init raw) (g raw) k ∧
      k ≤ iterations.eval raw.length) :
    ComputesWithin (compose I (machine M)) g
      (fun n => (totalBound pI p lengthBound iterations).eval n) := by
  intro raw
  obtain ⟨a,outI,ha,hrI,hoI⟩ := hI raw
  obtain ⟨k,hk,hbound⟩ := hiteration raw
  obtain ⟨b,hb,hrM⟩ := eval_run M f _ hM _
    (fun _ h => StandardBitTimeComposition.eval_mono p h) hk
  have hrM' : run (machine M) (ticks b) (initial (machine M) (init raw)) =
      some (finalConfig M (g raw)) := by
    rw [initial_eq]
    exact hrM
  have hc := compose_exact I (machine M) init (fun _ => g raw) raw a b
    outI (finalConfig M (g raw)) hrI hoI hrM' (final_output M (g raw))
  refine ⟨a+1+b,encodeConfigB (nsA := nsI) (ntA := ntI) (machine M)
    (finalConfig M (g raw)),?_,hc.1,hc.2⟩
  change a+1+b ≤ (totalBound pI p lengthBound iterations).eval raw.length
  rw [totalBound_eval]
  exact Nat.add_le_add (Nat.add_le_add_right ha 1)
    (hb.trans (Nat.mul_le_mul_right _ hbound))

theorem polyBitTime (init f g : List Bool → List Bool)
    (hI : PolyBitTime init) (hM : PolyBitTime f)
    (lengthBound iterations : Polynomial Nat)
    (hiteration : ∀ raw, ∃ k,
      Eval f (lengthBound.eval raw.length) (init raw) (g raw) k ∧
      k ≤ iterations.eval raw.length) : PolyBitTime g := by
  obtain ⟨nsI,ntI,I,pI,hI⟩ := hI
  obtain ⟨ns,nt,M,p,hM⟩ := hM
  exact ⟨nsI+(ns+25)+2,ntI+(nt+7)+3,compose I (machine M),
    totalBound pI p lengthBound iterations,
    computes I M init f g pI p lengthBound iterations hI hM hiteration⟩

end PakFixedPolyomino.StandardBitInitializedFlagLoop
