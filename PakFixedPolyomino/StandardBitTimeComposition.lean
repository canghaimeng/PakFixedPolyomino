import PakFixedPolyomino.StandardBitMachineComposition
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-! # Polynomial bit-time closure under function composition

The composed machine is the operational common-alphabet compiler. The
time bound uses the actual intermediate output-length inequality, not an
external arithmetic-unit or compiler certificate.
-/

namespace PakFixedPolyomino.StandardBitTimeComposition

open StandardNondeterministicMachine StandardBitTime
open StandardBitMachineComposition
open Polynomial

variable {nsA ntA nsB ntB : ℕ}

theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [eval_add]
      exact Nat.add_le_add hp hq
  | monomial n c =>
      simp only [eval_monomial]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

noncomputable def composedBound (p q : Polynomial ℕ) : Polynomial ℕ :=
  p + C 1 + q.comp (X + p + C 1)

theorem composedBound_eval (p q : Polynomial ℕ) (n : ℕ) :
    (composedBound p q).eval n =
      p.eval n + 1 + q.eval (n + p.eval n + 1) := by
  simp [composedBound, eval_add, eval_comp, eval_X, add_assoc]

theorem ComputesWithin.comp_mono (M : DeterministicMachine nsA ntA)
    (N : DeterministicMachine nsB ntB)
    (f g : List Bool → List Bool) (pBound qBound : ℕ → ℕ)
    (hqmono : ∀ {a b : ℕ}, a ≤ b → qBound a ≤ qBound b)
    (hM : ComputesWithin M f pBound) (hN : ComputesWithin N g qBound) :
    ComputesWithin (compose M N) (g ∘ f)
      (fun n => pBound n + 1 + qBound (n + pBound n + 1)) := by
  intro x
  obtain ⟨n, outM, hn, hrunM, houtM⟩ := hM x
  obtain ⟨m, outN, hm, hrunN, houtN⟩ := hN (f x)
  have hlen := ComputesWithin.output_length M f pBound hM x
  have hm' : m ≤ qBound (x.length + pBound x.length + 1) :=
    hm.trans (hqmono hlen)
  have htime : n + 1 + m ≤
      pBound x.length + 1 + qBound (x.length + pBound x.length + 1) := by
    omega
  refine ⟨n + 1 + m,
    encodeConfigB (nsA := nsA) (ntA := ntA) N outN, htime, ?_, ?_⟩
  · exact (compose_exact M N f g x n m outM outN hrunM houtM hrunN houtN).1
  · exact (compose_exact M N f g x n m outM outN hrunM houtM hrunN houtN).2

theorem polyBitTime_comp {f g : List Bool → List Bool}
    (hf : PolyBitTime f) (hg : PolyBitTime g) : PolyBitTime (g ∘ f) := by
  obtain ⟨nsA, ntA, M, p, hM⟩ := hf
  obtain ⟨nsB, ntB, N, q, hN⟩ := hg
  refine ⟨nsA + nsB + 2, ntA + ntB + 3, compose M N, composedBound p q, ?_⟩
  intro x
  have hcomp :=
    ComputesWithin.comp_mono M N f g (fun n => p.eval n) (fun n => q.eval n)
      (fun {_ _} h => eval_mono q h) hM hN x
  obtain ⟨k, out, hk, hrun, hout⟩ := hcomp
  refine ⟨k, out, ?_, hrun, hout⟩
  simpa [composedBound_eval] using hk

end PakFixedPolyomino.StandardBitTimeComposition
