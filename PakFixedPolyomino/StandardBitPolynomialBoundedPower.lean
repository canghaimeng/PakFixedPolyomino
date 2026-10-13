import PakFixedPolyomino.StandardBitBoundedPower

/-! A polynomially bounded exponent may be physically computed before the
fixed-base power loop. This generic closure retains the exponent compiler
and pure polynomial bound explicitly; concrete callers must prove both. -/
namespace PakFixedPolyomino.StandardBitPolynomialBoundedPower
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition
open StandardBitMetric (pairBits)

def init (e : List Bool → Nat) (raw : List Bool) : List Bool :=
  StandardBitBoundedPower.frame (e raw) 1

theorem init_polyBitTime (e : List Bool → Nat)
    (he : PolyBitTime (fun raw => encodeNat (e raw))) : PolyBitTime (init e) := by
  have h1 : PolyBitTime (fun _ : List Bool => [true]) := by
    simpa only [Function.comp_def] using polyBitTime_comp StandardBitPairSanitize.empty_polyBitTime
      (StandardBitPrepend.prepend_polyBitTime true)
  have h := StandardBitPairMaps.parallel_polyBitTime
    (fun raw => encodeNat (e raw)) (fun _ : List Bool => [true]) he h1
  have heq : StandardBitPairMaps.parallel (fun raw => encodeNat (e raw))
      (fun _ : List Bool => [true])=init e := by
    funext raw
    rw [StandardBitPairMaps.parallel_pair]
    rfl
  rwa [heq] at h

theorem power_polyBitTime (c : Nat) (e : List Bool → Nat) (q : Polynomial Nat)
    (he : PolyBitTime (fun raw => encodeNat (e raw)))
    (hbound : ∀ raw,e raw≤q.eval raw.length) :
    PolyBitTime (fun raw => encodeNat (c^e raw)) := by
  apply StandardBitInitializedFlagLoop.polyBitTime (init e) (StandardBitBoundedPower.body c)
    (fun raw => encodeNat (c^e raw)) (init_polyBitTime e he)
    (StandardBitBoundedPower.body_polyBitTime c) (Polynomial.C (c+2)*q+3) (q+1)
  intro raw
  refine ⟨e raw+1,?_,?_⟩
  · have h := StandardBitBoundedPower.eval c (q.eval raw.length) (e raw) 0 (by simpa using hbound raw)
    simpa only [init,StandardBitBoundedPower.frame,pow_zero,Nat.add_zero,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_ofNat] using h
  · simpa only [Polynomial.eval_add,Polynomial.eval_one] using Nat.add_le_add_right (hbound raw) 1
end
end PakFixedPolyomino.StandardBitPolynomialBoundedPower
