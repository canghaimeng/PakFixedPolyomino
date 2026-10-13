import PakFixedPolyomino.StandardBitInitializedFunctionBoundLoop
import PakFixedPolyomino.StandardPolynomialExponentialBounds

/-! Exponential time for the actual finite initialized flag-loop compiler.
The body is polynomial in its physical frame length; frames and iteration
counts may be exponential in ORIGINAL raw length. Every term in totalBound
counts physical tape transitions. This intermediate theorem retains pure
initialization/body/loop premises for concrete membership to discharge. -/
namespace PakFixedPolyomino.StandardBitInitializedExponentialLoop
noncomputable section
open Polynomial StandardBitTime StandardNondeterministicMachine
open StandardBitInitializedFunctionBoundLoop (totalBound)
open StandardPolynomialExponentialBounds (polynomial_bound evaluated_bound)

theorem total_bound_exponential (pI p : Polynomial Nat)
    (L K : Nat → Nat) (q r : Polynomial Nat)
    (hL : ∀ n,L n≤2^q.eval n) (hK : ∀ n,K n≤2^r.eval n) :
    ∃ e : Polynomial Nat, ∀ n,totalBound pI p L K n≤2^e.eval n := by
  obtain ⟨u,hu⟩ := polynomial_bound pI
  obtain ⟨v,hv⟩ := evaluated_bound (5*p+4*X+11) L q hL
  refine ⟨u+r+v+2,?_⟩
  intro n
  have hc : StandardBitFlagLoop.cycleBound (fun a => p.eval a) (L n)≤2^v.eval n := by
    simpa only [StandardBitFlagLoop.cycleBound,eval_add,eval_mul,eval_ofNat,eval_X] using hv n
  have hk : K n*StandardBitFlagLoop.cycleBound (fun a => p.eval a) (L n)≤
      2^(r.eval n+v.eval n) := by
    rw [pow_add]
    exact Nat.mul_le_mul (hK n) hc
  let w := u.eval n+r.eval n+v.eval n
  have hi : pI.eval n≤2^w := (hu n).trans
    (Nat.pow_le_pow_right (by decide) (by dsimp [w];omega))
  have ht : K n*StandardBitFlagLoop.cycleBound (fun a => p.eval a) (L n)≤2^w := hk.trans
    (Nat.pow_le_pow_right (by decide) (by dsimp [w];omega))
  have h1 : 1≤2^w := Nat.one_le_pow _ _ (by decide)
  simp only [totalBound,eval_add,eval_ofNat]
  change pI.eval n+1+K n*StandardBitFlagLoop.cycleBound (fun a => p.eval a) (L n)≤2^(w+2)
  have hsum : pI.eval n+1+K n*StandardBitFlagLoop.cycleBound (fun a => p.eval a) (L n)≤4*2^w := by omega
  simpa only [pow_add,show (2 : Nat)^2=4 from rfl,Nat.mul_comm] using hsum

theorem compiled (init f g : List Bool → List Bool)
    (hI : PolyBitTime init) (hM : PolyBitTime f)
    (L K : Nat → Nat) (q r : Polynomial Nat)
    (hL : ∀ n,L n≤2^q.eval n) (hK : ∀ n,K n≤2^r.eval n)
    (hiteration : ∀ raw, ∃ k,
      StandardBitFlagLoop.Eval f (L raw.length) (init raw) (g raw) k ∧
      k ≤ K raw.length) :
    ∃ ns nt, ∃ M : DeterministicMachine ns nt, ∃ e : Polynomial Nat,
      ComputesWithin M g (fun n => 2^e.eval n) := by
  obtain ⟨ns,nt,M,pI,p,h⟩ :=
    StandardBitInitializedFunctionBoundLoop.compiled init f g hI hM L K hiteration
  obtain ⟨e,he⟩ := total_bound_exponential pI p L K q r hL hK
  refine ⟨ns,nt,M,e,?_⟩
  intro raw
  obtain ⟨t,out,ht,hr,ho⟩ := h raw
  exact ⟨t,out,ht.trans (he raw.length),hr,ho⟩

end
end PakFixedPolyomino.StandardBitInitializedExponentialLoop
