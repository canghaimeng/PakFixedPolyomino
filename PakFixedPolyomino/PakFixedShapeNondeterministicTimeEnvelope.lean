import PakFixedPolyomino.PakFixedShapeNondeterministicPhases
import PakFixedPolyomino.PakFixedShapeFlaggedFrameBounds
import PakFixedPolyomino.StandardPolynomialExponentialBounds

/-! Numerical envelope for the actual phase transition costs. Actual full
feedback prefix inversion supplies the phase sum separately; this module
does not infer a machine runtime from arithmetic-operation counts. -/
namespace PakFixedPolyomino.PakFixedShapeNondeterministicTimeEnvelope
noncomputable section
open Polynomial
open PakFixedShapeFlaggedFrameBounds (frameBound frameBound_exponential square_cells_bound)
open PakFixedShapeNondeterministicPhases (preparation)

def cyclePolynomial : Polynomial Nat := preparation.polynomial+
  PakFixedShapeNondeterministicRound.polynomial+8*X+12
def cycleBudget (m : Nat) := cyclePolynomial.eval (frameBound m)
def loopBudget (m : Nat) := (2^(2*m)+1)*cycleBudget m
def totalBudget (initExponent : Polynomial Nat) (m : Nat) := 2^initExponent.eval m+loopBudget m+2

theorem cycleBudget_eq (m : Nat) : cycleBudget m=
    preparation.polynomial.eval (frameBound m)+
      PakFixedShapeNondeterministicRound.polynomial.eval (frameBound m)+
      2*(4*frameBound m+4)+4 := by
  simp only [cycleBudget,cyclePolynomial,eval_add,eval_mul,eval_ofNat,eval_X]
  omega

theorem phase_envelope (side : List Bool) (done : PakFixedShapeChoiceWords.Done)
    (a b c : Nat)
    (ha : a≤preparation.polynomial.eval (PakFixedShapeFlaggedPreparation.state side done).length)
    (hb : b≤PakFixedShapeNondeterministicRound.polynomial.eval
      (PakFixedShapeFlaggedPreparation.prepare (PakFixedShapeFlaggedPreparation.state side done)).tail.length)
    (hc : c≤4*frameBound side.length+4) :
    a+b+2*c+4≤cycleBudget side.length := by
  have hstate := PakFixedShapeFlaggedFrameBounds.state_frame_bound side done
  have hprep := PakFixedShapeFlaggedFrameBounds.prepared_frame_bound side done
  have htail : (PakFixedShapeFlaggedPreparation.prepare (PakFixedShapeFlaggedPreparation.state side done)).tail.length≤frameBound side.length := by
    rw [List.length_tail];omega
  have hap := ha.trans (StandardBitTimeComposition.eval_mono preparation.polynomial hstate)
  have hbp := hb.trans (StandardBitTimeComposition.eval_mono PakFixedShapeNondeterministicRound.polynomial htail)
  rw [cycleBudget_eq]
  omega

theorem rank_cycles_envelope (side : List Bool) (k : Nat) (hk : k≤(PakFixedWeightedStandardBinaryCount.value side)^2) :
    (k+1)*cycleBudget side.length≤loopBudget side.length := by
  apply Nat.mul_le_mul_right
  exact Nat.add_le_add_right (hk.trans (square_cells_bound side)) 1

theorem totalBudget_exponential (initExponent : Polynomial Nat) :
    ∃ e : Polynomial Nat,∀ m,totalBudget initExponent m≤2^e.eval m := by
  obtain ⟨v,hv⟩ := StandardPolynomialExponentialBounds.evaluated_bound cyclePolynomial frameBound
    (2*X+C (2*PakFixedShapeFiniteLabelRound.L+27)) frameBound_exponential
  refine ⟨initExponent+2*X+v+3,?_⟩
  intro m
  have hcycles : 2^(2*m)+1≤2^(2*m+1) := by
    have hp : 1≤2^(2*m) := Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]
    omega
  have hloop : loopBudget m≤2^(2*m+1+v.eval m) := by
    rw [loopBudget,pow_add]
    exact Nat.mul_le_mul hcycles (hv m)
  let w := initExponent.eval m+2*m+v.eval m+1
  have hi : 2^initExponent.eval m≤2^w := Nat.pow_le_pow_right (by decide) (by dsimp [w];omega)
  have hl : loopBudget m≤2^w := hloop.trans (Nat.pow_le_pow_right (by decide) (by dsimp [w];omega))
  have hp : 1≤2^w := Nat.one_le_pow _ _ (by decide)
  have hs : totalBudget initExponent m≤4*2^w := by dsimp [totalBudget];omega
  have he : (initExponent+2*X+v+3).eval m=w+2 := by
    simp only [eval_add,eval_mul,eval_ofNat,eval_X];dsimp [w];omega
  rw [he,pow_add]
  simpa only [show (2:Nat)^2=4 from rfl,Nat.mul_comm] using hs
end
end PakFixedPolyomino.PakFixedShapeNondeterministicTimeEnvelope
