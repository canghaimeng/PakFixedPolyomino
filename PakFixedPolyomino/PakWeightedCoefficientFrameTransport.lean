import PakFixedPolyomino.PakWeightedCoupledCoefficient

/-! Transport the actual full-mask skeleton weight to EVERY physical full
frame through the existing literal equivalence. No source-path census or
bit-time claim is supplied by this finite weighted transport. -/
namespace PakFixedPolyomino.PakWeightedCoefficientFrameTransport
open PakCoupledCoefficient PakWeightedCoupledInventory PakWeightedCoupledCoefficient
open PakMStarCouplingCorrectness
noncomputable section
set_option maxHeartbeats 1000000

theorem filtered_sum_as_subtype {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] [Fintype {a // p a}] (g : α → ℕ) :
    (∑ a : α, if p a then g a else 0) = ∑ a : {a // p a}, g a.val := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

def actualWeightedFullFrameSum (w h : ℕ) : ℕ :=
  ∑ F : FullFrame w h, coupledIdentityWeight F.tiling

theorem full_mask_equiv_preserves_weight {w h : ℕ} (hw : 0 < w) (hh : 0 < h)
    (S : FullMaskSkeleton w h hw hh) :
    coupledIdentityWeight ((fullMaskSkeletonEquivFullFrame hw hh) S).tiling =
      coupledIdentityWeight S.val := by
  rfl

theorem weightedFullFrameCount_eq_actualWeightedFullFrameSum
    {w h : ℕ} (hw : 0 < w) (hh : 0 < h) :
    weightedFullFrameCount hw hh = actualWeightedFullFrameSum w h := by
  classical
  let e := fullMaskSkeletonEquivFullFrame hw hh
  have filter := filtered_sum_as_subtype
    (fun s : CoupledTiling 1 w h => skeletonMask hw hh s = PakAmpCoefficient.BoundaryMask.full)
    coupledIdentityWeight
  calc
    weightedFullFrameCount hw hh =
        ∑ S : FullMaskSkeleton w h hw hh, coupledIdentityWeight S.val := by
      exact filter
    _ = ∑ S : FullMaskSkeleton w h hw hh, coupledIdentityWeight (e S).tiling := by
      apply Fintype.sum_congr
      intro S
      exact (full_mask_equiv_preserves_weight hw hh S).symm
    _ = actualWeightedFullFrameSum w h :=
      e.sum_comp (fun F => coupledIdentityWeight F.tiling)

theorem weightedSquare_div_fullPower_eq_actualWeightedFullFrameSum
    {n : ℕ} (hn : 5 ≤ n) :
    openWangCount (weightedCoupledWangTile weightedExtractionQ) n n /
        weightedExtractionQ ^ PakAmpCoefficient.BoundaryMask.full.qDegree n n =
      actualWeightedFullFrameSum n n := by
  rw [weightedSquare_div_fullPower_eq_fullFrameCount hn]
  exact weightedFullFrameCount_eq_actualWeightedFullFrameSum _ _

end
end PakFixedPolyomino.PakWeightedCoefficientFrameTransport
