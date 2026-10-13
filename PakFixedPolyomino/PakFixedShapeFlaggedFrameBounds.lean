import PakFixedPolyomino.PakFixedShapeFlaggedChoiceWords
import PakFixedPolyomino.PakFixedShapeOccupancyInitialization

/-! Literal frame and choice-depth bounds for the ORIGINAL flagged algorithm.
These are pure bounds to be supplied internally to the physical ND compiler;
they do not assert a standard bit-time bound from arithmetic-operation counts. -/
namespace PakFixedPolyomino.PakFixedShapeFlaggedFrameBounds
noncomputable section
open Computability StandardBitMetric
open PakFixedWeightedStandardBinaryCount (value value_lt_pow_length)
open PakFixedShapeChoiceWords (Done)
open PakFixedShapeFiniteLabelRound (L labelAt)
open PakFixedShapeFlaggedPreparation (state prepare)
open PakFixedShapeOccupancyScan (mask mask_length)

theorem state_length (side : List Bool) (done : Done) :
    (state side done).length=2*side.length+2*(value side)^2+2 := by
  simp only [state,StandardBitWordVector.encode_length,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,mask_length]
  omega

theorem initialized_state (side : List Bool) :
    PakFixedShapeOccupancyInitialization.initialized side=state side ∅ := by
  simp only [PakFixedShapeOccupancyInitialization.initialized,state,
    PakFixedShapeOccupancyInitialization.empty_mask,
    StandardBitSquareOccupancyAllocation.cells,pow_two]

theorem frame_length (side : List Bool) (done : Done) (x y : Nat)
    (hx : x≤(value side)^2) (hy : y≤(value side)^2) :
    (PakFixedShapeStencilCellAlignment.frame side done x y).length≤
      2*side.length+6*(value side)^2+4 := by
  have hxl := StandardBitLiteralLength.encode_length_le x
  have hyl := StandardBitLiteralLength.encode_length_le y
  simp only [PakFixedShapeStencilCellAlignment.frame,StandardBitWordVector.encode_length,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,mask_length]
  omega

theorem prepared_length (side : List Bool) (done : Done) :
    (prepare (state side done)).length≤2*side.length+6*(value side)^2+5 := by
  have hi := StandardBitFirstZero.index_le (mask (value side) done)
  rw [mask_length] at hi
  have hx := (Nat.mod_le (StandardBitFirstZero.index (mask (value side) done)) (value side)).trans hi
  have hy := (Nat.div_le_self (StandardBitFirstZero.index (mask (value side) done)) (value side)).trans hi
  have hb := frame_length side done _ _ hx hy
  rw [PakFixedShapeFlaggedPreparation.prepare_original,List.length_cons]
  omega

theorem labelled_prepared_length (side : List Bool) (done : Done) (i : Fin L) :
    (pairBits (StandardBitFiniteChoicePrefix.labelCode L i) (prepare (state side done)).tail).length≤
      4*side.length+12*(value side)^2+2*L+11 := by
  have hb : (prepare (state side done)).tail.length≤2*side.length+6*(value side)^2+5 := by
    have h := prepared_length side done
    rw [List.length_tail]
    omega
  rw [pairBits_length,StandardBitFiniteChoicePrefix.labelCode_length]
  omega

def frameBound (m : Nat) : Nat := 12*2^(2*m)+4*m+2*L+11

theorem square_cells_bound (side : List Bool) : (value side)^2≤2^(2*side.length) := by
  have h := Nat.le_of_lt (value_lt_pow_length side)
  calc
    (value side)^2≤(2^side.length)^2 := Nat.pow_le_pow_left h 2
    _=2^(2*side.length) := by rw [← pow_mul,Nat.mul_comm]

theorem state_frame_bound (side : List Bool) (done : Done) :
    (state side done).length≤frameBound side.length := by
  rw [state_length]
  have h := square_cells_bound side
  dsimp [frameBound]
  omega

theorem prepared_frame_bound (side : List Bool) (done : Done) :
    (prepare (state side done)).length≤frameBound side.length := by
  have h := prepared_length side done
  have hn := square_cells_bound side
  dsimp [frameBound]
  omega

theorem labelled_frame_bound (side : List Bool) (done : Done) (i : Fin L) :
    (pairBits (StandardBitFiniteChoicePrefix.labelCode L i) (prepare (state side done)).tail).length≤
      frameBound side.length := by
  have h := labelled_prepared_length side done i
  have hn := square_cells_bound side
  dsimp [frameBound]
  omega

theorem frameBound_exponential (m : Nat) :
    frameBound m≤2^((2*Polynomial.X+Polynomial.C (2*L+27) : Polynomial Nat).eval m) := by
  have hm : m≤2^(2*m) := (Nat.le_of_lt Nat.lt_two_pow_self).trans
    (Nat.pow_le_pow_right (by decide) (by omega : m≤2*m))
  have hp : 1≤2^(2*m) := Nat.one_le_pow _ _ (by decide)
  have hc : 2*L+27≤2^(2*L+27) := Nat.le_of_lt Nat.lt_two_pow_self
  have hk := Nat.mul_le_mul_left (2*L+11) hp
  simp only [Nat.mul_one,Nat.add_mul] at hk
  have hm4 := Nat.mul_le_mul_left 4 hm
  have hb : frameBound m≤(2*L+27)*2^(2*m) := by
    dsimp [frameBound]
    rw [Nat.add_mul]
    omega
  have he := hb.trans (Nat.mul_le_mul_right (2^(2*m)) hc)
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_X,Polynomial.eval_C,pow_add,Nat.mul_comm] using he

theorem successful_choice_depth (side : List Bool) (done : Done) (is : List (Fin L))
    (out : List Bool) (h : PakFixedShapeFlaggedChoiceWords.run is (state side done)=some out) :
    is.length≤2^(2*side.length) :=
  (PakFixedShapeFlaggedChoiceWords.successful_prefix_length_le side done is out h).trans (square_cells_bound side)

theorem flagged_frame_bounds_spec :
    (∀ side done,(state side done).length≤frameBound side.length) ∧
    (∀ side done,(prepare (state side done)).length≤frameBound side.length) ∧
    (∀ side done i,(pairBits (StandardBitFiniteChoicePrefix.labelCode L i)
      (prepare (state side done)).tail).length≤frameBound side.length) ∧
    (∀ m,frameBound m≤2^((2*Polynomial.X+Polynomial.C (2*L+27) : Polynomial Nat).eval m)) :=
  ⟨state_frame_bound,prepared_frame_bound,labelled_frame_bound,frameBound_exponential⟩

end
end PakFixedPolyomino.PakFixedShapeFlaggedFrameBounds
