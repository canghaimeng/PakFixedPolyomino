import PakFixedPolyomino.PakFixedWeightedShapeFamily
import Mathlib.Computability.Encoding

/-! ONE shape-set target on EVERY binary word with the fixed pinned natural
encoding. Canonical encodeNat names every natural square; other words use
the explicit total pinned decoder. The empty square has one empty tiling.
The source extraction below is arithmetic, with BIT and membership open. -/
namespace PakFixedPolyomino.PakFixedWeightedBinarySquareCount
noncomputable section
open PakFixedWeightedShapeFamily
open PakFixedWeightedPhysicalSourceReadout (sourceSide sourceAnswer)
open StandardNondeterministicMachine (Machine RunsAtMost acceptingCount SharpEXP)

def binarySquareCount (bits : List Bool) : Nat := squareCount (Computability.decodeNat bits)

theorem binary_square_count_encode (n : Nat) :
    binarySquareCount (Computability.encodeNat n) = squareCount n := by
  simp [binarySquareCount]

def emptySquareTiling : Tiling shapeSupport (square 0) where
  placements := ∅
  disjoint := by simp
  covers := by simp

theorem empty_square_tiling_unique (T : Tiling shapeSupport (square 0)) :
    T = emptySquareTiling := by
  apply TilingRelabelEquiv.tiling_eq_of_placements
  change T.placements = ∅
  apply Finset.eq_empty_of_forall_notMem
  intro p hp
  obtain ⟨z, hz⟩ := shape_nonempty p.tile
  have placed : z + p.shift ∈ Placement.cells shapeSupport p :=
    Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have impossible := T.placement_subset hp placed
  simpa using impossible

theorem square_count_zero : squareCount 0 = 1 :=
  Fintype.card_eq_one_iff.mpr ⟨emptySquareTiling, empty_square_tiling_unique⟩

theorem binary_square_count_nil : binarySquareCount [] = 1 := by
  change squareCount 0 = 1
  exact square_count_zero

theorem binary_source_readout {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) :
    sourceAnswer M p x (binarySquareCount (Computability.encodeNat (sourceSide M p x))) =
      acceptingCount M x (2 ^ p.eval x.length) := by
  rw [binary_square_count_encode]
  exact physical_source_readout M p x ht

theorem standard_sharp_exp_binary_source_readout (f : List Bool → Nat) (hf : SharpEXP f) :
    ∃ ns nt, ∃ M : Machine ns nt 2, ∃ p : Polynomial Nat,
      ∀ x, sourceAnswer M p x
        (binarySquareCount (Computability.encodeNat (sourceSide M p x))) = f x := by
  obtain ⟨ns, nt, M, p, h⟩ := standard_sharp_exp_physical_source_readout f hf
  refine ⟨ns, nt, M, p, ?_⟩
  intro x
  rw [binary_square_count_encode]
  exact h x

def fixed_binary_square_source_spec : Prop :=
  binarySquareCount [] = 1 ∧
  (∀ n, binarySquareCount (Computability.encodeNat n) = squareCount n) ∧
  (∀ f : List Bool → Nat, SharpEXP f →
    ∃ ns nt, ∃ M : Machine ns nt 2, ∃ p : Polynomial Nat,
      ∀ x, sourceAnswer M p x
        (binarySquareCount (Computability.encodeNat (sourceSide M p x))) = f x)

theorem fixed_binary_square_source_spec_holds : fixed_binary_square_source_spec :=
  ⟨binary_square_count_nil, binary_square_count_encode, standard_sharp_exp_binary_source_readout⟩

end
end PakFixedPolyomino.PakFixedWeightedBinarySquareCount
