import PakFixedPolyomino.PakFixedWeightedStandardBinaryCount

/-! The headline counting model uses finite sets of actual integer-lattice
shapes, their translations, and the original square on every binary input. -/
namespace PakFixedPolyomino.PakFixedShapeExactCountingModel
noncomputable section

def exactTranslationSquareCount (family : Finset Polyomino) (side : Nat) : Nat :=
  Nat.card (Tiling (fun P : ↥family => P.val) (square side))

def binaryTranslationSquareCount (family : Finset Polyomino) (bits : List Bool) : Nat :=
  exactTranslationSquareCount family (PakFixedWeightedStandardBinaryCount.value bits)

theorem placement_cells (family : Finset Polyomino) (p : Placement ↥family) :
    Placement.cells (fun P : ↥family => P.val) p=translate p.tile.val p.shift := rfl

theorem fixed_square_count (side : Nat) :
    exactTranslationSquareCount PakFixedWeightedRegisterInventory.tileFamily side=
      PakFixedWeightedShapeFamily.squareCount side := by
  change Nat.card (Tiling PakFixedWeightedShapeFamily.shapeSupport (square side))=
    PakFixedWeightedShapeFamily.squareCount side
  exact Nat.card_eq_fintype_card

theorem fixed_binary_count (bits : List Bool) :
    binaryTranslationSquareCount PakFixedWeightedRegisterInventory.tileFamily bits=
      PakFixedWeightedStandardBinaryCount.binarySquareCount bits :=
  fixed_square_count _

theorem fixed_binary_count_function :
    binaryTranslationSquareCount PakFixedWeightedRegisterInventory.tileFamily=
      PakFixedWeightedStandardBinaryCount.binarySquareCount :=
  funext fixed_binary_count

theorem fixed_geometry_and_count_spec :
    PakFixedWeightedRegisterInventory.tileFamily.Nonempty ∧
    (∀ P ∈ PakFixedWeightedRegisterInventory.tileFamily,P.Nonempty ∧ FourConnected P) ∧
    (∀ side, exactTranslationSquareCount PakFixedWeightedRegisterInventory.tileFamily side=
      PakFixedWeightedShapeFamily.squareCount side) ∧
    (∀ bits, binaryTranslationSquareCount PakFixedWeightedRegisterInventory.tileFamily bits=
      PakFixedWeightedStandardBinaryCount.binarySquareCount bits) :=
  ⟨PakFixedWeightedShapeFamily.tile_family_nonempty,
    PakFixedWeightedRegisterInventory.tile_family_members,fixed_square_count,fixed_binary_count⟩

end
end PakFixedPolyomino.PakFixedShapeExactCountingModel
