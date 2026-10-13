import PakFixedPolyomino.TilingRelabelEquiv
import PakFixedPolyomino.PakFixedWeightedPhysicalSourceReadout

/-! Exact model alignment with the finite SET of physical shapes: indices
create no extra copies, and every shape-set tiling remains in the count. -/
namespace PakFixedPolyomino.PakFixedWeightedShapeFamily
noncomputable section
open PakFixedWeightedRegisterInventory (Tile support tileFamily)
open PakFixedWeightedPhysicalSourceReadout
open StandardNondeterministicMachine (Machine RunsAtMost acceptingCount SharpEXP)
local instance tileDecidableEq : DecidableEq Tile := Classical.decEq _

abbrev Shape := ↥tileFamily

theorem tile_family_nonempty : tileFamily.Nonempty := by
  classical
  exact ⟨support (none : Tile), Finset.mem_image.mpr ⟨none, Finset.mem_univ _, rfl⟩⟩

def shapeEquiv : Tile ≃ Shape := Equiv.ofBijective
  (fun t => ⟨support t, by
    classical
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩⟩)
  (by
    constructor
    · intro t u same
      have supports := congrArg Subtype.val same
      have translated : translate (support t) (0, 0) = translate (support u) (0, 0) := by
        simpa only [translate_zero] using supports
      exact (PakFixedWeightedRegisterInventory.translated_support_injective translated).1
    · intro P
      obtain ⟨t, _, same⟩ := Finset.mem_image.mp P.property
      exact ⟨t, Subtype.ext same⟩)

theorem shape_equiv_support (t : Tile) : (shapeEquiv t).val = support t := rfl

def shapeSupport (P : Shape) : Polyomino := P.val

theorem shape_nonempty (P : Shape) : (shapeSupport P).Nonempty :=
  (PakFixedWeightedRegisterInventory.tile_family_members P.val P.property).1

theorem shape_connected (P : Shape) : FourConnected (shapeSupport P) :=
  (PakFixedWeightedRegisterInventory.tile_family_members P.val P.property).2

def tilingEquiv (region : Polyomino) : Tiling support region ≃ Tiling shapeSupport region :=
  TilingRelabelEquiv.equiv shapeEquiv support shapeSupport shape_equiv_support region

instance shapeTilingsFintype (n : Nat) : Fintype (Tiling shapeSupport (square n)) :=
  tilingFintype shapeSupport (square n) shape_nonempty

def squareCount (n : Nat) : Nat := Fintype.card (Tiling shapeSupport (square n))

theorem square_count_eq_indexed (n : Nat) :
    squareCount n = PakFixedWeightedRegisterInventory.squareCount n :=
  (Fintype.card_congr (tilingEquiv (square n))).symm

theorem physical_source_readout {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) :
    sourceAnswer M p x (squareCount (sourceSide M p x)) =
      acceptingCount M x (2 ^ p.eval x.length) := by
  rw [square_count_eq_indexed]
  exact PakFixedWeightedPhysicalSourceReadout.physical_source_readout M p x ht

theorem standard_sharp_exp_physical_source_readout (f : List Bool → Nat) (hf : SharpEXP f) :
    ∃ ns nt, ∃ M : Machine ns nt 2, ∃ p : Polynomial Nat,
      ∀ x, sourceAnswer M p x (squareCount (sourceSide M p x)) = f x := by
  obtain ⟨ns, nt, M, p, h⟩ :=
    PakFixedWeightedPhysicalSourceReadout.standard_sharp_exp_physical_source_readout f hf
  refine ⟨ns, nt, M, p, ?_⟩
  intro x
  rw [square_count_eq_indexed]
  exact h x

def fixed_shape_family_spec : Prop :=
  tileFamily.Nonempty ∧
  (∀ P : Shape, (shapeSupport P).Nonempty ∧ FourConnected (shapeSupport P)) ∧
  (∀ n, squareCount n = PakFixedWeightedRegisterInventory.squareCount n) ∧
  (∀ f : List Bool → Nat, SharpEXP f →
    ∃ ns nt, ∃ M : Machine ns nt 2, ∃ p : Polynomial Nat,
      ∀ x, sourceAnswer M p x (squareCount (sourceSide M p x)) = f x)

theorem fixed_shape_family_spec_holds : fixed_shape_family_spec :=
  ⟨tile_family_nonempty, fun P => ⟨shape_nonempty P, shape_connected P⟩,
    square_count_eq_indexed, standard_sharp_exp_physical_source_readout⟩

end
end PakFixedPolyomino.PakFixedWeightedShapeFamily
