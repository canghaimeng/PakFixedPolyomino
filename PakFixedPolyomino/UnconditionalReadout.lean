import PakFixedPolyomino.AnchoredGridMacroData

/-!
# Final floor-readout integration

This module is the narrow assembly point.  It deliberately keeps the large
geometric decoder stable and combines its physical equivalence with the two
independent semantic certificates: the rectangular-dissection census and the
concrete Wang perimeter bound.
-/

namespace PakFixedPolyomino

noncomputable section

local instance unconditionalReadoutDecidableEqRegisterTile
    (P : RegisterParams) : DecidableEq (RegisterTile P) := Classical.decEq _

/-- Once the two independently checkable semantic facts are supplied, the
physical square count has the exact amplified floor readout.  There is no
decoder, realization, finite-sum, or amplifier-algebra premise left. -/
theorem physical_floor_readout_of_dissection_and_wang
    (P : RegisterParams) {n : ℕ} (hn : 2 ≤ n)
    (D : RectangularDissectionFacts n
      (wholePartition n (lt_of_lt_of_le (by decide) hn)))
    (W : WangRectangleBound P.perimeterBase (registerWangTile P)) :
    Fintype.card (Tiling (registerTileSupport P) (square (P.pitch * n))) /
        P.amp ^ amplifierExponent n =
      openWangCount (registerWangTile P) n n := by
  apply physical_floor_readout_of_rectangular_bounds P hn
  exact RectangularJunkBounds.ofDissectionAndWang n P.perimeterBase
    (registerWangTile P) (wholePartition n (lt_of_lt_of_le (by decide) hn)) D W

end
end PakFixedPolyomino
