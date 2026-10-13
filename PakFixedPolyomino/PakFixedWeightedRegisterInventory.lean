import PakFixedPolyomino.PakWeightedRegisterRectangleBound
import PakFixedPolyomino.PakFixedCoefficientAllCapacityNatCensus
import PakFixedPolyomino.PakCompleteReadout

/-! ONE fixed connected translation-only register inventory for the original
weighted Wang system. The square counting function is defined on EVERY side,
including zero. The physical readout is arithmetic; bit-time and #EXP
membership/hardness are separate obligations. -/
namespace PakFixedPolyomino.PakFixedWeightedRegisterInventory
noncomputable section
set_option maxRecDepth 100000
open PakWeightedCoupledInventory PakWeightedCoupledCoefficient
open PakCoupledCoefficient (Machine Coupled CoupledTiling)

def liveWangTile := weightedCoupledWangTile weightedExtractionQ
def wangTile := withDummyWangTile liveWangTile

def unweightedRectangleBase : Nat :=
  PakWeightedRegisterRectangleBound.unweightedRectangleBase weightedExtractionQ

theorem unweighted_rectangle_base_ge_two : 2 ≤ unweightedRectangleBase :=
  PakWeightedRegisterRectangleBound.unweighted_rectangle_base_ge_two weightedExtractionQ

def liveRectangleBase : Nat :=
  PakWeightedRegisterRectangleBound.liveRectangleBase weightedExtractionQ

theorem live_rectangle_base_pos : 0 < liveRectangleBase :=
  PakWeightedRegisterRectangleBound.live_rectangle_base_pos weightedExtractionQ

def liveRectangleBound : WangRectangleBound liveRectangleBase liveWangTile :=
  PakWeightedRegisterRectangleBound.liveRectangleBound weightedExtractionQ

def rectangleBase : Nat :=
  PakWeightedRegisterRectangleBound.rectangleBase weightedExtractionQ

theorem rectangle_base_ge_two : 2 ≤ rectangleBase :=
  PakWeightedRegisterRectangleBound.rectangle_base_ge_two weightedExtractionQ

def rectangleBound : WangRectangleBound rectangleBase wangTile :=
  PakWeightedRegisterRectangleBound.rectangleBound weightedExtractionQ

def params : RegisterParams :=
  registerParamsOfWang wangTile rectangleBase rectangle_base_ge_two

abbrev Tile := RegisterTile params

local instance tileDecidableEq : DecidableEq Tile := Classical.decEq _

def support : Tile → Polyomino := registerTileSupport params

theorem support_nonempty (t : Tile) : (support t).Nonempty :=
  registerTileSupport_nonempty params t

theorem support_connected (t : Tile) : FourConnected (support t) :=
  registerTileSupport_fourConnected params t

theorem translated_support_injective {t t' : Tile} {a b : Cell}
    (same : translate (support t) a = translate (support t') b) :
    t = t' ∧ a = b :=
  registerTile_geometric_injective params same

def tileFamily : Finset Polyomino := Finset.univ.image support

theorem tile_family_members (P : Polyomino) (member : P ∈ tileFamily) :
    P.Nonempty ∧ FourConnected P := by
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp member
  exact ⟨support_nonempty t, support_connected t⟩

instance tilingsFintype (side : Nat) : Fintype (Tiling support (square side)) :=
  tilingFintype support (square side) support_nonempty

def squareCount (side : Nat) : Nat := Fintype.card (Tiling support (square side))

theorem physical_floor_readout (n : Nat) (hn : 2 ≤ n) :
    squareCount (params.pitch * n) / params.amp ^ amplifierExponent n =
      openWangCount wangTile n n := by
  have bound : WangRectangleBound params.perimeterBase (registerWangTile params) :=
    registerParamsOfWang.rectangleBound wangTile rectangleBase rectangle_base_ge_two rectangleBound
  have physical := physical_floor_readout_of_dissection_and_wang params hn
    (concreteRectangularDissectionFacts n (by omega)) bound
  exact physical.trans
    (openWangCount_registerParamsOfWang wangTile rectangleBase rectangle_base_ge_two n n)

theorem physical_live_readout (n : Nat) (hn : 2 ≤ n) :
    squareCount (params.pitch * n) / params.amp ^ amplifierExponent n - 1 =
      openWangCount liveWangTile n n := by
  rw [physical_floor_readout n hn]
  change openWangCount (withDummyWangTile liveWangTile) n n - 1 = _
  rw [withDummyOpenCount_eq_add_one liveWangTile n n (by omega) (by omega)]
  omega

end
end PakFixedPolyomino.PakFixedWeightedRegisterInventory
