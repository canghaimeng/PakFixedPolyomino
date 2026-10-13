import PakFixedPolyomino.MStarULogAssembly
import PakFixedPolyomino.PakCompleteReadout

/-! A literal `Q = 1` diagnostic specialization of the M-star/ULog register.

This is a genuinely fixed finite polyomino family and is useful for checking
all enumerations and geometric readout maps.  It is not by itself the final
hardness target: the live Wang system also admits inactive amplifier frames,
so a later coefficient extraction (or a different sufficiently large fixed
`Q`) must isolate full computation frames. -/

namespace PakFixedPolyomino.FixedPakPolyomino

noncomputable section

set_option maxRecDepth 100000

abbrev State := MStarULogAssembly.State
abbrev Tape := MStarULogAssembly.Tape
abbrev Arrow := MStarULogAssembly.Arrow

/-- Diagnostic one-colour specialization.  It does not force amplifier
activity and therefore must not be used to identify all live tilings with
accepting computations. -/
def Q : ℕ := 1

instance : NeZero Q := ⟨by decide⟩

abbrev ScannerState := ConcretePakScanner.State
abbrev Machine := MStarULogAssembly.tableauData
abbrev Tracks := ConcreteWProd.Tracks Machine Q ScannerState

def couplingTable : ConcreteWProd.FiveCouplingTable Machine Q ScannerState :=
  MStarULogAssembly.fiveCouplings Q

def Coupled : Tracks → Prop :=
  ConcreteWProd.FiveCouplingTable.accepts Machine Q couplingTable

instance : DecidablePred Coupled :=
  fun _ => Classical.propDecidable _

/-- The fully enumerated, input-independent register parameters. -/
def params : RegisterParams :=
  ConcreteWProd.registerParams Machine Q Coupled

/-- The actual fixed finite tile type and polyomino family.  Only the square
size varies with the encoded source instance. -/
abbrev Tile := RegisterTile params

local instance fixedRegisterTileDecidableEq :
    DecidableEq
      (RegisterTile (ConcreteWProd.registerParams Machine Q Coupled)) :=
  Classical.decEq _

local instance : DecidableEq Tile := Classical.decEq _

def support : Tile → Polyomino := registerTileSupport params

theorem support_nonempty (t : Tile) : (support t).Nonempty :=
  registerTileSupport_nonempty params t

def wangTile := ConcreteWProd.wangTile Machine Q Coupled

def liveWangTile := wProdComputeTile Q
  (higherBlockTableauWangTile Machine) Coupled

theorem wangTile_eq_withDummy :
    wangTile = withDummyWangTile liveWangTile := rfl

theorem wangCount_eq_one_add_live {n : ℕ} (hn : 0 < n) :
    openWangCount wangTile n n =
      1 + openWangCount liveWangTile n n := by
  rw [wangTile_eq_withDummy]
  exact withDummyOpenCount_eq_add_one liveWangTile n n hn hn

theorem registerWangCount_eq_wangCount (n : ℕ) :
    openWangCount (registerWangTile params) n n =
      openWangCount wangTile n n := by
  unfold params ConcreteWProd.registerParams
  exact openWangCount_registerParamsOfWang wangTile
    (ConcreteWProd.perimeterBase Machine Q (ScanState := ScannerState))
    (ConcreteWProd.perimeterBase_ge_two Machine Q
      (ScanState := ScannerState)) n n

theorem registerWangCount_eq_one_add_live {n : ℕ} (hn : 0 < n) :
    openWangCount (registerWangTile params) n n =
      1 + openWangCount liveWangTile n n := by
  rw [registerWangCount_eq_wangCount]
  exact wangCount_eq_one_add_live hn

/-- The amplified square side attached to a macro side length. -/
def squareSide (n : ℕ) : ℕ := params.pitch * n

noncomputable instance tilingsFintype (n : ℕ) :
    Fintype (Tiling support (square (squareSide n))) :=
  tilingFintype support (square (squareSide n)) support_nonempty

/-- The fixed-target counting function before the floor postprocessor. -/
def tilingCount (n : ℕ) : ℕ :=
  Fintype.card (Tiling support (square (squareSide n)))

/-- Fully specialized physical floor readout for the fixed support. -/
theorem floorReadout {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card
        (Tiling
          (registerTileSupport
            (ConcreteWProd.registerParams Machine Q Coupled))
          (square
            ((ConcreteWProd.registerParams Machine Q Coupled).pitch * n))) /
        (ConcreteWProd.registerParams Machine Q Coupled).amp ^
          amplifierExponent n =
      openWangCount
        (registerWangTile
          (ConcreteWProd.registerParams Machine Q Coupled)) n n :=
  ConcreteWProd.physicalFloorReadoutUnconditional Machine Q Coupled hn

/-- The same fixed floor readout with the private dummy contribution exposed.
The dummy contributes exactly one; the remaining live count still includes
inactive/non-full-frame coupled tilings and is not yet an accepting-run count. -/
theorem floorReadout_live {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card
        (Tiling
          (registerTileSupport
            (ConcreteWProd.registerParams Machine Q Coupled))
          (square
            ((ConcreteWProd.registerParams Machine Q Coupled).pitch * n))) /
        (ConcreteWProd.registerParams Machine Q Coupled).amp ^
          amplifierExponent n =
      1 + openWangCount liveWangTile n n := by
  calc
    _ = openWangCount
        (registerWangTile
          (ConcreteWProd.registerParams Machine Q Coupled)) n n :=
      floorReadout hn
    _ = 1 + openWangCount liveWangTile n n :=
      registerWangCount_eq_one_add_live (lt_of_lt_of_le (by decide) hn)

theorem floorReadout_one :
    Fintype.card
        (Tiling
          (registerTileSupport
            (ConcreteWProd.registerParams Machine Q Coupled))
          (square
            ((ConcreteWProd.registerParams Machine Q Coupled).pitch * 1))) /
        (ConcreteWProd.registerParams Machine Q Coupled).amp ^
          amplifierExponent 1 =
      openWangCount
        (registerWangTile
          (ConcreteWProd.registerParams Machine Q Coupled)) 1 1 :=
  ConcreteWProd.physicalFloorReadoutOneUnconditional Machine Q Coupled

end

end PakFixedPolyomino.FixedPakPolyomino
