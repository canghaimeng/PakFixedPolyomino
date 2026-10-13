import PakFixedPolyomino.StandardBitHead
import PakFixedPolyomino.StandardBitDecrementAlignment

/-! The physical low-bit primitive uses the original usual positional value
on every literal word; no pinned noncanonical decoder is used. -/
namespace PakFixedPolyomino.StandardBitHeadAlignment

theorem head_original_value (w : List Bool) :
    (w.headD false).toNat=PakFixedWeightedStandardBinaryCount.value w % 2 := by
  rw [← StandardBitDecrementAlignment.value_eq_original]
  exact StandardBitHead.head_value w

theorem head_spec :
    StandardBitTime.PolyBitTime (fun w : List Bool => [w.headD false]) ∧
    ∀ w : List Bool, (w.headD false).toNat=PakFixedWeightedStandardBinaryCount.value w % 2 :=
  ⟨StandardBitHead.head_polyBitTime,head_original_value⟩

end PakFixedPolyomino.StandardBitHeadAlignment
