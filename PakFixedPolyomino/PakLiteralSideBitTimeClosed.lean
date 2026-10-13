import PakFixedPolyomino.PakLiteralSideBitTimeAssembly
import PakFixedPolyomino.StandardBitReverseClosed

/-! Actual polynomial bit time for the unchanged original instance map. -/
namespace PakFixedPolyomino.PakLiteralSideBitTimeClosed
open StandardBitTime PakFixedPitchBinaryInstance
open StandardNondeterministicMachine (Machine)

theorem instanceBits_polyBitTime {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (instanceBits M p) :=
  PakLiteralSideBitTimeAssembly.instanceBits_polyBitTime
    StandardBitReverseClosed.reverse_polyBitTime M p

theorem unchanged_instance_bit_spec :
    ∀ ns nt (M : Machine ns nt 2) (p : Polynomial Nat),
      PolyBitTime (instanceBits M p) ∧
      (∀ x,instanceBits M p x =
        Computability.encodeNat (PakFixedWeightedPhysicalSourceReadout.sourceSide M p x)) :=
  PakLiteralSideBitTimeAssembly.unchanged_instance_bit_spec
    StandardBitReverseClosed.reverse_polyBitTime

end PakFixedPolyomino.PakLiteralSideBitTimeClosed
