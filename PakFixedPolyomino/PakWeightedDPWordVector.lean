import PakFixedPolyomino.StandardBitWordVector
import PakFixedPolyomino.PakWeightedScannerDPBinaryWidths

/-! A single fixed ordering of the ORIGINAL scanner/head-budget coordinates.
Packing keeps every coordinate as ordinary canonical binary in nested pairs.
Fixed-coordinate extraction and initialization have actual tape compilers;
the whole-vector width bounds are numerical storage bounds, not DP runtime. -/
namespace PakFixedPolyomino.PakWeightedDPWordVector
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition
open PakScannerBaselineDP PakWeightedScannerDP PakWeightedScannerDPBinaryWidths
open StandardNondeterministicMachine (Machine)

def basis : List BudgetState := (Finset.univ : Finset BudgetState).toList
def index (sb : BudgetState) : Nat := basis.idxOf sb

def pack (v : BudgetState → Nat) : List Bool :=
  StandardBitWordVector.encode (basis.map fun sb => encodeNat (v sb))

def coordinate (sb : BudgetState) : List Bool → List Bool :=
  StandardBitWordVector.field (index sb)

theorem basis_mem (sb : BudgetState) : sb ∈ basis := by simp [basis]
theorem basis_length : basis.length=Fintype.card BudgetState := by
  simp only [basis,Finset.length_toList,Finset.card_univ]

theorem coordinate_pack (sb : BudgetState) (v : BudgetState → Nat) :
    coordinate sb (pack v)=encodeNat (v sb) := by
  unfold coordinate pack index
  rw [StandardBitWordVector.field_encode,List.getElem?_map,List.getElem?_idxOf (basis_mem sb)]
  rfl

theorem coordinate_original_value (sb : BudgetState) (v : BudgetState → Nat) :
    PakFixedWeightedStandardBinaryCount.value (coordinate sb (pack v))=v sb := by
  rw [coordinate_pack,PakFixedWeightedStandardBinaryCount.value_encode_nat]

theorem coordinate_polyBitTime (sb : BudgetState) : PolyBitTime (coordinate sb) :=
  StandardBitWordVector.field_polyBitTime (index sb)

theorem pack_length_le (v : BudgetState → Nat) (B : Nat)
    (hv : ∀ sb,(encodeNat (v sb)).length ≤ B) :
    (pack v).length ≤ basis.length*(2*B+1) := by
  have h : ∀ w ∈ basis.map (fun sb => encodeNat (v sb)),w.length ≤ B := by
    intro w hw
    obtain ⟨sb,_,rfl⟩ := List.mem_map.mp hw
    exact hv sb
  have ht := StandardBitWordVector.encode_length_le _ B h
  simpa only [pack,List.length_map] using ht

theorem fold_length (n k : Nat) :
    (pack (weightedFold n k)).length ≤ basis.length*(2*(growthBase*k+1)+1) :=
  pack_length_le _ _ (fold_bits_length n k)

theorem guarded_fold_length {ns nt : Nat} (M : Machine ns nt 2) (p : Polynomial Nat)
    (raw x bits : List Bool) (hpair : StandardBitMetric.unpairBits raw=some (x,bits))
    (hguard : PakFixedWeightedOracleLengthGuard.macroSide M p x < bits.length)
    (k : Nat) (hk : k ≤ PakFixedWeightedOracleLengthGuard.macroSide M p x) :
    (pack (weightedFold (PakFixedWeightedOracleLengthGuard.macroSide M p x) k)).length ≤
      basis.length*(2*(growthBase*raw.length+1)+1) :=
  pack_length_le _ _ (fun sb => guarded_pair_counter_width M p raw x bits hpair hguard k hk sb)

theorem initial_polyBitTime : PolyBitTime (fun _ : List Bool => pack initialVector) := by
  have h := polyBitTime_comp StandardBitPairSanitize.empty_polyBitTime
    (StandardBitPrepend.fixed_prefix_polyBitTime (pack initialVector))
  simpa only [Function.comp_def,List.append_nil] using h

end
end PakFixedPolyomino.PakWeightedDPWordVector
