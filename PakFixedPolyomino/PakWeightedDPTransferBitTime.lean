import PakFixedPolyomino.PakWeightedDPWordVector
import PakFixedPolyomino.StandardBitFixedMultiply
import PakFixedPolyomino.StandardBitVariableAdd

/-! The ORIGINAL weighted scanner transfer is compiled from fixed-coordinate
access, fixed multiplication, ordinary pairing and variable addition. The
variable adder's actual PolyBitTime remains an explicit stage hypothesis;
this module does not assert that the currently unfinished adder runs.
-/
set_option maxRecDepth 4096

namespace PakFixedPolyomino.PakWeightedDPTransferBitTime
noncomputable section
open Computability StandardBitTime StandardBitMetric StandardBitTimeComposition
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open PakScannerBaselineDP PakScannerBaselineAutomaton PakWeightedScannerDP
open PakWeightedDPWordVector (basis pack coordinate coordinate_pack coordinate_original_value coordinate_polyBitTime)

def sumFields : List (List Bool → List Bool) → List Bool → List Bool
  | [] => fun _ => []
  | f::fs => fun raw => StandardBitVariableAdd.addBits (pairBits (f raw) (sumFields fs raw))

theorem sumFields_canonical (fs : List (List Bool → List Bool)) (raw : List Bool) :
    sumFields fs raw=encodeNat ((fs.map fun f => value (f raw)).sum) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [sumFields,StandardBitVariableAdd.add_pair,ih,value_encode_nat,List.map_cons,List.sum_cons]

theorem sumFields_polyBitTime (fs : List (List Bool → List Bool))
    (hadd : PolyBitTime StandardBitVariableAdd.addBits)
    (hf : ∀ f ∈ fs,PolyBitTime f) : PolyBitTime (sumFields fs) := by
  induction fs with
  | nil => exact StandardBitPairSanitize.empty_polyBitTime
  | cons f fs ih =>
    have ht := StandardBitPairMaps.parallel_polyBitTime f (sumFields fs)
      (hf f (by simp)) (ih (fun g hg => hf g (by simp [hg])))
    have hc := polyBitTime_comp ht hadd
    simpa only [sumFields,Function.comp_def,StandardBitPairMaps.parallel_pair] using hc

def coefficient (bit : Bool) (source target : BudgetState) : Nat :=
  if ConcretePakScanner.LegalScan source.1 target.1 bit ∧
      addHead (stateHead source.1) source.2=target.2
  then edgeWeight source.1 target.1 else 0

def term (bit : Bool) (source target : BudgetState) (raw : List Bool) : List Bool :=
  encodeNat (coefficient bit source target * value (coordinate source raw))

theorem term_polyBitTime (bit : Bool) (source target : BudgetState) : PolyBitTime (term bit source target) :=
  polyBitTime_comp (coordinate_polyBitTime source)
    (StandardBitFixedMultiply.fixed_multiply_polyBitTime (coefficient bit source target))

def coordinateStep (bit : Bool) (target : BudgetState) : List Bool → List Bool :=
  sumFields (basis.map fun source => term bit source target)

theorem coordinateStep_polyBitTime (bit : Bool) (target : BudgetState)
    (hadd : PolyBitTime StandardBitVariableAdd.addBits) : PolyBitTime (coordinateStep bit target) := by
  apply sumFields_polyBitTime _ hadd
  intro f hf
  obtain ⟨source,_,rfl⟩ := List.mem_map.mp hf
  exact term_polyBitTime bit source target

def transferBits (bit : Bool) : List Bool → List Bool :=
  StandardBitWordVector.assemble (basis.map fun target => coordinateStep bit target)

theorem transfer_polyBitTime (bit : Bool)
    (hadd : PolyBitTime StandardBitVariableAdd.addBits) : PolyBitTime (transferBits bit) := by
  apply StandardBitWordVector.assemble_polyBitTime
  intro f hf
  obtain ⟨target,_,rfl⟩ := List.mem_map.mp hf
  exact coordinateStep_polyBitTime bit target hadd

theorem basis_sum (g : BudgetState → Nat) : (basis.map g).sum=∑ sb,g sb := by
  classical
  exact Finset.sum_map_toList Finset.univ g

theorem coordinateStep_pack (bit : Bool) (target : BudgetState) (v : BudgetState → Nat) :
    coordinateStep bit target (pack v)=encodeNat (transfer bit v target) := by
  rw [coordinateStep,sumFields_canonical]
  simp only [List.map_map,Function.comp_def,term,value_encode_nat,coordinate_original_value]
  rw [basis_sum]
  apply congrArg encodeNat
  calc
    (∑ sb : BudgetState,coefficient bit sb target*v sb) =
        ∑ source : ConcretePakScanner.State,∑ old : HeadBudget,coefficient bit (source,old) target*v (source,old) :=
      Fintype.sum_prod_type _
    _ = transfer bit v target := by
      unfold transfer
      apply Finset.sum_congr rfl
      intro source _
      apply Finset.sum_congr rfl
      intro old _
      simp only [coefficient]
      split_ifs <;> simp only [Nat.mul_comm,Nat.zero_mul]

theorem transfer_pack (bit : Bool) (v : BudgetState → Nat) :
    transferBits bit (pack v)=pack (transfer bit v) := by
  unfold transferBits StandardBitWordVector.assemble pack
  congr 1
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro target _
  exact coordinateStep_pack bit target v

end
end PakFixedPolyomino.PakWeightedDPTransferBitTime
