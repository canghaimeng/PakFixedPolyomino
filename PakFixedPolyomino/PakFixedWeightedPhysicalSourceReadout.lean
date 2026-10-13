import PakFixedPolyomino.PakFixedWeightedRegisterInventory
import PakFixedPolyomino.PakAllFrameWeightedOrdinarySourceReadout
import PakFixedPolyomino.StandardMachineBinaryChoices

/-! Arithmetic extraction from ONE actual fixed connected translation-only
polyomino square count, for the entire standard #EXP source class. Effective
binary-choice normalization and all physical count certificates are supplied
internally. These arithmetic maps do not yet have bit-time certificates. -/
namespace PakFixedPolyomino.PakFixedWeightedPhysicalSourceReadout
noncomputable section
set_option maxRecDepth 100000
open StandardNondeterministicMachine (Machine RunsAtMost acceptingCount SharpEXP)
open ULogTernaryGeneratedMarginScanner (input)
open PakAllFrameWeightedOrdinarySourceReadout
open PakWeightedCoupledCoefficient PakWeightedCoupledInventory
open PakWeightedFullFrameStandardFirstBranch
open PakFixedWeightedRegisterInventory (params squareCount)
variable {ns nt : Nat}

def sourceSide (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool) : Nat :=
  params.pitch * ConcretePakSide.sideValue (input M p x)

def sourceAnswer (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool)
    (answer : Nat) : Nat :=
  ((answer / params.amp ^ amplifierExponent (ConcretePakSide.sideValue (input M p x)) - 1) /
    weightedExtractionQ ^ PakAmpCoefficient.BoundaryMask.full.qDegree
      (ConcretePakSide.sideValue (input M p x)) (ConcretePakSide.sideValue (input M p x)) -
    weightedBaselineCount (ConcretePakSide.sideValue (input M p x)) +
      sourceReadoutWeight M p x - 1) / sourceReadoutWeight M p x

theorem physical_source_readout (M : Machine ns nt 2) (p : Polynomial Nat)
    (x : List Bool) (ht : RunsAtMost M x (2 ^ p.eval x.length)) :
    sourceAnswer M p x (squareCount (sourceSide M p x)) =
      acceptingCount M x (2 ^ p.eval x.length) := by
  have hn : 2 ≤ ConcretePakSide.sideValue (input M p x) :=
    (by decide : 2 ≤ 5).trans (PakSideScanner.sideValue_ge_five (input M p x))
  have physical := PakFixedWeightedRegisterInventory.physical_live_readout _ hn
  have extracted := congrArg (fun k : Nat =>
    (k / weightedExtractionQ ^ PakAmpCoefficient.BoundaryMask.full.qDegree
      (ConcretePakSide.sideValue (input M p x)) (ConcretePakSide.sideValue (input M p x)) -
      weightedBaselineCount (ConcretePakSide.sideValue (input M p x)) +
        sourceReadoutWeight M p x - 1) / sourceReadoutWeight M p x) physical
  exact extracted.trans (fixed_wang_all_frame_source_readout M p x ht)

theorem standard_sharp_exp_physical_source_readout (f : List Bool → Nat)
    (hf : SharpEXP f) :
    ∃ ns nt, ∃ M : Machine ns nt 2, ∃ p : Polynomial Nat,
      ∀ x, sourceAnswer M p x (squareCount (sourceSide M p x)) = f x := by
  obtain ⟨ns, nt, M, p, hM⟩ := (StandardMachineBinaryChoices.sharpEXP_iff_binary f).mp hf
  refine ⟨ns, nt, M, p, ?_⟩
  intro x
  obtain ⟨ht, hc⟩ := hM x
  exact (physical_source_readout M p x ht).trans hc.symm

def fixed_physical_source_readout_spec : Prop :=
  (∀ P ∈ PakFixedWeightedRegisterInventory.tileFamily, P.Nonempty ∧ FourConnected P) ∧
  (∀ {t t' : PakFixedWeightedRegisterInventory.Tile} {a b : Cell},
    translate (PakFixedWeightedRegisterInventory.support t) a =
      translate (PakFixedWeightedRegisterInventory.support t') b → t = t' ∧ a = b) ∧
  (∀ (ns nt : Nat) (M : Machine ns nt 2) (p : Polynomial Nat) (x : List Bool),
    RunsAtMost M x (2 ^ p.eval x.length) →
      sourceAnswer M p x (squareCount (sourceSide M p x)) =
        acceptingCount M x (2 ^ p.eval x.length)) ∧
  (∀ f : List Bool → Nat, SharpEXP f →
    ∃ ns nt, ∃ M : Machine ns nt 2, ∃ p : Polynomial Nat,
      ∀ x, sourceAnswer M p x (squareCount (sourceSide M p x)) = f x)

theorem fixed_physical_source_readout_spec_holds : fixed_physical_source_readout_spec :=
  ⟨PakFixedWeightedRegisterInventory.tile_family_members,
    fun same => PakFixedWeightedRegisterInventory.translated_support_injective same,
    fun _ _ M p x ht => physical_source_readout M p x ht,
    standard_sharp_exp_physical_source_readout⟩

end
end PakFixedPolyomino.PakFixedWeightedPhysicalSourceReadout
