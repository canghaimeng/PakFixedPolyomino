import PakFixedPolyomino.PakWeightedDPTransferBitTime
import PakFixedPolyomino.PakGuardComparatorBitTimeClosed
import PakFixedPolyomino.StandardBitInitializedFlagLoop
import PakFixedPolyomino.StandardBitBoundedPower
import PakFixedPolyomino.StandardBitHalveAlignment
import PakFixedPolyomino.StandardBitHeadAlignment

/-! The ORIGINAL weighted scanner DP is iterated by a fixed ordinary tape
program. Its counter and every vector coordinate are bounded in the ORIGINAL
raw input length by the original literal-answer guard. The only remaining
physical compiler premise is the unfinished ordinary variable adder. -/
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace PakFixedPolyomino.PakWeightedDPIterationBitTime
noncomputable section
open Computability StandardBitTime StandardBitMetric StandardBitTimeComposition
open StandardNondeterministicMachine (Machine)
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open PakWeightedScannerDP PakScannerBaselineDP
open PakWeightedDPWordVector (basis pack coordinate coordinate_pack)
open StandardBitWordVector (field assemble field_polyBitTime)
open PakGuardCounterBitTimeClosed (counterBits counter_polyBitTime counter_value_pair)
open PakGuardComparatorBitTimeClosed (predicate predicate_pair predicate_none predicate_polyBitTime)

variable {ns nt : Nat}

def side (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) : Nat :=
  if predicate M p raw then value (counterBits M p raw) else 0

def sideBits (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) : List Bool :=
  if predicate M p raw then counterBits M p raw else []

def target : BudgetState := (ConcretePakScanner.topNorth,HeadBudget.one)
def frame (m : Nat) (digits : List Bool) (v : BudgetState → Nat) : List Bool :=
  StandardBitWordVector.encode [encodeNat m,digits,pack v]

def init (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) : List Bool :=
  frame (side M p raw) (encodeNat (side M p raw)) initialVector

def dpBits (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) : List Bool :=
  encodeNat (weightedAccept (side M p raw))

theorem side_le (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) :
    side M p raw≤raw.length := by
  cases h : unpairBits raw with
  | none => simp [side,predicate_none M p raw h]
  | some xy =>
    obtain ⟨x,y⟩ := xy
    rw [StandardBitPairProjection.unpairBits_eq_some.mp h]
    simp only [side,predicate_pair,counter_value_pair]
    split_ifs with hg
    · have ht : PakFixedWeightedOracleLengthGuard.macroSide M p x<y.length := of_decide_eq_true hg
      rw [pairBits_length]
      omega
    · exact Nat.zero_le _

theorem sideBits_eq (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool) :
    sideBits M p raw=encodeNat (side M p raw) := by
  have hc : counterBits M p raw=encodeNat (value (counterBits M p raw)) := by
    unfold counterBits
    simp only [Function.comp_apply,PakMacroSideBitTimeClosed.macroBits_eq_encode,value_encode_nat]
  unfold sideBits side
  split_ifs
  · exact hc
  · rfl

theorem sideBits_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat) :
    PolyBitTime (sideBits M p) := by
  exact StandardBitConditionalBitTime.conditional_polyBitTime (predicate M p)
    (fun _ => []) (counterBits M p) (predicate_polyBitTime M p)
    StandardBitPairSanitize.empty_polyBitTime (counter_polyBitTime M p)

theorem init_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat) : PolyBitTime (init M p) := by
  have h := StandardBitWordVector.assemble_polyBitTime
    [sideBits M p,sideBits M p,fun _ => pack initialVector] (by
      intro f hf
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
      rcases hf with rfl|rfl|rfl
      · exact sideBits_polyBitTime M p
      · exact sideBits_polyBitTime M p
      · exact PakWeightedDPWordVector.initial_polyBitTime)
  have heq : assemble [sideBits M p,sideBits M p,fun _ => pack initialVector]=init M p := by
    funext raw
    simp only [assemble,List.map_cons,List.map_nil,init,frame,sideBits_eq]
  rwa [heq] at h

def stepVector (raw : List Bool) : List Bool :=
  if (field 1 raw).headD false then PakWeightedDPTransferBitTime.transferBits true (field 2 raw)
  else PakWeightedDPTransferBitTime.transferBits false (field 2 raw)

def next (raw : List Bool) : List Bool :=
  assemble [fun w => encodeNat (value (field 0 w)-1),fun w => (field 1 w).tail,stepVector] raw

def body (raw : List Bool) : List Bool :=
  if StandardBitZero.zeroBit (field 0 raw) then false::coordinate target (field 2 raw)
  else true::next raw

theorem stepVector_polyBitTime (hadd : PolyBitTime StandardBitVariableAdd.addBits) :
    PolyBitTime stepVector := by
  have hb := polyBitTime_comp (field_polyBitTime 1) StandardBitHead.head_polyBitTime
  have ht := polyBitTime_comp (field_polyBitTime 2) (PakWeightedDPTransferBitTime.transfer_polyBitTime true hadd)
  have hf := polyBitTime_comp (field_polyBitTime 2) (PakWeightedDPTransferBitTime.transfer_polyBitTime false hadd)
  exact StandardBitConditionalBitTime.conditional_polyBitTime (fun raw => (field 1 raw).headD false)
    (PakWeightedDPTransferBitTime.transferBits false ∘ field 2)
    (PakWeightedDPTransferBitTime.transferBits true ∘ field 2) hb hf ht

theorem next_polyBitTime (hadd : PolyBitTime StandardBitVariableAdd.addBits) : PolyBitTime next := by
  have hp := polyBitTime_comp (field_polyBitTime 0) StandardBitCanonicalDecrement.predecessor_polyBitTime
  have ht := polyBitTime_comp (field_polyBitTime 1) StandardBitHalve.halve_polyBitTime
  apply StandardBitWordVector.assemble_polyBitTime
  intro f hf
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact hp
  · exact ht
  · exact stepVector_polyBitTime hadd

theorem body_polyBitTime (hadd : PolyBitTime StandardBitVariableAdd.addBits) : PolyBitTime body := by
  have hz := polyBitTime_comp (field_polyBitTime 0) StandardBitZero.zero_polyBitTime
  have hc := polyBitTime_comp (field_polyBitTime 2) (PakWeightedDPWordVector.coordinate_polyBitTime target)
  have hs := polyBitTime_comp hc (StandardBitPrepend.prepend_polyBitTime false)
  have hn := polyBitTime_comp (next_polyBitTime hadd) (StandardBitPrepend.prepend_polyBitTime true)
  exact StandardBitConditionalBitTime.conditional_polyBitTime
    (fun raw => StandardBitZero.zeroBit (field 0 raw))
    (List.cons true ∘ next) (List.cons false ∘ (coordinate target ∘ field 2)) hz hn hs

theorem field_frame (m : Nat) (digits : List Bool) (v : BudgetState → Nat) :
    field 0 (frame m digits v)=encodeNat m ∧
    field 1 (frame m digits v)=digits ∧ field 2 (frame m digits v)=pack v := by
  simp [frame,StandardBitWordVector.field_encode]

theorem head_drop (w : List Bool) (k : Nat) : (w.drop k).headD false=(value w).testBit k := by
  induction k generalizing w with
  | zero =>
    simp only [List.drop_zero,Nat.testBit_zero,← StandardBitHeadAlignment.head_original_value]
    cases w.headD false <;> rfl
  | succ k ih =>
    rw [Nat.testBit_add_one,← StandardBitHalveAlignment.halve_original_value w]
    simpa only [StandardBitHalve.halveBits,List.drop_tail] using ih w.tail

theorem body_zero (digits : List Bool) (v : BudgetState → Nat) :
    body (frame 0 digits v)=false::encodeNat (v target) := by
  simp only [body,(field_frame 0 digits v).1,(field_frame 0 digits v).2.2,
    coordinate_pack]
  rfl

theorem body_succ (n m k : Nat) :
    body (frame (m+1) ((encodeNat n).drop k) (weightedFold n k))=
      true::frame m ((encodeNat n).drop (k+1)) (weightedFold n (k+1)) := by
  have h := field_frame (m+1) ((encodeNat n).drop k) (weightedFold n k)
  simp only [body,h.1,StandardBitBoundedPower.zero_succ,Bool.false_eq_true,if_false,
    next,assemble,List.map_cons,List.map_nil,h.1,h.2.1,h.2.2,value_encode_nat,Nat.add_sub_cancel,
    stepVector,h.2.1,h.2.2,head_drop,value_encode_nat]
  have ht : (if n.testBit k then PakWeightedDPTransferBitTime.transferBits true (pack (weightedFold n k))
      else PakWeightedDPTransferBitTime.transferBits false (pack (weightedFold n k)))=
      pack (weightedFold n (k+1)) := by
    cases hb : n.testBit k <;> simp only [hb,Bool.false_eq_true,if_false,if_true,
      PakWeightedDPTransferBitTime.transfer_pack,weightedFold_succ]
  rw [ht]
  simp only [frame,List.tail_drop]

noncomputable def lengthBound (N : Nat) : Nat :=
  (4+4*basis.length*growthBase)*N+7+6*basis.length

theorem frame_length (N n m k : Nat) (hn : n≤N) (hm : m+k=n) :
    (frame m ((encodeNat n).drop k) (weightedFold n k)).length≤lengthBound N := by
  have hc := StandardBinaryFixedMultiplyWord.encode_nat_length_le m
  have hd : ((encodeNat n).drop k).length≤n :=
    (show ((encodeNat n).drop k).length≤(encodeNat n).length by rw [List.length_drop];omega).trans
      (StandardBinaryFixedMultiplyWord.encode_nat_length_le n)
  have hv := PakWeightedDPWordVector.fold_length n k
  have hk : k≤N := by omega
  have hmc : m≤N := by omega
  have hg := Nat.mul_le_mul_left growthBase hk
  have hw := Nat.mul_le_mul_left basis.length (show 2*(growthBase*k+1)+1≤2*(growthBase*N+1)+1 by omega)
  simp only [frame,StandardBitWordVector.encode_length,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil] at *
  unfold lengthBound
  nlinarith

theorem eval (N n m k : Nat) (hn : n≤N) (hm : m+k=n) :
    StandardBitFlagLoop.Eval body (lengthBound N)
      (frame m ((encodeNat n).drop k) (weightedFold n k))
      (encodeNat (weightedAccept n)) (m+1) := by
  induction m generalizing k with
  | zero =>
    have he : k=n := by omega
    subst k
    simpa only [body_zero,List.tail_cons,weightedAccept,target] using
      (StandardBitFlagLoop.Eval.stop (frame_length N n 0 n hn hm)
        (by rw [body_zero];rfl) : StandardBitFlagLoop.Eval body (lengthBound N)
        (frame 0 ((encodeNat n).drop n) (weightedFold n n))
        (body (frame 0 ((encodeNat n).drop n) (weightedFold n n))).tail 1)
  | succ m ih =>
    have hnext := ih (k+1) (by omega)
    have he : (body (frame (m+1) ((encodeNat n).drop k) (weightedFold n k))).tail=
        frame m ((encodeNat n).drop (k+1)) (weightedFold n (k+1)) := by
      rw [body_succ,List.tail_cons]
    exact StandardBitFlagLoop.Eval.next (frame_length N n (m+1) k hn hm)
      (by rw [body_succ];rfl) (he.symm ▸ hnext)

theorem dp_polyBitTime (M : Machine ns nt 2) (p : Polynomial Nat)
    (hadd : PolyBitTime StandardBitVariableAdd.addBits) : PolyBitTime (dpBits M p) := by
  apply StandardBitInitializedFlagLoop.polyBitTime (init M p) body (dpBits M p)
    (init_polyBitTime M p) (body_polyBitTime hadd)
    (Polynomial.C (4+4*basis.length*growthBase)*Polynomial.X+Polynomial.C (7+6*basis.length))
    (Polynomial.X+1)
  intro raw
  refine ⟨side M p raw+1,?_,?_⟩
  · have h := eval raw.length (side M p raw) (side M p raw) 0 (side_le M p raw) (by omega)
    simpa only [init,dpBits,lengthBound,List.drop_zero,weightedFold_zero,Nat.add_assoc,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using h
  · simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using
      Nat.add_le_add_right (side_le M p raw) 1

theorem dp_pair (M : Machine ns nt 2) (p : Polynomial Nat) (x y : List Bool) :
    dpBits M p (pairBits x y)=encodeNat (weightedAccept
      (if PakFixedWeightedOracleLengthGuard.macroSide M p x<y.length
      then PakFixedWeightedOracleLengthGuard.macroSide M p x else 0)) := by
  simp only [dpBits,side,predicate_pair,counter_value_pair,decide_eq_true_eq]

theorem dp_none (M : Machine ns nt 2) (p : Polynomial Nat) (raw : List Bool)
    (h : unpairBits raw=none) : dpBits M p raw=[] := by
  simp only [dpBits,side,predicate_none M p raw h,Bool.false_eq_true,if_false,weightedAccept_zero]
  rfl

theorem dp_pair_baseline (M : Machine ns nt 2) (p : Polynomial Nat) (x y : List Bool) :
    dpBits M p (pairBits x y)=encodeNat
      (if PakFixedWeightedOracleLengthGuard.macroSide M p x<y.length
      then PakWeightedFullFrameStandardFirstBranch.weightedBaselineCount
        (PakFixedWeightedOracleLengthGuard.macroSide M p x) else 0) := by
  rw [dp_pair,weightedAccept_eq_weightedBaselineCount]
  split_ifs
  · rfl
  · rw [weightedBaselineCount_zero]

theorem dp_spec (M : Machine ns nt 2) (p : Polynomial Nat)
    (hadd : PolyBitTime StandardBitVariableAdd.addBits) :
    PolyBitTime (dpBits M p) ∧
    (∀ x y,dpBits M p (pairBits x y)=encodeNat
      (if PakFixedWeightedOracleLengthGuard.macroSide M p x<y.length
      then PakWeightedFullFrameStandardFirstBranch.weightedBaselineCount
        (PakFixedWeightedOracleLengthGuard.macroSide M p x) else 0)) ∧
    (∀ raw,unpairBits raw=none → dpBits M p raw=[]) :=
  ⟨dp_polyBitTime M p hadd,dp_pair_baseline M p,dp_none M p⟩

end
end PakFixedPolyomino.PakWeightedDPIterationBitTime
