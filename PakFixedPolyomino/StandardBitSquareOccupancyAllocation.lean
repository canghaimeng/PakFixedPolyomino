import PakFixedPolyomino.StandardBitInitializedExponentialLoop
import PakFixedPolyomino.StandardBitVariableMultiplyLoop
import PakFixedPolyomino.StandardBitVariableAddClosed
import PakFixedPolyomino.StandardBitZero
import PakFixedPolyomino.StandardBitCanonicalDecrement
import PakFixedPolyomino.StandardBitBoundedPower

/-! A fixed ordinary deterministic tape machine physically allocates n^2
empty occupancy bits for EVERY original raw binary side word of value n.
Initialization computes binary n^2 by the actual multiplication compiler;
each subsequent epoch decrements its canonical counter and prepends a zero.
The exponential time bound, every frame bound and every iteration are proved
internally in ORIGINAL literal input length. This is a concrete grid primitive,
not the nondeterministic tiling machine or a membership certificate. -/
namespace PakFixedPolyomino.StandardBitSquareOccupancyAllocation
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition StandardBitMetric
open StandardNondeterministicMachine
open PakFixedWeightedStandardBinaryCount (value value_encode_nat value_lt_pow_length)
open StandardBitPairFirstCompaction (firstBits firstBits_pair first_polyBitTime)
open StandardBitPairProjection (secondBits secondBits_pair secondBits_polyBitTime)

def cells (raw : List Bool) : Nat := value raw*value raw
def allocation (raw : List Bool) : List Bool := List.replicate (cells raw) false
def frame (n k : Nat) : List Bool := pairBits (encodeNat n) (List.replicate k false)
def init (raw : List Bool) : List Bool := frame (cells raw) 0

theorem cells_polyBitTime : PolyBitTime (fun raw => encodeNat (cells raw)) := by
  have hp := StandardBitPairMaps.parallel_polyBitTime id id
    StandardBitTime.identity_polyBitTime StandardBitTime.identity_polyBitTime
  have h := polyBitTime_comp hp (StandardBitVariableMultiplyLoop.multiply_polyBitTime
    StandardBitVariableAddClosed.add_polyBitTime)
  have he : StandardBitVariableMultiplyLoop.multiplyBits ∘
      StandardBitPairMaps.parallel id id=(fun raw => encodeNat (cells raw)) := by
    funext raw
    simp only [Function.comp_apply,StandardBitPairMaps.parallel_pair,
      StandardBitVariableMultiplyLoop.multiply_pair,id_eq,cells]
  rwa [he] at h

theorem init_polyBitTime : PolyBitTime init := by
  have h := StandardBitPairMaps.parallel_polyBitTime (fun raw => encodeNat (cells raw))
    (fun _ => []) cells_polyBitTime StandardBitPairSanitize.empty_polyBitTime
  have he : StandardBitPairMaps.parallel (fun raw => encodeNat (cells raw))
      (fun _ => [])=init := by
    funext raw
    rw [StandardBitPairMaps.parallel_pair]
    rfl
  rwa [he] at h

def body (raw : List Bool) : List Bool :=
  if StandardBitZero.zeroBit (firstBits raw) then false::secondBits raw
  else true::pairBits (encodeNat (value (firstBits raw)-1)) (false::secondBits raw)

theorem body_polyBitTime : PolyBitTime body := by
  have hb := polyBitTime_comp first_polyBitTime StandardBitZero.zero_polyBitTime
  have hd := polyBitTime_comp first_polyBitTime StandardBitCanonicalDecrement.predecessor_polyBitTime
  have hz := polyBitTime_comp secondBits_polyBitTime (StandardBitPrepend.prepend_polyBitTime false)
  have hp := StandardBitPairMaps.parallel_polyBitTime
    (fun raw => encodeNat (value (firstBits raw)-1)) (fun raw => false::secondBits raw) hd hz
  have ht := polyBitTime_comp hp (StandardBitPrepend.prepend_polyBitTime true)
  have he : List.cons true ∘ StandardBitPairMaps.parallel
      (fun raw => encodeNat (value (firstBits raw)-1)) (fun raw => false::secondBits raw)=
      (fun raw => true::pairBits (encodeNat (value (firstBits raw)-1)) (false::secondBits raw)) := by
    funext raw
    rw [Function.comp_apply,StandardBitPairMaps.parallel_pair]
  rw [he] at ht
  have hf := polyBitTime_comp secondBits_polyBitTime (StandardBitPrepend.prepend_polyBitTime false)
  exact StandardBitConditionalBitTime.conditional_polyBitTime
    (fun raw => StandardBitZero.zeroBit (firstBits raw)) _ _ hb ht hf

theorem body_zero (k : Nat) : body (frame 0 k)=false::List.replicate k false := by
  simp only [body,frame,firstBits_pair,secondBits_pair]
  rfl

theorem body_succ (n k : Nat) : body (frame (n+1) k)=true::frame n (k+1) := by
  simp only [body,frame,firstBits_pair,secondBits_pair,StandardBitBoundedPower.zero_succ,
    Bool.false_eq_true,if_false,value_encode_nat,Nat.add_sub_cancel,List.replicate_succ]

theorem frame_length (B n k : Nat) (h : n+k≤B) : (frame n k).length≤3*B+1 := by
  have hn := StandardBinaryFixedMultiplyWord.encode_nat_length_le n
  simp only [frame,pairBits_length,List.length_replicate]
  omega

theorem eval (B n k : Nat) (h : n+k≤B) :
    StandardBitFlagLoop.Eval body (3*B+1) (frame n k) (List.replicate (n+k) false) (n+1) := by
  induction n generalizing k with
  | zero =>
    simpa only [Nat.zero_add,body_zero,List.tail_cons] using
      (StandardBitFlagLoop.Eval.stop (frame_length B 0 k h)
        (by rw [body_zero];rfl) : StandardBitFlagLoop.Eval body (3*B+1)
        (frame 0 k) (body (frame 0 k)).tail 1)
  | succ n ih =>
    have rest := ih (k+1) (by omega)
    have ht : (body (frame (n+1) k)).tail=frame n (k+1) := by rw [body_succ];rfl
    have he : n+1+k=n+(k+1) := by omega
    rw [he]
    exact StandardBitFlagLoop.Eval.next (frame_length B (n+1) k h)
      (by rw [body_succ];rfl) (ht.symm ▸ rest)

theorem cells_lt (raw : List Bool) : cells raw<2^(2*raw.length) := by
  have h := value_lt_pow_length raw
  have he : 2^(2*raw.length)=(2^raw.length)*(2^raw.length) := by
    rw [two_mul,pow_add]
  rw [cells,he]
  nlinarith

theorem allocation_compiled :
    ∃ ns nt, ∃ M : DeterministicMachine ns nt, ∃ e : Polynomial Nat,
      ComputesWithin M allocation (fun n => 2^e.eval n) := by
  apply StandardBitInitializedExponentialLoop.compiled init body allocation
    init_polyBitTime body_polyBitTime (fun m => 3*2^(2*m)+1) (fun m => 2^(2*m))
    (2*Polynomial.X+3) (2*Polynomial.X)
  · intro m
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,pow_add]
    have hp : 1≤2^(2*m) := Nat.one_le_pow _ _ (by decide)
    change 3*2^(2*m)+1≤2^(2*m)*8
    omega
  · intro m;simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X];rfl
  · intro raw
    refine ⟨cells raw+1,?_,by have h := cells_lt raw;omega⟩
    have h := eval (2^(2*raw.length)) (cells raw) 0 (by have h := cells_lt raw;omega)
    simpa only [init,allocation,Nat.add_zero] using h

theorem allocation_spec :
    (∀ raw,(allocation raw).length=(value raw)^2) ∧
    ∃ ns nt, ∃ M : DeterministicMachine ns nt, ∃ e : Polynomial Nat,
      ComputesWithin M allocation (fun n => 2^e.eval n) ∧
      ∀ raw,RunsAtMost M raw (2^e.eval raw.length) := by
  obtain ⟨ns,nt,M,e,h⟩ := allocation_compiled
  refine ⟨?_,ns,nt,M,e,h,?_⟩
  · intro raw;simp only [allocation,List.length_replicate,cells,pow_two]
  · intro raw;exact (ComputesWithin.actual_bounds M allocation _ h raw).1

end
end PakFixedPolyomino.StandardBitSquareOccupancyAllocation
