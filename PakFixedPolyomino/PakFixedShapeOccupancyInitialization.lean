import PakFixedPolyomino.StandardBitSquareOccupancyAllocation
import PakFixedPolyomino.StandardBitWordVector
import PakFixedPolyomino.PakFixedShapeOccupancyScan

/-! A fixed ordinary finite tape machine constructs the actual membership
frame [original literal side word, n^2 empty occupancy bits]. Its binary-square
initializer, allocation body, original-word retention, every frame/iteration
bound and exponential physical transition cost are supplied internally on
EVERY input word. The empty/highzero cases keep the original square count.
This initializer alone does not implement the remaining ND tiling program. -/
namespace PakFixedPolyomino.PakFixedShapeOccupancyInitialization
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition
open StandardNondeterministicMachine
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open StandardBitWordVector (field field_polyBitTime assemble)
open StandardBitSquareOccupancyAllocation (cells cells_lt)

def frame (side : List Bool) (n k : Nat) : List Bool :=
  StandardBitWordVector.encode [encodeNat n,List.replicate k false,side]
def init (raw : List Bool) : List Bool := frame raw (cells raw) 0
def initialized (raw : List Bool) : List Bool :=
  StandardBitWordVector.encode [raw,List.replicate (cells raw) false]
def next (raw : List Bool) : List Bool :=
  assemble [fun w => encodeNat (value (field 0 w)-1),fun w => false::field 1 w,field 2] raw
def finish (raw : List Bool) : List Bool := assemble [field 2,field 1] raw
def body (raw : List Bool) : List Bool :=
  if StandardBitZero.zeroBit (field 0 raw) then false::finish raw else true::next raw

theorem init_polyBitTime : PolyBitTime init := by
  have h := StandardBitWordVector.assemble_polyBitTime
    [fun raw => encodeNat (cells raw),fun _ => [],id] (by
      intro f hf
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
      rcases hf with rfl|rfl|rfl
      · exact StandardBitSquareOccupancyAllocation.cells_polyBitTime
      · exact StandardBitPairSanitize.empty_polyBitTime
      · exact identity_polyBitTime)
  have he : assemble [fun raw => encodeNat (cells raw),fun _ => [],id]=init := by
    funext raw
    simp only [assemble,List.map_cons,List.map_nil,id_eq,init,frame]
    rfl
  rwa [he] at h

theorem next_polyBitTime : PolyBitTime next := by
  apply StandardBitWordVector.assemble_polyBitTime
  intro f hf
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact polyBitTime_comp (field_polyBitTime 0) StandardBitCanonicalDecrement.predecessor_polyBitTime
  · exact polyBitTime_comp (field_polyBitTime 1) (StandardBitPrepend.prepend_polyBitTime false)
  · exact field_polyBitTime 2

theorem finish_polyBitTime : PolyBitTime finish := by
  apply StandardBitWordVector.assemble_polyBitTime
  intro f hf
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl
  · exact field_polyBitTime 2
  · exact field_polyBitTime 1

theorem body_polyBitTime : PolyBitTime body := by
  have hb := polyBitTime_comp (field_polyBitTime 0) StandardBitZero.zero_polyBitTime
  have ht := polyBitTime_comp next_polyBitTime (StandardBitPrepend.prepend_polyBitTime true)
  have hf := polyBitTime_comp finish_polyBitTime (StandardBitPrepend.prepend_polyBitTime false)
  exact StandardBitConditionalBitTime.conditional_polyBitTime
    (fun raw => StandardBitZero.zeroBit (field 0 raw)) _ _ hb ht hf

theorem field_frame (side : List Bool) (n k : Nat) :
    field 0 (frame side n k)=encodeNat n ∧
    field 1 (frame side n k)=List.replicate k false ∧ field 2 (frame side n k)=side := by
  simp [frame,StandardBitWordVector.field_encode]

theorem body_zero (side : List Bool) (k : Nat) :
    body (frame side 0 k)=false::StandardBitWordVector.encode [side,List.replicate k false] := by
  simp only [body,(field_frame side 0 k).1]
  change false::finish (frame side 0 k)=_
  simp only [finish,assemble,List.map_cons,List.map_nil,(field_frame side 0 k).2.1,
    (field_frame side 0 k).2.2]

theorem body_succ (side : List Bool) (n k : Nat) :
    body (frame side (n+1) k)=true::frame side n (k+1) := by
  simp only [body,(field_frame side (n+1) k).1,StandardBitBoundedPower.zero_succ,
    Bool.false_eq_true,if_false,next,assemble,List.map_cons,List.map_nil,
    (field_frame side (n+1) k).1,(field_frame side (n+1) k).2.1,
    (field_frame side (n+1) k).2.2,value_encode_nat,Nat.add_sub_cancel,List.replicate_succ]
  rfl

theorem frame_length (B : Nat) (side : List Bool) (n k : Nat) (h : n+k≤B) :
    (frame side n k).length≤2*B+2*side.length+3 := by
  have hn := StandardBitLiteralLength.encode_length_le n
  simp only [frame,StandardBitWordVector.encode_length,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,List.length_replicate,List.length_cons,List.length_nil]
  omega

theorem eval (B : Nat) (side : List Bool) (n k : Nat) (h : n+k≤B) :
    StandardBitFlagLoop.Eval body (2*B+2*side.length+3) (frame side n k)
      (StandardBitWordVector.encode [side,List.replicate (n+k) false]) (n+1) := by
  induction n generalizing k with
  | zero =>
    simpa only [Nat.zero_add,body_zero,List.tail_cons] using
      (StandardBitFlagLoop.Eval.stop (frame_length B side 0 k h)
        (by rw [body_zero];rfl) : StandardBitFlagLoop.Eval body (2*B+2*side.length+3)
        (frame side 0 k) (body (frame side 0 k)).tail 1)
  | succ n ih =>
    have rest := ih (k+1) (by omega)
    have ht : (body (frame side (n+1) k)).tail=frame side n (k+1) := by rw [body_succ];rfl
    have he : n+1+k=n+(k+1) := by omega
    rw [he]
    exact StandardBitFlagLoop.Eval.next (frame_length B side (n+1) k h)
      (by rw [body_succ];rfl) (ht.symm ▸ rest)

theorem initialization_compiled :
    ∃ ns nt, ∃ M : DeterministicMachine ns nt, ∃ e : Polynomial Nat,
      ComputesWithin M initialized (fun n => 2^e.eval n) := by
  apply StandardBitInitializedExponentialLoop.compiled init body initialized
    init_polyBitTime body_polyBitTime (fun m => 2*2^(2*m)+2*m+3) (fun m => 2^(2*m))
    (2*Polynomial.X+3) (2*Polynomial.X)
  · intro m
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,pow_add]
    have hm : m≤2^(2*m) := (Nat.le_of_lt Nat.lt_two_pow_self).trans
      (Nat.pow_le_pow_right (by decide) (by omega : m≤2*m))
    have hp : 1≤2^(2*m) := Nat.one_le_pow _ _ (by decide)
    change 2*2^(2*m)+2*m+3≤2^(2*m)*8
    omega
  · intro m;simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X];rfl
  · intro raw
    refine ⟨cells raw+1,?_,by have h := cells_lt raw;omega⟩
    have h := eval (2^(2*raw.length)) raw (cells raw) 0 (by have h := cells_lt raw;omega)
    simpa only [init,initialized,Nat.add_zero] using h

theorem empty_mask (n : Nat) : PakFixedShapeOccupancyScan.mask n ∅=List.replicate (n^2) false := by
  rw [PakFixedShapeOccupancyScan.mask_covered]
  simp [TilingAnchoredChoices.covered,PakFixedShapeOccupancyScan.scan_length]

theorem initialized_fields (raw : List Bool) :
    field 0 (initialized raw)=raw ∧
    field 1 (initialized raw)=PakFixedShapeOccupancyScan.mask (value raw) ∅ := by
  simp [initialized,StandardBitWordVector.field_encode,empty_mask,cells,pow_two]

theorem initialization_spec :
    (∀ raw,field 0 (initialized raw)=raw ∧
      field 1 (initialized raw)=PakFixedShapeOccupancyScan.mask (value raw) ∅) ∧
    ∃ ns nt, ∃ M : DeterministicMachine ns nt, ∃ e : Polynomial Nat,
      ComputesWithin M initialized (fun n => 2^e.eval n) ∧
      ∀ raw,RunsAtMost M raw (2^e.eval raw.length) := by
  obtain ⟨ns,nt,M,e,h⟩ := initialization_compiled
  exact ⟨initialized_fields,ns,nt,M,e,h,fun raw => (ComputesWithin.actual_bounds M initialized _ h raw).1⟩

end
end PakFixedPolyomino.PakFixedShapeOccupancyInitialization
