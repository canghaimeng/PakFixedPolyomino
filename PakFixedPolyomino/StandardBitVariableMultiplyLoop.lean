import PakFixedPolyomino.StandardBitWordVector
import PakFixedPolyomino.StandardBitInitializedFlagLoop
import PakFixedPolyomino.StandardBitCanonicalDecrement
import PakFixedPolyomino.StandardBitHalveAlignment
import PakFixedPolyomino.StandardBitVariableAdd
import PakFixedPolyomino.StandardBitHead
import PakFixedPolyomino.PakWeightedScannerDPBinaryWidths

/-! Binary shift-and-add on every raw pair. Each physical loop consumes one
literal multiplier digit, shifts the other operand once, and conditionally
uses the ordinary variable adder. The adder Poly proof is the sole explicit
compiler premise; all iteration and intermediate tape bounds are internal. -/
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace PakFixedPolyomino.StandardBitVariableMultiplyLoop
noncomputable section
open Computability StandardBitTime StandardBitMetric StandardBitTimeComposition
open PakFixedWeightedStandardBinaryCount (value value_encode_nat value_lt_pow_length)
open StandardBitWordVector (field field_polyBitTime assemble)
open StandardBitPairFirstCompaction (firstBits first_polyBitTime firstBits_pair)
open StandardBitPairProjection (secondBits secondBits_polyBitTime secondBits_pair)

def frame (x y : List Bool) (a : Nat) : List Bool :=
  StandardBitWordVector.encode [x,y,encodeNat a]
def init (raw : List Bool) : List Bool := frame (firstBits raw) (secondBits raw) 0
def multiplyBits (raw : List Bool) : List Bool := encodeNat (value (firstBits raw)*value (secondBits raw))

def addend (raw : List Bool) : List Bool :=
  if (field 0 raw).headD false then
    StandardBitVariableAdd.addBits (pairBits (field 2 raw) (field 1 raw)) else field 2 raw

def next (raw : List Bool) : List Bool :=
  assemble [fun w => (field 0 w).tail,fun w => false::field 1 w,addend] raw

def body (raw : List Bool) : List Bool :=
  if StandardBitZero.zeroBit (field 0 raw) then false::field 2 raw else true::next raw

theorem init_polyBitTime : PolyBitTime init := by
  have h := StandardBitWordVector.assemble_polyBitTime
    [firstBits,secondBits,fun _ : List Bool => []] (by
      intro f hf
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
      rcases hf with rfl|rfl|rfl
      · exact first_polyBitTime
      · exact secondBits_polyBitTime
      · exact StandardBitPairSanitize.empty_polyBitTime)
  exact h

theorem addend_polyBitTime (hadd : PolyBitTime StandardBitVariableAdd.addBits) : PolyBitTime addend := by
  have hp := StandardBitPairMaps.parallel_polyBitTime (field 2) (field 1)
    (field_polyBitTime 2) (field_polyBitTime 1)
  have hs := polyBitTime_comp hp hadd
  have heq : StandardBitVariableAdd.addBits ∘ StandardBitPairMaps.parallel (field 2) (field 1)=
      (fun raw => StandardBitVariableAdd.addBits (pairBits (field 2 raw) (field 1 raw))) := by
    funext raw
    rw [Function.comp_apply,StandardBitPairMaps.parallel_pair]
  rw [heq] at hs
  have hb := polyBitTime_comp (field_polyBitTime 0) StandardBitHead.head_polyBitTime
  exact StandardBitConditionalBitTime.conditional_polyBitTime
    (fun raw => (field 0 raw).headD false) (field 2)
    (fun raw => StandardBitVariableAdd.addBits (pairBits (field 2 raw) (field 1 raw)))
    hb (field_polyBitTime 2) hs

theorem next_polyBitTime (hadd : PolyBitTime StandardBitVariableAdd.addBits) : PolyBitTime next := by
  have ht := polyBitTime_comp (field_polyBitTime 0) StandardBitHalve.halve_polyBitTime
  have hs := polyBitTime_comp (field_polyBitTime 1) (StandardBitPrepend.prepend_polyBitTime false)
  apply StandardBitWordVector.assemble_polyBitTime
  intro f hf
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ht
  · exact hs
  · exact addend_polyBitTime hadd

theorem body_polyBitTime (hadd : PolyBitTime StandardBitVariableAdd.addBits) : PolyBitTime body := by
  have hz := polyBitTime_comp (field_polyBitTime 0) StandardBitZero.zero_polyBitTime
  have hs := polyBitTime_comp (field_polyBitTime 2) (StandardBitPrepend.prepend_polyBitTime false)
  have hn := polyBitTime_comp (next_polyBitTime hadd) (StandardBitPrepend.prepend_polyBitTime true)
  exact StandardBitConditionalBitTime.conditional_polyBitTime
    (fun raw => StandardBitZero.zeroBit (field 0 raw)) (List.cons true ∘ next)
    (List.cons false ∘ field 2) hz hn hs

theorem field_frame (x y : List Bool) (a : Nat) :
    field 0 (frame x y a)=x ∧ field 1 (frame x y a)=y ∧ field 2 (frame x y a)=encodeNat a := by
  simp [frame,StandardBitWordVector.field_encode]

def advance (b : Bool) (a v : Nat) : Nat := if b then a+v else a

theorem next_frame (b : Bool) (x y : List Bool) (a : Nat) :
    next (frame (b::x) y a)=frame x (false::y) (advance b a (value y)) := by
  have h := field_frame (b::x) y a
  simp only [next,assemble,List.map_cons,List.map_nil,h.1,h.2.1,List.tail_cons,addend,h.1,
    List.headD_cons,h.2.1,h.2.2,StandardBitVariableAdd.add_pair,value_encode_nat]
  cases b <;> rfl

theorem total_advance (b : Bool) (x y : List Bool) (a : Nat) :
    advance b a (value y)+value x*value (false::y)=a+value (b::x)*value y := by
  cases b <;> simp only [advance,Bool.false_eq_true,if_false,if_true,value,Bool.toNat_false,
    Bool.toNat_true,zero_add] <;> ring

theorem frame_length (B : Nat) (x y : List Bool) (a : Nat)
    (hxy : x.length+y.length≤B) (ha : a+value x*value y<2^B) :
    (frame x y a).length≤4*B+3 := by
  have hlen := PakWeightedScannerDPBinaryWidths.encode_length_of_lt_pow
    (show a<2^B by omega)
  simp only [frame,StandardBitWordVector.encode_length,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil]
  omega

theorem eval (B : Nat) (x y : List Bool) (a : Nat)
    (hxy : x.length+y.length≤B) (ha : a+value x*value y<2^B) :
    ∃ k≤x.length+1,StandardBitFlagLoop.Eval body (4*B+3) (frame x y a)
      (encodeNat (a+value x*value y)) k := by
  induction x generalizing y a with
  | nil =>
    have hb : body (frame [] y a)=false::encodeNat a := by
      simp only [body,(field_frame [] y a).1,(field_frame [] y a).2.2]
      rfl
    refine ⟨1,by simp,?_⟩
    simpa only [hb,List.tail_cons,value,Nat.zero_mul,Nat.add_zero] using
      (StandardBitFlagLoop.Eval.stop (frame_length B [] y a hxy ha)
        (by rw [hb];rfl) : StandardBitFlagLoop.Eval body (4*B+3) (frame [] y a)
        (body (frame [] y a)).tail 1)
  | cons b x ih =>
    cases hz : StandardBitZero.zeroBit (b::x) with
    | true =>
      have hv : value (b::x)=0 := by
        have h := (StandardBitZero.zeroBit_iff (b::x)).mp hz
        rwa [StandardBitDecrementAlignment.value_eq_original] at h
      have hb : body (frame (b::x) y a)=false::encodeNat a := by
        simp only [body,(field_frame (b::x) y a).1,(field_frame (b::x) y a).2.2,hz,if_true]
      refine ⟨1,by simp,?_⟩
      simpa only [hv,Nat.zero_mul,Nat.add_zero,hb,List.tail_cons] using
        (StandardBitFlagLoop.Eval.stop (frame_length B (b::x) y a hxy ha)
          (by rw [hb];rfl) : StandardBitFlagLoop.Eval body (4*B+3) (frame (b::x) y a)
          (body (frame (b::x) y a)).tail 1)
    | false =>
      have hn : x.length+(false::y).length≤B := by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hxy
      have ha' : advance b a (value y)+value x*value (false::y)<2^B := by
        rw [total_advance]
        exact ha
      obtain ⟨k,hk,he⟩ := ih (false::y) (advance b a (value y)) hn ha'
      have hb : body (frame (b::x) y a)=true::frame x (false::y) (advance b a (value y)) := by
        simp only [body,(field_frame (b::x) y a).1,hz,Bool.false_eq_true,if_false,next_frame]
      rw [total_advance] at he
      refine ⟨k+1,by simp only [List.length_cons];omega,?_⟩
      have ht : (body (frame (b::x) y a)).tail=frame x (false::y) (advance b a (value y)) := by rw [hb,List.tail_cons]
      exact StandardBitFlagLoop.Eval.next (frame_length B (b::x) y a hxy ha)
        (by rw [hb];rfl) (ht.symm ▸ he)

theorem input_product_bound (raw : List Bool) :
    value (firstBits raw)*value (secondBits raw)<2^(2*raw.length+1) := by
  have hx := value_lt_pow_length (firstBits raw)
  have hy := value_lt_pow_length (secondBits raw)
  have hm := Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_of_lt hy) (pow_pos (by decide : 0<2) _)
  rw [← pow_add] at hm
  have hl := StandardBitWordVector.projection_lengths raw
  have hp := Nat.pow_le_pow_right (by decide : 1≤2)
    (show (firstBits raw).length+(secondBits raw).length≤2*raw.length+1 by omega)
  exact hm.trans_le hp

theorem multiply_polyBitTime (hadd : PolyBitTime StandardBitVariableAdd.addBits) : PolyBitTime multiplyBits := by
  apply StandardBitInitializedFlagLoop.polyBitTime init body multiplyBits
    init_polyBitTime (body_polyBitTime hadd) (8*Polynomial.X+7) (Polynomial.X+1)
  intro raw
  have hxy : (firstBits raw).length+(secondBits raw).length≤2*raw.length+1 := by
    have h := StandardBitWordVector.projection_lengths raw
    omega
  obtain ⟨k,hk,he⟩ := eval (2*raw.length+1) (firstBits raw) (secondBits raw) 0 hxy
    (by simpa using input_product_bound raw)
  have hbound : 4*(2*raw.length+1)+3=8*raw.length+7 := by omega
  rw [hbound] at he
  refine ⟨k,?_,?_⟩
  · simpa only [init,multiplyBits,Nat.zero_add,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Nat.mul_add] using he
  · have hx := (StandardBitWordVector.projection_lengths raw).1
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    omega

theorem multiply_pair (x y : List Bool) :
    multiplyBits (pairBits x y)=encodeNat (value x*value y) := by
  simp only [multiplyBits,firstBits_pair,secondBits_pair]

theorem multiply_none (raw : List Bool) (h : unpairBits raw=none) : multiplyBits raw=[] := by
  simp only [multiplyBits,StandardBitPairFirstCompaction.firstBits,StandardBitPairProjection.secondBits,h]
  rfl

theorem multiply_spec (hadd : PolyBitTime StandardBitVariableAdd.addBits) :
    PolyBitTime multiplyBits ∧ (∀ x y,multiplyBits (pairBits x y)=encodeNat (value x*value y)) ∧
    (∀ raw,unpairBits raw=none → multiplyBits raw=[]) :=
  ⟨multiply_polyBitTime hadd,multiply_pair,multiply_none⟩
end
end PakFixedPolyomino.StandardBitVariableMultiplyLoop
