import PakFixedPolyomino.StandardBitWordVector
import PakFixedPolyomino.StandardBitInitializedFlagLoop
import PakFixedPolyomino.StandardBitVariableSubtractClosed
import PakFixedPolyomino.StandardBitReverseClosed
import PakFixedPolyomino.StandardBitNormalize
import PakFixedPolyomino.StandardBitZero
import PakFixedPolyomino.StandardBitHead
import PakFixedPolyomino.StandardBitHalve
import PakFixedPolyomino.StandardBitLiteralLength
import PakFixedPolyomino.StandardBitPairMaps
import PakFixedPolyomino.StandardBitPairSanitize
import PakFixedPolyomino.StandardBitFixedMultiply
import PakFixedPolyomino.StandardBitFixedAdd
import PakFixedPolyomino.StandardBitDecrementAlignment
import PakFixedPolyomino.PakWeightedScannerDPBinaryWidths

/-! Ordinary Nat division and remainder on every raw pair. MSB-first long
division uses the closed adder internally through the subtract/compare
wrapper. Numeric divisor zero preserves X/0=0 and X%0=X. All iteration,
width and tape bounds are supplied internally. -/
set_option maxHeartbeats 0
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace PakFixedPolyomino.StandardBitVariableDivideLoop
noncomputable section
open Computability StandardBitTime StandardBitMetric StandardBitTimeComposition
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open StandardBitWordVector (field field_polyBitTime assemble)
open StandardBitPairFirstCompaction (firstBits first_polyBitTime firstBits_pair)
open StandardBitPairProjection (secondBits secondBits_polyBitTime secondBits_pair)
open StandardBitVariableSubtractLoop (subtractBits ltBits)
open StandardBinaryWordNormalization (normalizeBits normalize_eq_encodeNat)

def divModBits (raw : List Bool) : List Bool :=
  pairBits (encodeNat (value (firstBits raw)/value (secondBits raw)))
    (encodeNat (value (firstBits raw)%value (secondBits raw)))
def divideBits (raw : List Bool) : List Bool :=
  encodeNat (value (firstBits raw)/value (secondBits raw))
def moduloBits (raw : List Bool) : List Bool :=
  encodeNat (value (firstBits raw)%value (secondBits raw))

def msbVal : List Bool → Nat
  | [] => 0
  | b::m => b.toNat * 2^m.length + msbVal m

def frame (m y : List Bool) (q r : Nat) : List Bool :=
  StandardBitWordVector.encode [m,y,encodeNat q,encodeNat r]

def initPos (raw : List Bool) : List Bool :=
  frame (firstBits raw).reverse (secondBits raw) 0 0
def initZero (raw : List Bool) : List Bool :=
  frame [] (secondBits raw) 0 (value (firstBits raw))
def init (raw : List Bool) : List Bool :=
  if StandardBitZero.zeroBit (secondBits raw) then initZero raw else initPos raw

def shifted (raw : List Bool) : List Bool :=
  if (field 0 raw).headD false then true::field 3 raw else false::field 3 raw
def rCand (raw : List Bool) : List Bool := normalizeBits (shifted raw)
def cmpRaw : List Bool → List Bool :=
  StandardBitPairMaps.parallel rCand (field 1)
def ltFlag (raw : List Bool) : Bool := (ltBits (cmpRaw raw)).headD false
def qDbl (raw : List Bool) : List Bool := encodeNat (2*value (field 2 raw))
def qDbl1 (raw : List Bool) : List Bool := encodeNat (2*value (field 2 raw)+1)
def rKeep (raw : List Bool) : List Bool := rCand raw
def rSub (raw : List Bool) : List Bool := subtractBits (cmpRaw raw)
def qNext (raw : List Bool) : List Bool := if ltFlag raw then qDbl raw else qDbl1 raw
def rNext (raw : List Bool) : List Bool := if ltFlag raw then rKeep raw else rSub raw
def next (raw : List Bool) : List Bool :=
  assemble [fun w => (field 0 w).tail,field 1,qNext,rNext] raw
def finish (raw : List Bool) : List Bool :=
  StandardBitPairMaps.parallel (field 2) (field 3) raw
def body (raw : List Bool) : List Bool :=
  if (field 0 raw).isEmpty then false::finish raw else true::next raw

theorem true_polyBitTime : PolyBitTime (fun _ : List Bool => [true]) := by
  simpa only [Function.comp_def] using polyBitTime_comp
    StandardBitPairSanitize.empty_polyBitTime (StandardBitPrepend.prepend_polyBitTime true)

theorem ite_bit_poly (b : List Bool → Bool) (f g : List Bool → List Bool)
    (hb : PolyBitTime (fun x => [b x])) (hf : PolyBitTime f) (hg : PolyBitTime g) :
    PolyBitTime (fun x => if b x then g x else f x) :=
  StandardBitConditionalBitTime.conditional_polyBitTime b f g hb hf hg

theorem xbit_polyBitTime : PolyBitTime (fun raw => [(field 0 raw).headD false]) :=
  polyBitTime_comp (field_polyBitTime 0) StandardBitHead.head_polyBitTime

theorem shifted_polyBitTime : PolyBitTime shifted :=
  ite_bit_poly (fun raw => (field 0 raw).headD false)
    (List.cons false ∘ field 3) (List.cons true ∘ field 3) xbit_polyBitTime
    (polyBitTime_comp (field_polyBitTime 3) (StandardBitPrepend.prepend_polyBitTime false))
    (polyBitTime_comp (field_polyBitTime 3) (StandardBitPrepend.prepend_polyBitTime true))

theorem rCand_polyBitTime : PolyBitTime rCand :=
  polyBitTime_comp shifted_polyBitTime StandardBitNormalize.normalize_polyBitTime

theorem cmpRaw_polyBitTime : PolyBitTime cmpRaw :=
  StandardBitPairMaps.parallel_polyBitTime rCand (field 1)
    rCand_polyBitTime (field_polyBitTime 1)

theorem ltBits_singleton (w : List Bool) : ltBits w=[(ltBits w).headD false] := by
  simp only [ltBits]
  rfl

theorem ltBits_head_polyBitTime : PolyBitTime (fun raw => [(ltBits (cmpRaw raw)).headD false]) := by
  have h : (fun raw => [(ltBits (cmpRaw raw)).headD false])=ltBits ∘ cmpRaw := by
    funext raw; exact (ltBits_singleton (cmpRaw raw)).symm
  rw [h]
  exact polyBitTime_comp cmpRaw_polyBitTime
    StandardBitVariableSubtractClosed.lt_polyBitTime

theorem qDbl_polyBitTime : PolyBitTime qDbl :=
  polyBitTime_comp (field_polyBitTime 2) (StandardBitFixedMultiply.fixed_multiply_polyBitTime 2)

theorem qDbl1_polyBitTime : PolyBitTime qDbl1 := by
  have h := polyBitTime_comp qDbl_polyBitTime (StandardBitFixedAdd.fixed_add_polyBitTime 1)
  have he : (fun w => encodeNat (value w+1)) ∘ qDbl=qDbl1 := by
    funext raw
    simp [Function.comp_apply,qDbl,qDbl1,value_encode_nat]
  rwa [he] at h

theorem rSub_polyBitTime : PolyBitTime rSub :=
  polyBitTime_comp cmpRaw_polyBitTime StandardBitVariableSubtractClosed.subtract_polyBitTime

theorem qNext_polyBitTime : PolyBitTime qNext :=
  ite_bit_poly ltFlag qDbl1 qDbl ltBits_head_polyBitTime qDbl1_polyBitTime qDbl_polyBitTime

theorem rNext_polyBitTime : PolyBitTime rNext :=
  ite_bit_poly ltFlag rSub rKeep ltBits_head_polyBitTime rSub_polyBitTime rCand_polyBitTime

theorem next_polyBitTime : PolyBitTime next := by
  have ht := polyBitTime_comp (field_polyBitTime 0) StandardBitHalve.halve_polyBitTime
  apply StandardBitWordVector.assemble_polyBitTime
  intro f hf
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl
  · exact ht
  · exact field_polyBitTime 1
  · exact qNext_polyBitTime
  · exact rNext_polyBitTime

theorem finish_polyBitTime : PolyBitTime finish :=
  StandardBitPairMaps.parallel_polyBitTime (field 2) (field 3)
    (field_polyBitTime 2) (field_polyBitTime 3)

theorem initPos_polyBitTime : PolyBitTime initPos := by
  have hr := polyBitTime_comp first_polyBitTime StandardBitReverseClosed.reverse_polyBitTime
  exact StandardBitWordVector.assemble_polyBitTime
    [List.reverse ∘ firstBits,secondBits,fun _ : List Bool => [],fun _ : List Bool => []] (by
      intro f hf
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
      rcases hf with rfl|rfl|rfl|rfl
      · exact hr
      · exact secondBits_polyBitTime
      · exact StandardBitPairSanitize.empty_polyBitTime
      · exact StandardBitPairSanitize.empty_polyBitTime)

theorem initZero_polyBitTime : PolyBitTime initZero := by
  have hn := polyBitTime_comp first_polyBitTime StandardBitNormalize.normalize_polyBitTime
  have he : normalizeBits ∘ firstBits=
      (fun raw => encodeNat (value (firstBits raw))) := by
    funext raw; exact normalize_eq_encodeNat _
  rw [he] at hn
  exact StandardBitWordVector.assemble_polyBitTime
    [fun _ : List Bool => [],secondBits,fun _ : List Bool => [],
      fun raw => encodeNat (value (firstBits raw))] (by
      intro f hf
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
      rcases hf with rfl|rfl|rfl|rfl
      · exact StandardBitPairSanitize.empty_polyBitTime
      · exact secondBits_polyBitTime
      · exact StandardBitPairSanitize.empty_polyBitTime
      · exact hn)

theorem init_polyBitTime : PolyBitTime init :=
  ite_bit_poly (fun raw => StandardBitZero.zeroBit (secondBits raw)) initPos initZero
    (polyBitTime_comp secondBits_polyBitTime StandardBitZero.zero_polyBitTime)
    initPos_polyBitTime initZero_polyBitTime

theorem body_polyBitTime : PolyBitTime body := by
  have he0 := polyBitTime_comp (field_polyBitTime 0) StandardBitLiteralLength.empty_polyBitTime
  have hn := polyBitTime_comp next_polyBitTime (StandardBitPrepend.prepend_polyBitTime true)
  have hs := polyBitTime_comp finish_polyBitTime (StandardBitPrepend.prepend_polyBitTime false)
  exact ite_bit_poly (fun raw => (field 0 raw).isEmpty) (List.cons true ∘ next)
    (List.cons false ∘ finish) he0 hn hs

theorem field_frame (m y : List Bool) (q r : Nat) :
    field 0 (frame m y q r)=m ∧ field 1 (frame m y q r)=y ∧
    field 2 (frame m y q r)=encodeNat q ∧ field 3 (frame m y q r)=encodeNat r := by
  simp [frame,StandardBitWordVector.field_encode]

theorem encodeNat_zero : encodeNat 0=[] := rfl

theorem msbVal_snoc (m : List Bool) (b : Bool) :
    msbVal (m++[b])=2*msbVal m+b.toNat := by
  induction m with
  | nil => cases b <;> simp [msbVal]
  | cons a m ih =>
    simp [msbVal,List.append_eq,ih,List.length_append,Nat.pow_succ]
    cases a <;> cases b <;> simp [Bool.toNat] <;> ring

theorem msbVal_reverse (x : List Bool) : msbVal x.reverse=value x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    simp [List.reverse_cons,msbVal_snoc,ih,value]
    cases b <;> simp [Bool.toNat] <;> ring

theorem msbVal_cons (b : Bool) (m : List Bool) :
    msbVal (b::m)=b.toNat*2^m.length+msbVal m := rfl

theorem zeroBit_value (w : List Bool) :
    StandardBitZero.zeroBit w=true ↔ value w=0 := by
  rw [StandardBitZero.zeroBit_iff,StandardBitDecrementAlignment.value_eq_original]

theorem shifted_frame (b : Bool) (m y : List Bool) (q r : Nat) :
    shifted (frame (b::m) y q r)=b::encodeNat r := by
  have h := field_frame (b::m) y q r
  simp only [shifted,h.1,List.headD_cons,h.2.2.2]
  cases b <;> rfl

theorem rCand_frame (b : Bool) (m y : List Bool) (q r : Nat) :
    rCand (frame (b::m) y q r)=encodeNat (2*r+b.toNat) := by
  simp only [rCand,shifted_frame,normalize_eq_encodeNat,value,value_encode_nat]
  cases b <;> simp [Bool.toNat,Nat.add_comm]

theorem ltFlag_frame (b : Bool) (m y : List Bool) (q r : Nat) :
    ltFlag (frame (b::m) y q r)=decide (2*r+b.toNat<value y) := by
  have h := field_frame (b::m) y q r
  simp [ltFlag,cmpRaw,StandardBitPairMaps.parallel_pair,rCand_frame,ltBits,h.2.1,
    firstBits_pair,secondBits_pair,value_encode_nat]

theorem qDbl_frame (m y : List Bool) (q r : Nat) :
    qDbl (frame m y q r)=encodeNat (2*q) := by
  simp [qDbl,field_frame,value_encode_nat]

theorem qDbl1_frame (m y : List Bool) (q r : Nat) :
    qDbl1 (frame m y q r)=encodeNat (2*q+1) := by
  simp [qDbl1,field_frame,value_encode_nat]

theorem rSub_frame (b : Bool) (m y : List Bool) (q r : Nat) :
    rSub (frame (b::m) y q r)=encodeNat ((2*r+b.toNat)-value y) := by
  have h := field_frame (b::m) y q r
  simp [rSub,cmpRaw,StandardBitPairMaps.parallel_pair,rCand_frame,subtractBits,h.2.1,
    firstBits_pair,secondBits_pair,value_encode_nat]

theorem next_frame (b : Bool) (m y : List Bool) (q r : Nat) :
    next (frame (b::m) y q r)=
      frame m y (if 2*r+b.toNat<value y then 2*q else 2*q+1)
        (if 2*r+b.toNat<value y then 2*r+b.toNat else (2*r+b.toNat)-value y) := by
  have h := field_frame (b::m) y q r
  have hq : qNext (frame (b::m) y q r)=
      encodeNat (if 2*r+b.toNat<value y then 2*q else 2*q+1) := by
    simp only [qNext,ltFlag_frame,qDbl_frame (b::m),qDbl1_frame (b::m)]
    by_cases hP : 2*r+b.toNat<value y
    · simp [decide_eq_true hP,hP]
    · simp [decide_eq_false hP,hP]
  have hrn : rNext (frame (b::m) y q r)=
      encodeNat (if 2*r+b.toNat<value y then 2*r+b.toNat
        else (2*r+b.toNat)-value y) := by
    simp only [rNext,ltFlag_frame,rKeep,rCand_frame,rSub_frame]
    by_cases hP : 2*r+b.toNat<value y
    · simp [decide_eq_true hP,hP]
    · simp [decide_eq_false hP,hP]
  simp only [next,assemble,List.map_cons,List.map_nil]
  rw [h.1,List.tail_cons,h.2.1,hq,hrn]
  rfl

theorem finish_frame (m y : List Bool) (q r : Nat) :
    finish (frame m y q r)=pairBits (encodeNat q) (encodeNat r) := by
  have h := field_frame m y q r
  simp [finish,StandardBitPairMaps.parallel_pair,h.2.2.1,h.2.2.2]

theorem body_stop (y : List Bool) (q r : Nat) :
    body (frame [] y q r)=false::finish (frame [] y q r) := by
  have h := field_frame [] y q r
  simp [body,h.1]

theorem body_continue (b : Bool) (m y : List Bool) (q r : Nat) :
    body (frame (b::m) y q r)=true::next (frame (b::m) y q r) := by
  have h := field_frame (b::m) y q r
  simp [body,h.1]

theorem step_inv (q r d bit : Nat) (hd : 0<d) (hr : r<d) (hbit : bit≤1) :
    (2*(q*d+r)+bit)=
      (if 2*r+bit<d then 2*q else 2*q+1)*d +
        (if 2*r+bit<d then 2*r+bit else 2*r+bit-d) ∧
    (if 2*r+bit<d then 2*r+bit else 2*r+bit-d)<d := by
  have hdist : 2*(q*d+r)+bit=(2*q)*d+(2*r+bit) := by
    have h1 : 2*(q*d+r)=2*(q*d)+2*r := Nat.mul_add 2 (q*d) r
    have h2 : 2*(q*d)=(2*q)*d := by
      simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    rw [h1,h2,Nat.add_assoc]
  by_cases hlt : 2*r+bit<d
  · simp only [if_pos hlt]
    exact ⟨hdist,hlt⟩
  · simp only [if_neg hlt]
    have hge : d≤2*r+bit := Nat.le_of_not_lt hlt
    constructor
    · have hsum : (2*q+1)*d+(2*r+bit-d)=(2*q)*d+(2*r+bit) := by
        have hsub := Nat.sub_add_cancel hge
        rw [Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_comm d,hsub]
      exact hdist.trans hsum.symm
    · omega

theorem div_mod_of_decomp (q r d n : Nat) (hd : 0<d) (hr : r<d) (hn : n=q*d+r) :
    n/d=q ∧ n%d=r := by
  subst n
  constructor
  · rw [Nat.mul_comm,Nat.add_comm,Nat.add_mul_div_left _ _ hd,Nat.div_eq_of_lt hr]
    exact Nat.zero_add q
  · rw [Nat.mul_comm,Nat.add_comm,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr]

theorem prefix_step (q r d : Nat) (b : Bool) (m : List Bool)
    (hd : 0<d) (hr : r<d) :
    (q*d+r)*2^(m.length+1)+msbVal (b::m)=
      ((if 2*r+b.toNat<d then 2*q else 2*q+1)*d +
        (if 2*r+b.toNat<d then 2*r+b.toNat else 2*r+b.toNat-d))*2^m.length +
        msbVal m ∧
    (if 2*r+b.toNat<d then 2*r+b.toNat else 2*r+b.toNat-d)<d := by
  have hbit : b.toNat≤1 := by cases b <;> simp
  obtain ⟨hs,hr''⟩ := step_inv q r d b.toNat hd hr hbit
  have hpow : 2^(m.length+1)=2^m.length*2 := Nat.pow_succ 2 m.length
  constructor
  · rw [msbVal_cons,hpow]
    have hmul := congrArg (fun t => t*2^m.length) hs
    have hL : (2*(q*d+r)+b.toNat)*2^m.length=
        (q*d+r)*(2^m.length*2)+b.toNat*2^m.length := by
      simp [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
    have hmain := hL.symm.trans hmul
    rw [← Nat.add_assoc]
    exact congrArg (fun t => t+msbVal m) hmain
  · exact hr''

theorem frame_length (B : Nat) (m y : List Bool) (q r : Nat)
    (hm : m.length≤B) (hy : y.length≤B)
    (hq : (encodeNat q).length≤B) (hr : (encodeNat r).length≤B+1) :
    (frame m y q r).length≤8*B+9 := by
  have hlen := StandardBitWordVector.encode_length [m,y,encodeNat q,encodeNat r]
  simp only [frame,hlen,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

theorem value_lt_pow (w : List Bool) : value w<2^w.length :=
  PakFixedWeightedStandardBinaryCount.value_lt_pow_length w

theorem eval_pos (B : Nat) (y : List Bool) (hd : 0<value y) (hy : y.length≤B) :
    ∀ (m : List Bool) (q r : Nat),
      m.length≤B → r<value y →
      (q*value y+r)*2^m.length+msbVal m<2^B →
      q<2^B → r<2^(B+1) →
      ∃ t, t ≤ m.length + 1 ∧ StandardBitFlagLoop.Eval body (8 * B + 9) (frame m y q r)
        (pairBits
          (encodeNat (((q*value y+r)*2^m.length+msbVal m)/value y))
          (encodeNat (((q*value y+r)*2^m.length+msbVal m)%value y))) t := by
  intro m
  induction m with
  | nil =>
    intro q r hm hr0 hpre hq hrb
    have hlen := frame_length B [] y q r (by simp) hy
      (PakWeightedScannerDPBinaryWidths.encode_length_of_lt_pow hq)
      (PakWeightedScannerDPBinaryWidths.encode_length_of_lt_pow hrb)
    have hb := body_stop y q r
    have hf := finish_frame [] y q r
    obtain ⟨hqe,hre⟩ := div_mod_of_decomp q r (value y) (q*value y+r) hd hr0 rfl
    refine ⟨1, by omega, ?_⟩
    have hflag : (body (frame [] y q r)).headD false=false := by rw [hb]; rfl
    have ht : (body (frame [] y q r)).tail=pairBits (encodeNat q) (encodeNat r) := by
      rw [hb,List.tail_cons,hf]
    simpa [ht,msbVal,Nat.pow_zero,hqe,hre] using
      (StandardBitFlagLoop.Eval.stop hlen hflag :
        StandardBitFlagLoop.Eval body (8*B+9) (frame [] y q r)
          (body (frame [] y q r)).tail 1)
  | cons b m ih =>
    intro q r hm hr0 hpre hq hrb
    have hbit : b.toNat≤1 := by cases b <;> simp
    obtain ⟨_,hr'⟩ := step_inv q r (value y) b.toNat hd hr0 hbit
    have hlen := frame_length B (b::m) y q r hm hy
      (PakWeightedScannerDPBinaryWidths.encode_length_of_lt_pow hq)
      (PakWeightedScannerDPBinaryWidths.encode_length_of_lt_pow hrb)
    have hbod := body_continue b m y q r
    have hnext := next_frame b m y q r
    have hflag : (body (frame (b::m) y q r)).headD false=true := by rw [hbod]; rfl
    set r' := 2*r+b.toNat
    set q' := if r'<value y then 2*q else 2*q+1
    set r'' := if r'<value y then r' else r'-value y
    have hp := prefix_step q r (value y) b m hd hr0
    have heq : (q*value y+r)*2^(m.length+1)+msbVal (b::m)=
        (q'*value y+r'')*2^m.length+msbVal m := by
      simpa [r',q',r''] using hp.1
    have hpre' : (q'*value y+r'')*2^m.length+msbVal m<2^B := by
      rw [← heq]; simpa [List.length_cons] using hpre
    have hq' : q'<2^B := by
      have h1 : q'≤q'*value y := Nat.le_mul_of_pos_right q' hd
      have h2 : q'*value y+r''≤(q'*value y+r'')*2^m.length :=
        Nat.le_mul_of_pos_right _ (Nat.two_pow_pos m.length)
      have h3 : (q'*value y+r'')*2^m.length≤
          (q'*value y+r'')*2^m.length+msbVal m := Nat.le_add_right _ _
      exact lt_of_le_of_lt (((h1.trans (Nat.le_add_right _ r'')).trans h2).trans h3) hpre'
    have hr''b : r''<2^(B+1) := by
      have hyv : value y<2^B :=
        (value_lt_pow y).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) hy)
      have : r''<value y := by simpa [r',r''] using hr'
      omega
    have hm' : m.length≤B := by simp [List.length_cons] at hm; omega
    obtain ⟨t,ht,he⟩ := ih q' r'' hm' hr' hpre' hq' hr''b
    have htail : (body (frame (b::m) y q r)).tail=frame m y q' r'' := by
      rw [hbod,List.tail_cons,hnext]
    have hpow : ((q*value y+r)*2^(b::m).length+msbVal (b::m))=
        (q'*value y+r'')*2^m.length+msbVal m := by
      simpa [List.length_cons,Nat.succ_eq_add_one] using heq
    rw [hpow]
    refine ⟨t + 1, by simp [List.length_cons]; omega, ?_⟩
    exact StandardBitFlagLoop.Eval.next hlen hflag (htail.symm ▸ he)

theorem eval_zero (B : Nat) (y : List Bool) (X : Nat)
    (hy : y.length≤B) (hX : X<2^B) :
    ∃ t, t ≤ 1 ∧ StandardBitFlagLoop.Eval body (8 * B + 9) (frame [] y 0 X)
      (pairBits [] (encodeNat X)) t := by
  have hlen := frame_length B [] y 0 X (by simp) hy (by simp [encodeNat_zero])
    ((PakWeightedScannerDPBinaryWidths.encode_length_of_lt_pow hX).trans (by omega))
  have hb := body_stop y 0 X
  have hf := finish_frame [] y 0 X
  refine ⟨1, by omega, ?_⟩
  have hflag : (body (frame [] y 0 X)).headD false=false := by rw [hb]; rfl
  have ht : (body (frame [] y 0 X)).tail=pairBits [] (encodeNat X) := by
    rw [hb,List.tail_cons,hf,encodeNat_zero]
  simpa [ht] using
    (StandardBitFlagLoop.Eval.stop hlen hflag :
      StandardBitFlagLoop.Eval body (8*B+9) (frame [] y 0 X)
        (body (frame [] y 0 X)).tail 1)

theorem divMod_polyBitTime : PolyBitTime divModBits := by
  apply StandardBitInitializedFlagLoop.polyBitTime init body divModBits
    init_polyBitTime body_polyBitTime (16*Polynomial.X+17) (Polynomial.X+1)
  intro raw
  have hproj := StandardBitWordVector.projection_lengths raw
  let B := 2*raw.length+1
  have hB : (firstBits raw).length≤B ∧ (secondBits raw).length≤B := by omega
  have hxlt : value (firstBits raw)<2^B :=
    (value_lt_pow (firstBits raw)).trans_le
      (Nat.pow_le_pow_right (by decide : 1≤2) hB.1)
  have hbound : 8*B+9=16*raw.length+17 := by
    simp only [B]; omega
  by_cases hz : StandardBitZero.zeroBit (secondBits raw)
  · have hval : value (secondBits raw)=0 := (zeroBit_value _).mp hz
    have hinit : init raw=frame [] (secondBits raw) 0 (value (firstBits raw)) := by
      simp [init,initZero,hz]
    obtain ⟨t,ht,he⟩ := eval_zero B (secondBits raw) (value (firstBits raw)) hB.2 hxlt
    rw [hbound] at he
    refine ⟨t,?_,?_⟩
    · simpa only [hinit,divModBits,hval,Nat.div_zero,Nat.mod_zero,encodeNat_zero,
        Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
        Polynomial.eval_X] using he
    · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
        Polynomial.eval_X,Polynomial.eval_one]
      omega
  · have hd : 0<value (secondBits raw) := by
      have : value (secondBits raw)≠0 := by
        intro h; exact hz ((zeroBit_value _).mpr h)
      omega
    have hinit : init raw=frame (firstBits raw).reverse (secondBits raw) 0 0 := by
      simp [init,initPos,hz]
    have hm : (firstBits raw).reverse.length≤B := by simpa using hB.1
    have hpre : (0*value (secondBits raw)+0)*2^(firstBits raw).reverse.length+
        msbVal (firstBits raw).reverse<2^B := by
      simpa [msbVal_reverse] using hxlt
    obtain ⟨t,ht,he⟩ := eval_pos B (secondBits raw) hd hB.2
      (firstBits raw).reverse 0 0 hm (by simpa using hd) hpre
      (Nat.two_pow_pos B) (Nat.two_pow_pos (B+1))
    rw [hbound] at he
    refine ⟨t,?_,?_⟩
    · simpa only [hinit,divModBits,msbVal_reverse,Nat.zero_mul,Nat.zero_add,
        Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
        Polynomial.eval_X] using he
    · have : (firstBits raw).reverse.length≤raw.length := by simpa using hproj.1
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
        Polynomial.eval_X,Polynomial.eval_one]
      omega

theorem divideBits_eq (raw : List Bool) : divideBits raw=firstBits (divModBits raw) := by
  simp [divideBits,divModBits,firstBits_pair]

theorem moduloBits_eq (raw : List Bool) : moduloBits raw=secondBits (divModBits raw) := by
  simp [moduloBits,divModBits,secondBits_pair]

theorem divide_polyBitTime : PolyBitTime divideBits := by
  have h := polyBitTime_comp divMod_polyBitTime first_polyBitTime
  have he : firstBits ∘ divModBits=divideBits := by
    funext raw; exact (divideBits_eq raw).symm
  rwa [he] at h

theorem modulo_polyBitTime : PolyBitTime moduloBits := by
  have h := polyBitTime_comp divMod_polyBitTime secondBits_polyBitTime
  have he : secondBits ∘ divModBits=moduloBits := by
    funext raw; exact (moduloBits_eq raw).symm
  rwa [he] at h

theorem divMod_pair (x y : List Bool) :
    divModBits (pairBits x y)=
      pairBits (encodeNat (value x/value y)) (encodeNat (value x%value y)) := by
  simp [divModBits,firstBits_pair,secondBits_pair]

theorem divMod_none (raw : List Bool) (h : unpairBits raw=none) :
    divModBits raw=pairBits [] [] ∧ divideBits raw=[] ∧ moduloBits raw=[] := by
  simp [divModBits,divideBits,moduloBits,firstBits,secondBits,h,value,encodeNat_zero]

theorem division_spec :
    PolyBitTime divModBits ∧ PolyBitTime divideBits ∧ PolyBitTime moduloBits ∧
    (∀ x y,divModBits (pairBits x y)=
      pairBits (encodeNat (value x/value y)) (encodeNat (value x%value y))) ∧
    (∀ raw,unpairBits raw=none →
      divModBits raw=pairBits [] [] ∧ divideBits raw=[] ∧ moduloBits raw=[]) :=
  ⟨divMod_polyBitTime,divide_polyBitTime,modulo_polyBitTime,divMod_pair,divMod_none⟩
end
end PakFixedPolyomino.StandardBitVariableDivideLoop
