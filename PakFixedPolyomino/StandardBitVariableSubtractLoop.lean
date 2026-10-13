import PakFixedPolyomino.StandardBitWordVector
import PakFixedPolyomino.StandardBitInitializedFlagLoop
import PakFixedPolyomino.StandardBitVariableAdd
import PakFixedPolyomino.StandardBitHead
import PakFixedPolyomino.StandardBitHalve
import PakFixedPolyomino.StandardBitLiteralLength
import PakFixedPolyomino.StandardBitPairMaps
import PakFixedPolyomino.StandardBitPairSanitize
import PakFixedPolyomino.PakWeightedScannerDPBinaryWidths

/-! Saturated Nat subtraction and usual-value strict comparison on every raw
pair. Each physical loop consumes one low bit from each remaining operand
(default false), updates a fixed eight-case digit/borrow table, conditionally
adds the current weight through the ordinary variable adder, and doubles the
weight by prepending false. Halt occurs only when both remaining operands are
literally empty. The adder Poly proof is the sole explicit compiler premise. -/
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace PakFixedPolyomino.StandardBitVariableSubtractLoop
noncomputable section
open Computability StandardBitTime StandardBitMetric StandardBitTimeComposition
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open StandardBitWordVector (field field_polyBitTime assemble)
open StandardBitPairFirstCompaction (firstBits first_polyBitTime firstBits_pair)
open StandardBitPairProjection (secondBits secondBits_polyBitTime secondBits_pair)

def subCompareBits (raw : List Bool) : List Bool :=
  pairBits (encodeNat (value (firstBits raw)-value (secondBits raw)))
    [decide (value (firstBits raw)<value (secondBits raw))]
def subtractBits (raw : List Bool) : List Bool :=
  encodeNat (value (firstBits raw)-value (secondBits raw))
def ltBits (raw : List Bool) : List Bool :=
  [decide (value (firstBits raw)<value (secondBits raw))]

def xor3 (x y b : Bool) : Bool := xor (xor x y) b
def nextBorrow (x y b : Bool) : Bool := (!x && y) || (!x && b) || (y && b)

def frame (x y : List Bool) (br : Bool) (a : Nat) (v : List Bool) : List Bool :=
  StandardBitWordVector.encode [x,y,[br],encodeNat a,v]
def init (raw : List Bool) : List Bool :=
  frame (firstBits raw) (secondBits raw) false 0 [true]

def digitBits (raw : List Bool) : List Bool :=
  if (field 0 raw).headD false then
    if (field 1 raw).headD false then
      if (field 2 raw).headD false then [true] else [false]
    else
      if (field 2 raw).headD false then [false] else [true]
  else
    if (field 1 raw).headD false then
      if (field 2 raw).headD false then [false] else [true]
    else
      if (field 2 raw).headD false then [true] else [false]

def nbBits (raw : List Bool) : List Bool :=
  if (field 0 raw).headD false then
    if (field 1 raw).headD false then
      if (field 2 raw).headD false then [true] else [false]
    else [false]
  else
    if (field 1 raw).headD false then [true]
    else if (field 2 raw).headD false then [true] else [false]

def addend (raw : List Bool) : List Bool :=
  if (digitBits raw).headD false then
    StandardBitVariableAdd.addBits (pairBits (field 3 raw) (field 4 raw)) else field 3 raw

def next (raw : List Bool) : List Bool :=
  assemble [fun w => (field 0 w).tail,fun w => (field 1 w).tail,nbBits,addend,
    fun w => false::field 4 w] raw

def satDiff (raw : List Bool) : List Bool :=
  if (field 2 raw).headD false then [] else field 3 raw

def finish (raw : List Bool) : List Bool :=
  StandardBitPairMaps.parallel satDiff (field 2) raw

def body (raw : List Bool) : List Bool :=
  if (field 0 raw).isEmpty then
    if (field 1 raw).isEmpty then false::finish raw else true::next raw
  else true::next raw

theorem true_polyBitTime : PolyBitTime (fun _ : List Bool => [true]) := by
  simpa only [Function.comp_def] using polyBitTime_comp
    StandardBitPairSanitize.empty_polyBitTime (StandardBitPrepend.prepend_polyBitTime true)

theorem ite_bit_poly (b : List Bool → Bool) (f g : List Bool → List Bool)
    (hb : PolyBitTime (fun x => [b x])) (hf : PolyBitTime f) (hg : PolyBitTime g) :
    PolyBitTime (fun x => if b x then g x else f x) :=
  StandardBitConditionalBitTime.conditional_polyBitTime b f g hb hf hg

theorem xbit_polyBitTime : PolyBitTime (fun raw => [(field 0 raw).headD false]) :=
  polyBitTime_comp (field_polyBitTime 0) StandardBitHead.head_polyBitTime
theorem ybit_polyBitTime : PolyBitTime (fun raw => [(field 1 raw).headD false]) :=
  polyBitTime_comp (field_polyBitTime 1) StandardBitHead.head_polyBitTime
theorem bbit_polyBitTime : PolyBitTime (fun raw => [(field 2 raw).headD false]) :=
  polyBitTime_comp (field_polyBitTime 2) StandardBitHead.head_polyBitTime

theorem digitBits_polyBitTime : PolyBitTime digitBits := by
  have hx := xbit_polyBitTime
  have hy := ybit_polyBitTime
  have hb := bbit_polyBitTime
  have ht := true_polyBitTime
  have hf := StandardBitPairSanitize.false_polyBitTime
  have hbbt : PolyBitTime (fun raw =>
      if (field 2 raw).headD false then [true] else [false]) :=
    ite_bit_poly (fun raw => (field 2 raw).headD false)
      (fun _ => [false]) (fun _ => [true]) hb hf ht
  have hbbf : PolyBitTime (fun raw =>
      if (field 2 raw).headD false then [false] else [true]) :=
    ite_bit_poly (fun raw => (field 2 raw).headD false)
      (fun _ => [true]) (fun _ => [false]) hb ht hf
  have hyt : PolyBitTime (fun raw =>
      if (field 1 raw).headD false then
        (if (field 2 raw).headD false then [true] else [false])
      else (if (field 2 raw).headD false then [false] else [true])) :=
    ite_bit_poly (fun raw => (field 1 raw).headD false)
      (fun raw => if (field 2 raw).headD false then [false] else [true])
      (fun raw => if (field 2 raw).headD false then [true] else [false]) hy hbbf hbbt
  have hyf : PolyBitTime (fun raw =>
      if (field 1 raw).headD false then
        (if (field 2 raw).headD false then [false] else [true])
      else (if (field 2 raw).headD false then [true] else [false])) :=
    ite_bit_poly (fun raw => (field 1 raw).headD false)
      (fun raw => if (field 2 raw).headD false then [true] else [false])
      (fun raw => if (field 2 raw).headD false then [false] else [true]) hy hbbt hbbf
  exact ite_bit_poly (fun raw => (field 0 raw).headD false)
    (fun raw => if (field 1 raw).headD false then
        (if (field 2 raw).headD false then [false] else [true])
      else (if (field 2 raw).headD false then [true] else [false]))
    (fun raw => if (field 1 raw).headD false then
        (if (field 2 raw).headD false then [true] else [false])
      else (if (field 2 raw).headD false then [false] else [true])) hx hyf hyt

theorem nbBits_polyBitTime : PolyBitTime nbBits := by
  have hx := xbit_polyBitTime
  have hy := ybit_polyBitTime
  have hb := bbit_polyBitTime
  have ht := true_polyBitTime
  have hf := StandardBitPairSanitize.false_polyBitTime
  have hbbt : PolyBitTime (fun raw =>
      if (field 2 raw).headD false then [true] else [false]) :=
    ite_bit_poly (fun raw => (field 2 raw).headD false)
      (fun _ => [false]) (fun _ => [true]) hb hf ht
  have hyt : PolyBitTime (fun raw =>
      if (field 1 raw).headD false then
        (if (field 2 raw).headD false then [true] else [false]) else [false]) :=
    ite_bit_poly (fun raw => (field 1 raw).headD false)
      (fun _ => [false])
      (fun raw => if (field 2 raw).headD false then [true] else [false]) hy hf hbbt
  have hyf : PolyBitTime (fun raw =>
      if (field 1 raw).headD false then [true]
      else if (field 2 raw).headD false then [true] else [false]) :=
    ite_bit_poly (fun raw => (field 1 raw).headD false)
      (fun raw => if (field 2 raw).headD false then [true] else [false])
      (fun _ => [true]) hy hbbt ht
  exact ite_bit_poly (fun raw => (field 0 raw).headD false) _ _ hx hyf hyt

theorem init_polyBitTime : PolyBitTime init := by
  have h := StandardBitWordVector.assemble_polyBitTime
    [firstBits,secondBits,fun _ : List Bool => [false],fun _ : List Bool => [],
      fun _ : List Bool => [true]] (by
      intro f hf
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
      rcases hf with rfl|rfl|rfl|rfl|rfl
      · exact first_polyBitTime
      · exact secondBits_polyBitTime
      · exact StandardBitPairSanitize.false_polyBitTime
      · exact StandardBitPairSanitize.empty_polyBitTime
      · exact true_polyBitTime)
  exact h

theorem addend_polyBitTime (hadd : PolyBitTime StandardBitVariableAdd.addBits) :
    PolyBitTime addend := by
  have hp := StandardBitPairMaps.parallel_polyBitTime (field 3) (field 4)
    (field_polyBitTime 3) (field_polyBitTime 4)
  have hs := polyBitTime_comp hp hadd
  have heq : StandardBitVariableAdd.addBits ∘
      StandardBitPairMaps.parallel (field 3) (field 4)=
      (fun raw => StandardBitVariableAdd.addBits (pairBits (field 3 raw) (field 4 raw))) := by
    funext raw
    rw [Function.comp_apply,StandardBitPairMaps.parallel_pair]
  rw [heq] at hs
  have hd : (fun raw => [(digitBits raw).headD false])=digitBits := by
    funext raw
    simp only [digitBits]; split_ifs <;> rfl
  exact ite_bit_poly (fun raw => (digitBits raw).headD false) (field 3)
    (fun raw => StandardBitVariableAdd.addBits (pairBits (field 3 raw) (field 4 raw)))
    (hd ▸ digitBits_polyBitTime) (field_polyBitTime 3) hs

theorem next_polyBitTime (hadd : PolyBitTime StandardBitVariableAdd.addBits) : PolyBitTime next := by
  have ht0 := polyBitTime_comp (field_polyBitTime 0) StandardBitHalve.halve_polyBitTime
  have ht1 := polyBitTime_comp (field_polyBitTime 1) StandardBitHalve.halve_polyBitTime
  have hs := polyBitTime_comp (field_polyBitTime 4) (StandardBitPrepend.prepend_polyBitTime false)
  apply StandardBitWordVector.assemble_polyBitTime
  intro f hf
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl
  · exact ht0
  · exact ht1
  · exact nbBits_polyBitTime
  · exact addend_polyBitTime hadd
  · exact hs

theorem satDiff_polyBitTime : PolyBitTime satDiff :=
  ite_bit_poly (fun raw => (field 2 raw).headD false) (field 3)
    (fun _ => []) bbit_polyBitTime (field_polyBitTime 3)
    StandardBitPairSanitize.empty_polyBitTime

theorem finish_polyBitTime : PolyBitTime finish :=
  StandardBitPairMaps.parallel_polyBitTime satDiff (field 2)
    satDiff_polyBitTime (field_polyBitTime 2)

theorem body_polyBitTime (hadd : PolyBitTime StandardBitVariableAdd.addBits) : PolyBitTime body := by
  have he0 := polyBitTime_comp (field_polyBitTime 0) StandardBitLiteralLength.empty_polyBitTime
  have he1 := polyBitTime_comp (field_polyBitTime 1) StandardBitLiteralLength.empty_polyBitTime
  have hn := polyBitTime_comp (next_polyBitTime hadd) (StandardBitPrepend.prepend_polyBitTime true)
  have hs := polyBitTime_comp finish_polyBitTime (StandardBitPrepend.prepend_polyBitTime false)
  have inner := ite_bit_poly (fun raw => (field 1 raw).isEmpty)
    (List.cons true ∘ next) (List.cons false ∘ finish) he1 hn hs
  exact ite_bit_poly (fun raw => (field 0 raw).isEmpty)
    (List.cons true ∘ next) (fun raw => if (field 1 raw).isEmpty then false::finish raw
      else true::next raw) he0 hn inner

theorem field_frame (x y : List Bool) (br : Bool) (a : Nat) (v : List Bool) :
    field 0 (frame x y br a v)=x ∧ field 1 (frame x y br a v)=y ∧
    field 2 (frame x y br a v)=[br] ∧ field 3 (frame x y br a v)=encodeNat a ∧
    field 4 (frame x y br a v)=v := by
  simp [frame,StandardBitWordVector.field_encode]

theorem encodeNat_zero : encodeNat 0=[] := rfl
theorem encodeNat_one : encodeNat 1=[true] := rfl
theorem value_true : value [true]=1 := rfl

theorem value_head_tail (w : List Bool) :
    value w=(w.headD false).toNat+2*value w.tail := by
  cases w <;> simp [value]

theorem digit_identity (x y b : Bool) :
    x.toNat+2*(nextBorrow x y b).toNat=y.toNat+b.toNat+(xor3 x y b).toNat := by
  cases x <;> cases y <;> cases b <;> simp [xor3,nextBorrow]

theorem digitBits_eq (raw : List Bool) :
    digitBits raw=[xor3 ((field 0 raw).headD false) ((field 1 raw).headD false)
      ((field 2 raw).headD false)] := by
  cases h0 : (field 0 raw).headD false <;>
    cases h1 : (field 1 raw).headD false <;>
      cases h2 : (field 2 raw).headD false
  all_goals
    simp only [digitBits,xor3]
    rw [h0,h1,h2]
    rfl

theorem nbBits_eq (raw : List Bool) :
    nbBits raw=[nextBorrow ((field 0 raw).headD false) ((field 1 raw).headD false)
      ((field 2 raw).headD false)] := by
  cases h0 : (field 0 raw).headD false <;>
    cases h1 : (field 1 raw).headD false <;>
      cases h2 : (field 2 raw).headD false
  all_goals
    simp only [nbBits,nextBorrow]
    rw [h0,h1,h2]
    rfl

theorem addend_frame (x y : List Bool) (br : Bool) (a : Nat) (v : List Bool) :
    addend (frame x y br a v)=
      if xor3 (x.headD false) (y.headD false) br then encodeNat (a+value v)
      else encodeNat a := by
  have h := field_frame x y br a v
  have hd := digitBits_eq (frame x y br a v)
  simp only [addend,hd,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,List.headD_cons,
    StandardBitVariableAdd.add_pair,value_encode_nat]

theorem encode_ite (d : Bool) (a n : Nat) :
    (if d then encodeNat (a+n) else encodeNat a)=encodeNat (if d then a+n else a) := by
  cases d <;> rfl

theorem next_frame (x y : List Bool) (br : Bool) (a : Nat) (v : List Bool) :
    next (frame x y br a v)=
      frame x.tail y.tail (nextBorrow (x.headD false) (y.headD false) br)
        (if xor3 (x.headD false) (y.headD false) br then a+value v else a)
        (false::v) := by
  have h := field_frame x y br a v
  have hn := nbBits_eq (frame x y br a v)
  simp only [next,assemble,List.map_cons,List.map_nil,h.1,h.2.1,h.2.2.2.2]
  rw [hn]
  simp only [h.1,h.2.1,h.2.2.1,List.headD_cons]
  rw [addend_frame,encode_ite]
  rfl

theorem finish_frame (x y : List Bool) (br : Bool) (a : Nat) (v : List Bool) :
    finish (frame x y br a v)=pairBits (if br then [] else encodeNat a) [br] := by
  have h := field_frame x y br a v
  simp only [finish,StandardBitPairMaps.parallel_pair,satDiff,h.2.2.1,h.2.2.2.1,
    List.headD_cons]

theorem body_stop (br : Bool) (a : Nat) (v : List Bool) :
    body (frame [] [] br a v)=false::finish (frame [] [] br a v) := by
  have h := field_frame [] [] br a v
  simp [body,h.1,h.2.1]

theorem body_continue (x y : List Bool) (br : Bool) (a : Nat) (v : List Bool)
    (h : ¬ (x.isEmpty ∧ y.isEmpty)) :
    body (frame x y br a v)=true::next (frame x y br a v) := by
  have hf := field_frame x y br a v
  simp only [body,hf.1,hf.2.1]
  cases hx : x.isEmpty <;> cases hy : y.isEmpty <;> simp_all

theorem tail_sum_lt (x y : List Bool) (h : ¬ (x.isEmpty ∧ y.isEmpty)) :
    x.tail.length+y.tail.length<x.length+y.length := by
  cases x <;> cases y <;> simp [List.isEmpty] at h <;> simp [List.tail] <;> omega

theorem halt_sat (X Y a v : Nat) (br : Bool) (hpos : 0<v) (ha : a<v)
    (hinv : X+v*br.toNat=Y+a) :
    (if br then 0 else a)=X-Y ∧ br=decide (X<Y) := by
  cases br with
  | false =>
    simp only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero,Bool.false_eq_true,ite_false] at hinv ⊢
    have : ¬ X<Y := by omega
    simp [this,hinv]
  | true =>
    simp only [Bool.toNat_true,Nat.mul_one,ite_true] at hinv ⊢
    have : X<Y := by omega
    simp [this]
    omega

theorem halt_output (X Y a v : Nat) (br : Bool) (hpos : 0<v) (ha : a<v)
    (hinv : X+v*br.toNat=Y+a) :
    pairBits (if br then [] else encodeNat a) [br]=
      pairBits (encodeNat (X-Y)) [decide (X<Y)] := by
  obtain ⟨hsub,hcmp⟩ := halt_sat X Y a v br hpos ha hinv
  cases br with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at hsub hcmp ⊢
    rw [hsub,hcmp]
  | true =>
    simp only [ite_true] at hsub hcmp ⊢
    rw [hcmp,← hsub,encodeNat_zero]

theorem ite_digit (d : Bool) (a n : Nat) :
    (if d then a+n else a)=a+n*d.toNat := by
  cases d <;> simp

theorem inv_step (X Y a k : Nat) (x y : List Bool) (br : Bool)
    (hinv : X+2^k*value y+2^k*br.toNat=Y+a+2^k*value x) :
    X+2^(k+1)*value y.tail+2^(k+1)*(nextBorrow (x.headD false) (y.headD false) br).toNat=
      Y+(if xor3 (x.headD false) (y.headD false) br then a+2^k else a)+
        2^(k+1)*value x.tail := by
  rw [value_head_tail x,value_head_tail y] at hinv
  simp only [Nat.mul_add] at hinv
  rw [← Nat.mul_assoc (2^k),← Nat.mul_assoc (2^k)] at hinv
  have hpow : 2^(k+1)=2^k*2 := Nat.pow_succ 2 k
  rw [hpow,ite_digit]
  have hid := congrArg (fun t => 2^k*t)
    (digit_identity (x.headD false) (y.headD false) br)
  simp only [Nat.mul_add] at hid
  rw [← Nat.mul_assoc (2^k) 2] at hid
  omega

theorem advance_lt (a k : Nat) (d : Bool) (ha : a<2^k) :
    (if d then a+2^k else a)<2^(k+1) := by
  have hpow : 2^(k+1)=2^k*2 := Nat.pow_succ 2 k
  rw [hpow]
  cases d <;> simp <;> omega

theorem frame_length (B : Nat) (x y : List Bool) (br : Bool) (a : Nat) (v : List Bool)
    (hxy : x.length+y.length≤B) (ha : (encodeNat a).length≤B) (hv : v.length≤B+1) :
    (frame x y br a v).length≤6*B+9 := by
  have hlen := StandardBitWordVector.encode_length [x,y,[br],encodeNat a,v]
  simp only [frame,hlen,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.length_singleton]
  omega

theorem eval_aux (B X Y : Nat) :
    ∀ n x y br a k v,
      n=x.length+y.length → k+n≤B → value v=2^k → v.length≤k+1 → a<2^k →
      X+2^k*value y+2^k*br.toNat=Y+a+2^k*value x →
      ∃ t≤n+1, StandardBitFlagLoop.Eval body (6*B+9) (frame x y br a v)
        (pairBits (encodeNat (X-Y)) [decide (X<Y)]) t := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro x y br a k v hn hkrem hv hlenv ha hinv
    have hxy : x.length+y.length≤B := by omega
    have hk : k≤B := by omega
    have haenc : (encodeNat a).length≤B :=
      (PakWeightedScannerDPBinaryWidths.encode_length_of_lt_pow ha).trans hk
    have hvB : v.length≤B+1 := by omega
    have hlen := frame_length B x y br a v hxy haenc hvB
    by_cases hstop : x.isEmpty ∧ y.isEmpty
    · have hx : x=[] := List.isEmpty_iff.mp hstop.1
      have hy : y=[] := List.isEmpty_iff.mp hstop.2
      subst hx; subst hy
      have hn0 : n=0 := by simpa using hn
      have hpos : 0<2^k := Nat.two_pow_pos k
      have hhalt := halt_output X Y a (2^k) br hpos ha (by
        simpa [value,Nat.mul_zero,Nat.add_zero] using hinv)
      refine ⟨1,by omega,?_⟩
      have hb := body_stop br a v
      have ht : (body (frame [] [] br a v)).tail=finish (frame [] [] br a v) := by
        rw [hb,List.tail_cons]
      have hf := finish_frame [] [] br a v
      have hflag : (body (frame [] [] br a v)).headD false=false := by
        rw [hb]; rfl
      simpa only [ht,hf,hhalt] using
        (StandardBitFlagLoop.Eval.stop hlen hflag :
          StandardBitFlagLoop.Eval body (6*B+9) (frame [] [] br a v)
            (body (frame [] [] br a v)).tail 1)
    · have hdec := tail_sum_lt x y hstop
      have hn' : x.tail.length+y.tail.length<n := by simpa [hn] using hdec
      have hbod := body_continue x y br a v hstop
      have hnext := next_frame x y br a v
      have hflag : (body (frame x y br a v)).headD false=true := by
        rw [hbod]; rfl
      have htail : (body (frame x y br a v)).tail=
          frame x.tail y.tail (nextBorrow (x.headD false) (y.headD false) br)
            (if xor3 (x.headD false) (y.headD false) br then a+value v else a)
            (false::v) := by
        rw [hbod,List.tail_cons,hnext]
      have hv' : value (false::v)=2^(k+1) := by
        simp only [value,Bool.toNat_false,Nat.zero_add,hv]
        rw [Nat.pow_succ,Nat.mul_comm]
      have ha' : (if xor3 (x.headD false) (y.headD false) br then a+value v else a)<2^(k+1) := by
        simpa [hv] using advance_lt a k (xor3 (x.headD false) (y.headD false) br) ha
      have hinv' := inv_step X Y a k x y br hinv
      have hinv'' :
          X+2^(k+1)*value y.tail+2^(k+1)*
            (nextBorrow (x.headD false) (y.headD false) br).toNat=
          Y+(if xor3 (x.headD false) (y.headD false) br then a+value v else a)+
            2^(k+1)*value x.tail := by
        simpa [hv] using hinv'
      have hlenv' : (false::v).length≤(k+1)+1 := by
        simp only [List.length_cons]; omega
      have hkrem' : (k+1)+(x.tail.length+y.tail.length)≤B := by
        have : 1≤x.length+y.length := by
          cases x <;> cases y <;> simp [List.isEmpty] at hstop <;> omega
        omega
      obtain ⟨t,ht,he⟩ := ih (x.tail.length+y.tail.length) hn' x.tail y.tail
        (nextBorrow (x.headD false) (y.headD false) br)
        (if xor3 (x.headD false) (y.headD false) br then a+value v else a)
        (k+1) (false::v) rfl hkrem' hv' hlenv' ha' hinv''
      refine ⟨t+1,by omega,?_⟩
      exact StandardBitFlagLoop.Eval.next hlen hflag (htail.symm ▸ he)

theorem eval (B : Nat) (X Y : Nat) (x y : List Bool) (br : Bool) (a k : Nat)
    (v : List Bool)
    (hkrem : k+(x.length+y.length)≤B) (hv : value v=2^k) (hlenv : v.length≤k+1)
    (ha : a<2^k)
    (hinv : X+2^k*value y+2^k*br.toNat=Y+a+2^k*value x) :
    ∃ t≤x.length+y.length+1, StandardBitFlagLoop.Eval body (6*B+9)
      (frame x y br a v) (pairBits (encodeNat (X-Y)) [decide (X<Y)]) t :=
  eval_aux B X Y (x.length+y.length) x y br a k v rfl hkrem hv hlenv ha hinv

theorem subCompare_polyBitTime (hadd : PolyBitTime StandardBitVariableAdd.addBits) :
    PolyBitTime subCompareBits := by
  apply StandardBitInitializedFlagLoop.polyBitTime init body subCompareBits
    init_polyBitTime (body_polyBitTime hadd) (12*Polynomial.X+15) (2*Polynomial.X+1)
  intro raw
  have hproj := StandardBitWordVector.projection_lengths raw
  have hB : 0+(firstBits raw).length+(secondBits raw).length≤2*raw.length+1 := by omega
  have hinv :
      value (firstBits raw)+2^0*value (secondBits raw)+2^0*false.toNat=
        value (secondBits raw)+0+2^0*value (firstBits raw) := by
    simp [Nat.pow_zero,Bool.toNat_false]; omega
  obtain ⟨t,ht,he⟩ := eval (2*raw.length+1) (value (firstBits raw))
    (value (secondBits raw)) (firstBits raw) (secondBits raw) false 0 0 [true]
    (by simpa using hB) value_true (by simp) (by decide) (by simpa using hinv)
  have hbound : 6*(2*raw.length+1)+9=12*raw.length+15 := by omega
  rw [hbound] at he
  refine ⟨t,?_,?_⟩
  · simpa only [init,subCompareBits,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X] using he
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_X,Polynomial.eval_one]
    omega

theorem subtractBits_eq (raw : List Bool) : subtractBits raw=firstBits (subCompareBits raw) := by
  simp [subtractBits,subCompareBits,firstBits_pair]

theorem ltBits_eq (raw : List Bool) : ltBits raw=secondBits (subCompareBits raw) := by
  simp [ltBits,subCompareBits,secondBits_pair]

theorem subtract_polyBitTime (hadd : PolyBitTime StandardBitVariableAdd.addBits) :
    PolyBitTime subtractBits := by
  have h := polyBitTime_comp (subCompare_polyBitTime hadd) first_polyBitTime
  have he : firstBits ∘ subCompareBits=subtractBits := by
    funext raw; exact (subtractBits_eq raw).symm
  rwa [he] at h

theorem lt_polyBitTime (hadd : PolyBitTime StandardBitVariableAdd.addBits) :
    PolyBitTime ltBits := by
  have h := polyBitTime_comp (subCompare_polyBitTime hadd) secondBits_polyBitTime
  have he : secondBits ∘ subCompareBits=ltBits := by
    funext raw; exact (ltBits_eq raw).symm
  rwa [he] at h

theorem subCompare_pair (x y : List Bool) :
    subCompareBits (pairBits x y)=
      pairBits (encodeNat (value x-value y)) [decide (value x<value y)] := by
  simp [subCompareBits,firstBits_pair,secondBits_pair]

theorem subCompare_none (raw : List Bool) (h : unpairBits raw=none) :
    subCompareBits raw=pairBits [] [false] ∧ subtractBits raw=[] ∧ ltBits raw=[false] := by
  simp [subCompareBits,subtractBits,ltBits,firstBits,secondBits,h,value,encodeNat_zero]

theorem subtraction_comparison_spec
    (hadd : PolyBitTime StandardBitVariableAdd.addBits) :
    PolyBitTime subCompareBits ∧ PolyBitTime subtractBits ∧ PolyBitTime ltBits ∧
    (∀ x y,subCompareBits (pairBits x y)=
      pairBits (encodeNat (value x-value y)) [decide (value x<value y)]) ∧
    (∀ raw,unpairBits raw=none →
      subCompareBits raw=pairBits [] [false] ∧ subtractBits raw=[] ∧ ltBits raw=[false]) :=
  ⟨subCompare_polyBitTime hadd,subtract_polyBitTime hadd,lt_polyBitTime hadd,
    subCompare_pair,subCompare_none⟩
end
end PakFixedPolyomino.StandardBitVariableSubtractLoop
