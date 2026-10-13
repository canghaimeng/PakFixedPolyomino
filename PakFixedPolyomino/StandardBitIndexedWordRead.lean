import PakFixedPolyomino.StandardBitLiteralLength
import PakFixedPolyomino.StandardBitCanonicalDecrement
import PakFixedPolyomino.StandardBitBoundedPower
import PakFixedPolyomino.StandardBitHead

/-! An ordinary finite tape transducer reads a literal word at a binary index.
It emits the bit and an explicit in-range flag as a literal pair. EVERY raw
input, malformed/empty/highzeros and huge out-of-range indices are covered.
The loop consumes one word cell per counter decrement and stops at literal
word exhaustion, so iteration count is bounded by physical input length.
All binary-counter widths and actual initialization/body/handoff ticks are
proved internally; no unit-cost indexing or arithmetic-operation bound. -/
namespace PakFixedPolyomino.StandardBitIndexedWordRead
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition StandardBitMetric
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open StandardBitPairFirstCompaction (firstBits firstBits_pair first_polyBitTime)
open StandardBitPairProjection (secondBits secondBits_pair secondBits_polyBitTime)

def readBits (raw : List Bool) : List Bool :=
  pairBits [((secondBits raw)[value (firstBits raw)]?).getD false]
    [decide (value (firstBits raw)<(secondBits raw).length)]
def frame (n : Nat) (w : List Bool) : List Bool := pairBits (encodeNat n) w
def init (raw : List Bool) : List Bool := frame (value (firstBits raw)) (secondBits raw)
def found (raw : List Bool) : List Bool := pairBits [(secondBits raw).headD false] [true]
def missing : List Bool → List Bool := fun _ => pairBits [false] [false]
def next (raw : List Bool) : List Bool :=
  pairBits (encodeNat (value (firstBits raw)-1)) (secondBits raw).tail
def body (raw : List Bool) : List Bool :=
  if (secondBits raw).isEmpty then false::missing raw
  else if StandardBitZero.zeroBit (firstBits raw) then false::found raw else true::next raw

theorem constant_pair_polyBitTime (b c : Bool) :
    PolyBitTime (fun _ : List Bool => pairBits [b] [c]) := by
  have hb : PolyBitTime (fun _ : List Bool => [b]) := by
    simpa only [Function.comp_def] using polyBitTime_comp
      StandardBitPairSanitize.empty_polyBitTime (StandardBitPrepend.prepend_polyBitTime b)
  have hc : PolyBitTime (fun _ : List Bool => [c]) := by
    simpa only [Function.comp_def] using polyBitTime_comp
      StandardBitPairSanitize.empty_polyBitTime (StandardBitPrepend.prepend_polyBitTime c)
  have h := StandardBitPairMaps.parallel_polyBitTime (fun _ => [b]) (fun _ => [c]) hb hc
  have he : StandardBitPairMaps.parallel (fun _ : List Bool => [b]) (fun _ => [c])=
      (fun _ => pairBits [b] [c]) := by funext raw;rw [StandardBitPairMaps.parallel_pair]
  rwa [he] at h

theorem init_polyBitTime : PolyBitTime init := by
  have hn := polyBitTime_comp first_polyBitTime StandardBitNormalize.normalize_polyBitTime
  have he : StandardBinaryWordNormalization.normalizeBits ∘ firstBits=
      (fun raw => encodeNat (value (firstBits raw))) := by
    funext raw;exact StandardBinaryWordNormalization.normalize_eq_encodeNat _
  rw [he] at hn
  have h := StandardBitPairMaps.parallel_polyBitTime
    (fun raw => encodeNat (value (firstBits raw))) secondBits hn secondBits_polyBitTime
  have heq : StandardBitPairMaps.parallel (fun raw => encodeNat (value (firstBits raw))) secondBits=init := by
    funext raw;rw [StandardBitPairMaps.parallel_pair];rfl
  rwa [heq] at h

theorem found_polyBitTime : PolyBitTime found := by
  have hb := polyBitTime_comp secondBits_polyBitTime StandardBitHead.head_polyBitTime
  have hc : PolyBitTime (fun _ : List Bool => [true]) := by
    simpa only [Function.comp_def] using polyBitTime_comp
      StandardBitPairSanitize.empty_polyBitTime (StandardBitPrepend.prepend_polyBitTime true)
  have h := StandardBitPairMaps.parallel_polyBitTime
    (fun raw => [(secondBits raw).headD false]) (fun _ => [true]) hb hc
  have he : StandardBitPairMaps.parallel (fun raw => [(secondBits raw).headD false])
      (fun _ => [true])=found := by funext raw;rw [StandardBitPairMaps.parallel_pair];rfl
  rwa [he] at h

theorem next_polyBitTime : PolyBitTime next := by
  have hn := polyBitTime_comp first_polyBitTime StandardBitCanonicalDecrement.predecessor_polyBitTime
  have ht := polyBitTime_comp secondBits_polyBitTime StandardBitHalve.halve_polyBitTime
  have h := StandardBitPairMaps.parallel_polyBitTime
    (fun raw => encodeNat (value (firstBits raw)-1)) (fun raw => (secondBits raw).tail) hn ht
  have he : StandardBitPairMaps.parallel (fun raw => encodeNat (value (firstBits raw)-1))
      (fun raw => (secondBits raw).tail)=next := by funext raw;rw [StandardBitPairMaps.parallel_pair];rfl
  rwa [he] at h

theorem body_polyBitTime : PolyBitTime body := by
  have hz := polyBitTime_comp first_polyBitTime StandardBitZero.zero_polyBitTime
  have hf := polyBitTime_comp found_polyBitTime (StandardBitPrepend.prepend_polyBitTime false)
  have hn := polyBitTime_comp next_polyBitTime (StandardBitPrepend.prepend_polyBitTime true)
  have h := StandardBitConditionalBitTime.conditional_polyBitTime
    (fun raw => StandardBitZero.zeroBit (firstBits raw)) (List.cons true ∘ next)
    (List.cons false ∘ found) hz hn hf
  have he := polyBitTime_comp secondBits_polyBitTime StandardBitLiteralLength.empty_polyBitTime
  have hm := polyBitTime_comp (constant_pair_polyBitTime false false) (StandardBitPrepend.prepend_polyBitTime false)
  exact StandardBitConditionalBitTime.conditional_polyBitTime
    (fun raw => (secondBits raw).isEmpty) _ _ he h hm

theorem body_nil (n : Nat) : body (frame n [])=false::pairBits [false] [false] := by
  simp only [body,frame,secondBits_pair,List.isEmpty_nil,if_true,missing]

theorem body_zero (b : Bool) (w : List Bool) :
    body (frame 0 (b::w))=false::pairBits [b] [true] := by
  simp only [body,frame,secondBits_pair,firstBits_pair,List.isEmpty_cons,
    Bool.false_eq_true,if_false]
  change false::found (pairBits (encodeNat 0) (b::w))=_
  simp only [found,secondBits_pair,List.headD_cons]

theorem body_succ (n : Nat) (b : Bool) (w : List Bool) :
    body (frame (n+1) (b::w))=true::frame n w := by
  simp only [body,frame,firstBits_pair,secondBits_pair,List.isEmpty_cons,Bool.false_eq_true,if_false,
    StandardBitBoundedPower.zero_succ,next,value_encode_nat,Nat.add_sub_cancel,List.tail_cons]

theorem frame_length (B n : Nat) (w : List Bool) (hn : n<2^B) (hw : w.length≤B) :
    (frame n w).length≤3*B+1 := by
  have hl := PakWeightedScannerDPBinaryWidths.encode_length_of_lt_pow hn
  simp only [frame,pairBits_length]
  omega

theorem eval (B : Nat) (w : List Bool) : ∀ n,w.length≤B → n<2^B →
    ∃ t,t≤w.length+1 ∧ StandardBitFlagLoop.Eval body (3*B+1) (frame n w)
      (pairBits [(w[n]?).getD false] [decide (n<w.length)]) t := by
  induction w with
  | nil =>
    intro n hw hn
    refine ⟨1,by omega,?_⟩
    simpa only [List.getElem?_nil,Option.getD_none,List.length_nil,Nat.not_lt_zero,decide_false,
      body_nil,List.tail_cons] using
      (StandardBitFlagLoop.Eval.stop (frame_length B n [] hn hw)
        (by rw [body_nil];rfl) : StandardBitFlagLoop.Eval body (3*B+1)
        (frame n []) (body (frame n [])).tail 1)
  | cons b w ih =>
    intro n hw hn
    cases n with
    | zero =>
      refine ⟨1,by simp,?_⟩
      simpa only [List.getElem?_cons_zero,Option.getD_some,List.length_cons,Nat.zero_lt_succ,
        decide_true,body_zero,List.tail_cons] using
        (StandardBitFlagLoop.Eval.stop (frame_length B 0 (b::w) hn hw)
          (by rw [body_zero];rfl) : StandardBitFlagLoop.Eval body (3*B+1)
          (frame 0 (b::w)) (body (frame 0 (b::w))).tail 1)
    | succ n =>
      obtain ⟨t,ht,he⟩ := ih n (by simp only [List.length_cons] at hw;omega) (by omega)
      have htail : (body (frame (n+1) (b::w))).tail=frame n w := by rw [body_succ];rfl
      refine ⟨t+1,by simp only [List.length_cons];omega,?_⟩
      have h := StandardBitFlagLoop.Eval.next (frame_length B (n+1) (b::w) hn hw)
        (by rw [body_succ];rfl) (htail.symm ▸ he)
      simpa only [List.getElem?_cons_succ,List.length_cons,Nat.add_lt_add_iff_right] using h

theorem read_polyBitTime : PolyBitTime readBits := by
  apply StandardBitInitializedFlagLoop.polyBitTime init body readBits init_polyBitTime
    body_polyBitTime (3*Polynomial.X+1) (Polynomial.X+1)
  intro raw
  have hproj := StandardBitWordVector.projection_lengths raw
  have hn : value (firstBits raw)<2^raw.length :=
    (PakFixedWeightedStandardBinaryCount.value_lt_pow_length _).trans_le
      (Nat.pow_le_pow_right (by decide) hproj.1)
  obtain ⟨t,ht,he⟩ := eval raw.length (secondBits raw) (value (firstBits raw)) hproj.2 hn
  refine ⟨t,?_,?_⟩
  · simpa only [init,readBits,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_X,Polynomial.eval_one] using he
  · simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using
      ht.trans (Nat.add_le_add_right hproj.2 1)

theorem read_pair (i : Nat) (w : List Bool) : readBits (pairBits (encodeNat i) w)=
    pairBits [(w[i]?).getD false] [decide (i<w.length)] := by
  simp only [readBits,firstBits_pair,secondBits_pair,value_encode_nat]

theorem read_none (raw : List Bool) (h : unpairBits raw=none) : readBits raw=pairBits [false] [false] := by
  simp [readBits,firstBits,secondBits,h,value]

theorem indexed_word_read_spec : PolyBitTime readBits ∧
    (∀ i w,readBits (pairBits (encodeNat i) w)=pairBits [(w[i]?).getD false] [decide (i<w.length)]) ∧
    (∀ raw,unpairBits raw=none → readBits raw=pairBits [false] [false]) :=
  ⟨read_polyBitTime,read_pair,read_none⟩

end
end PakFixedPolyomino.StandardBitIndexedWordRead
