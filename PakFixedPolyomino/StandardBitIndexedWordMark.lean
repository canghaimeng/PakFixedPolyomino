import PakFixedPolyomino.StandardBitIndexedWordRead
import PakFixedPolyomino.StandardBitFixedAdd
import PakFixedPolyomino.StandardBitReverseClosed

/-! A fixed ordinary polynomial tape-time transducer marks one literal word
cell at a binary index. It scans the physical word once, accumulating a reverse
copy, then uses the actual reversing machine. An index beyond the word leaves
it unchanged, even when the index is exponentially larger than the word.
The counter starts at index+1 and saturates at zero after the chosen cell, so
exactly one cell is changed. All frame widths, iterations, initialization,
conditional control, pairing, cleanup and tape/head handoffs are internal. -/
namespace PakFixedPolyomino.StandardBitIndexedWordMark
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition StandardBitMetric
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open StandardBitPairFirstCompaction (firstBits firstBits_pair first_polyBitTime)
open StandardBitPairProjection (secondBits secondBits_pair secondBits_polyBitTime)
open StandardBitWordVector (encode field field_encode field_polyBitTime)

def emit (n : Nat) (b : Bool) : Bool := if n=1 then true else b
def marked : Nat → List Bool → List Bool
  | _,[] => []
  | n,b::w => emit n b :: marked (n-1) w
def markBits (raw : List Bool) : List Bool :=
  (secondBits raw).set (value (firstBits raw)) true
def reverseBits (raw : List Bool) : List Bool := (markBits raw).reverse
def frame (n : Nat) (w acc : List Bool) : List Bool := encode [encodeNat n,w,acc]
def init (raw : List Bool) : List Bool := frame (value (firstBits raw)+1) (secondBits raw) []
def selected (raw : List Bool) : List Bool :=
  if StandardBitZero.zeroBit (field 0 raw) then [(field 1 raw).headD false]
  else if StandardBitZero.zeroBit (encodeNat (value (field 0 raw)-1)) then [true]
  else [(field 1 raw).headD false]
def accumulate (raw : List Bool) : List Bool :=
  if (selected raw).headD false then true::field 2 raw else false::field 2 raw
def next (raw : List Bool) : List Bool :=
  encode [encodeNat (value (field 0 raw)-1),(field 1 raw).tail,accumulate raw]
def body (raw : List Bool) : List Bool :=
  if (field 1 raw).isEmpty then false::field 2 raw else true::next raw

theorem marked_zero (w : List Bool) : marked 0 w=w := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa only [marked,emit,Nat.zero_ne_one,if_false,Nat.zero_sub] using congrArg (List.cons b) ih

theorem marked_succ (i : Nat) (w : List Bool) : marked (i+1) w=w.set i true := by
  induction w generalizing i with
  | nil => rfl
  | cons b w ih =>
    cases i with
    | zero => simp only [marked,emit,if_true,Nat.add_sub_cancel,marked_zero,List.set_cons_zero]
    | succ i =>
      have h : i+1+1≠1 := by omega
      simpa only [marked,emit,h,if_false,Nat.add_sub_cancel,List.set_cons_succ] using congrArg (List.cons b) (ih i)

theorem field_frame (k n : Nat) (w acc : List Bool) :
    field k (frame n w acc)=([encodeNat n,w,acc][k]?).getD [] := field_encode _ _

theorem init_polyBitTime : PolyBitTime init := by
  have hn := polyBitTime_comp first_polyBitTime (StandardBitFixedAdd.fixed_add_polyBitTime 1)
  have ha := StandardBitWordVector.assemble_polyBitTime
    [(fun raw => encodeNat (value (firstBits raw)+1)),secondBits,(fun _ => [])]
    (by intro f hf; simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
        rcases hf with rfl|rfl|rfl
        · exact hn
        · exact secondBits_polyBitTime
        · exact StandardBitPairSanitize.empty_polyBitTime)
  exact ha

theorem selected_polyBitTime : PolyBitTime selected := by
  have hh := polyBitTime_comp (field_polyBitTime 1) StandardBitHead.head_polyBitTime
  have hp := polyBitTime_comp (field_polyBitTime 0) StandardBitCanonicalDecrement.predecessor_polyBitTime
  have hz := polyBitTime_comp hp StandardBitZero.zero_polyBitTime
  have hc : PolyBitTime (fun _ : List Bool => [true]) := by
    simpa only [Function.comp_def] using polyBitTime_comp
      StandardBitPairSanitize.empty_polyBitTime (StandardBitPrepend.prepend_polyBitTime true)
  have hi := StandardBitConditionalBitTime.conditional_polyBitTime
    (fun raw => StandardBitZero.zeroBit (encodeNat (value (field 0 raw)-1))) _ _ hz hh hc
  have hzero := polyBitTime_comp (field_polyBitTime 0) StandardBitZero.zero_polyBitTime
  exact StandardBitConditionalBitTime.conditional_polyBitTime
    (fun raw => StandardBitZero.zeroBit (field 0 raw)) _ _ hzero hi hh

theorem accumulate_polyBitTime : PolyBitTime accumulate := by
  have hb := polyBitTime_comp selected_polyBitTime StandardBitHead.head_polyBitTime
  have hf := polyBitTime_comp (field_polyBitTime 2) (StandardBitPrepend.prepend_polyBitTime false)
  have ht := polyBitTime_comp (field_polyBitTime 2) (StandardBitPrepend.prepend_polyBitTime true)
  exact StandardBitConditionalBitTime.conditional_polyBitTime
    (fun raw => (selected raw).headD false) _ _ hb hf ht

theorem next_polyBitTime : PolyBitTime next := by
  have hn := polyBitTime_comp (field_polyBitTime 0) StandardBitCanonicalDecrement.predecessor_polyBitTime
  have hw := polyBitTime_comp (field_polyBitTime 1) StandardBitHalve.halve_polyBitTime
  have h := StandardBitWordVector.assemble_polyBitTime
    [(fun raw => encodeNat (value (field 0 raw)-1)),(fun raw => (field 1 raw).tail),accumulate]
    (by intro f hf; simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
        rcases hf with rfl|rfl|rfl
        · exact hn
        · exact hw
        · exact accumulate_polyBitTime)
  exact h

theorem body_polyBitTime : PolyBitTime body := by
  have he := polyBitTime_comp (field_polyBitTime 1) StandardBitLiteralLength.empty_polyBitTime
  have hs := polyBitTime_comp (field_polyBitTime 2) (StandardBitPrepend.prepend_polyBitTime false)
  have hn := polyBitTime_comp next_polyBitTime (StandardBitPrepend.prepend_polyBitTime true)
  exact StandardBitConditionalBitTime.conditional_polyBitTime
    (fun raw => (field 1 raw).isEmpty) _ _ he hn hs

theorem selected_frame (n : Nat) (b : Bool) (w acc : List Bool) :
    selected (frame n (b::w) acc)=[emit n b] := by
  cases n with
  | zero =>
    have hz : StandardBitZero.zeroBit (encodeNat 0)=true :=
      (StandardBitZero.zeroBit_iff _).2 (value_encode_nat 0)
    simp only [selected,field_frame,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some,hz,if_true,List.headD_cons,emit,Nat.zero_ne_one,if_false]
  | succ n =>
    cases n with
    | zero =>
      simp only [selected,field_frame,List.getElem?_cons_zero,List.getElem?_cons_succ,
        Option.getD_some,List.headD_cons,StandardBitBoundedPower.zero_succ,Bool.false_eq_true,
        if_false,value_encode_nat,Nat.add_sub_cancel,emit,if_true]
      rfl
    | succ n =>
      have h : n+1+1≠1 := by omega
      simp only [selected,field_frame,List.getElem?_cons_zero,List.getElem?_cons_succ,
        Option.getD_some,List.headD_cons,StandardBitBoundedPower.zero_succ,Bool.false_eq_true,
        if_false,value_encode_nat,Nat.add_sub_cancel,emit,h]

theorem body_nil (n : Nat) (acc : List Bool) : body (frame n [] acc)=false::acc := by
  simp only [body,field_frame,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,List.isEmpty_nil,if_true]

theorem body_cons (n : Nat) (b : Bool) (w acc : List Bool) :
    body (frame n (b::w) acc)=true::frame (n-1) w (emit n b::acc) := by
  simp only [body,field_frame,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,List.isEmpty_cons,Bool.false_eq_true,if_false,next,value_encode_nat,
    List.tail_cons,accumulate,selected_frame,List.headD_cons]
  cases emit n b <;> rfl

theorem frame_length (B n : Nat) (w acc : List Bool)
    (hn : n<2^(B+1)) (hw : w.length+acc.length≤B) : (frame n w acc).length≤4*B+5 := by
  have hl := PakWeightedScannerDPBinaryWidths.encode_length_of_lt_pow hn
  simp only [frame,StandardBitWordVector.encode_length,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil]
  omega

theorem eval (B : Nat) (w : List Bool) : ∀ n acc, n<2^(B+1) → w.length+acc.length≤B →
    StandardBitFlagLoop.Eval body (4*B+5) (frame n w acc)
      ((marked n w).reverse++acc) (w.length+1) := by
  induction w with
  | nil =>
    intro n acc hn hw
    simpa only [marked,List.reverse_nil,List.nil_append,List.length_nil,Nat.zero_add,
      body_nil,List.tail_cons] using
      (StandardBitFlagLoop.Eval.stop (frame_length B n [] acc hn hw)
        (by rw [body_nil];rfl) : StandardBitFlagLoop.Eval body (4*B+5)
        (frame n [] acc) (body (frame n [] acc)).tail 1)
  | cons b w ih =>
    intro n acc hn hw
    have hn' : n-1<2^(B+1) := (Nat.sub_le n 1).trans_lt hn
    have hw' : w.length+(emit n b::acc).length≤B := by simp only [List.length_cons] at *;omega
    have he := ih (n-1) (emit n b::acc) hn' hw'
    have ht : (body (frame n (b::w) acc)).tail=frame (n-1) w (emit n b::acc) := by rw [body_cons];rfl
    have hs := StandardBitFlagLoop.Eval.next (frame_length B n (b::w) acc hn hw)
      (by rw [body_cons];rfl) (ht.symm ▸ he)
    simpa only [marked,List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons] using hs

theorem reverse_polyBitTime : PolyBitTime reverseBits := by
  apply StandardBitInitializedFlagLoop.polyBitTime init body reverseBits init_polyBitTime
    body_polyBitTime (4*Polynomial.X+5) (Polynomial.X+1)
  intro raw
  have hp := StandardBitWordVector.projection_lengths raw
  have hv : value (firstBits raw)<2^raw.length :=
    (PakFixedWeightedStandardBinaryCount.value_lt_pow_length _).trans_le
      (Nat.pow_le_pow_right (by decide) hp.1)
  have hpow : 2^raw.length<2^(raw.length+1) := by
    rw [Nat.pow_succ];have hpos : 0<2^raw.length := Nat.pow_pos (by decide);omega
  have hn : value (firstBits raw)+1<2^(raw.length+1) := by omega
  refine ⟨(secondBits raw).length+1,?_,?_⟩
  · simpa only [init,reverseBits,markBits,marked_succ,List.append_nil,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X] using
      eval raw.length (secondBits raw) (value (firstBits raw)+1) [] hn (by simpa using hp.2)
  · simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using
      Nat.add_le_add_right hp.2 1

theorem mark_polyBitTime : PolyBitTime markBits := by
  have h := polyBitTime_comp reverse_polyBitTime StandardBitReverseClosed.reverse_polyBitTime
  have he : List.reverse ∘ reverseBits=markBits := by funext raw;exact List.reverse_reverse _
  rwa [he] at h

theorem mark_pair (i : List Bool) (w : List Bool) :
    markBits (pairBits i w)=w.set (value i) true := by
  simp only [markBits,firstBits_pair,secondBits_pair]

theorem mark_none (raw : List Bool) (h : unpairBits raw=none) : markBits raw=[] := by
  simp [markBits,firstBits,secondBits,h]

theorem mark_length (raw : List Bool) : (markBits raw).length=(secondBits raw).length := List.length_set

theorem mark_out_of_range (i : List Bool) (w : List Bool) (h : w.length≤value i) :
    markBits (pairBits i w)=w := by rw [mark_pair];exact List.set_eq_of_length_le h

theorem indexed_word_mark_spec : PolyBitTime markBits ∧
    (∀ i w,markBits (pairBits i w)=w.set (value i) true) ∧
    (∀ raw,unpairBits raw=none → markBits raw=[]) ∧
    (∀ raw,(markBits raw).length=(secondBits raw).length) ∧
    (∀ i w,w.length≤value i → markBits (pairBits i w)=w) :=
  ⟨mark_polyBitTime,mark_pair,mark_none,mark_length,mark_out_of_range⟩

end
end PakFixedPolyomino.StandardBitIndexedWordMark
