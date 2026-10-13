import PakFixedPolyomino.StandardBitLiteralLength
import PakFixedPolyomino.StandardBitPairMaps
import PakFixedPolyomino.StandardBitFixedAdd
import PakFixedPolyomino.StandardBitHead

/-! A fixed ordinary polynomial-time tape transducer finds the first literal
false bit in an occupancy word. It counts only the initial true prefix and
returns its canonical binary index paired with a singleton presence flag.
Empty/all-true words return length and false. Every raw word, literal stopping,
counter/frame bound, flag strip, clean output and physical handoff is internal.
Connecting occupancy positions to row-major square cells remains separate. -/
namespace PakFixedPolyomino.StandardBitFirstZero
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition StandardBitMetric
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open StandardBitPairFirstCompaction (firstBits firstBits_pair first_polyBitTime)
open StandardBitPairProjection (secondBits secondBits_pair secondBits_polyBitTime)

def index : List Bool → Nat
  | [] => 0
  | b::w => if b then index w+1 else 0

def firstZeroBits (raw : List Bool) : List Bool :=
  pairBits (encodeNat (index raw)) [decide (index raw<raw.length)]

def frame (w : List Bool) (n : Nat) : List Bool := pairBits w (encodeNat n)
def init (raw : List Bool) : List Bool := frame raw 0
def finish (b : Bool) (raw : List Bool) : List Bool := pairBits (secondBits raw) [b]
def next (raw : List Bool) : List Bool :=
  pairBits (firstBits raw).tail (encodeNat (value (secondBits raw)+1))
def body (raw : List Bool) : List Bool :=
  if (firstBits raw).isEmpty then false::finish false raw
  else if (firstBits raw).headD false then true::next raw else false::finish true raw

theorem index_le (raw : List Bool) : index raw≤raw.length := by
  induction raw with
  | nil => rfl
  | cons b w ih => cases b <;> simp only [index,Bool.false_eq_true,if_false,if_true,List.length_cons] <;> omega

theorem init_polyBitTime : PolyBitTime init := by
  have h := StandardBitPairMaps.parallel_polyBitTime id (fun _ => [])
    identity_polyBitTime StandardBitPairSanitize.empty_polyBitTime
  have he : StandardBitPairMaps.parallel id (fun _ => [])=init := by
    funext raw
    rw [StandardBitPairMaps.parallel_pair]
    rfl
  rwa [he] at h

theorem finish_polyBitTime (b : Bool) : PolyBitTime (finish b) := by
  have hb : PolyBitTime (fun _ : List Bool => [b]) := by
    simpa only [Function.comp_def] using polyBitTime_comp
      StandardBitPairSanitize.empty_polyBitTime (StandardBitPrepend.prepend_polyBitTime b)
  have h := StandardBitPairMaps.parallel_polyBitTime secondBits (fun _ => [b]) secondBits_polyBitTime hb
  have he : StandardBitPairMaps.parallel secondBits (fun _ => [b])=finish b := by
    funext raw
    rw [StandardBitPairMaps.parallel_pair]
    rfl
  rwa [he] at h

theorem next_polyBitTime : PolyBitTime next := by
  have ht := polyBitTime_comp first_polyBitTime StandardBitHalve.halve_polyBitTime
  have hn := polyBitTime_comp secondBits_polyBitTime (StandardBitFixedAdd.fixed_add_polyBitTime 1)
  have h := StandardBitPairMaps.parallel_polyBitTime
    (fun raw => (firstBits raw).tail) (fun raw => encodeNat (value (secondBits raw)+1)) ht hn
  have he : StandardBitPairMaps.parallel (fun raw => (firstBits raw).tail)
      (fun raw => encodeNat (value (secondBits raw)+1))=next := by
    funext raw
    rw [StandardBitPairMaps.parallel_pair]
    rfl
  rwa [he] at h

theorem body_polyBitTime : PolyBitTime body := by
  have hb := polyBitTime_comp first_polyBitTime StandardBitHead.head_polyBitTime
  have hn := polyBitTime_comp next_polyBitTime (StandardBitPrepend.prepend_polyBitTime true)
  have hs := polyBitTime_comp (finish_polyBitTime true) (StandardBitPrepend.prepend_polyBitTime false)
  have hc := StandardBitConditionalBitTime.conditional_polyBitTime
    (fun raw => (firstBits raw).headD false) (List.cons false ∘ finish true)
    (List.cons true ∘ next) hb hs hn
  have he := polyBitTime_comp first_polyBitTime StandardBitLiteralLength.empty_polyBitTime
  have hf := polyBitTime_comp (finish_polyBitTime false) (StandardBitPrepend.prepend_polyBitTime false)
  exact StandardBitConditionalBitTime.conditional_polyBitTime
    (fun raw => (firstBits raw).isEmpty) _ _ he hc hf

theorem body_nil (n : Nat) : body (frame [] n)=false::pairBits (encodeNat n) [false] := by
  simp only [body,frame,firstBits_pair,List.isEmpty_nil,if_true,finish,secondBits_pair]

theorem body_false (w : List Bool) (n : Nat) :
    body (frame (false::w) n)=false::pairBits (encodeNat n) [true] := by
  simp only [body,frame,firstBits_pair,List.isEmpty_cons,Bool.false_eq_true,if_false,
    List.headD_cons,finish,secondBits_pair]

theorem body_true (w : List Bool) (n : Nat) :
    body (frame (true::w) n)=true::frame w (n+1) := by
  simp only [body,frame,firstBits_pair,List.isEmpty_cons,Bool.false_eq_true,if_false,
    List.headD_cons,if_true,next,secondBits_pair,value_encode_nat,List.tail_cons]

theorem frame_length (N : Nat) (w : List Bool) (n : Nat) (h : n+w.length≤N) :
    (frame w n).length≤2*N+1 := by
  have hn := StandardBitLiteralLength.encode_length_le n
  simp only [frame,pairBits_length]
  omega

theorem eval (N : Nat) (w : List Bool) (n : Nat) (h : n+w.length≤N) :
    StandardBitFlagLoop.Eval body (2*N+1) (frame w n)
      (pairBits (encodeNat (n+index w)) [decide (index w<w.length)]) (index w+1) := by
  induction w generalizing n with
  | nil =>
    simpa only [index,List.length_nil,Nat.add_zero,Nat.zero_add,Nat.lt_irrefl,
      decide_false,body_nil,List.tail_cons] using
      (StandardBitFlagLoop.Eval.stop (frame_length N [] n h)
        (by rw [body_nil];rfl) : StandardBitFlagLoop.Eval body (2*N+1)
        (frame [] n) (body (frame [] n)).tail 1)
  | cons b w ih =>
    cases b with
    | false =>
      simpa only [index,Bool.false_eq_true,if_false,Nat.add_zero,List.length_cons,
        Nat.zero_lt_succ,decide_true,body_false,List.tail_cons] using
        (StandardBitFlagLoop.Eval.stop (frame_length N (false::w) n h)
          (by rw [body_false];rfl) : StandardBitFlagLoop.Eval body (2*N+1)
          (frame (false::w) n) (body (frame (false::w) n)).tail 1)
    | true =>
      have hn : n+1+w.length≤N := by simp only [List.length_cons] at h;omega
      have rest := ih (n+1) hn
      have ho : n+1+index w=n+(index w+1) := by omega
      rw [ho] at rest
      have ht : (body (frame (true::w) n)).tail=frame w (n+1) := by rw [body_true];rfl
      have hs := StandardBitFlagLoop.Eval.next (frame_length N (true::w) n h)
        (by rw [body_true];rfl) (ht.symm ▸ rest)
      simpa only [index,if_true,List.length_cons,Nat.add_lt_add_iff_right] using hs

theorem firstZero_polyBitTime : PolyBitTime firstZeroBits := by
  apply StandardBitInitializedFlagLoop.polyBitTime init body firstZeroBits
    init_polyBitTime body_polyBitTime (2*Polynomial.X+1) (Polynomial.X+1)
  intro raw
  refine ⟨index raw+1,?_,?_⟩
  · simpa only [init,firstZeroBits,Nat.zero_add,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one] using
      eval raw.length raw 0 (by omega)
  · simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using
      Nat.add_le_add_right (index_le raw) 1

theorem first_zero_spec : PolyBitTime firstZeroBits ∧
    (∀ raw,firstZeroBits raw=pairBits (encodeNat (index raw)) [decide (index raw<raw.length)]) ∧
    (∀ raw,index raw≤raw.length) :=
  ⟨firstZero_polyBitTime,fun _ => rfl,index_le⟩

end
end PakFixedPolyomino.StandardBitFirstZero
