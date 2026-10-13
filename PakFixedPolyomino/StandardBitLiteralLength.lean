import PakFixedPolyomino.StandardBitWordVector
import PakFixedPolyomino.StandardBitInitializedFlagLoop
import PakFixedPolyomino.StandardBitIncrement
import PakFixedPolyomino.StandardBitHalve
import PakFixedPolyomino.StandardBitMealy
import PakFixedPolyomino.StandardBitZero

/-! Count every literal input cell with an actual initialized finite-machine
loop. Numeric zero tests cannot detect an empty word with high zero bits:
the body first marks every remaining literal bit true, then tests that word.
Initialization, body executions, clean handoffs, storage and iteration bounds
are all supplied internally on every raw word. -/
namespace PakFixedPolyomino.StandardBitLiteralLength
noncomputable section
open Computability StandardBitTime StandardBitTimeComposition
open StandardBitWordVector (field field_polyBitTime assemble)

def markDelta (_q : Fin 1) (_b : Bool) : Fin 1 × Bool := (0,true)

theorem marked_zero (w : List Bool) :
    StandardBitZero.zeroBit (StandardBitMealy.transform markDelta 0 w)=w.isEmpty := by
  cases w with
  | nil => rfl
  | cons b w =>
    simp [StandardBitMealy.transform,markDelta,StandardBitZero.zeroBit,
      StandardBitZero.after_any]

theorem empty_polyBitTime : PolyBitTime (fun w : List Bool => [w.isEmpty]) := by
  have h := polyBitTime_comp (StandardBitMealy.transducer_polyBitTime markDelta 0)
    StandardBitZero.zero_polyBitTime
  simpa only [Function.comp_def,marked_zero] using h

def frame (w : List Bool) (n : Nat) : List Bool :=
  StandardBitWordVector.encode [w,encodeNat n]

def init (raw : List Bool) : List Bool := frame raw 0
def lengthBits (raw : List Bool) : List Bool := encodeNat raw.length

def next (raw : List Bool) : List Bool :=
  assemble [fun w => (field 0 w).tail,
    StandardBitIncrement.incrementBits ∘ field 1] raw

def body (raw : List Bool) : List Bool :=
  if (field 0 raw).isEmpty then false::field 1 raw else true::next raw

theorem init_polyBitTime : PolyBitTime init := by
  exact StandardBitWordVector.assemble_polyBitTime
    [id,fun _ : List Bool => []] (by
      intro f hf
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
      rcases hf with rfl|rfl
      · exact identity_polyBitTime
      · exact StandardBitPairSanitize.empty_polyBitTime)

theorem next_polyBitTime : PolyBitTime next := by
  apply StandardBitWordVector.assemble_polyBitTime
  intro f hf
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl
  · exact polyBitTime_comp (field_polyBitTime 0) StandardBitHalve.halve_polyBitTime
  · exact polyBitTime_comp (field_polyBitTime 1) StandardBitIncrement.increment_polyBitTime

theorem body_polyBitTime : PolyBitTime body := by
  have hp := polyBitTime_comp (field_polyBitTime 0) empty_polyBitTime
  have hs := polyBitTime_comp (field_polyBitTime 1) (StandardBitPrepend.prepend_polyBitTime false)
  have hn := polyBitTime_comp next_polyBitTime (StandardBitPrepend.prepend_polyBitTime true)
  exact StandardBitConditionalBitTime.conditional_polyBitTime
    (fun raw => (field 0 raw).isEmpty) (List.cons true ∘ next)
    (List.cons false ∘ field 1) hp hn hs

theorem field_frame (w : List Bool) (n : Nat) :
    field 0 (frame w n)=w ∧ field 1 (frame w n)=encodeNat n := by
  simp [frame,StandardBitWordVector.field_encode]

theorem next_frame (b : Bool) (w : List Bool) (n : Nat) :
    next (frame (b::w) n)=frame w (n+1) := by
  simp only [next,assemble,List.map_cons,List.map_nil,Function.comp_apply,
    (field_frame (b::w) n).1,(field_frame (b::w) n).2,List.tail_cons,
    StandardBitIncrement.increment_encodeNat]
  rfl

theorem encode_length_le (n : Nat) : (encodeNat n).length≤n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← StandardBitIncrement.increment_encodeNat]
    exact (StandardBitIncrement.increment_length _).trans (Nat.add_le_add_right ih 1)

theorem frame_length (w : List Bool) (n : Nat) :
    (frame w n).length≤2*(w.length+n)+2 := by
  have h := encode_length_le n
  simp only [frame,StandardBitWordVector.encode_length,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil]
  omega

theorem eval (w : List Bool) (n : Nat) :
    StandardBitFlagLoop.Eval body (2*(w.length+n)+2) (frame w n)
      (encodeNat (n+w.length)) (w.length+1) := by
  induction w generalizing n with
  | nil =>
    have hb : body (frame [] n)=false::encodeNat n := by
      simp only [body,(field_frame [] n).1,(field_frame [] n).2,List.isEmpty_nil,if_true]
    simpa only [hb,List.tail_cons,List.length_nil,Nat.add_zero] using
      (StandardBitFlagLoop.Eval.stop (frame_length [] n) (by rw [hb];rfl) :
        StandardBitFlagLoop.Eval body (2*(0+n)+2) (frame [] n) (body (frame [] n)).tail 1)
  | cons b w ih =>
    have hb : body (frame (b::w) n)=true::frame w (n+1) := by
      simp only [body,(field_frame (b::w) n).1,List.isEmpty_cons,Bool.false_eq_true,
        if_false,next_frame]
    have hs : 2*(w.length+(n+1))+2=2*((b::w).length+n)+2 := by simp;omega
    have ho : n+(b::w).length=n+1+w.length := by simp;omega
    have hrest := ih (n+1)
    rw [hs,← ho] at hrest
    apply StandardBitFlagLoop.Eval.next (frame_length (b::w) n) (by rw [hb];rfl)
    simpa only [hb,List.tail_cons,List.length_cons] using hrest

theorem length_polyBitTime : PolyBitTime lengthBits := by
  apply StandardBitInitializedFlagLoop.polyBitTime init body lengthBits init_polyBitTime
    body_polyBitTime (2*Polynomial.X+2) (Polynomial.X+1)
  intro raw
  refine ⟨raw.length+1,?_,?_⟩
  · simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_X,init,lengthBits,Nat.add_zero,Nat.zero_add] using eval raw 0
  · simp

theorem length_spec : PolyBitTime lengthBits ∧
    (∀ raw,lengthBits raw=encodeNat raw.length) ∧
    (∀ raw,(lengthBits raw).length≤raw.length) :=
  ⟨length_polyBitTime,fun _ => rfl,fun raw => encode_length_le raw.length⟩

end
end PakFixedPolyomino.StandardBitLiteralLength
