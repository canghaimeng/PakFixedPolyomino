import PakFixedPolyomino.StandardBitZero
import PakFixedPolyomino.StandardBitInitializedFlagLoop
import PakFixedPolyomino.StandardBitUnaryBudgetClosed
import PakFixedPolyomino.StandardBitWordVector
import PakFixedPolyomino.StandardBitCanonicalDecrement
import PakFixedPolyomino.StandardBitFixedMultiply
import PakFixedPolyomino.PakWeightedScannerDPBinaryWidths

/-! A concrete ALLraw bounded power transducer. The first paired operand
is an ordinary binary exponent; the second supplies its LITERAL length
budget. Invalid or over-budget inputs use exponent0. Guard, initialization,
decrement, fixed multiplication and every loop tick are compiled internally.
This helper does not replace the ORIGINAL guarded sourceAnswer function.
-/
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace PakFixedPolyomino.StandardBitBoundedPower
noncomputable section
open Computability StandardBitTime StandardBitMetric StandardBitTimeComposition
open PakFixedWeightedStandardBinaryCount (value value_encode_nat)
open StandardBitPairFirstCompaction (firstBits firstBits_pair first_polyBitTime)
open StandardBitPairProjection (secondBits secondBits_pair secondBits_polyBitTime)
open StandardBitUnaryBudgetClosed (predicate predicate_polyBitTime)

def exponent (raw : List Bool) : Nat := if predicate raw then value (firstBits raw) else 0
def frame (n a : Nat) : List Bool := pairBits (encodeNat n) (encodeNat a)
def init (raw : List Bool) : List Bool := frame (exponent raw) 1
def powerBits (c : Nat) (raw : List Bool) : List Bool := encodeNat (c^exponent raw)

theorem exponent_le (raw : List Bool) : exponent raw ≤ raw.length := by
  cases h : unpairBits raw with
  | none => simp [exponent,StandardBitUnaryBudgetClosed.predicate_none raw h]
  | some xy =>
    obtain ⟨x,y⟩ := xy
    have hr := StandardBitPairProjection.unpairBits_eq_some.mp h
    rw [hr]
    simp only [exponent,StandardBitUnaryBudgetClosed.predicate_pair,firstBits_pair]
    split_ifs with hg
    · have hv : value x<y.length := of_decide_eq_true hg
      rw [pairBits_length]
      omega
    · exact Nat.zero_le _

theorem init_polyBitTime : PolyBitTime init := by
  have hn := polyBitTime_comp first_polyBitTime StandardBitNormalize.normalize_polyBitTime
  have he : PolyBitTime (fun raw => encodeNat (exponent raw)) := by
    have h := StandardBitConditionalBitTime.conditional_polyBitTime predicate
      (fun _ => []) (StandardBinaryWordNormalization.normalizeBits ∘ firstBits)
      predicate_polyBitTime StandardBitPairSanitize.empty_polyBitTime hn
    change PolyBitTime (fun raw => if predicate raw then
      StandardBinaryWordNormalization.normalizeBits (firstBits raw) else []) at h
    simpa only [Function.comp_def,
      StandardBinaryWordNormalization.normalize_eq_encodeNat,exponent,
      show encodeNat 0=[] from rfl,apply_ite] using h
  have h1 : PolyBitTime (fun _ : List Bool => [true]) := by
    simpa only [Function.comp_def] using polyBitTime_comp StandardBitPairSanitize.empty_polyBitTime
      (StandardBitPrepend.prepend_polyBitTime true)
  have hpair := StandardBitPairMaps.parallel_polyBitTime
    (fun raw => encodeNat (exponent raw)) (fun _ : List Bool => [true]) he h1
  have heq : StandardBitPairMaps.parallel (fun raw => encodeNat (exponent raw))
      (fun _ : List Bool => [true])=init := by
    funext raw
    rw [StandardBitPairMaps.parallel_pair]
    rfl
  rwa [heq] at hpair

def body (c : Nat) (raw : List Bool) : List Bool :=
  if StandardBitZero.zeroBit (firstBits raw) then false::secondBits raw
  else true::pairBits (encodeNat (value (firstBits raw)-1))
    (encodeNat (c*value (secondBits raw)))

theorem body_polyBitTime (c : Nat) : PolyBitTime (body c) := by
  have hp := polyBitTime_comp first_polyBitTime StandardBitZero.zero_polyBitTime
  have hd := polyBitTime_comp first_polyBitTime StandardBitCanonicalDecrement.predecessor_polyBitTime
  have hm := polyBitTime_comp secondBits_polyBitTime (StandardBitFixedMultiply.fixed_multiply_polyBitTime c)
  have hpair := StandardBitPairMaps.parallel_polyBitTime
    (fun raw => encodeNat (value (firstBits raw)-1))
    (fun raw => encodeNat (c*value (secondBits raw))) hd hm
  have hnext := polyBitTime_comp hpair (StandardBitPrepend.prepend_polyBitTime true)
  have hnext' : PolyBitTime (fun raw => true::pairBits
      (encodeNat (value (firstBits raw)-1)) (encodeNat (c*value (secondBits raw)))) := by
    have heq : List.cons true ∘ StandardBitPairMaps.parallel
        (fun raw => encodeNat (value (firstBits raw)-1))
        (fun raw => encodeNat (c*value (secondBits raw))) =
        (fun raw => true::pairBits (encodeNat (value (firstBits raw)-1))
          (encodeNat (c*value (secondBits raw)))) := by
      funext raw
      rw [Function.comp_apply,StandardBitPairMaps.parallel_pair]
    rwa [heq] at hnext
  have hstop := polyBitTime_comp secondBits_polyBitTime (StandardBitPrepend.prepend_polyBitTime false)
  have h := StandardBitConditionalBitTime.conditional_polyBitTime
    (fun raw => StandardBitZero.zeroBit (firstBits raw))
    (fun raw => true::pairBits (encodeNat (value (firstBits raw)-1))
      (encodeNat (c*value (secondBits raw))))
    (fun raw => false::secondBits raw) hp hnext' hstop
  change PolyBitTime (body c) at h
  exact h

theorem body_zero (c a : Nat) : body c (frame 0 a)=false::encodeNat a := by
  simp only [body,frame,firstBits_pair,secondBits_pair]
  rfl

theorem zero_succ (n : Nat) : StandardBitZero.zeroBit (encodeNat (n+1))=false := by
  cases h : StandardBitZero.zeroBit (encodeNat (n+1)) with
  | false => rfl
  | true =>
    have hz := (StandardBitZero.zeroBit_iff _).mp h
    rw [StandardBitDecrementAlignment.value_eq_original,value_encode_nat] at hz
    omega

theorem body_succ (c n a : Nat) : body c (frame (n+1) a)=true::frame n (c*a) := by
  simp only [body,frame,firstBits_pair,secondBits_pair,zero_succ,Bool.false_eq_true,
    if_false,value_encode_nat,Nat.add_sub_cancel]

theorem power_length (c k : Nat) : (encodeNat (c^k)).length ≤ c*k+1 := by
  apply PakWeightedScannerDPBinaryWidths.encode_length_of_lt_pow
  have hc : c ≤ 2^c := Nat.le_of_lt Nat.lt_two_pow_self
  have hp := Nat.pow_le_pow_left hc k
  rw [← pow_mul] at hp
  have hn : 2^(c*k)<2^(c*k+1) := by
    rw [pow_succ]
    have hpos : 0<2^(c*k) := pow_pos (by decide) _
    omega
  exact hp.trans_lt hn

theorem frame_length (c N n k : Nat) (h : n+k≤N) :
    (frame n (c^k)).length ≤ (c+2)*N+3 := by
  have hn := StandardBinaryFixedMultiplyWord.encode_nat_length_le n
  have hk := power_length c k
  have hm := Nat.mul_le_mul_left c (show k≤N by omega)
  simp only [frame,pairBits_length]
  rw [Nat.add_mul]
  omega

theorem eval (c N n k : Nat) (h : n+k≤N) :
    StandardBitFlagLoop.Eval (body c) ((c+2)*N+3)
      (frame n (c^k)) (encodeNat (c^(n+k))) (n+1) := by
  induction n generalizing k with
  | zero =>
    simpa only [Nat.zero_add,body_zero,List.tail_cons] using
      (StandardBitFlagLoop.Eval.stop (frame_length c N 0 k h)
        (by rw [body_zero];rfl) : StandardBitFlagLoop.Eval (body c) ((c+2)*N+3)
          (frame 0 (c^k)) (body c (frame 0 (c^k))).tail 1)
  | succ n ih =>
    have hn : n+(k+1)≤N := by omega
    have rest := ih (k+1) hn
    have ht : (body c (frame (n+1) (c^k))).tail=frame n (c^(k+1)) := by
      rw [body_succ]
      simp only [List.tail_cons,pow_succ']
    have he : n+1+k=n+(k+1) := by omega
    rw [he]
    exact StandardBitFlagLoop.Eval.next (frame_length c N (n+1) k h)
      (by rw [body_succ];rfl) (ht.symm ▸ rest)

theorem power_polyBitTime (c : Nat) : PolyBitTime (powerBits c) := by
  apply StandardBitInitializedFlagLoop.polyBitTime init (body c) (powerBits c)
    init_polyBitTime (body_polyBitTime c) (Polynomial.C (c+2)*Polynomial.X+3) (Polynomial.X+1)
  intro raw
  refine ⟨exponent raw+1,?_,?_⟩
  · have h := eval c raw.length (exponent raw) 0 (by simpa using exponent_le raw)
    simpa only [init,powerBits,frame,pow_zero,Nat.add_zero,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_ofNat] using h
  · simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using
      Nat.add_le_add_right (exponent_le raw) 1

theorem power_pair (c : Nat) (x y : List Bool) :
    powerBits c (pairBits x y)=encodeNat (c^(if value x<y.length then value x else 0)) := by
  simp only [powerBits,exponent,StandardBitUnaryBudgetClosed.predicate_pair,firstBits_pair,
    decide_eq_true_eq]

theorem power_none (c : Nat) (raw : List Bool) (h : unpairBits raw=none) :
    powerBits c raw=[true] := by
  simp only [powerBits,exponent,StandardBitUnaryBudgetClosed.predicate_none raw h,
    Bool.false_eq_true,if_false,pow_zero]
  rfl

theorem power_spec (c : Nat) :
    PolyBitTime (powerBits c) ∧
    (∀ x y,powerBits c (pairBits x y)=encodeNat (c^(if value x<y.length then value x else 0))) ∧
    (∀ raw,unpairBits raw=none → powerBits c raw=[true]) :=
  ⟨power_polyBitTime c,power_pair c,power_none c⟩

end
end PakFixedPolyomino.StandardBitBoundedPower
