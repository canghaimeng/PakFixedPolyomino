import PakFixedPolyomino.StandardBitMealy
import PakFixedPolyomino.StandardBitZero
import PakFixedPolyomino.StandardBitTimeComposition

/-! The least significant literal bit, including the empty word default,
is computed by actual finite tape transducers with complete clean output. -/
namespace PakFixedPolyomino.StandardBitHead
open StandardBitTime StandardBitTimeComposition

def maskDelta (_q : Fin 2) (b : Bool) : Fin 2 × Bool :=
  (1,if _q=0 then b else false)

theorem mask_started (w : List Bool) :
    StandardBitMealy.transform maskDelta 1 w=List.replicate w.length false := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change false :: StandardBitMealy.transform maskDelta 1 w = _
    simpa only [List.length_cons,List.replicate_succ] using congrArg (List.cons false) ih

theorem mask_cons (b : Bool) (w : List Bool) :
    StandardBitMealy.transform maskDelta 0 (b::w)=b::List.replicate w.length false := by
  simp [StandardBitMealy.transform,maskDelta,mask_started]

theorem any_false (n : Nat) : (List.replicate n false).any id=false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ih]

theorem zero_mask (w : List Bool) :
    StandardBitZero.zeroBit (StandardBitMealy.transform maskDelta 0 w)=!(w.headD false) := by
  cases w with
  | nil => rfl
  | cons b w => simp [mask_cons,StandardBitZero.zeroBit,StandardBitZero.after_any,any_false]

def flipDelta (q : Fin 1) (b : Bool) : Fin 1 × Bool := (q,!b)

theorem head_polyBitTime : PolyBitTime (fun w : List Bool => [w.headD false]) := by
  have hmask := StandardBitMealy.transducer_polyBitTime maskDelta 0
  have hzero := polyBitTime_comp hmask StandardBitZero.zero_polyBitTime
  have h := polyBitTime_comp hzero (StandardBitMealy.transducer_polyBitTime flipDelta 0)
  have he : StandardBitMealy.transform flipDelta 0 ∘
      ((fun w => [StandardBitZero.zeroBit w]) ∘ StandardBitMealy.transform maskDelta 0)=
      (fun w : List Bool => [w.headD false]) := by
    funext w
    simp [Function.comp_def,StandardBitMealy.transform,flipDelta,zero_mask]
  rwa [he] at h

theorem head_value (w : List Bool) :
    (w.headD false).toNat=StandardBitDecrementWord.value w % 2 := by
  cases w with
  | nil => rfl
  | cons b w => cases b <;> simp [StandardBitDecrementWord.value]

end PakFixedPolyomino.StandardBitHead
