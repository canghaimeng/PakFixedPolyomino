import PakFixedPolyomino.StandardBitPairMaps
import PakFixedPolyomino.StandardBitPairSanitize

/-! A fixed finite vector of literal binary words is stored as nested pairs.
Every fixed-coordinate access and assembly is compiled from actual ordinary
pairing/projection machines. Vector dimensions are fixed program data, never
an input-dependent family of machines. Numeric DP transfer is separate. -/
namespace PakFixedPolyomino.StandardBitWordVector
open StandardBitTime StandardBitMetric StandardBitTimeComposition
open StandardBitPairFirstCompaction (firstBits firstBits_pair first_polyBitTime)
open StandardBitPairProjection (secondBits secondBits_pair secondBits_polyBitTime)

def encode : List (List Bool) → List Bool
  | [] => []
  | w::ws => pairBits w (encode ws)

def field : Nat → List Bool → List Bool
  | 0 => firstBits
  | k+1 => field k ∘ secondBits

theorem field_nil (k : Nat) : field k []=[] := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

theorem field_encode (ws : List (List Bool)) (k : Nat) :
    field k (encode ws)=ws[k]?.getD [] := by
  induction ws generalizing k with
  | nil => simpa [encode] using field_nil k
  | cons w ws ih =>
    cases k with
    | zero => exact firstBits_pair w (encode ws)
    | succ k => simpa only [encode,field,Function.comp_apply,secondBits_pair,List.getElem?_cons_succ] using ih k

theorem field_polyBitTime (k : Nat) : PolyBitTime (field k) := by
  induction k with
  | zero => exact first_polyBitTime
  | succ k ih => exact polyBitTime_comp secondBits_polyBitTime ih

theorem projection_lengths (raw : List Bool) :
    (firstBits raw).length ≤ raw.length ∧ (secondBits raw).length ≤ raw.length := by
  cases h : unpairBits raw with
  | none => simp [firstBits,secondBits,h]
  | some xy =>
    rcases xy with ⟨x,y⟩
    have he := StandardBitPairProjection.unpairBits_eq_some.mp h
    rw [he,firstBits_pair,secondBits_pair,pairBits_length]
    omega

theorem field_length_le (k : Nat) (raw : List Bool) : (field k raw).length ≤ raw.length := by
  induction k generalizing raw with
  | zero => exact (projection_lengths raw).1
  | succ k ih => exact (ih (secondBits raw)).trans (projection_lengths raw).2

def assemble (fs : List (List Bool → List Bool)) (raw : List Bool) : List Bool :=
  encode (fs.map fun f => f raw)

theorem assemble_nil : assemble []=(fun _ : List Bool => []) := rfl

theorem assemble_cons (f : List Bool → List Bool) (fs : List (List Bool → List Bool)) :
    assemble (f::fs)=StandardBitPairMaps.parallel f (assemble fs) := by
  funext raw
  rw [StandardBitPairMaps.parallel_pair]
  rfl

theorem assemble_polyBitTime (fs : List (List Bool → List Bool))
    (hf : ∀ f ∈ fs, PolyBitTime f) : PolyBitTime (assemble fs) := by
  induction fs with
  | nil => exact StandardBitPairSanitize.empty_polyBitTime
  | cons f fs ih =>
    rw [assemble_cons]
    exact StandardBitPairMaps.parallel_polyBitTime f (assemble fs)
      (hf f (by simp)) (ih (fun g hg => hf g (by simp [hg])))

theorem encode_length (ws : List (List Bool)) :
    (encode ws).length=(ws.map fun w => 2*w.length+1).sum := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [encode,pairBits_length,List.map_cons,List.sum_cons,ih]

theorem encode_length_le (ws : List (List Bool)) (B : Nat)
    (h : ∀ w ∈ ws, w.length ≤ B) : (encode ws).length ≤ ws.length*(2*B+1) := by
  induction ws with
  | nil => simp [encode]
  | cons w ws ih =>
    have hw := h w (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [encode,pairBits_length,List.length_cons]
    rw [Nat.add_mul,Nat.one_mul]
    omega

end PakFixedPolyomino.StandardBitWordVector
