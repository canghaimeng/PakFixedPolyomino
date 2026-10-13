import PakFixedPolyomino.StandardBitTime

/-! Literal saturated subtraction of one, including arbitrary high zero bits. -/
namespace PakFixedPolyomino.StandardBitDecrementWord

def value : List Bool → Nat
  | [] => 0
  | b::x => b.toNat+2*value x

def borrowBits : List Bool → Option (List Bool)
  | [] => none
  | true::x => some (false::x)
  | false::x => (borrowBits x).map (true::·)

def decrementBits (x : List Bool) : List Bool := (borrowBits x).getD []

def zeroPrefix : List Bool → Nat
  | [] => 0
  | true::_ => 0
  | false::x => zeroPrefix x+1

theorem zeroPrefix_le (x : List Bool) : zeroPrefix x ≤ x.length := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp [zeroPrefix] <;> omega

theorem zeroPrefix_get (x : List Bool) (k : Nat) (hk : k < zeroPrefix x) :
    x[k]'(Nat.lt_of_lt_of_le hk (zeroPrefix_le x)) = false := by
  induction x generalizing k with
  | nil => simp [zeroPrefix] at hk
  | cons b x ih =>
    cases b with
    | true => simp [zeroPrefix] at hk
    | false =>
      cases k with
      | zero => rfl
      | succ k =>
        have hh : k < zeroPrefix x := by simp only [zeroPrefix] at hk; omega
        simpa using ih k hh

theorem zeroPrefix_stop (x : List Bool) (h : zeroPrefix x < x.length) :
    x[zeroPrefix x] = true := by
  induction x with
  | nil => simp [zeroPrefix] at h
  | cons b x ih =>
    cases b with
    | true => rfl
    | false =>
      simp only [zeroPrefix,List.length_cons] at h ⊢
      exact ih (by omega)

theorem borrow_layout (x : List Bool) :
    borrowBits x = if zeroPrefix x = x.length then none
      else some (List.replicate (zeroPrefix x) true ++ false::x.drop (zeroPrefix x+1)) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    cases b with
    | true => simp [borrowBits,zeroPrefix]
    | false =>
      simp only [borrowBits,ih,zeroPrefix,List.length_cons]
      by_cases he : zeroPrefix x = x.length
      · simp [he]
      · simp [he,List.replicate_succ,List.cons_append]

theorem borrow_none_iff (x : List Bool) : borrowBits x = none ↔ value x = 0 := by
  induction x with
  | nil => simp [borrowBits,value]
  | cons b x ih =>
    cases b with
    | true => simp [borrowBits,value]
    | false =>
      cases h : borrowBits x <;> simp [borrowBits,h,value] at *
      · exact ih
      · exact ih

theorem borrow_value {x y : List Bool} (h : borrowBits x = some y) :
    value y+1 = value x := by
  induction x generalizing y with
  | nil => simp [borrowBits] at h
  | cons b x ih =>
    cases b with
    | true =>
      have hy : false::x = y := Option.some.inj h
      subst y
      simp [value,add_comm]
    | false =>
      obtain ⟨z,hz,hy⟩ := Option.map_eq_some_iff.mp h
      subst y
      have hv := ih hz
      simp only [value,Bool.toNat_true,Bool.toNat_false]
      omega

theorem borrow_length {x y : List Bool} (h : borrowBits x = some y) : y.length = x.length := by
  induction x generalizing y with
  | nil => simp [borrowBits] at h
  | cons b x ih =>
    cases b with
    | true =>
      have hy : false::x = y := Option.some.inj h
      subst y
      rfl
    | false =>
      obtain ⟨z,hz,hy⟩ := Option.map_eq_some_iff.mp h
      subst y
      simp only [List.length_cons,ih hz]

theorem decrement_value (x : List Bool) : value (decrementBits x) = value x-1 := by
  cases h : borrowBits x with
  | none => simp [decrementBits,h,(borrow_none_iff x).mp h,value]
  | some y =>
    have hv := borrow_value h
    simp only [decrementBits,h,Option.getD_some]
    omega

theorem decrement_none {x : List Bool} (h : zeroPrefix x = x.length) : decrementBits x = [] := by
  simp [decrementBits,borrow_layout,h]

theorem decrement_layout {x : List Bool} (h : zeroPrefix x < x.length) :
    decrementBits x = List.replicate (zeroPrefix x) true ++ false::x.drop (zeroPrefix x+1) := by
  simp [decrementBits,borrow_layout,show zeroPrefix x ≠ x.length by omega]

theorem decrement_length {x : List Bool} (h : zeroPrefix x < x.length) :
    (decrementBits x).length = x.length := by
  apply borrow_length
  simp [decrementBits,borrow_layout,show zeroPrefix x ≠ x.length by omega]

theorem decrement_length_le (x : List Bool) : (decrementBits x).length ≤ x.length := by
  by_cases h : zeroPrefix x < x.length
  · rw [decrement_length h]
  · have he : zeroPrefix x = x.length := by have := zeroPrefix_le x; omega
    rw [decrement_none he]
    simp

theorem decrement_get_lt {x : List Bool} (h : zeroPrefix x < x.length)
    (k : Nat) (hk : k < zeroPrefix x) : (decrementBits x)[k]? = some true := by
  have hl : k < (List.replicate (zeroPrefix x) true).length := by simpa using hk
  rw [decrement_layout h,List.getElem?_append_left hl,List.getElem?_replicate]
  simp [hk]

theorem decrement_get_eq {x : List Bool} (h : zeroPrefix x < x.length) :
    (decrementBits x)[zeroPrefix x]? = some false := by
  rw [decrement_layout h,List.getElem?_append_right (by simp)]
  simp

theorem decrement_get_gt {x : List Bool} (h : zeroPrefix x < x.length)
    (i : Nat) (hi : zeroPrefix x < i) : (decrementBits x)[i]? = x[i]? := by
  rw [decrement_layout h,List.getElem?_append_right (by simp; omega)]
  simp only [List.length_replicate]
  rw [show i-zeroPrefix x = (i-zeroPrefix x-1)+1 by omega,
    List.getElem?_cons_succ,List.getElem?_drop]
  congr 1
  omega

end PakFixedPolyomino.StandardBitDecrementWord
