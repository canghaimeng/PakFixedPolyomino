import PakFixedPolyomino.ULogBinaryCounter

/-! Pure little-endian values used to prove iteration of the actual fixed
counter. These arithmetic lemmas do not assert tape execution or bit time;
the one-cell increment/return and their concatenation are separate proofs. -/

namespace PakFixedPolyomino.ULogBinaryCounterValue

def value : List Bool → Nat
  | [] => 0
  | false :: bs => 2 * value bs
  | true :: bs => 1 + 2 * value bs

def increment : List Bool → Option (List Bool)
  | [] => none
  | false :: bs => some (true :: bs)
  | true :: bs => (increment bs).map (false :: ·)

theorem value_lt_pow_length (bs : List Bool) : value bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [value]
  | cons b bs ih =>
      cases b <;> simp only [value, List.length_cons, pow_succ] <;> omega

theorem increment_length {bs next : List Bool} (h : increment bs = some next) :
    next.length = bs.length := by
  induction bs generalizing next with
  | nil => simp [increment] at h
  | cons b bs ih =>
      cases b with
      | false =>
          have hn : true :: bs = next := Option.some.inj h
          rw [← hn]
          rfl
      | true =>
          obtain ⟨tail, ht, hn⟩ := Option.map_eq_some_iff.mp h
          rw [← hn]
          simp only [List.length_cons]
          exact congrArg Nat.succ (ih ht)

theorem increment_value {bs next : List Bool} (h : increment bs = some next) :
    value next = value bs + 1 := by
  induction bs generalizing next with
  | nil => simp [increment] at h
  | cons b bs ih =>
      cases b with
      | false =>
          have hn : true :: bs = next := Option.some.inj h
          rw [← hn]
          simp only [value]
          omega
      | true =>
          obtain ⟨tail, ht, hn⟩ := Option.map_eq_some_iff.mp h
          rw [← hn]
          simp only [value]
          have hv := ih ht
          omega

theorem increment_none_value {bs : List Bool} (h : increment bs = none) :
    value bs = 2 ^ bs.length - 1 := by
  induction bs with
  | nil => simp [value]
  | cons b bs ih =>
      cases b with
      | false => simp [increment] at h
      | true =>
          have ht : increment bs = none := by
            cases hi : increment bs <;> simp [increment, hi] at h ⊢
          have hv := ih ht
          have hp : 0 < 2 ^ bs.length := by positivity
          simp only [value, List.length_cons, pow_succ]
          omega

theorem increment_none_iff (bs : List Bool) :
    increment bs = none ↔ value bs = 2 ^ bs.length - 1 := by
  constructor
  · exact increment_none_value
  · intro hv
    cases hi : increment bs with
    | none => rfl
    | some next =>
        have hlen := increment_length hi
        have hvalue := increment_value hi
        have hlt := value_lt_pow_length next
        rw [hlen] at hlt
        have hp : 0 < 2 ^ bs.length := by positivity
        omega

theorem increment_first_zero {bs next : List Bool} (h : increment bs = some next) :
    ∃ n tail,
      bs = List.replicate n true ++ false :: tail ∧
        next = List.replicate n false ++ true :: tail := by
  induction bs generalizing next with
  | nil => simp [increment] at h
  | cons b bs ih =>
      cases b with
      | false => exact ⟨0, bs, rfl, (Option.some.inj h).symm⟩
      | true =>
          obtain ⟨rest, ht, hn⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨n, tail, hb, hr⟩ := ih ht
          refine ⟨n + 1, tail, ?_, ?_⟩
          · simp [List.replicate_succ, hb]
          · rw [← hn, hr]
            simp [List.replicate_succ]

def remaining (bs : List Bool) : Nat := 2 ^ bs.length - value bs

theorem remaining_positive (bs : List Bool) : 0 < remaining bs := by
  have h := value_lt_pow_length bs
  unfold remaining
  omega

theorem remaining_increment {bs next : List Bool} (h : increment bs = some next) :
    remaining bs = remaining next + 1 := by
  have hlen := increment_length h
  have hv := increment_value h
  have hb := value_lt_pow_length bs
  have hn := value_lt_pow_length next
  unfold remaining
  rw [hlen] at hn ⊢
  omega

theorem remaining_overflow {bs : List Bool} (h : increment bs = none) :
    remaining bs = 1 := by
  have hv := increment_none_value h
  have hp : 0 < 2 ^ bs.length := by positivity
  unfold remaining
  omega

theorem remaining_zero_bits (k : Nat) : remaining (List.replicate k false) = 2 ^ k := by
  have hv : value (List.replicate k false) = 0 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, value, ih]
  simp [remaining, hv]

theorem increment_none_bits {bs : List Bool} (h : increment bs = none) :
    bs = List.replicate bs.length true := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      cases b with
      | false => simp [increment] at h
      | true =>
          have ht : increment bs = none := by
            cases hi : increment bs <;> simp [increment, hi] at h ⊢
          calc
            true :: bs = true :: List.replicate bs.length true :=
              congrArg (List.cons true) (ih ht)
            _ = List.replicate (true :: bs).length true := by
              simp only [List.length_cons, List.replicate_succ]

def ones : List Bool → Nat
  | [] => 0
  | false :: bs => ones bs
  | true :: bs => ones bs + 1

theorem ones_append (xs ys : List Bool) : ones (xs ++ ys) = ones xs + ones ys := by
  induction xs with
  | nil => simp [ones]
  | cons b xs ih => cases b <;> simp [ones, ih] <;> omega

theorem ones_replicate_true (k : Nat) : ones (List.replicate k true) = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ones, ih]

theorem ones_replicate_false (k : Nat) : ones (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ones, ih]

theorem remaining_cons_false (bs : List Bool) :
    remaining (false :: bs) = 2 * remaining bs := by
  have hv := value_lt_pow_length bs
  simp only [remaining, value, List.length_cons, pow_succ]
  omega

theorem remaining_cons_true (bs : List Bool) :
    remaining (true :: bs) + 1 = 2 * remaining bs := by
  have hv := value_lt_pow_length bs
  simp only [remaining, value, List.length_cons, pow_succ]
  omega

theorem remaining_add_ones (bs : List Bool) :
    bs.length + 1 ≤ remaining bs + ones bs := by
  induction bs with
  | nil => simp [remaining, value, ones]
  | cons b bs ih =>
      have hp := remaining_positive bs
      cases b with
      | false => simp only [List.length_cons, remaining_cons_false, ones]; omega
      | true =>
          have hr := remaining_cons_true bs
          simp only [List.length_cons, ones]
          omega

/-- An explicit natural-valued potential. Its identification with actual
one-cell fuel is proved by composing the operational increment runs. -/
def fuel (bs : List Bool) : Nat := 5 * remaining bs + 2 * ones bs - bs.length - 3

theorem fuel_balance (bs : List Bool) :
    fuel bs + bs.length + 3 = 5 * remaining bs + 2 * ones bs := by
  have h := remaining_add_ones bs
  have hp := remaining_positive bs
  unfold fuel
  omega

theorem fuel_overflow {bs : List Bool} (h : increment bs = none) :
    fuel bs = bs.length + 2 := by
  have hr := remaining_overflow h
  have ho : ones bs = bs.length := by
    conv_lhs => rw [increment_none_bits h]
    exact ones_replicate_true _
  have hf := fuel_balance bs
  omega

theorem fuel_increment {bs next : List Bool} (h : increment bs = some next)
    {n : Nat} {tail : List Bool}
    (hb : bs = List.replicate n true ++ false :: tail)
    (hn : next = List.replicate n false ++ true :: tail) :
    fuel bs = 2 * n + 3 + fuel next := by
  have hr := remaining_increment h
  have hl := increment_length h
  have hob : ones bs = n + ones tail := by
    rw [hb, ones_append, ones_replicate_true]; rfl
  have hon : ones next = 1 + ones tail := by
    rw [hn, ones_append, ones_replicate_false]
    simp [ones, Nat.add_comm]
  have hfb := fuel_balance bs
  have hfn := fuel_balance next
  omega

theorem fuel_zero_bits (k : Nat) :
    fuel (List.replicate k false) = 5 * 2 ^ k - k - 3 := by
  simp [fuel, remaining_zero_bits, ones_replicate_false]

end PakFixedPolyomino.ULogBinaryCounterValue
