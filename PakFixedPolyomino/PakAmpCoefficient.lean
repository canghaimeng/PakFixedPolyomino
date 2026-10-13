import PakFixedPolyomino.WangRectangleBoundConcrete

/-! Boundary-mask rigidity for the shared-`Q` four-side amplifier. -/

namespace PakFixedPolyomino.PakAmpCoefficient

noncomputable section

private theorem fin_value_eq_zero_of_adjacent
    {α : Type*} {n : ℕ} (hn : 0 < n) (f : Fin n → α)
    (hadj : ∀ (i : Fin n) (hi : i.1 + 1 < n),
      f i = f ⟨i.1 + 1, hi⟩) (j : Fin n) :
    f j = f ⟨0, hn⟩ := by
  have aux : ∀ d : ℕ, (hd : d < n) → f ⟨d, hd⟩ = f ⟨0, hn⟩ := by
    intro d
    induction d with
    | zero => intro hd; rfl
    | succ d ih =>
        intro hsucc
        have hd : d < n := by omega
        have hnext : d + 1 < n := by omega
        calc
          f ⟨d + 1, hnext⟩ = f ⟨d, hd⟩ :=
            (hadj ⟨d, hd⟩ hnext).symm
          _ = f ⟨0, hn⟩ := ih hd
  simpa using aux j.1 j.2

variable {Q : ℕ} [NeZero Q]

abbrev AmpTiling (w h : ℕ) :=
  OpenWangTiling (sharedQAmpWangTile Q) w h

theorem westActive_vertical_step {w h : ℕ} (F : AmpTiling (Q := Q) w h)
    (i : Fin w) (j : Fin h) (hj : j.1 + 1 < h) :
    (F.1 i j).1.westActive =
      (F.1 i ⟨j.1 + 1, hj⟩).1.westActive := by
  have hmatch := F.2.2 i j hj
  exact congrArg AmpVerticalColour.westChain hmatch

theorem eastActive_vertical_step {w h : ℕ} (F : AmpTiling (Q := Q) w h)
    (i : Fin w) (j : Fin h) (hj : j.1 + 1 < h) :
    (F.1 i j).1.eastActive =
      (F.1 i ⟨j.1 + 1, hj⟩).1.eastActive := by
  have hmatch := F.2.2 i j hj
  exact congrArg AmpVerticalColour.eastChain hmatch

theorem southActive_horizontal_step {w h : ℕ}
    (F : AmpTiling (Q := Q) w h)
    (i : Fin w) (j : Fin h) (hi : i.1 + 1 < w) :
    (F.1 i j).1.southActive =
      (F.1 ⟨i.1 + 1, hi⟩ j).1.southActive := by
  have hmatch := F.2.1 i j hi
  exact congrArg AmpHorizontalColour.southChain hmatch

theorem northActive_horizontal_step {w h : ℕ}
    (F : AmpTiling (Q := Q) w h)
    (i : Fin w) (j : Fin h) (hi : i.1 + 1 < w) :
    (F.1 i j).1.northActive =
      (F.1 ⟨i.1 + 1, hi⟩ j).1.northActive := by
  have hmatch := F.2.1 i j hi
  exact congrArg AmpHorizontalColour.northChain hmatch

theorem westActive_vertical_constant {w h : ℕ}
    (F : AmpTiling (Q := Q) w h) (hh : 0 < h)
    (i : Fin w) (j : Fin h) :
    (F.1 i j).1.westActive = (F.1 i ⟨0, hh⟩).1.westActive := by
  apply fin_value_eq_zero_of_adjacent hh
    (fun k => (F.1 i k).1.westActive)
  intro k hk
  exact westActive_vertical_step F i k hk

theorem eastActive_vertical_constant {w h : ℕ}
    (F : AmpTiling (Q := Q) w h) (hh : 0 < h)
    (i : Fin w) (j : Fin h) :
    (F.1 i j).1.eastActive = (F.1 i ⟨0, hh⟩).1.eastActive := by
  apply fin_value_eq_zero_of_adjacent hh
    (fun k => (F.1 i k).1.eastActive)
  intro k hk
  exact eastActive_vertical_step F i k hk

theorem southActive_horizontal_constant {w h : ℕ}
    (F : AmpTiling (Q := Q) w h) (hw : 0 < w)
    (i : Fin w) (j : Fin h) :
    (F.1 i j).1.southActive = (F.1 ⟨0, hw⟩ j).1.southActive := by
  apply fin_value_eq_zero_of_adjacent hw
    (fun k => (F.1 k j).1.southActive)
  intro k hk
  exact southActive_horizontal_step F k j hk

theorem northActive_horizontal_constant {w h : ℕ}
    (F : AmpTiling (Q := Q) w h) (hw : 0 < w)
    (i : Fin w) (j : Fin h) :
    (F.1 i j).1.northActive = (F.1 ⟨0, hw⟩ j).1.northActive := by
  apply fin_value_eq_zero_of_adjacent hw
    (fun k => (F.1 k j).1.northActive)
  intro k hk
  exact northActive_horizontal_step F k j hk

theorem westActive_forces_left_boundary {w h : ℕ}
    (F : AmpTiling (Q := Q) w h) (i : Fin w) (j : Fin h)
    (ha : (F.1 i j).1.westActive = true) : i.1 = 0 := by
  by_contra hi
  let il : Fin w := ⟨i.1 - 1, by omega⟩
  have hm := F.2.1 il j (by dsimp [il]; omega)
  have hil : (⟨il.1 + 1, by dsimp [il]; omega⟩ : Fin w) = i := by
    apply Fin.ext
    dsimp [il]
    omega
  rw [hil] at hm
  have hdead := congrArg AmpHorizontalColour.westDead hm
  simp [sharedQAmpWangTile, ha] at hdead

theorem eastActive_forces_right_boundary {w h : ℕ}
    (F : AmpTiling (Q := Q) w h) (i : Fin w) (j : Fin h)
    (ha : (F.1 i j).1.eastActive = true) : i.1 + 1 = w := by
  by_contra hi
  have hin : i.1 + 1 < w := by omega
  have hm := F.2.1 i j hin
  have hdead := congrArg AmpHorizontalColour.eastDead hm
  simp [sharedQAmpWangTile, ha] at hdead

theorem southActive_forces_bottom_boundary {w h : ℕ}
    (F : AmpTiling (Q := Q) w h) (i : Fin w) (j : Fin h)
    (ha : (F.1 i j).1.southActive = true) : j.1 = 0 := by
  by_contra hj
  let jb : Fin h := ⟨j.1 - 1, by omega⟩
  have hm := F.2.2 i jb (by dsimp [jb]; omega)
  have hjb : (⟨jb.1 + 1, by dsimp [jb]; omega⟩ : Fin h) = j := by
    apply Fin.ext
    dsimp [jb]
    omega
  rw [hjb] at hm
  have hdead := congrArg AmpVerticalColour.southDead hm
  simp [sharedQAmpWangTile, ha] at hdead

theorem northActive_forces_top_boundary {w h : ℕ}
    (F : AmpTiling (Q := Q) w h) (i : Fin w) (j : Fin h)
    (ha : (F.1 i j).1.northActive = true) : j.1 + 1 = h := by
  by_contra hj
  have hin : j.1 + 1 < h := by omega
  have hm := F.2.2 i j hin
  have hdead := congrArg AmpVerticalColour.northDead hm
  simp [sharedQAmpWangTile, ha] at hdead

@[ext] structure BoundaryMask where
  west : Bool
  east : Bool
  south : Bool
  north : Bool
  deriving DecidableEq, Fintype, Repr

def boundaryMask {w h : ℕ} (F : AmpTiling (Q := Q) w h)
    (hw : 0 < w) (hh : 0 < h) : BoundaryMask :=
  { west := (F.1 ⟨0, hw⟩ ⟨0, hh⟩).1.westActive
    east := (F.1 ⟨w - 1, by omega⟩ ⟨0, hh⟩).1.eastActive
    south := (F.1 ⟨0, hw⟩ ⟨0, hh⟩).1.southActive
    north := (F.1 ⟨0, hw⟩ ⟨h - 1, by omega⟩).1.northActive }

theorem westActive_iff_boundaryMask {w h : ℕ}
    (F : AmpTiling (Q := Q) w h) (hw : 0 < w) (hh : 0 < h)
    (i : Fin w) (j : Fin h) :
    (F.1 i j).1.westActive = true ↔
      (boundaryMask F hw hh).west = true ∧ i.1 = 0 := by
  constructor
  · intro ha
    have hi := westActive_forces_left_boundary F i j ha
    have hieq : i = ⟨0, hw⟩ := Fin.eq_of_val_eq hi
    subst i
    refine ⟨?_, rfl⟩
    have hc := westActive_vertical_constant F hh ⟨0, hw⟩ j
    simpa [boundaryMask] using hc.symm.trans ha
  · rintro ⟨ha, hi⟩
    have hieq : i = ⟨0, hw⟩ := Fin.eq_of_val_eq hi
    subst i
    have hc := westActive_vertical_constant F hh ⟨0, hw⟩ j
    exact hc.trans (by simpa [boundaryMask] using ha)

theorem eastActive_iff_boundaryMask {w h : ℕ}
    (F : AmpTiling (Q := Q) w h) (hw : 0 < w) (hh : 0 < h)
    (i : Fin w) (j : Fin h) :
    (F.1 i j).1.eastActive = true ↔
      (boundaryMask F hw hh).east = true ∧ i.1 + 1 = w := by
  constructor
  · intro ha
    have hi := eastActive_forces_right_boundary F i j ha
    have hiv : i.1 = w - 1 := by omega
    have hieq : i = ⟨w - 1, by omega⟩ := Fin.eq_of_val_eq hiv
    rw [hieq] at ha ⊢
    refine ⟨?_, by omega⟩
    have hc := eastActive_vertical_constant F hh ⟨w - 1, by omega⟩ j
    simpa [boundaryMask] using hc.symm.trans ha
  · rintro ⟨ha, hi⟩
    have hiv : i.1 = w - 1 := by omega
    have hieq : i = ⟨w - 1, by omega⟩ := Fin.eq_of_val_eq hiv
    rw [hieq] at ⊢
    have hc := eastActive_vertical_constant F hh ⟨w - 1, by omega⟩ j
    exact hc.trans (by simpa [boundaryMask] using ha)

theorem southActive_iff_boundaryMask {w h : ℕ}
    (F : AmpTiling (Q := Q) w h) (hw : 0 < w) (hh : 0 < h)
    (i : Fin w) (j : Fin h) :
    (F.1 i j).1.southActive = true ↔
      (boundaryMask F hw hh).south = true ∧ j.1 = 0 := by
  constructor
  · intro ha
    have hj := southActive_forces_bottom_boundary F i j ha
    have hjeq : j = ⟨0, hh⟩ := Fin.eq_of_val_eq hj
    subst j
    refine ⟨?_, rfl⟩
    have hc := southActive_horizontal_constant F hw i ⟨0, hh⟩
    simpa [boundaryMask] using hc.symm.trans ha
  · rintro ⟨ha, hj⟩
    have hjeq : j = ⟨0, hh⟩ := Fin.eq_of_val_eq hj
    subst j
    have hc := southActive_horizontal_constant F hw i ⟨0, hh⟩
    exact hc.trans (by simpa [boundaryMask] using ha)

theorem northActive_iff_boundaryMask {w h : ℕ}
    (F : AmpTiling (Q := Q) w h) (hw : 0 < w) (hh : 0 < h)
    (i : Fin w) (j : Fin h) :
    (F.1 i j).1.northActive = true ↔
      (boundaryMask F hw hh).north = true ∧ j.1 + 1 = h := by
  constructor
  · intro ha
    have hj := northActive_forces_top_boundary F i j ha
    have hjv : j.1 = h - 1 := by omega
    have hjeq : j = ⟨h - 1, by omega⟩ := Fin.eq_of_val_eq hjv
    rw [hjeq] at ha ⊢
    refine ⟨?_, by omega⟩
    have hc := northActive_horizontal_constant F hw i ⟨h - 1, by omega⟩
    simpa [boundaryMask] using hc.symm.trans ha
  · rintro ⟨ha, hj⟩
    have hjv : j.1 = h - 1 := by omega
    have hjeq : j = ⟨h - 1, by omega⟩ := Fin.eq_of_val_eq hjv
    rw [hjeq] at ⊢
    have hc := northActive_horizontal_constant F hw i ⟨h - 1, by omega⟩
    exact hc.trans (by simpa [boundaryMask] using ha)

def BoundaryMask.full : BoundaryMask := ⟨true, true, true, true⟩

def BoundaryMask.activeIncidences (mask : BoundaryMask) (w h : ℕ) : ℕ :=
  (if mask.west then h else 0) + (if mask.east then h else 0) +
    (if mask.south then w else 0) + (if mask.north then w else 0)

def BoundaryMask.activeCorners (mask : BoundaryMask) : ℕ :=
  (if mask.west && mask.south then 1 else 0) +
    (if mask.west && mask.north then 1 else 0) +
    (if mask.east && mask.south then 1 else 0) +
    (if mask.east && mask.north then 1 else 0)

def BoundaryMask.qDegree (mask : BoundaryMask) (w h : ℕ) : ℕ :=
  mask.activeIncidences w h - mask.activeCorners

@[simp] theorem BoundaryMask.full_qDegree {w h : ℕ}
    (hw : 2 ≤ w) (hh : 2 ≤ h) :
    BoundaryMask.full.qDegree w h = 2 * w + 2 * h - 4 := by
  simp [BoundaryMask.qDegree, BoundaryMask.activeIncidences,
    BoundaryMask.activeCorners, BoundaryMask.full]
  omega

theorem BoundaryMask.not_full_degree_gap_square
    (mask : BoundaryMask) {n : ℕ} (hn : 2 ≤ n)
    (hnot : mask ≠ BoundaryMask.full) :
    mask.qDegree n n + (n - 2) ≤ BoundaryMask.full.qDegree n n := by
  rcases mask with ⟨west, east, south, north⟩
  cases west <;> cases east <;> cases south <;> cases north <;>
    simp [BoundaryMask.qDegree, BoundaryMask.activeIncidences,
      BoundaryMask.activeCorners, BoundaryMask.full] at hnot ⊢ <;> omega

def nonFullMasks : Finset BoundaryMask :=
  Finset.univ.erase BoundaryMask.full

@[simp] theorem card_boundaryMask : Fintype.card BoundaryMask = 16 := by
  decide

@[simp] theorem card_nonFullMasks : nonFullMasks.card = 15 := by
  simp [nonFullMasks]

theorem BoundaryMask.nonFull_degree_le_sub
    (mask : BoundaryMask) {n : ℕ} (hn : 2 ≤ n)
    (hmask : mask ∈ nonFullMasks) :
    mask.qDegree n n ≤
      BoundaryMask.full.qDegree n n - (n - 2) := by
  apply Nat.le_sub_of_add_le
  exact mask.not_full_degree_gap_square hn (Finset.ne_of_mem_erase hmask)

def nonFullMaskTail (count : BoundaryMask → ℕ) (Q n : ℕ) : ℕ :=
  ∑ mask ∈ nonFullMasks, Q ^ mask.qDegree n n * count mask

theorem nonFullMaskTail_le
    (count : BoundaryMask → ℕ) {Q C n : ℕ}
    (hQ : 0 < Q) (hn : 2 ≤ n)
    (hcount : ∀ mask ∈ nonFullMasks, count mask ≤ C ^ (2 * n)) :
    nonFullMaskTail count Q n ≤
      15 *
        (Q ^ (BoundaryMask.full.qDegree n n - (n - 2)) * C ^ (2 * n)) := by
  unfold nonFullMaskTail
  calc
    ∑ mask ∈ nonFullMasks, Q ^ mask.qDegree n n * count mask ≤
        ∑ _mask ∈ nonFullMasks,
          Q ^ (BoundaryMask.full.qDegree n n - (n - 2)) * C ^ (2 * n) := by
      apply Finset.sum_le_sum
      intro mask hmask
      apply Nat.mul_le_mul
      · exact Nat.pow_le_pow_right hQ
          (mask.nonFull_degree_le_sub hn hmask)
      · exact hcount mask hmask
    _ = 15 *
        (Q ^ (BoundaryMask.full.qDegree n n - (n - 2)) * C ^ (2 * n)) := by
      simp [card_nonFullMasks, Nat.mul_comm]

theorem nonFullMaskTail_lt_fullPower
    (count : BoundaryMask → ℕ) {Q C n : ℕ}
    (hQ : 0 < Q) (hn : 2 ≤ n)
    (hcount : ∀ mask ∈ nonFullMasks, count mask ≤ C ^ (2 * n))
    (hdom : 15 *
        (Q ^ (BoundaryMask.full.qDegree n n - (n - 2)) * C ^ (2 * n)) <
      Q ^ BoundaryMask.full.qDegree n n) :
    nonFullMaskTail count Q n < Q ^ BoundaryMask.full.qDegree n n :=
  (nonFullMaskTail_le count hQ hn hcount).trans_lt hdom

/-- A single fixed base, depending only on the fixed non-amplifier perimeter
base, is large enough for the linear-in-`n` boundary-degree gap. -/
def coefficientBase (C : ℕ) : ℕ := 16 * C ^ 4

theorem coefficientBase_pos {C : ℕ} (hC : 0 < C) :
    0 < coefficientBase C := by
  simp [coefficientBase, hC]

theorem coefficientBase_gap_dominates {C n : ℕ}
    (hC : 0 < C) (hn : 5 ≤ n) :
    15 * C ^ (2 * n) < coefficientBase C ^ (n - 2) := by
  have hgap : 3 ≤ n - 2 := by omega
  have h16 : 15 < 16 ^ (n - 2) := by
    calc
      15 < 16 ^ 1 := by norm_num
      _ ≤ 16 ^ (n - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hexp : 2 * n ≤ 4 * (n - 2) := by omega
  calc
    15 * C ^ (2 * n) < 16 ^ (n - 2) * C ^ (2 * n) := by
      exact Nat.mul_lt_mul_of_pos_right h16 (pow_pos hC _)
    _ ≤ 16 ^ (n - 2) * C ^ (4 * (n - 2)) := by
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hC hexp)
    _ = (16 * C ^ 4) ^ (n - 2) := by
      rw [mul_pow, ← pow_mul]
    _ = coefficientBase C ^ (n - 2) := rfl

theorem nonFullMaskTail_lt_fullPower_fixedBase
    (count : BoundaryMask → ℕ) {C n : ℕ}
    (hC : 0 < C) (hn : 5 ≤ n)
    (hcount : ∀ mask ∈ nonFullMasks, count mask ≤ C ^ (2 * n)) :
    nonFullMaskTail count (coefficientBase C) n <
      coefficientBase C ^ BoundaryMask.full.qDegree n n := by
  apply nonFullMaskTail_lt_fullPower count (coefficientBase_pos hC) (by omega)
    hcount
  let gap := n - 2
  let degree := BoundaryMask.full.qDegree n n
  have hgapDegree : gap ≤ degree := by
    simp [gap, degree, BoundaryMask.full_qDegree (w := n) (h := n)
      (by omega) (by omega)]
    omega
  have hsplit : degree - gap + gap = degree := Nat.sub_add_cancel hgapDegree
  have hdom := coefficientBase_gap_dominates hC hn
  calc
    15 * (coefficientBase C ^ (degree - gap) * C ^ (2 * n)) =
        coefficientBase C ^ (degree - gap) * (15 * C ^ (2 * n)) := by ring
    _ < coefficientBase C ^ (degree - gap) * coefficientBase C ^ gap := by
      exact Nat.mul_lt_mul_of_pos_left hdom
        (pow_pos (coefficientBase_pos hC) _)
    _ = coefficientBase C ^ degree := by
      rw [← pow_add, hsplit]

/-- Canonical independent `Q`-slots for a boundary mask.  West/east sides own
all their incidences.  South/north sides omit a corner precisely when the
corresponding vertical side is active, implementing the four `AmpLegal`
corner identifications without a quotient. -/
def BoundaryMask.horizontalFreeCount (mask : BoundaryMask) (w : ℕ) : ℕ :=
  w - mask.west.toNat - mask.east.toNat

abbrev BoundaryQSlot (mask : BoundaryMask) (w h : ℕ) :=
  (Fin (if mask.west then h else 0) ⊕
    Fin (if mask.east then h else 0)) ⊕
  (Fin (if mask.south then mask.horizontalFreeCount w else 0) ⊕
    Fin (if mask.north then mask.horizontalFreeCount w else 0))

def BoundaryQAssignment (mask : BoundaryMask) (Q w h : ℕ) :=
  BoundaryQSlot mask w h → Fin Q

noncomputable instance (mask : BoundaryMask) (Q w h : ℕ) :
    Fintype (BoundaryQAssignment mask Q w h) := by
  unfold BoundaryQAssignment
  infer_instance

theorem card_boundaryQSlot (mask : BoundaryMask) {w h : ℕ}
    (hw : 2 ≤ w) :
    Fintype.card (BoundaryQSlot mask w h) = mask.qDegree w h := by
  rcases mask with ⟨west, east, south, north⟩
  cases west <;> cases east <;> cases south <;> cases north <;>
    simp [BoundaryQSlot, BoundaryMask.horizontalFreeCount,
      BoundaryMask.qDegree, BoundaryMask.activeIncidences,
      BoundaryMask.activeCorners] <;> omega

theorem card_boundaryQAssignment (mask : BoundaryMask) (Q : ℕ)
    {w h : ℕ} (hw : 2 ≤ w) :
    Fintype.card (BoundaryQAssignment mask Q w h) =
      Q ^ mask.qDegree w h := by
  simp [BoundaryQAssignment, Fintype.card_fun, card_boundaryQSlot mask hw]

def activeSideIndex (b : Bool) {n : ℕ} (hb : b = true)
    (i : Fin n) : Fin (if b then n else 0) := by
  simp [hb]
  exact i

@[simp] theorem activeSideIndex_val (b : Bool) {n : ℕ} (hb : b = true)
    (i : Fin n) : (activeSideIndex b hb i).1 = i.1 := by
  subst b
  rfl

def freeHorizontalIndex (mask : BoundaryMask) {w : ℕ} (hw : 2 ≤ w)
    (i : Fin w)
    (hwest : mask.west = true → i.1 ≠ 0)
    (heast : mask.east = true → i.1 + 1 ≠ w) :
    Fin (mask.horizontalFreeCount w) := by
  refine ⟨i.1 - mask.west.toNat, ?_⟩
  rcases mask with ⟨west, east, south, north⟩
  cases west <;> cases east <;>
    simp_all [BoundaryMask.horizontalFreeCount] <;> omega

@[simp] theorem freeHorizontalIndex_val (mask : BoundaryMask) {w : ℕ}
    (hw : 2 ≤ w) (i : Fin w)
    (hwest : mask.west = true → i.1 ≠ 0)
    (heast : mask.east = true → i.1 + 1 ≠ w) :
    (freeHorizontalIndex mask hw i hwest heast).1 =
      i.1 - mask.west.toNat := rfl

def BoundaryQAssignment.westValue {mask : BoundaryMask} {Q w h : ℕ}
    [NeZero Q] (A : BoundaryQAssignment mask Q w h) (j : Fin h) : Fin Q :=
  if hb : mask.west = true then
    A (.inl (.inl (activeSideIndex mask.west hb j)))
  else 0

def BoundaryQAssignment.eastValue {mask : BoundaryMask} {Q w h : ℕ}
    [NeZero Q] (A : BoundaryQAssignment mask Q w h) (j : Fin h) : Fin Q :=
  if hb : mask.east = true then
    A (.inl (.inr (activeSideIndex mask.east hb j)))
  else 0

def BoundaryQAssignment.southValue {mask : BoundaryMask} {Q w h : ℕ}
    [NeZero Q] (A : BoundaryQAssignment mask Q w h)
    (hw : 2 ≤ w) (hh : 0 < h) (i : Fin w) : Fin Q :=
  if hs : mask.south = true then
    if hwest : mask.west = true ∧ i.1 = 0 then
      A.westValue ⟨0, hh⟩
    else if heast : mask.east = true ∧ i.1 + 1 = w then
      A.eastValue ⟨0, hh⟩
    else
      A (.inr (.inl (activeSideIndex mask.south hs
        (freeHorizontalIndex mask hw i
          (fun h => fun hi => hwest ⟨h, hi⟩)
          (fun h => fun hi => heast ⟨h, hi⟩)))))
  else 0

def BoundaryQAssignment.northValue {mask : BoundaryMask} {Q w h : ℕ}
    [NeZero Q] (A : BoundaryQAssignment mask Q w h)
    (hw : 2 ≤ w) (hh : 0 < h) (i : Fin w) : Fin Q :=
  if hn : mask.north = true then
    if hwest : mask.west = true ∧ i.1 = 0 then
      A.westValue ⟨h - 1, by omega⟩
    else if heast : mask.east = true ∧ i.1 + 1 = w then
      A.eastValue ⟨h - 1, by omega⟩
    else
      A (.inr (.inr (activeSideIndex mask.north hn
        (freeHorizontalIndex mask hw i
          (fun h => fun hi => hwest ⟨h, hi⟩)
          (fun h => fun hi => heast ⟨h, hi⟩)))))
  else 0

def sideIndexToFin (b : Bool) {n : ℕ} :
    Fin (if b then n else 0) → Fin n := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact Fin.elim0
  · simp
    exact id

theorem activeSideIndex_sideIndexToFin (b : Bool) {n : ℕ}
    (hb : b = true) (k : Fin (if b then n else 0)) :
    activeSideIndex b hb (sideIndexToFin b k) = k := by
  subst b
  apply Fin.ext
  rfl

theorem sideIndexToFin_activeSideIndex (b : Bool) {n : ℕ}
    (hb : b = true) (i : Fin n) :
    sideIndexToFin b (activeSideIndex b hb i) = i := by
  subst b
  apply Fin.ext
  rfl

def freeHorizontalPosition (mask : BoundaryMask) {w : ℕ} (hw : 2 ≤ w)
    (k : Fin (mask.horizontalFreeCount w)) : Fin w := by
  refine ⟨k.1 + mask.west.toNat, ?_⟩
  rcases mask with ⟨west, east, south, north⟩
  cases west <;> cases east <;>
    simp_all [BoundaryMask.horizontalFreeCount] <;> omega

theorem freeHorizontalPosition_ne_left (mask : BoundaryMask) {w : ℕ}
    (hw : 2 ≤ w) (k : Fin (mask.horizontalFreeCount w))
    (hwest : mask.west = true) :
    (freeHorizontalPosition mask hw k).1 ≠ 0 := by
  rcases mask with ⟨west, east, south, north⟩
  cases west <;> cases east <;>
    simp_all [freeHorizontalPosition, BoundaryMask.horizontalFreeCount] <;> omega

theorem freeHorizontalPosition_ne_right (mask : BoundaryMask) {w : ℕ}
    (hw : 2 ≤ w) (k : Fin (mask.horizontalFreeCount w))
    (heast : mask.east = true) :
    (freeHorizontalPosition mask hw k).1 + 1 ≠ w := by
  rcases mask with ⟨west, east, south, north⟩
  cases west <;> cases east <;>
    simp_all [freeHorizontalPosition, BoundaryMask.horizontalFreeCount] <;> omega

theorem freeHorizontalIndex_position (mask : BoundaryMask) {w : ℕ}
    (hw : 2 ≤ w) (k : Fin (mask.horizontalFreeCount w))
    (hwest : mask.west = true →
      (freeHorizontalPosition mask hw k).1 ≠ 0)
    (heast : mask.east = true →
      (freeHorizontalPosition mask hw k).1 + 1 ≠ w) :
    freeHorizontalIndex mask hw (freeHorizontalPosition mask hw k)
      hwest heast = k := by
  apply Fin.ext
  rcases mask with ⟨west, east, south, north⟩
  cases west <;> cases east <;>
    simp_all [freeHorizontalPosition, freeHorizontalIndex,
      BoundaryMask.horizontalFreeCount] <;> try rfl <;> omega

theorem freeHorizontalPosition_index (mask : BoundaryMask) {w : ℕ}
    (hw : 2 ≤ w) (i : Fin w)
    (hwest : mask.west = true → i.1 ≠ 0)
    (heast : mask.east = true → i.1 + 1 ≠ w) :
    freeHorizontalPosition mask hw
      (freeHorizontalIndex mask hw i hwest heast) = i := by
  apply Fin.ext
  change i.1 - mask.west.toNat + mask.west.toNat = i.1
  cases hwestBit : mask.west
  · rfl
  · have hi : i.1 ≠ 0 := hwest (by simp [hwestBit])
    simp [hwestBit]
    omega

def boundaryAssignmentOfTiling {Q w h : ℕ} [NeZero Q]
    (F : AmpTiling (Q := Q) w h) (hw : 2 ≤ w) (hh : 0 < h) :
    BoundaryQAssignment (boundaryMask F (by omega) hh) Q w h := by
  intro slot
  rcases slot with ((westSlot | eastSlot) | (southSlot | northSlot))
  · exact (F.1 ⟨0, by omega⟩
      (sideIndexToFin (boundaryMask F (by omega) hh).west westSlot)).1.qWest
  · exact (F.1 ⟨w - 1, by omega⟩
      (sideIndexToFin (boundaryMask F (by omega) hh).east eastSlot)).1.qEast
  · exact (F.1
      (freeHorizontalPosition (boundaryMask F (by omega) hh) hw
        (sideIndexToFin (boundaryMask F (by omega) hh).south southSlot))
      ⟨0, hh⟩).1.qSouth
  · exact (F.1
      (freeHorizontalPosition (boundaryMask F (by omega) hh) hw
        (sideIndexToFin (boundaryMask F (by omega) hh).north northSlot))
      ⟨h - 1, by omega⟩).1.qNorth

/-! ## Forgetting the `Q` labels

The Boolean activity pattern is the `Q = 1` skeleton over which the exact
coefficient fibre will be counted.  The following map is deliberately defined
on the actual amplifier tilings, rather than on an auxiliary boundary code. -/

def eraseAmpRaw {Q : ℕ} (u : AmpRaw Q) : AmpRaw 1 where
  westActive := u.westActive
  eastActive := u.eastActive
  southActive := u.southActive
  northActive := u.northActive
  qWest := 0
  qEast := 0
  qSouth := 0
  qNorth := 0

theorem eraseAmpRaw_legal {Q : ℕ} [NeZero Q] (u : SharedQAmpTile Q) :
    AmpLegal (eraseAmpRaw u.1) := by
  rcases u with ⟨u, hu⟩
  unfold AmpLegal eraseAmpRaw
  simp

def eraseAmpTile {Q : ℕ} [NeZero Q]
    (u : SharedQAmpTile Q) : SharedQAmpTile 1 :=
  ⟨eraseAmpRaw u.1, eraseAmpRaw_legal u⟩

@[simp] theorem eraseAmpTile_westActive {Q : ℕ} [NeZero Q]
    (u : SharedQAmpTile Q) :
    (eraseAmpTile u).1.westActive = u.1.westActive := rfl

@[simp] theorem eraseAmpTile_eastActive {Q : ℕ} [NeZero Q]
    (u : SharedQAmpTile Q) :
    (eraseAmpTile u).1.eastActive = u.1.eastActive := rfl

@[simp] theorem eraseAmpTile_southActive {Q : ℕ} [NeZero Q]
    (u : SharedQAmpTile Q) :
    (eraseAmpTile u).1.southActive = u.1.southActive := rfl

@[simp] theorem eraseAmpTile_northActive {Q : ℕ} [NeZero Q]
    (u : SharedQAmpTile Q) :
    (eraseAmpTile u).1.northActive = u.1.northActive := rfl

theorem eraseAmpTile_horizontal_match {Q : ℕ} [NeZero Q]
    (u v : SharedQAmpTile Q)
    (hm : (sharedQAmpWangTile Q u).east =
      (sharedQAmpWangTile Q v).west) :
    (sharedQAmpWangTile 1 (eraseAmpTile u)).east =
      (sharedQAmpWangTile 1 (eraseAmpTile v)).west := by
  apply AmpHorizontalColour.ext
  · simpa [sharedQAmpWangTile, eraseAmpTile, eraseAmpRaw] using
      congrArg AmpHorizontalColour.westDead hm
  · exact Subsingleton.elim _ _
  · simpa [sharedQAmpWangTile, eraseAmpTile, eraseAmpRaw] using
      congrArg AmpHorizontalColour.eastDead hm
  · exact Subsingleton.elim _ _
  · simpa [sharedQAmpWangTile, eraseAmpTile, eraseAmpRaw] using
      congrArg AmpHorizontalColour.southChain hm
  · simpa [sharedQAmpWangTile, eraseAmpTile, eraseAmpRaw] using
      congrArg AmpHorizontalColour.northChain hm

theorem eraseAmpTile_vertical_match {Q : ℕ} [NeZero Q]
    (u v : SharedQAmpTile Q)
    (hm : (sharedQAmpWangTile Q u).north =
      (sharedQAmpWangTile Q v).south) :
    (sharedQAmpWangTile 1 (eraseAmpTile u)).north =
      (sharedQAmpWangTile 1 (eraseAmpTile v)).south := by
  apply AmpVerticalColour.ext
  · simpa [sharedQAmpWangTile, eraseAmpTile, eraseAmpRaw] using
      congrArg AmpVerticalColour.westChain hm
  · simpa [sharedQAmpWangTile, eraseAmpTile, eraseAmpRaw] using
      congrArg AmpVerticalColour.eastChain hm
  · simpa [sharedQAmpWangTile, eraseAmpTile, eraseAmpRaw] using
      congrArg AmpVerticalColour.southDead hm
  · exact Subsingleton.elim _ _
  · simpa [sharedQAmpWangTile, eraseAmpTile, eraseAmpRaw] using
      congrArg AmpVerticalColour.northDead hm
  · exact Subsingleton.elim _ _

def eraseAmpTiling {Q : ℕ} [NeZero Q] {w h : ℕ}
    (F : AmpTiling (Q := Q) w h) : AmpTiling (Q := 1) w h := by
  refine ⟨fun i j => eraseAmpTile (F.1 i j), ?_⟩
  constructor
  · intro i j hi
    exact eraseAmpTile_horizontal_match _ _ (F.2.1 i j hi)
  · intro i j hj
    exact eraseAmpTile_vertical_match _ _ (F.2.2 i j hj)

@[simp] theorem eraseAmpTiling_cell {Q : ℕ} [NeZero Q] {w h : ℕ}
    (F : AmpTiling (Q := Q) w h) (i : Fin w) (j : Fin h) :
    (eraseAmpTiling F).1 i j = eraseAmpTile (F.1 i j) := rfl

theorem boundaryMask_eraseAmpTiling {Q : ℕ} [NeZero Q]
    {w h : ℕ} (F : AmpTiling (Q := Q) w h) (hw : 0 < w) (hh : 0 < h) :
    boundaryMask (eraseAmpTiling F) hw hh = boundaryMask F hw hh := by
  apply BoundaryMask.ext <;> rfl

/-- The actual fibre of `Q`-labelled amplifier tilings above one Boolean
activity skeleton. -/
abbrev AmpSkeletonFiber {w h : ℕ}
    (Q : ℕ) [NeZero Q] (skeleton : AmpTiling (Q := 1) w h) :=
  {F : AmpTiling (Q := Q) w h // eraseAmpTiling F = skeleton}

noncomputable instance {w h : ℕ} (Q : ℕ) [NeZero Q]
    (skeleton : AmpTiling (Q := 1) w h) :
    Fintype (AmpSkeletonFiber Q skeleton) := Fintype.ofFinite _

def liftAmpRaw {Q w h : ℕ} [NeZero Q]
    (skeleton : AmpTiling (Q := 1) w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : BoundaryQAssignment (boundaryMask skeleton (by omega) hh) Q w h)
    (i : Fin w) (j : Fin h) : AmpRaw Q :=
  let mask := boundaryMask skeleton (by omega) hh
  let u := (skeleton.1 i j).1
  { westActive := u.westActive
    eastActive := u.eastActive
    southActive := u.southActive
    northActive := u.northActive
    qWest := if u.westActive then A.westValue j else 0
    qEast := if u.eastActive then A.eastValue j else 0
    qSouth := if u.southActive then A.southValue hw hh i else 0
    qNorth := if u.northActive then A.northValue hw hh i else 0 }

theorem liftAmpRaw_legal {Q w h : ℕ} [NeZero Q]
    (skeleton : AmpTiling (Q := 1) w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : BoundaryQAssignment (boundaryMask skeleton (by omega) hh) Q w h)
    (i : Fin w) (j : Fin h) : AmpLegal (liftAmpRaw skeleton hw hh A i j) := by
  let mask := boundaryMask skeleton (by omega) hh
  have hwest := westActive_iff_boundaryMask skeleton (by omega) hh i j
  have heast := eastActive_iff_boundaryMask skeleton (by omega) hh i j
  have hsouth := southActive_iff_boundaryMask skeleton (by omega) hh i j
  have hnorth := northActive_iff_boundaryMask skeleton (by omega) hh i j
  unfold AmpLegal
  constructor
  · intro h
    change (skeleton.1 i j).1.westActive = false at h
    simp [liftAmpRaw, h]
  constructor
  · intro h
    change (skeleton.1 i j).1.eastActive = false at h
    simp [liftAmpRaw, h]
  constructor
  · intro h
    change (skeleton.1 i j).1.southActive = false at h
    simp [liftAmpRaw, h]
  constructor
  · intro h
    change (skeleton.1 i j).1.northActive = false at h
    simp [liftAmpRaw, h]
  constructor
  · intro hwact hsact
    change (skeleton.1 i j).1.westActive = true at hwact
    change (skeleton.1 i j).1.southActive = true at hsact
    have hwinfo := hwest.mp hwact
    have hsinfo := hsouth.mp hsact
    have hj : j = ⟨0, hh⟩ := Fin.eq_of_val_eq hsinfo.2
    rw [hj] at hwact hsact ⊢
    simp only [liftAmpRaw, hwact, hsact, if_true]
    unfold BoundaryQAssignment.southValue
    rw [dif_pos hsinfo.1, dif_pos ⟨hwinfo.1, hwinfo.2⟩]
  constructor
  · intro hwact hnact
    change (skeleton.1 i j).1.westActive = true at hwact
    change (skeleton.1 i j).1.northActive = true at hnact
    have hwinfo := hwest.mp hwact
    have hninfo := hnorth.mp hnact
    have hjv : j.1 = h - 1 := by omega
    have hj : j = ⟨h - 1, by omega⟩ := Fin.eq_of_val_eq hjv
    rw [hj] at hwact hnact ⊢
    simp only [liftAmpRaw, hwact, hnact, if_true]
    unfold BoundaryQAssignment.northValue
    rw [dif_pos hninfo.1, dif_pos ⟨hwinfo.1, hwinfo.2⟩]
  constructor
  · intro heact hsact
    change (skeleton.1 i j).1.eastActive = true at heact
    change (skeleton.1 i j).1.southActive = true at hsact
    have heinfo := heast.mp heact
    have hsinfo := hsouth.mp hsact
    have hj : j = ⟨0, hh⟩ := Fin.eq_of_val_eq hsinfo.2
    rw [hj] at heact hsact ⊢
    simp only [liftAmpRaw, heact, hsact, if_true]
    unfold BoundaryQAssignment.southValue
    have hnwest : ¬((boundaryMask skeleton (by omega) hh).west = true ∧ i.1 = 0) := by
      rintro ⟨-, hi⟩
      omega
    rw [dif_pos hsinfo.1, dif_neg hnwest, dif_pos ⟨heinfo.1, heinfo.2⟩]
  · intro heact hnact
    change (skeleton.1 i j).1.eastActive = true at heact
    change (skeleton.1 i j).1.northActive = true at hnact
    have heinfo := heast.mp heact
    have hninfo := hnorth.mp hnact
    have hjv : j.1 = h - 1 := by omega
    have hj : j = ⟨h - 1, by omega⟩ := Fin.eq_of_val_eq hjv
    rw [hj] at heact hnact ⊢
    simp only [liftAmpRaw, heact, hnact, if_true]
    unfold BoundaryQAssignment.northValue
    have hnwest : ¬((boundaryMask skeleton (by omega) hh).west = true ∧ i.1 = 0) := by
      rintro ⟨-, hi⟩
      omega
    rw [dif_pos hninfo.1, dif_neg hnwest, dif_pos ⟨heinfo.1, heinfo.2⟩]

def liftAmpTile {Q w h : ℕ} [NeZero Q]
    (skeleton : AmpTiling (Q := 1) w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : BoundaryQAssignment (boundaryMask skeleton (by omega) hh) Q w h)
    (i : Fin w) (j : Fin h) : SharedQAmpTile Q :=
  ⟨liftAmpRaw skeleton hw hh A i j, liftAmpRaw_legal skeleton hw hh A i j⟩

theorem erase_liftAmpTile {Q w h : ℕ} [NeZero Q]
    (skeleton : AmpTiling (Q := 1) w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : BoundaryQAssignment (boundaryMask skeleton (by omega) hh) Q w h)
    (i : Fin w) (j : Fin h) :
    eraseAmpTile (liftAmpTile skeleton hw hh A i j) = skeleton.1 i j := by
  apply Subtype.ext
  apply AmpRaw.ext
  · rfl
  · rfl
  · rfl
  · rfl
  all_goals exact Subsingleton.elim _ _

theorem liftAmpTile_horizontal_match {Q w h : ℕ} [NeZero Q]
    (skeleton : AmpTiling (Q := 1) w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : BoundaryQAssignment (boundaryMask skeleton (by omega) hh) Q w h)
    (i : Fin w) (j : Fin h) (hi : i.1 + 1 < w) :
    (sharedQAmpWangTile Q (liftAmpTile skeleton hw hh A i j)).east =
      (sharedQAmpWangTile Q
        (liftAmpTile skeleton hw hh A ⟨i.1 + 1, hi⟩ j)).west := by
  let k : Fin w := ⟨i.1 + 1, hi⟩
  have hm := skeleton.2.1 i j hi
  have hleftEast : (skeleton.1 i j).1.eastActive = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hact
    have hb := eastActive_forces_right_boundary skeleton i j hact
    omega
  have hrightWest : (skeleton.1 k j).1.westActive = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hact
    have hb := westActive_forces_left_boundary skeleton k j hact
    dsimp [k] at hb
    omega
  apply AmpHorizontalColour.ext
  · simpa [sharedQAmpWangTile, liftAmpTile, liftAmpRaw, k] using
      congrArg AmpHorizontalColour.westDead hm
  · simp [sharedQAmpWangTile, liftAmpTile, liftAmpRaw, k, hrightWest]
  · simpa [sharedQAmpWangTile, liftAmpTile, liftAmpRaw, k] using
      congrArg AmpHorizontalColour.eastDead hm
  · simp [sharedQAmpWangTile, liftAmpTile, liftAmpRaw, hleftEast]
  · simpa [sharedQAmpWangTile, liftAmpTile, liftAmpRaw, k] using
      congrArg AmpHorizontalColour.southChain hm
  · simpa [sharedQAmpWangTile, liftAmpTile, liftAmpRaw, k] using
      congrArg AmpHorizontalColour.northChain hm

theorem liftAmpTile_vertical_match {Q w h : ℕ} [NeZero Q]
    (skeleton : AmpTiling (Q := 1) w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : BoundaryQAssignment (boundaryMask skeleton (by omega) hh) Q w h)
    (i : Fin w) (j : Fin h) (hj : j.1 + 1 < h) :
    (sharedQAmpWangTile Q (liftAmpTile skeleton hw hh A i j)).north =
      (sharedQAmpWangTile Q
        (liftAmpTile skeleton hw hh A i ⟨j.1 + 1, hj⟩)).south := by
  let k : Fin h := ⟨j.1 + 1, hj⟩
  have hm := skeleton.2.2 i j hj
  have hlowerNorth : (skeleton.1 i j).1.northActive = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hact
    have hb := northActive_forces_top_boundary skeleton i j hact
    omega
  have hupperSouth : (skeleton.1 i k).1.southActive = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hact
    have hb := southActive_forces_bottom_boundary skeleton i k hact
    dsimp [k] at hb
    omega
  apply AmpVerticalColour.ext
  · simpa [sharedQAmpWangTile, liftAmpTile, liftAmpRaw, k] using
      congrArg AmpVerticalColour.westChain hm
  · simpa [sharedQAmpWangTile, liftAmpTile, liftAmpRaw, k] using
      congrArg AmpVerticalColour.eastChain hm
  · simpa [sharedQAmpWangTile, liftAmpTile, liftAmpRaw, k] using
      congrArg AmpVerticalColour.southDead hm
  · simp [sharedQAmpWangTile, liftAmpTile, liftAmpRaw, k, hupperSouth]
  · simpa [sharedQAmpWangTile, liftAmpTile, liftAmpRaw, k] using
      congrArg AmpVerticalColour.northDead hm
  · simp [sharedQAmpWangTile, liftAmpTile, liftAmpRaw, hlowerNorth]

def liftAmpTiling {Q w h : ℕ} [NeZero Q]
    (skeleton : AmpTiling (Q := 1) w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : BoundaryQAssignment (boundaryMask skeleton (by omega) hh) Q w h) :
    AmpTiling (Q := Q) w h := by
  refine ⟨fun i j => liftAmpTile skeleton hw hh A i j, ?_⟩
  constructor
  · intro i j hi
    exact liftAmpTile_horizontal_match skeleton hw hh A i j hi
  · intro i j hj
    exact liftAmpTile_vertical_match skeleton hw hh A i j hj

@[simp] theorem erase_liftAmpTiling {Q w h : ℕ} [NeZero Q]
    (skeleton : AmpTiling (Q := 1) w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : BoundaryQAssignment (boundaryMask skeleton (by omega) hh) Q w h) :
    eraseAmpTiling (liftAmpTiling skeleton hw hh A) = skeleton := by
  apply Subtype.ext
  funext i j
  exact erase_liftAmpTile skeleton hw hh A i j

theorem boundaryMask_fiber_eq {Q w h : ℕ} [NeZero Q]
    {skeleton : AmpTiling (Q := 1) w h}
    (F : AmpSkeletonFiber Q skeleton) (hw : 2 ≤ w) (hh : 0 < h) :
    boundaryMask F.1 (by omega) hh = boundaryMask skeleton (by omega) hh := by
  calc
    boundaryMask F.1 (by omega) hh =
        boundaryMask (eraseAmpTiling F.1) (by omega) hh :=
      (boundaryMask_eraseAmpTiling F.1 (by omega) hh).symm
    _ = boundaryMask skeleton (by omega) hh := by rw [F.2]

noncomputable def fiberAssignment {Q w h : ℕ} [NeZero Q]
    {skeleton : AmpTiling (Q := 1) w h}
    (F : AmpSkeletonFiber Q skeleton) (hw : 2 ≤ w) (hh : 0 < h) :
    BoundaryQAssignment (boundaryMask skeleton (by omega) hh) Q w h := by
  have hmask := boundaryMask_fiber_eq F hw hh
  rw [← hmask]
  exact boundaryAssignmentOfTiling F.1 hw hh

def assignmentFiber {Q w h : ℕ} [NeZero Q]
    (skeleton : AmpTiling (Q := 1) w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : BoundaryQAssignment (boundaryMask skeleton (by omega) hh) Q w h) :
    AmpSkeletonFiber Q skeleton :=
  ⟨liftAmpTiling skeleton hw hh A, erase_liftAmpTiling skeleton hw hh A⟩

theorem boundaryAssignment_lift_west {Q w h : ℕ} [NeZero Q]
    (skeleton : AmpTiling (Q := 1) w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : BoundaryQAssignment (boundaryMask skeleton (by omega) hh) Q w h)
    (k : Fin (if (boundaryMask skeleton (by omega) hh).west then h else 0)) :
    boundaryAssignmentOfTiling (liftAmpTiling skeleton hw hh A) hw hh
        (.inl (.inl k)) = A (.inl (.inl k)) := by
  let mask := boundaryMask skeleton (by omega) hh
  have hb : mask.west = true := by
    cases heq : mask.west
    · have hk := k.2
      simp [mask, heq] at hk
    · rfl
  let j : Fin h := sideIndexToFin mask.west k
  have hact : (skeleton.1 ⟨0, by omega⟩ j).1.westActive = true :=
    (westActive_iff_boundaryMask skeleton (by omega) hh ⟨0, by omega⟩ j).mpr
      ⟨by simpa [mask] using hb, rfl⟩
  change (if (skeleton.1 ⟨0, by omega⟩ j).1.westActive then
      A.westValue j else 0) = A (.inl (.inl k))
  rw [if_pos hact]
  unfold BoundaryQAssignment.westValue
  rw [dif_pos (by simpa [mask] using hb)]
  congr
  exact activeSideIndex_sideIndexToFin mask.west hb k

theorem boundaryAssignment_lift_east {Q w h : ℕ} [NeZero Q]
    (skeleton : AmpTiling (Q := 1) w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : BoundaryQAssignment (boundaryMask skeleton (by omega) hh) Q w h)
    (k : Fin (if (boundaryMask skeleton (by omega) hh).east then h else 0)) :
    boundaryAssignmentOfTiling (liftAmpTiling skeleton hw hh A) hw hh
        (.inl (.inr k)) = A (.inl (.inr k)) := by
  let mask := boundaryMask skeleton (by omega) hh
  have hb : mask.east = true := by
    cases heq : mask.east
    · have hk := k.2
      simp [mask, heq] at hk
    · rfl
  let j : Fin h := sideIndexToFin mask.east k
  have hact : (skeleton.1 ⟨w - 1, by omega⟩ j).1.eastActive = true :=
    (eastActive_iff_boundaryMask skeleton (by omega) hh
      ⟨w - 1, by omega⟩ j).mpr ⟨by simpa [mask] using hb, by
        change w - 1 + 1 = w
        omega⟩
  change (if (skeleton.1 ⟨w - 1, by omega⟩ j).1.eastActive then
      A.eastValue j else 0) = A (.inl (.inr k))
  rw [if_pos hact]
  unfold BoundaryQAssignment.eastValue
  rw [dif_pos (by simpa [mask] using hb)]
  congr
  exact activeSideIndex_sideIndexToFin mask.east hb k

theorem boundaryAssignment_lift_south {Q w h : ℕ} [NeZero Q]
    (skeleton : AmpTiling (Q := 1) w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : BoundaryQAssignment (boundaryMask skeleton (by omega) hh) Q w h)
    (k : Fin (if (boundaryMask skeleton (by omega) hh).south then
      (boundaryMask skeleton (by omega) hh).horizontalFreeCount w else 0)) :
    boundaryAssignmentOfTiling (liftAmpTiling skeleton hw hh A) hw hh
        (.inr (.inl k)) = A (.inr (.inl k)) := by
  let mask := boundaryMask skeleton (by omega) hh
  have hb : mask.south = true := by
    cases heq : mask.south
    · have hk := k.2
      simp [mask, heq] at hk
    · rfl
  let k' : Fin (mask.horizontalFreeCount w) := sideIndexToFin mask.south k
  let i : Fin w := freeHorizontalPosition mask hw k'
  have hwest : mask.west = true → i.1 ≠ 0 := by
    intro h
    exact freeHorizontalPosition_ne_left mask hw k' h
  have heast : mask.east = true → i.1 + 1 ≠ w := by
    intro h
    exact freeHorizontalPosition_ne_right mask hw k' h
  have hnwest : ¬(mask.west = true ∧ i.1 = 0) :=
    fun h => hwest h.1 h.2
  have hneast : ¬(mask.east = true ∧ i.1 + 1 = w) :=
    fun h => heast h.1 h.2
  have hact : (skeleton.1 i ⟨0, hh⟩).1.southActive = true :=
    (southActive_iff_boundaryMask skeleton (by omega) hh i ⟨0, hh⟩).mpr
      ⟨by simpa [mask] using hb, rfl⟩
  change (if (skeleton.1 i ⟨0, hh⟩).1.southActive then
      A.southValue hw hh i else 0) = A (.inr (.inl k))
  rw [if_pos hact]
  unfold BoundaryQAssignment.southValue
  rw [dif_pos (by simpa [mask] using hb), dif_neg hnwest, dif_neg hneast]
  have hfree := freeHorizontalIndex_position mask hw k' hwest heast
  have hslot : activeSideIndex mask.south hb
      (freeHorizontalIndex mask hw i hwest heast) = k := by
    rw [hfree]
    exact activeSideIndex_sideIndexToFin mask.south hb k
  rw [hslot]

theorem boundaryAssignment_lift_north {Q w h : ℕ} [NeZero Q]
    (skeleton : AmpTiling (Q := 1) w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : BoundaryQAssignment (boundaryMask skeleton (by omega) hh) Q w h)
    (k : Fin (if (boundaryMask skeleton (by omega) hh).north then
      (boundaryMask skeleton (by omega) hh).horizontalFreeCount w else 0)) :
    boundaryAssignmentOfTiling (liftAmpTiling skeleton hw hh A) hw hh
        (.inr (.inr k)) = A (.inr (.inr k)) := by
  let mask := boundaryMask skeleton (by omega) hh
  have hb : mask.north = true := by
    cases heq : mask.north
    · have hk := k.2
      simp [mask, heq] at hk
    · rfl
  let k' : Fin (mask.horizontalFreeCount w) := sideIndexToFin mask.north k
  let i : Fin w := freeHorizontalPosition mask hw k'
  have hwest : mask.west = true → i.1 ≠ 0 := by
    intro h
    exact freeHorizontalPosition_ne_left mask hw k' h
  have heast : mask.east = true → i.1 + 1 ≠ w := by
    intro h
    exact freeHorizontalPosition_ne_right mask hw k' h
  have hnwest : ¬(mask.west = true ∧ i.1 = 0) :=
    fun h => hwest h.1 h.2
  have hneast : ¬(mask.east = true ∧ i.1 + 1 = w) :=
    fun h => heast h.1 h.2
  have hact : (skeleton.1 i ⟨h - 1, by omega⟩).1.northActive = true :=
    (northActive_iff_boundaryMask skeleton (by omega) hh i
      ⟨h - 1, by omega⟩).mpr ⟨by simpa [mask] using hb, by
        change h - 1 + 1 = h
        omega⟩
  change (if (skeleton.1 i ⟨h - 1, by omega⟩).1.northActive then
      A.northValue hw hh i else 0) = A (.inr (.inr k))
  rw [if_pos hact]
  unfold BoundaryQAssignment.northValue
  rw [dif_pos (by simpa [mask] using hb), dif_neg hnwest, dif_neg hneast]
  have hfree := freeHorizontalIndex_position mask hw k' hwest heast
  have hslot : activeSideIndex mask.north hb
      (freeHorizontalIndex mask hw i hwest heast) = k := by
    rw [hfree]
    exact activeSideIndex_sideIndexToFin mask.north hb k
  rw [hslot]

theorem boundaryAssignment_lift {Q w h : ℕ} [NeZero Q]
    (skeleton : AmpTiling (Q := 1) w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : BoundaryQAssignment (boundaryMask skeleton (by omega) hh) Q w h) :
    boundaryAssignmentOfTiling (liftAmpTiling skeleton hw hh A) hw hh = A := by
  funext slot
  rcases slot with ((west | east) | (south | north))
  · exact boundaryAssignment_lift_west skeleton hw hh A west
  · exact boundaryAssignment_lift_east skeleton hw hh A east
  · exact boundaryAssignment_lift_south skeleton hw hh A south
  · exact boundaryAssignment_lift_north skeleton hw hh A north

noncomputable def erasedBoundaryAssignment {Q w h : ℕ} [NeZero Q]
    (F : AmpTiling (Q := Q) w h) (hw : 2 ≤ w) (hh : 0 < h) :
    BoundaryQAssignment
      (boundaryMask (eraseAmpTiling F) (by omega) hh) Q w h :=
  boundaryAssignmentOfTiling F hw hh

noncomputable def reliftAmpTiling {Q w h : ℕ} [NeZero Q]
    (F : AmpTiling (Q := Q) w h) (hw : 2 ≤ w) (hh : 0 < h) :
    AmpTiling (Q := Q) w h :=
  liftAmpTiling (eraseAmpTiling F) hw hh (erasedBoundaryAssignment F hw hh)

theorem reliftAmpTiling_qWest {Q w h : ℕ} [NeZero Q]
    (F : AmpTiling (Q := Q) w h) (hw : 2 ≤ w) (hh : 0 < h)
    (i : Fin w) (j : Fin h) :
    (reliftAmpTiling F hw hh).1 i j |>.1.qWest = (F.1 i j).1.qWest := by
  cases hact : (F.1 i j).1.westActive
  · have hz := (F.1 i j).2.1 hact
    simpa [reliftAmpTiling, liftAmpTiling, liftAmpTile, liftAmpRaw,
      eraseAmpTiling, eraseAmpTile, eraseAmpRaw, hact] using hz.symm
  · have hi := westActive_forces_left_boundary F i j hact
    have hmask : (boundaryMask F (by omega) hh).west = true :=
      (westActive_iff_boundaryMask F (by omega) hh i j).mp hact |>.1
    have hieq : i = ⟨0, by omega⟩ := Fin.eq_of_val_eq hi
    rw [hieq] at hact ⊢
    have hmaskErase :
        (boundaryMask (eraseAmpTiling F) (by omega) hh).west = true := by
      simpa [boundaryMask_eraseAmpTiling] using hmask
    change (if (F.1 ⟨0, by omega⟩ j).1.westActive then
      (erasedBoundaryAssignment F hw hh).westValue j else 0) =
        (F.1 ⟨0, by omega⟩ j).1.qWest
    rw [if_pos hact]
    unfold BoundaryQAssignment.westValue
    rw [dif_pos hmaskErase]
    change (F.1 ⟨0, by omega⟩
      (sideIndexToFin (boundaryMask F (by omega) hh).west
        (activeSideIndex (boundaryMask F (by omega) hh).west hmask j))).1.qWest = _
    rw [sideIndexToFin_activeSideIndex]

theorem reliftAmpTiling_qEast {Q w h : ℕ} [NeZero Q]
    (F : AmpTiling (Q := Q) w h) (hw : 2 ≤ w) (hh : 0 < h)
    (i : Fin w) (j : Fin h) :
    (reliftAmpTiling F hw hh).1 i j |>.1.qEast = (F.1 i j).1.qEast := by
  cases hact : (F.1 i j).1.eastActive
  · have hz := (F.1 i j).2.2.1 hact
    simpa [reliftAmpTiling, liftAmpTiling, liftAmpTile, liftAmpRaw,
      eraseAmpTiling, eraseAmpTile, eraseAmpRaw, hact] using hz.symm
  · have hi := eastActive_forces_right_boundary F i j hact
    have hmask : (boundaryMask F (by omega) hh).east = true :=
      (eastActive_iff_boundaryMask F (by omega) hh i j).mp hact |>.1
    have hiv : i.1 = w - 1 := by omega
    have hieq : i = ⟨w - 1, by omega⟩ := Fin.eq_of_val_eq hiv
    rw [hieq] at hact ⊢
    have hmaskErase :
        (boundaryMask (eraseAmpTiling F) (by omega) hh).east = true := by
      simpa [boundaryMask_eraseAmpTiling] using hmask
    change (if (F.1 ⟨w - 1, by omega⟩ j).1.eastActive then
      (erasedBoundaryAssignment F hw hh).eastValue j else 0) =
        (F.1 ⟨w - 1, by omega⟩ j).1.qEast
    rw [if_pos hact]
    unfold BoundaryQAssignment.eastValue
    rw [dif_pos hmaskErase]
    change (F.1 ⟨w - 1, by omega⟩
      (sideIndexToFin (boundaryMask F (by omega) hh).east
        (activeSideIndex (boundaryMask F (by omega) hh).east hmask j))).1.qEast = _
    rw [sideIndexToFin_activeSideIndex]

theorem reliftAmpTiling_qSouth {Q w h : ℕ} [NeZero Q]
    (F : AmpTiling (Q := Q) w h) (hw : 2 ≤ w) (hh : 0 < h)
    (i : Fin w) (j : Fin h) :
    (reliftAmpTiling F hw hh).1 i j |>.1.qSouth = (F.1 i j).1.qSouth := by
  cases hact : (F.1 i j).1.southActive
  · have hz := (F.1 i j).2.2.2.1 hact
    simpa [reliftAmpTiling, liftAmpTiling, liftAmpTile, liftAmpRaw,
      eraseAmpTiling, eraseAmpTile, eraseAmpRaw, hact] using hz.symm
  · have hj := southActive_forces_bottom_boundary F i j hact
    have hmask : (boundaryMask F (by omega) hh).south = true :=
      (southActive_iff_boundaryMask F (by omega) hh i j).mp hact |>.1
    have hjeq : j = ⟨0, hh⟩ := Fin.eq_of_val_eq hj
    rw [hjeq] at hact ⊢
    have hmaskErase :
        (boundaryMask (eraseAmpTiling F) (by omega) hh).south = true := by
      simpa [boundaryMask_eraseAmpTiling] using hmask
    change (if (F.1 i ⟨0, hh⟩).1.southActive then
      (erasedBoundaryAssignment F hw hh).southValue hw hh i else 0) =
        (F.1 i ⟨0, hh⟩).1.qSouth
    rw [if_pos hact]
    unfold BoundaryQAssignment.southValue
    rw [dif_pos hmaskErase]
    by_cases hwestCorner :
        (boundaryMask F (by omega) hh).west = true ∧ i.1 = 0
    · have hwestCornerErase :
          (boundaryMask (eraseAmpTiling F) (by omega) hh).west = true ∧
            i.1 = 0 := by
        simpa [boundaryMask_eraseAmpTiling] using hwestCorner
      rw [dif_pos hwestCornerErase]
      unfold BoundaryQAssignment.westValue
      rw [dif_pos hwestCornerErase.1]
      have hwestAct : (F.1 i ⟨0, hh⟩).1.westActive = true :=
        (westActive_iff_boundaryMask F (by omega) hh i ⟨0, hh⟩).mpr
          ⟨hwestCorner.1, hwestCorner.2⟩
      change (F.1 ⟨0, by omega⟩
        (sideIndexToFin (boundaryMask F (by omega) hh).west
          (activeSideIndex (boundaryMask F (by omega) hh).west
            hwestCorner.1 ⟨0, hh⟩))).1.qWest = _
      rw [sideIndexToFin_activeSideIndex]
      have hieq : i = ⟨0, by omega⟩ := Fin.eq_of_val_eq hwestCorner.2
      rw [← hieq]
      exact (F.1 i ⟨0, hh⟩).2.2.2.2.2.1 hwestAct hact
    · by_cases heastCorner :
          (boundaryMask F (by omega) hh).east = true ∧ i.1 + 1 = w
      · have heastCornerErase :
            (boundaryMask (eraseAmpTiling F) (by omega) hh).east = true ∧
              i.1 + 1 = w := by
          simpa [boundaryMask_eraseAmpTiling] using heastCorner
        have hwestCornerErase : ¬
            ((boundaryMask (eraseAmpTiling F) (by omega) hh).west = true ∧
              i.1 = 0) := by
          simpa [boundaryMask_eraseAmpTiling] using hwestCorner
        rw [dif_neg hwestCornerErase, dif_pos heastCornerErase]
        unfold BoundaryQAssignment.eastValue
        rw [dif_pos heastCornerErase.1]
        have heastAct : (F.1 i ⟨0, hh⟩).1.eastActive = true :=
          (eastActive_iff_boundaryMask F (by omega) hh i ⟨0, hh⟩).mpr
            ⟨heastCorner.1, heastCorner.2⟩
        change (F.1 ⟨w - 1, by omega⟩
          (sideIndexToFin (boundaryMask F (by omega) hh).east
            (activeSideIndex (boundaryMask F (by omega) hh).east
              heastCorner.1 ⟨0, hh⟩))).1.qEast = _
        rw [sideIndexToFin_activeSideIndex]
        have hiv : i.1 = w - 1 := by omega
        have hieq : i = ⟨w - 1, by omega⟩ := Fin.eq_of_val_eq hiv
        rw [← hieq]
        exact (F.1 i ⟨0, hh⟩).2.2.2.2.2.2.2.1 heastAct hact
      · have hwest : (boundaryMask F (by omega) hh).west = true →
            i.1 ≠ 0 := fun hb hi => hwestCorner ⟨hb, hi⟩
        have heast : (boundaryMask F (by omega) hh).east = true →
            i.1 + 1 ≠ w := fun hb hi => heastCorner ⟨hb, hi⟩
        have hwestErase :
            (boundaryMask (eraseAmpTiling F) (by omega) hh).west = true →
              i.1 ≠ 0 := by
          simpa [boundaryMask_eraseAmpTiling] using hwest
        have heastErase :
            (boundaryMask (eraseAmpTiling F) (by omega) hh).east = true →
              i.1 + 1 ≠ w := by
          simpa [boundaryMask_eraseAmpTiling] using heast
        rw [dif_neg (fun h => hwestErase h.1 h.2),
          dif_neg (fun h => heastErase h.1 h.2)]
        change (F.1
          (freeHorizontalPosition (boundaryMask F (by omega) hh) hw
            (sideIndexToFin (boundaryMask F (by omega) hh).south
              (activeSideIndex (boundaryMask F (by omega) hh).south hmask
                (freeHorizontalIndex (boundaryMask F (by omega) hh) hw i
                  hwest heast)))) ⟨0, hh⟩).1.qSouth = _
        rw [sideIndexToFin_activeSideIndex,
          freeHorizontalPosition_index]

theorem reliftAmpTiling_qNorth {Q w h : ℕ} [NeZero Q]
    (F : AmpTiling (Q := Q) w h) (hw : 2 ≤ w) (hh : 0 < h)
    (i : Fin w) (j : Fin h) :
    (reliftAmpTiling F hw hh).1 i j |>.1.qNorth = (F.1 i j).1.qNorth := by
  cases hact : (F.1 i j).1.northActive
  · have hz := (F.1 i j).2.2.2.2.1 hact
    simpa [reliftAmpTiling, liftAmpTiling, liftAmpTile, liftAmpRaw,
      eraseAmpTiling, eraseAmpTile, eraseAmpRaw, hact] using hz.symm
  · have hj := northActive_forces_top_boundary F i j hact
    have hmask : (boundaryMask F (by omega) hh).north = true :=
      (northActive_iff_boundaryMask F (by omega) hh i j).mp hact |>.1
    have hjv : j.1 = h - 1 := by omega
    have hjeq : j = ⟨h - 1, by omega⟩ := Fin.eq_of_val_eq hjv
    rw [hjeq] at hact ⊢
    have hmaskErase :
        (boundaryMask (eraseAmpTiling F) (by omega) hh).north = true := by
      simpa [boundaryMask_eraseAmpTiling] using hmask
    change (if (F.1 i ⟨h - 1, by omega⟩).1.northActive then
      (erasedBoundaryAssignment F hw hh).northValue hw hh i else 0) =
        (F.1 i ⟨h - 1, by omega⟩).1.qNorth
    rw [if_pos hact]
    unfold BoundaryQAssignment.northValue
    rw [dif_pos hmaskErase]
    by_cases hwestCorner :
        (boundaryMask F (by omega) hh).west = true ∧ i.1 = 0
    · have hwestCornerErase :
          (boundaryMask (eraseAmpTiling F) (by omega) hh).west = true ∧
            i.1 = 0 := by
        simpa [boundaryMask_eraseAmpTiling] using hwestCorner
      rw [dif_pos hwestCornerErase]
      unfold BoundaryQAssignment.westValue
      rw [dif_pos hwestCornerErase.1]
      have hwestAct : (F.1 i ⟨h - 1, by omega⟩).1.westActive = true :=
        (westActive_iff_boundaryMask F (by omega) hh i
          ⟨h - 1, by omega⟩).mpr ⟨hwestCorner.1, hwestCorner.2⟩
      change (F.1 ⟨0, by omega⟩
        (sideIndexToFin (boundaryMask F (by omega) hh).west
          (activeSideIndex (boundaryMask F (by omega) hh).west
            hwestCorner.1 ⟨h - 1, by omega⟩))).1.qWest = _
      rw [sideIndexToFin_activeSideIndex]
      have hieq : i = ⟨0, by omega⟩ := Fin.eq_of_val_eq hwestCorner.2
      rw [← hieq]
      exact (F.1 i ⟨h - 1, by omega⟩).2.2.2.2.2.2.1 hwestAct hact
    · by_cases heastCorner :
          (boundaryMask F (by omega) hh).east = true ∧ i.1 + 1 = w
      · have heastCornerErase :
            (boundaryMask (eraseAmpTiling F) (by omega) hh).east = true ∧
              i.1 + 1 = w := by
          simpa [boundaryMask_eraseAmpTiling] using heastCorner
        have hwestCornerErase : ¬
            ((boundaryMask (eraseAmpTiling F) (by omega) hh).west = true ∧
              i.1 = 0) := by
          simpa [boundaryMask_eraseAmpTiling] using hwestCorner
        rw [dif_neg hwestCornerErase, dif_pos heastCornerErase]
        unfold BoundaryQAssignment.eastValue
        rw [dif_pos heastCornerErase.1]
        have heastAct : (F.1 i ⟨h - 1, by omega⟩).1.eastActive = true :=
          (eastActive_iff_boundaryMask F (by omega) hh i
            ⟨h - 1, by omega⟩).mpr ⟨heastCorner.1, heastCorner.2⟩
        change (F.1 ⟨w - 1, by omega⟩
          (sideIndexToFin (boundaryMask F (by omega) hh).east
            (activeSideIndex (boundaryMask F (by omega) hh).east
              heastCorner.1 ⟨h - 1, by omega⟩))).1.qEast = _
        rw [sideIndexToFin_activeSideIndex]
        have hiv : i.1 = w - 1 := by omega
        have hieq : i = ⟨w - 1, by omega⟩ := Fin.eq_of_val_eq hiv
        rw [← hieq]
        exact (F.1 i ⟨h - 1, by omega⟩).2.2.2.2.2.2.2.2 heastAct hact
      · have hwest : (boundaryMask F (by omega) hh).west = true →
            i.1 ≠ 0 := fun hb hi => hwestCorner ⟨hb, hi⟩
        have heast : (boundaryMask F (by omega) hh).east = true →
            i.1 + 1 ≠ w := fun hb hi => heastCorner ⟨hb, hi⟩
        have hwestErase :
            (boundaryMask (eraseAmpTiling F) (by omega) hh).west = true →
              i.1 ≠ 0 := by
          simpa [boundaryMask_eraseAmpTiling] using hwest
        have heastErase :
            (boundaryMask (eraseAmpTiling F) (by omega) hh).east = true →
              i.1 + 1 ≠ w := by
          simpa [boundaryMask_eraseAmpTiling] using heast
        rw [dif_neg (fun h => hwestErase h.1 h.2),
          dif_neg (fun h => heastErase h.1 h.2)]
        change (F.1
          (freeHorizontalPosition (boundaryMask F (by omega) hh) hw
            (sideIndexToFin (boundaryMask F (by omega) hh).north
              (activeSideIndex (boundaryMask F (by omega) hh).north hmask
                (freeHorizontalIndex (boundaryMask F (by omega) hh) hw i
                  hwest heast)))) ⟨h - 1, by omega⟩).1.qNorth = _
        rw [sideIndexToFin_activeSideIndex,
          freeHorizontalPosition_index]

theorem reliftAmpTiling_eq {Q w h : ℕ} [NeZero Q]
    (F : AmpTiling (Q := Q) w h) (hw : 2 ≤ w) (hh : 0 < h) :
    reliftAmpTiling F hw hh = F := by
  apply Subtype.ext
  funext i j
  apply Subtype.ext
  apply AmpRaw.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · exact reliftAmpTiling_qWest F hw hh i j
  · exact reliftAmpTiling_qEast F hw hh i j
  · exact reliftAmpTiling_qSouth F hw hh i j
  · exact reliftAmpTiling_qNorth F hw hh i j

theorem fiberAssignment_assignmentFiber {Q w h : ℕ} [NeZero Q]
    (skeleton : AmpTiling (Q := 1) w h) (hw : 2 ≤ w) (hh : 0 < h)
    (A : BoundaryQAssignment (boundaryMask skeleton (by omega) hh) Q w h) :
    fiberAssignment (assignmentFiber skeleton hw hh A) hw hh = A := by
  unfold fiberAssignment assignmentFiber
  rw [show boundaryMask_fiber_eq
      (⟨liftAmpTiling skeleton hw hh A,
        erase_liftAmpTiling skeleton hw hh A⟩ : AmpSkeletonFiber Q skeleton)
      hw hh = rfl from Subsingleton.elim _ _]
  exact boundaryAssignment_lift skeleton hw hh A

theorem assignmentFiber_fiberAssignment {Q w h : ℕ} [NeZero Q]
    (skeleton : AmpTiling (Q := 1) w h) (hw : 2 ≤ w) (hh : 0 < h)
    (F : AmpSkeletonFiber Q skeleton) :
    assignmentFiber skeleton hw hh (fiberAssignment F hw hh) = F := by
  rcases F with ⟨F, hF⟩
  subst skeleton
  apply Subtype.ext
  change liftAmpTiling (eraseAmpTiling F) hw hh
      (erasedBoundaryAssignment F hw hh) = F
  exact reliftAmpTiling_eq F hw hh

/-- The concrete `Q`-labelled fibre over every actual Boolean amplifier
skeleton is exactly the canonical set of independent boundary slots. -/
noncomputable def ampSkeletonFiberEquivBoundaryQAssignment
    {Q w h : ℕ} [NeZero Q]
    (skeleton : AmpTiling (Q := 1) w h) (hw : 2 ≤ w) (hh : 0 < h) :
    AmpSkeletonFiber Q skeleton ≃
      BoundaryQAssignment (boundaryMask skeleton (by omega) hh) Q w h where
  toFun F := fiberAssignment F hw hh
  invFun A := assignmentFiber skeleton hw hh A
  left_inv := assignmentFiber_fiberAssignment skeleton hw hh
  right_inv := fiberAssignment_assignmentFiber skeleton hw hh

theorem card_ampSkeletonFiber {Q w h : ℕ} [NeZero Q]
    (skeleton : AmpTiling (Q := 1) w h) (hw : 2 ≤ w) (hh : 0 < h) :
    Fintype.card (AmpSkeletonFiber Q skeleton) =
      Q ^ (boundaryMask skeleton (by omega) hh).qDegree w h := by
  rw [Fintype.card_congr
    (ampSkeletonFiberEquivBoundaryQAssignment skeleton hw hh)]
  exact card_boundaryQAssignment _ Q hw

theorem eraseAmpTile_one (u : SharedQAmpTile 1) : eraseAmpTile u = u := by
  apply Subtype.ext
  apply AmpRaw.ext
  · rfl
  · rfl
  · rfl
  · rfl
  all_goals exact Subsingleton.elim _ _

@[simp] theorem eraseAmpTiling_one {w h : ℕ}
    (F : AmpTiling (Q := 1) w h) : eraseAmpTiling F = F := by
  apply Subtype.ext
  funext i j
  exact eraseAmpTile_one (F.1 i j)

theorem eraseAmpTiling_surjective (w h : ℕ) :
    Function.Surjective
      (eraseAmpTiling (Q := 1) (w := w) (h := h)) := by
  intro F
  exact ⟨F, eraseAmpTiling_one F⟩

/-- Exact decomposition of all `Q`-labelled amplifier tilings into their
`Q = 1` activity skeleton and the actual fibre above that skeleton. -/
noncomputable def ampTilingSigmaFiberEquiv (Q : ℕ) [NeZero Q]
    (w h : ℕ) :
    AmpTiling (Q := Q) w h ≃
      Σ skeleton : AmpTiling (Q := 1) w h,
        AmpSkeletonFiber Q skeleton :=
  (Equiv.sigmaFiberEquiv
    (eraseAmpTiling (Q := Q) (w := w) (h := h))).symm

theorem card_ampTiling_eq_sum_skeletonFibers (Q : ℕ) [NeZero Q]
    (w h : ℕ) :
    Fintype.card (AmpTiling (Q := Q) w h) =
      ∑ skeleton : AmpTiling (Q := 1) w h,
        Fintype.card (AmpSkeletonFiber Q skeleton) := by
  rw [Fintype.card_congr (ampTilingSigmaFiberEquiv Q w h)]
  simp [Fintype.card_sigma]

theorem card_ampTiling_eq_sum_skeletonPowers (Q : ℕ) [NeZero Q]
    {w h : ℕ} (hw : 2 ≤ w) (hh : 0 < h) :
    Fintype.card (AmpTiling (Q := Q) w h) =
      ∑ skeleton : AmpTiling (Q := 1) w h,
        Q ^ (boundaryMask skeleton (by omega) hh).qDegree w h := by
  rw [card_ampTiling_eq_sum_skeletonFibers]
  apply Fintype.sum_congr
  intro skeleton
  exact card_ampSkeletonFiber skeleton hw hh

end

end PakFixedPolyomino.PakAmpCoefficient
