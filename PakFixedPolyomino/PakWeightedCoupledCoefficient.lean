import PakFixedPolyomino.PakWeightedCoupledInventory

/-! Weighted shared-`Q` coefficient extraction for the actual coupled
inventory. Combinatorial only: not BIT-time. -/

namespace PakFixedPolyomino.PakWeightedCoupledCoefficient

open PakCoupledCoefficient
open PakWeightedCoupledInventory
open PakAmpCoefficient (BoundaryMask nonFullMaskTail)
open Finset

set_option maxHeartbeats 400000

noncomputable section

lemma erase_preserves_copies (Q : ℕ) [NeZero Q] (u : CoupledTrack Q) :
    coupledIdentityCopies 1 (eraseCoupledTrack u) =
      coupledIdentityCopies Q u :=
  rfl

lemma erase_preserves_weight {Q w h : ℕ} [NeZero Q]
    (F : CoupledTiling Q w h) :
    coupledIdentityWeight (eraseCoupledTiling F) =
      coupledIdentityWeight F := by
  unfold coupledIdentityWeight
  apply prod_congr rfl
  intro i _
  apply prod_congr rfl
  intro j _
  exact erase_preserves_copies Q (F.1 i j)

lemma sum_by_fibres {α β : Type*} [Fintype α] [Fintype β]
    {γ : β → Type*} [∀ y, Fintype (γ y)]
    (e : α ≃ Σ y : β, γ y) (g : α → ℕ) (gβ : β → ℕ)
    (hconst : ∀ y, ∀ z : γ y, g (e.symm ⟨y, z⟩) = gβ y) :
    (∑ x : α, g x) = ∑ y : β, Fintype.card (γ y) * gβ y := by
  have h1 : (∑ x : α, g x) = ∑ z : (Σ y : β, γ y), g (e.symm z) :=
    (e.symm.sum_comp g).symm
  rw [h1, Fintype.sum_sigma]
  refine Fintype.sum_congr _ _ ?_
  intro y
  have h2 : (∑ z : γ y, g (e.symm ⟨y, z⟩)) = ∑ _z : γ y, gβ y :=
    Fintype.sum_congr _ _ fun z => hconst y z
  rw [h2, sum_const_nat (fun _ _ => rfl), card_univ]

lemma fiber_weight_of_sigma {Q w h : ℕ} [NeZero Q]
    (s : CoupledTiling 1 w h) (F : CoupledSkeletonFiber Q s) :
    coupledIdentityWeight
        ((coupledTilingSigmaFiberEquiv Q w h).symm ⟨s, F⟩) =
      coupledIdentityWeight s := by
  change coupledIdentityWeight F.val = coupledIdentityWeight s
  have h := erase_preserves_weight F.val
  rw [F.property] at h
  exact h.symm

theorem weighted_sum_eq_sum_fiberCards (Q w h : ℕ) [NeZero Q] :
    (∑ F : CoupledTiling Q w h, coupledIdentityWeight F) =
      ∑ s : CoupledTiling 1 w h,
        Fintype.card (CoupledSkeletonFiber Q s) * coupledIdentityWeight s :=
  sum_by_fibres (coupledTilingSigmaFiberEquiv Q w h)
    (coupledIdentityWeight (Q := Q) (w := w) (h := h))
    (coupledIdentityWeight (Q := 1) (w := w) (h := h))
    fiber_weight_of_sigma

lemma skeletonMask_delta {w h : ℕ} (hw : 0 < w) (hh : 0 < h)
    (s : CoupledTiling 1 w h) :
    skeletonMask hw hh s =
      PakAmpCoefficient.boundaryMask (amplifierProjection s) hw hh :=
  rfl

theorem weighted_count_eq_sum_skeletonPowers
    (Q : ℕ) [NeZero Q] {w h : ℕ} (hw : 2 ≤ w) (hh : 0 < h) :
    openWangCount (weightedCoupledWangTile Q) w h =
      ∑ s : CoupledTiling 1 w h,
        Q ^ (skeletonMask (Nat.zero_lt_of_lt hw) hh s).qDegree w h *
          coupledIdentityWeight s := by
  rw [weighted_count_eq_sum, weighted_sum_eq_sum_fiberCards]
  refine Fintype.sum_congr _ _ ?_
  intro s
  rw [card_coupledSkeletonFiber s hw hh]
  rw [skeletonMask_delta (Nat.zero_lt_of_lt hw) hh s]

def weightedSkeletonCount {w h : ℕ} (hw : 0 < w) (hh : 0 < h)
    (mask : BoundaryMask) : ℕ :=
  ∑ s : CoupledTiling 1 w h,
    if skeletonMask hw hh s = mask then coupledIdentityWeight s else 0

def weightedFullFrameCount {w h : ℕ} (hw : 0 < w) (hh : 0 < h) : ℕ :=
  weightedSkeletonCount hw hh BoundaryMask.full

lemma sum_partition {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (g : α → ℕ) :
    (∑ x : α, g x) = ∑ y : β, ∑ x : α, if f x = y then g x else 0 := by
  have hcomm :
      (∑ y : β, ∑ x : α, if f x = y then g x else 0) =
        ∑ x : α, ∑ y : β, if f x = y then g x else 0 :=
    Finset.sum_comm
  rw [hcomm]
  refine Fintype.sum_congr _ _ ?_
  intro x
  exact (sum_ite_eq_of_mem (univ : Finset β) (f x)
      (fun _ => g x) (mem_univ (f x))).symm

lemma ite_mul_zero (p : Prop) [Decidable p] (a b : ℕ) :
    (if p then a * b else 0) = a * (if p then b else 0) := by
  split_ifs <;> simp

lemma ite_mul_sum {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (a : ℕ) (b : α → ℕ) :
    (∑ x : α, if p x then a * b x else 0) =
      a * ∑ x : α, if p x then b x else 0 := by
  have h :
      (∑ x : α, if p x then a * b x else 0) =
        ∑ x : α, a * (if p x then b x else 0) :=
    Fintype.sum_congr _ _ fun x => ite_mul_zero (p x) a (b x)
  rw [h]
  exact (mul_sum (univ : Finset α) (fun x => if p x then b x else 0) a).symm

lemma ite_skeleton_pow {Q w h : ℕ} {hw : 0 < w} {hh : 0 < h}
    (mask : BoundaryMask) (s : CoupledTiling 1 w h) :
    (if skeletonMask hw hh s = mask then
      Q ^ (skeletonMask hw hh s).qDegree w h * coupledIdentityWeight s else 0) =
      (if skeletonMask hw hh s = mask then
        Q ^ mask.qDegree w h * coupledIdentityWeight s else 0) := by
  split_ifs with h
  · rw [h]
  · rfl

theorem weighted_sum_partition
    (Q : ℕ) {w h : ℕ} (hw : 0 < w) (hh : 0 < h) :
    (∑ s : CoupledTiling 1 w h,
        Q ^ (skeletonMask hw hh s).qDegree w h * coupledIdentityWeight s) =
      ∑ mask : BoundaryMask,
        ∑ s : CoupledTiling 1 w h,
          if skeletonMask hw hh s = mask then
            Q ^ (skeletonMask hw hh s).qDegree w h * coupledIdentityWeight s
          else 0 :=
  sum_partition (skeletonMask hw hh)
    (fun s => Q ^ (skeletonMask hw hh s).qDegree w h * coupledIdentityWeight s)

theorem weighted_partition_eq_maskPowers
    (Q : ℕ) {w h : ℕ} (hw : 0 < w) (hh : 0 < h) :
    (∑ mask : BoundaryMask,
        ∑ s : CoupledTiling 1 w h,
          if skeletonMask hw hh s = mask then
            Q ^ (skeletonMask hw hh s).qDegree w h * coupledIdentityWeight s
          else 0) =
      ∑ mask : BoundaryMask,
        ∑ s : CoupledTiling 1 w h,
          if skeletonMask hw hh s = mask then
            Q ^ mask.qDegree w h * coupledIdentityWeight s else 0 :=
  Fintype.sum_congr _ _ fun mask =>
    Fintype.sum_congr _ _ fun s => ite_skeleton_pow (Q := Q) mask s

theorem weighted_maskPowers_eq_count
    (Q : ℕ) {w h : ℕ} (hw : 0 < w) (hh : 0 < h) :
    (∑ mask : BoundaryMask,
        ∑ s : CoupledTiling 1 w h,
          if skeletonMask hw hh s = mask then
            Q ^ mask.qDegree w h * coupledIdentityWeight s else 0) =
      ∑ mask : BoundaryMask,
        Q ^ mask.qDegree w h * weightedSkeletonCount hw hh mask :=
  Fintype.sum_congr _ _ fun mask =>
    ite_mul_sum (fun s => skeletonMask hw hh s = mask)
      (Q ^ mask.qDegree w h) coupledIdentityWeight

theorem weighted_count_eq_sum_masks
    (Q : ℕ) [NeZero Q] {w h : ℕ} (hw : 2 ≤ w) (hh : 0 < h) :
    openWangCount (weightedCoupledWangTile Q) w h =
      ∑ mask : BoundaryMask,
        Q ^ mask.qDegree w h *
          weightedSkeletonCount (Nat.zero_lt_of_lt hw) hh mask :=
  (weighted_count_eq_sum_skeletonPowers Q hw hh).trans
    ((weighted_sum_partition Q (Nat.zero_lt_of_lt hw) hh).trans
      ((weighted_partition_eq_maskPowers Q (Nat.zero_lt_of_lt hw) hh).trans
        (weighted_maskPowers_eq_count Q (Nat.zero_lt_of_lt hw) hh)))

lemma ite_weight_le {w h : ℕ} (hw : 0 < w) (hh : 0 < h)
    (mask : BoundaryMask) (s : CoupledTiling 1 w h) :
    (if skeletonMask hw hh s = mask then coupledIdentityWeight s else 0) ≤
      (if skeletonMask hw hh s = mask then 2 ^ h else 0) := by
  split_ifs
  · exact identity_weight_le_pow s
  · exact le_rfl

lemma sum_ite_one_eq_card {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] :
    (∑ x : α, if p x then (1 : ℕ) else 0) = Fintype.card {x // p x} := by
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem weightedSkeletonCount_le_revised_base
    {w h : ℕ} (hw : 0 < w) (hh : 0 < h) (mask : BoundaryMask) :
    weightedSkeletonCount hw hh mask ≤
      (2 * coefficientPerimeterBase) ^ (w + h) := by
  have hle :
      weightedSkeletonCount hw hh mask ≤
        ∑ s : CoupledTiling 1 w h,
          if skeletonMask hw hh s = mask then 2 ^ h else 0 := by
    unfold weightedSkeletonCount
    exact sum_le_sum fun s _ => ite_weight_le hw hh mask s
  have hfactor :
      (∑ s : CoupledTiling 1 w h,
          if skeletonMask hw hh s = mask then (2 : ℕ) ^ h else 0) =
        2 ^ h *
          ∑ s : CoupledTiling 1 w h,
            if skeletonMask hw hh s = mask then 1 else 0 := by
    have h :=
      ite_mul_sum (fun s => skeletonMask hw hh s = mask) (2 ^ h)
        (fun _ => (1 : ℕ))
    simpa [mul_one] using h
  have hones :
      (∑ s : CoupledTiling 1 w h,
          if skeletonMask hw hh s = mask then (1 : ℕ) else 0) =
        coupledSkeletonCount hw hh mask :=
    sum_ite_one_eq_card (fun s => skeletonMask hw hh s = mask)
  have hper := coupledSkeletonCount_le_perimeter hw hh mask
  have hmul : 2 ^ h * coupledSkeletonCount hw hh mask ≤
      2 ^ h * coefficientPerimeterBase ^ (w + h) :=
    Nat.mul_le_mul_left _ hper
  have hpow : 2 ^ h ≤ 2 ^ (w + h) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_left h w)
  have hmul2 :
      2 ^ h * coefficientPerimeterBase ^ (w + h) ≤
        2 ^ (w + h) * coefficientPerimeterBase ^ (w + h) :=
    Nat.mul_le_mul_right _ hpow
  have hre :
      2 ^ (w + h) * coefficientPerimeterBase ^ (w + h) =
        (2 * coefficientPerimeterBase) ^ (w + h) := by
    rw [Nat.mul_pow]
  exact hle.trans (le_of_eq hfactor) |>.trans (le_of_eq (by rw [hones])) |>.trans
    (hmul.trans (hmul2.trans (le_of_eq hre)))

lemma two_le_of_five {n : ℕ} (hn : 5 ≤ n) : 2 ≤ n :=
  le_trans (by decide : 2 ≤ 5) hn

lemma pos_of_five {n : ℕ} (hn : 5 ≤ n) : 0 < n :=
  Nat.zero_lt_of_lt (two_le_of_five hn)

theorem weighted_count_square_eq_full_add_tail
    (Q : ℕ) [NeZero Q] {n : ℕ} (hn : 2 ≤ n) :
    openWangCount (weightedCoupledWangTile Q) n n =
      Q ^ BoundaryMask.full.qDegree n n *
          weightedFullFrameCount (Nat.zero_lt_of_lt hn) (Nat.zero_lt_of_lt hn) +
        nonFullMaskTail
          (weightedSkeletonCount (Nat.zero_lt_of_lt hn)
            (Nat.zero_lt_of_lt hn)) Q n :=
  (weighted_count_eq_sum_masks Q hn (Nat.zero_lt_of_lt hn)).trans
    (maskSum_eq_full_add_nonFullTail
      (weightedSkeletonCount (Nat.zero_lt_of_lt hn)
        (Nat.zero_lt_of_lt hn)) Q n)

lemma two_mul_pos {C : ℕ} (hC : 0 < C) : 0 < 2 * C :=
  Nat.mul_pos (Nat.succ_pos 1) hC

lemma two_mul_pow (C n : ℕ) :
    (2 * C) ^ (n + n) = (2 * C) ^ (2 * n) :=
  congrArg (fun e => (2 * C) ^ e) (Eq.symm (Nat.two_mul n))

theorem two_mul_perimeter_pos : 0 < 2 * coefficientPerimeterBase :=
  two_mul_pos coefficientPerimeterBase_pos

def weightedExtractionBase : ℕ :=
  2 * coefficientPerimeterBase

def weightedExtractionQ : ℕ :=
  PakAmpCoefficient.coefficientBase (2 * coefficientPerimeterBase)

theorem weightedExtractionQ_pos : 0 < weightedExtractionQ :=
  PakAmpCoefficient.coefficientBase_pos two_mul_perimeter_pos

instance weightedExtractionQ_neZero : NeZero weightedExtractionQ :=
  ⟨Nat.ne_of_gt weightedExtractionQ_pos⟩

theorem revised_base_eq_extraction_pow {n : ℕ} :
    (2 * coefficientPerimeterBase) ^ (n + n) =
      (2 * coefficientPerimeterBase) ^ (2 * n) :=
  two_mul_pow coefficientPerimeterBase n

theorem weightedSkeletonCount_le_extractionBase {n : ℕ} (hn : 5 ≤ n)
    (mask : BoundaryMask) :
    weightedSkeletonCount (pos_of_five hn) (pos_of_five hn) mask ≤
      (2 * coefficientPerimeterBase) ^ (2 * n) :=
  (weightedSkeletonCount_le_revised_base (w := n) (h := n)
      (pos_of_five hn) (pos_of_five hn) mask).trans
    (le_of_eq revised_base_eq_extraction_pow)

lemma tail_lt_of_mask_bound {C : ℕ} (hC : 0 < C)
    (count : BoundaryMask → ℕ) {n : ℕ} (hn : 5 ≤ n)
    (hcount : ∀ mask, count mask ≤ C ^ (2 * n)) :
    nonFullMaskTail count (PakAmpCoefficient.coefficientBase C) n <
      PakAmpCoefficient.coefficientBase C ^
        BoundaryMask.full.qDegree n n :=
  PakAmpCoefficient.nonFullMaskTail_lt_fullPower_fixedBase
    count hC hn (fun mask _ => hcount mask)

theorem weightedNonFullTail_lt_extractionPower {n : ℕ} (hn : 5 ≤ n) :
    nonFullMaskTail
        (weightedSkeletonCount (pos_of_five hn) (pos_of_five hn))
        weightedExtractionQ n <
      weightedExtractionQ ^ BoundaryMask.full.qDegree n n :=
  tail_lt_of_mask_bound two_mul_perimeter_pos
    (weightedSkeletonCount (pos_of_five hn) (pos_of_five hn)) hn
    (fun mask => weightedSkeletonCount_le_extractionBase hn mask)

lemma nat_floor_extract (p full tail : ℕ) (hp : 0 < p) (ht : tail < p) :
    (p * full + tail) / p = full := by
  rw [Nat.mul_add_div hp, Nat.div_eq_of_lt ht, Nat.add_zero]

lemma extract_from_full_add_tail
    (card full tail power : ℕ) (hcard : card = power * full + tail)
    (hp : 0 < power) (ht : tail < power) :
    card / power = full :=
  (congrArg (fun k => k / power) hcard).trans
    (nat_floor_extract power full tail hp ht)

theorem weightedSquare_div_fullPower_eq_fullFrameCount
    {n : ℕ} (hn : 5 ≤ n) :
    openWangCount (weightedCoupledWangTile weightedExtractionQ) n n /
        weightedExtractionQ ^ BoundaryMask.full.qDegree n n =
      weightedFullFrameCount (pos_of_five hn) (pos_of_five hn) :=
  extract_from_full_add_tail
    (openWangCount (weightedCoupledWangTile weightedExtractionQ) n n)
    (weightedFullFrameCount (pos_of_five hn) (pos_of_five hn))
    (nonFullMaskTail
      (weightedSkeletonCount (pos_of_five hn) (pos_of_five hn))
      weightedExtractionQ n)
    (weightedExtractionQ ^ BoundaryMask.full.qDegree n n)
    (weighted_count_square_eq_full_add_tail (Q := weightedExtractionQ)
      (two_le_of_five hn))
    (pow_pos weightedExtractionQ_pos _)
    (weightedNonFullTail_lt_extractionPower hn)

def weighted_coupled_coefficient_spec : Prop :=
  (∀ Q : ℕ, [NeZero Q] → ∀ u : CoupledTrack Q,
    coupledIdentityCopies 1 (eraseCoupledTrack u) =
      coupledIdentityCopies Q u) ∧
  (∀ Q w h : ℕ, [NeZero Q] → ∀ F : CoupledTiling Q w h,
    coupledIdentityWeight (eraseCoupledTiling F) =
      coupledIdentityWeight F) ∧
  (∀ Q : ℕ, [NeZero Q] → ∀ w h : ℕ, ∀ hw : 2 ≤ w, ∀ hh : 0 < h,
    openWangCount (weightedCoupledWangTile Q) w h =
      ∑ s : CoupledTiling 1 w h,
        Q ^ (skeletonMask (Nat.zero_lt_of_lt hw) hh s).qDegree w h *
          coupledIdentityWeight s) ∧
  (∀ Q : ℕ, [NeZero Q] → ∀ w h : ℕ, ∀ hw : 2 ≤ w, ∀ hh : 0 < h,
    openWangCount (weightedCoupledWangTile Q) w h =
      ∑ mask : BoundaryMask,
        Q ^ mask.qDegree w h *
          weightedSkeletonCount (Nat.zero_lt_of_lt hw) hh mask) ∧
  (∀ w h : ℕ, ∀ hw : 0 < w, ∀ hh : 0 < h, ∀ mask : BoundaryMask,
    weightedSkeletonCount hw hh mask ≤
      (2 * coefficientPerimeterBase) ^ (w + h)) ∧
  (∀ n : ℕ, ∀ hn : 5 ≤ n,
    openWangCount (weightedCoupledWangTile weightedExtractionQ) n n /
        weightedExtractionQ ^ BoundaryMask.full.qDegree n n =
      weightedFullFrameCount (pos_of_five hn) (pos_of_five hn))

theorem weighted_coupled_coefficient_spec_holds :
    weighted_coupled_coefficient_spec :=
  ⟨erase_preserves_copies,
    fun Q _w _h _ F => erase_preserves_weight (Q := Q) F,
    fun Q _ _w _h hw hh =>
      weighted_count_eq_sum_skeletonPowers (Q := Q) hw hh,
    fun Q _ _w _h hw hh =>
      weighted_count_eq_sum_masks (Q := Q) hw hh,
    fun _w _h hw hh mask => weightedSkeletonCount_le_revised_base hw hh mask,
    fun _n hn => weightedSquare_div_fullPower_eq_fullFrameCount hn⟩

end
end PakFixedPolyomino.PakWeightedCoupledCoefficient
