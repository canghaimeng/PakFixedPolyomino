import PakFixedPolyomino.MacroBijection
import Mathlib.Tactic

namespace PakFixedPolyomino

noncomputable section

/-- Contribution of all rectangular partitions except the one-block
partition. -/
def macroJunk (n : ℕ) {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V] (tile : W → WangTile H V)
    (amp : ℕ) (whole : RectangularPartition n) : ℕ :=
  ∑ D ∈ (Finset.univ.erase whole), macroWeight tile amp D

@[simp] theorem macroJunk_one_whole {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V] (tile : W → WangTile H V) (amp : ℕ) :
    macroJunk 1 tile amp (wholePartition 1 (by decide)) = 0 := by
  unfold macroJunk
  have huniv : (Finset.univ : Finset (RectangularPartition 1)) =
      {wholePartition 1 (by decide)} := by
    ext D
    simp [rectangularPartition_one_eq D]
  rw [huniv]
  simp

theorem macro_partition_sum_split (n : ℕ) {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V] (tile : W → WangTile H V)
    (amp : ℕ) (whole : RectangularPartition n) :
    ∑ D : RectangularPartition n, macroWeight tile amp D =
      macroWeight tile amp whole + macroJunk n tile amp whole := by
  unfold macroJunk
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ whole)]

/-- Exact leading-term decomposition derived from the concrete blockwise
equivalence, rather than supplied as a separate numerical assumption. -/
theorem anchored_count_split {Tilings : Type*} [Fintype Tilings]
    (n : ℕ) {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V] (tile : W → WangTile H V)
    (amp : ℕ) (whole : RectangularPartition n)
    (h : LatticeAnchored Tilings (MacroData n tile amp)) :
    Fintype.card Tilings =
      macroWeight tile amp whole + macroJunk n tile amp whole := by
  rw [exact_macro_partition_count n tile amp h]
  exact macro_partition_sum_split n tile amp whole

/-- If the distinguished block is the full square, the previous equality has
the exact leading power required by the floor readout. -/
theorem anchored_count_split_whole {Tilings : Type*} [Fintype Tilings]
    (n : ℕ) {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V] (tile : W → WangTile H V)
    (amp : ℕ) (whole : RectangularPartition n)
    (h : LatticeAnchored Tilings (MacroData n tile amp))
    (hseam : whole.seamCount = 0)
    (hblock : macroBlockCount tile whole = openWangCount tile n n) :
    Fintype.card Tilings =
      amp ^ amplifierExponent n * openWangCount tile n n +
        macroJunk n tile amp whole := by
  rw [anchored_count_split n tile amp whole h]
  unfold macroWeight
  rw [whole.openEdgeCount_eq_grid_sub_seams, hseam, Nat.sub_zero, hblock]

/-- A direct floor theorem whose sole geometric premise is the future
`LatticeAnchored` certificate. -/
theorem anchored_floor_readout {Tilings : Type*} [Fintype Tilings]
    (n : ℕ) {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V] (tile : W → WangTile H V)
    (amp : ℕ) (whole : RectangularPartition n)
    (h : LatticeAnchored Tilings (MacroData n tile amp))
    (hamp : 0 < amp) (hseam : whole.seamCount = 0)
    (hblock : macroBlockCount tile whole = openWangCount tile n n)
    (hjunk : macroJunk n tile amp whole < amp ^ amplifierExponent n) :
    Fintype.card Tilings / amp ^ amplifierExponent n = openWangCount tile n n := by
  exact floor_readout hamp
    (anchored_count_split_whole n tile amp whole h hseam hblock) hjunk

/-- Product form of the rectangular perimeter estimate. -/
theorem product_bound_from_perimeter {Block : Type*} [Fintype Block]
    [DecidableEq Block] (count width height : Block → ℕ) (R n seam : ℕ)
    (hcount : ∀ B, count B ≤ R ^ (width B + height B))
    (hperimeter : ∑ B, (width B + height B) = 2 * n + seam) :
    ∏ B, count B ≤ R ^ (2 * n + seam) := by
  calc
    ∏ B, count B ≤ ∏ B, R ^ (width B + height B) := by
      apply Finset.prod_le_prod'
      intro B _
      exact hcount B
    _ = R ^ (∑ B, (width B + height B)) :=
      Finset.prod_pow_eq_pow_sum Finset.univ (fun B => width B + height B) R
    _ = R ^ (2 * n + seam) := by rw [hperimeter]

/-- Algebra behind one seam class.  It is kept entirely in `ℕ`, avoiding
negative exponents and rational-number coercions. -/
theorem amplifier_term_identity' (b edges seam : ℕ) (hseam : seam ≤ edges) :
    (4 * b) ^ (edges - seam) * b ^ seam = (4 * b) ^ edges / 4 ^ seam := by
  symm
  calc
    (4 * b) ^ edges / 4 ^ seam =
        ((4 * b) ^ (edges - seam) * (4 * b) ^ seam) / 4 ^ seam := by
      rw [← pow_add, Nat.sub_add_cancel hseam]
    _ = (((4 * b) ^ (edges - seam) * b ^ seam) * 4 ^ seam) / 4 ^ seam := by
      rw [mul_pow]
      congr 1
      ring
    _ = (4 * b) ^ (edges - seam) * b ^ seam := by simp

/-- The exact constants from the accepted construction imply a quarter-power
loss for every seam. -/
theorem amplified_seam_term_bound
    {R n seam edges : ℕ} (hR : 0 < R) (hn : n ≤ seam) (hseam : seam ≤ edges) :
    256 ^ seam * (1024 * R ^ 3) ^ (edges - seam) * R ^ (2 * n + seam)
      ≤ (1024 * R ^ 3) ^ edges / 4 ^ seam := by
  have hexp : 2 * n + seam ≤ 3 * seam := by omega
  have hpow : R ^ (2 * n + seam) ≤ R ^ (3 * seam) :=
    Nat.pow_le_pow_right hR hexp
  let b := 256 * R ^ 3
  have hamp : 1024 * R ^ 3 = 4 * b := by dsimp [b]; ring
  have hbpow : 256 ^ seam * R ^ (3 * seam) = b ^ seam := by
    dsimp [b]
    rw [mul_pow, ← pow_mul]
  calc
    256 ^ seam * (1024 * R ^ 3) ^ (edges - seam) * R ^ (2 * n + seam)
        ≤ 256 ^ seam * (1024 * R ^ 3) ^ (edges - seam) * R ^ (3 * seam) := by
          gcongr
    _ = (4 * b) ^ (edges - seam) * b ^ seam := by
      rw [hamp, ← hbpow]
      ring
    _ = (4 * b) ^ edges / 4 ^ seam := amplifier_term_identity' b edges seam hseam
    _ = (1024 * R ^ 3) ^ edges / 4 ^ seam := by rw [hamp]

/-- Complete finite geometric tail. -/
theorem quarter_tail_lt {leading n edges : ℕ} (term : ℕ → ℕ)
    (hn : 2 ≤ n) (hlead : 0 < leading)
    (hterm : ∀ i ∈ Finset.Icc n edges, term i ≤ leading / 4 ^ i) :
    ∑ i ∈ Finset.Icc n edges, term i < leading := by
  calc
    ∑ i ∈ Finset.Icc n edges, term i
        ≤ ∑ i ∈ Finset.Icc n edges, leading / 4 ^ i :=
      Finset.sum_le_sum hterm
    _ ≤ ∑ i ∈ Finset.Ico 1 (edges + 1), leading / 4 ^ i := by
      apply Finset.sum_le_sum_of_subset
      intro i hi
      simp only [Finset.mem_Icc, Finset.mem_Ico] at hi ⊢
      omega
    _ ≤ leading / (4 - 1) := Nat.geom_sum_Ico_le (by decide) leading (edges + 1)
    _ < leading := by
      apply Nat.div_lt_self hlead
      decide

/-- The dissection census and perimeter bound are isolated in this explicit
certificate.  Every geometric premise remains a visible theorem parameter. -/
structure SeamJunkCertificate (n edges R : ℕ) (junk : ℕ) where
  term : ℕ → ℕ
  junk_eq : junk = ∑ i ∈ Finset.Icc n edges, term i
  raw_bound : ∀ i ∈ Finset.Icc n edges,
    term i ≤ 256 ^ i * (1024 * R ^ 3) ^ (edges - i) * R ^ (2 * n + i)

theorem SeamJunkCertificate.lt_amplifier
    {n edges R junk : ℕ} (C : SeamJunkCertificate n edges R junk)
    (hn : 2 ≤ n) (hR : 0 < R) (hedges : ∀ i ∈ Finset.Icc n edges, i ≤ edges) :
    junk < (1024 * R ^ 3) ^ edges := by
  rw [C.junk_eq]
  apply quarter_tail_lt C.term hn (pow_pos (by positivity) edges)
  intro i hi
  exact (C.raw_bound i hi).trans
    (amplified_seam_term_bound hR (Finset.mem_Icc.mp hi).1 (hedges i hi))

/-- End-to-end downstream theorem for `n ≥ 2`.  Once anchoring supplies the
unique physical realization relation and the already accepted dissection
facts supply `SeamJunkCertificate`, no further geometric reasoning is needed. -/
theorem anchored_amplified_floor_readout {Tilings : Type*} [Fintype Tilings]
    (n R : ℕ) {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V] (tile : W → WangTile H V)
    (whole : RectangularPartition n)
    (h : LatticeAnchored Tilings (MacroData n tile (1024 * R ^ 3)))
    (hn : 2 ≤ n) (hR : 0 < R)
    (hseam : whole.seamCount = 0)
    (hblock : macroBlockCount tile whole = openWangCount tile n n)
    (C : SeamJunkCertificate n (amplifierExponent n) R
      (macroJunk n tile (1024 * R ^ 3) whole)) :
    Fintype.card Tilings / (1024 * R ^ 3) ^ amplifierExponent n =
      openWangCount tile n n := by
  apply anchored_floor_readout n tile (1024 * R ^ 3) whole h (by positivity)
    hseam hblock
  exact C.lt_amplifier hn hR (fun i hi => (Finset.mem_Icc.mp hi).2)

/-- `n ≥ 2` specialization to the canonical one-block partition; its zero
seam and square Wang factor are now discharged internally. -/
theorem anchored_amplified_floor_readout_whole
    {Tilings : Type*} [Fintype Tilings] (n R : ℕ)
    {W H V : Type*} [Fintype W] [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V)
    (h : LatticeAnchored Tilings (MacroData n tile (1024 * R ^ 3)))
    (hn : 2 ≤ n) (hR : 0 < R)
    (C : SeamJunkCertificate n (amplifierExponent n) R
      (macroJunk n tile (1024 * R ^ 3)
        (wholePartition n (lt_of_lt_of_le (by decide) hn)))) :
    Fintype.card Tilings / (1024 * R ^ 3) ^ amplifierExponent n =
      openWangCount tile n n := by
  let hnpos : 0 < n := lt_of_lt_of_le (by decide) hn
  exact anchored_amplified_floor_readout n R tile (wholePartition n hnpos)
    h hn hR (wholePartition_seamCount n hnpos)
    (macroBlockCount_whole n hnpos tile) C

/-- The `n = 1` branch, where the exponent is zero and there is no junk. -/
theorem anchored_amplified_floor_readout_one {Tilings : Type*} [Fintype Tilings]
    (R : ℕ) {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V] (tile : W → WangTile H V)
    (whole : RectangularPartition 1)
    (h : LatticeAnchored Tilings (MacroData 1 tile (1024 * R ^ 3)))
    (hR : 0 < R) (hseam : whole.seamCount = 0)
    (hblock : macroBlockCount tile whole = openWangCount tile 1 1)
    (hjunk : macroJunk 1 tile (1024 * R ^ 3) whole = 0) :
    Fintype.card Tilings / (1024 * R ^ 3) ^ amplifierExponent 1 =
      openWangCount tile 1 1 := by
  apply anchored_floor_readout 1 tile (1024 * R ^ 3) whole h (by positivity)
    hseam hblock
  simp [hjunk]

/-- Fully discharged exponent-zero branch for the concrete one-block
partition. -/
theorem anchored_amplified_floor_readout_one_whole
    {Tilings : Type*} [Fintype Tilings] (R : ℕ)
    {W H V : Type*} [Fintype W] [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V)
    (h : LatticeAnchored Tilings
      (MacroData 1 tile (1024 * R ^ 3))) (hR : 0 < R) :
    Fintype.card Tilings / (1024 * R ^ 3) ^ amplifierExponent 1 =
      openWangCount tile 1 1 := by
  exact anchored_amplified_floor_readout_one R tile
    (wholePartition 1 (by decide)) h hR
    (wholePartition_seamCount 1 (by decide))
    (macroBlockCount_whole 1 (by decide) tile)
    (macroJunk_one_whole tile _)

end
end PakFixedPolyomino
