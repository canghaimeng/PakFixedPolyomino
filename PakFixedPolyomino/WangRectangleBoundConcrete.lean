import PakFixedPolyomino.AnchoredGridMacroData
import Mathlib.Tactic

/-!
# Concrete perimeter bounds for the product Wang system

This file formalizes the part of accepted Fact `ca9bbc68cbedb02f`
which is independent of the particular Turing machine.  In particular it
contains actual Wang systems for the ripple and scanner tracks, product and
coupling constructions, and kernel-checked perimeter certificates.

The higher-block tableau is deliberately not replaced by an arbitrary
rectangle-bound hypothesis in the definitions below.  Its remaining concrete
instance is isolated at the end of this file as a *column-extension*
certificate, matching clause (D) of accepted Fact `b9df6c5fdbe1516b`.
-/

namespace PakFixedPolyomino

noncomputable section

/-! ## Cartesian products and locally coupled subsystems -/

/-- The componentwise Cartesian product of two Wang systems. -/
def wangProductTile {WA HA VA WB HB VB : Type*}
    (tileA : WA → WangTile HA VA) (tileB : WB → WangTile HB VB) :
    WA × WB → WangTile (HA × HB) (VA × VB) := fun u =>
  { west := ((tileA u.1).west, (tileB u.2).west)
    east := ((tileA u.1).east, (tileB u.2).east)
    south := ((tileA u.1).south, (tileB u.2).south)
    north := ((tileA u.1).north, (tileB u.2).north) }

/-- Project a tiling of a product system to its first track. -/
def openWangProductFst {WA HA VA WB HB VB : Type*} [Fintype WA] [Fintype WB]
    (tileA : WA → WangTile HA VA) (tileB : WB → WangTile HB VB)
    {w h : ℕ} (f : OpenWangTiling (wangProductTile tileA tileB) w h) :
    OpenWangTiling tileA w h := by
  refine ⟨fun i j => (f.1 i j).1, ?_⟩
  constructor
  · intro i j hi
    exact congrArg Prod.fst (f.2.1 i j hi)
  · intro i j hj
    exact congrArg Prod.fst (f.2.2 i j hj)

/-- Project a tiling of a product system to its second track. -/
def openWangProductSnd {WA HA VA WB HB VB : Type*} [Fintype WA] [Fintype WB]
    (tileA : WA → WangTile HA VA) (tileB : WB → WangTile HB VB)
    {w h : ℕ} (f : OpenWangTiling (wangProductTile tileA tileB) w h) :
    OpenWangTiling tileB w h := by
  refine ⟨fun i j => (f.1 i j).2, ?_⟩
  constructor
  · intro i j hi
    exact congrArg Prod.snd (f.2.1 i j hi)
  · intro i j hj
    exact congrArg Prod.snd (f.2.2 i j hj)

/-- Product Wang tilings are exactly pairs of component tilings. -/
def openWangProductEquiv {WA HA VA WB HB VB : Type*} [Fintype WA] [Fintype WB]
    (tileA : WA → WangTile HA VA) (tileB : WB → WangTile HB VB)
    (w h : ℕ) :
    OpenWangTiling (wangProductTile tileA tileB) w h ≃
      OpenWangTiling tileA w h × OpenWangTiling tileB w h where
  toFun f := (openWangProductFst tileA tileB f, openWangProductSnd tileA tileB f)
  invFun f := by
    refine ⟨fun i j => (f.1.1 i j, f.2.1 i j), ?_⟩
    constructor
    · intro i j hi
      exact Prod.ext (f.1.2.1 i j hi) (f.2.2.1 i j hi)
    · intro i j hj
      exact Prod.ext (f.1.2.2 i j hj) (f.2.2.2 i j hj)
  left_inv f := by
    apply Subtype.ext
    funext i j
    rfl
  right_inv f := by
    apply Prod.ext <;> apply Subtype.ext <;> funext i j <;> rfl

theorem openWangProductCount_eq_mul
    {WA HA VA WB HB VB : Type*} [Fintype WA] [Fintype WB]
    [DecidableEq HA] [DecidableEq VA] [DecidableEq HB] [DecidableEq VB]
    (tileA : WA → WangTile HA VA) (tileB : WB → WangTile HB VB)
    (w h : ℕ) :
    openWangCount (wangProductTile tileA tileB) w h =
      openWangCount tileA w h * openWangCount tileB w h := by
  unfold openWangCount
  rw [Fintype.card_congr (openWangProductEquiv tileA tileB w h)]
  exact Fintype.card_prod _ _

/-- Perimeter certificates multiply under Cartesian products. -/
def WangRectangleBound.product
    {WA HA VA WB HB VB : Type*} [Fintype WA] [Fintype WB]
    [DecidableEq HA] [DecidableEq VA] [DecidableEq HB] [DecidableEq VB]
    (tileA : WA → WangTile HA VA) (tileB : WB → WangTile HB VB)
    {RA RB : ℕ} (A : WangRectangleBound RA tileA)
    (B : WangRectangleBound RB tileB) :
    WangRectangleBound (RA * RB) (wangProductTile tileA tileB) where
  bound w h := by
    rw [openWangProductCount_eq_mul]
    calc
      openWangCount tileA w h * openWangCount tileB w h
          ≤ RA ^ (w + h) * RB ^ (w + h) :=
            Nat.mul_le_mul (A.bound w h) (B.bound w h)
      _ = (RA * RB) ^ (w + h) := by rw [mul_pow]

/-- A local coupling predicate only removes product tiles. -/
def coupledWangTile {W H V : Type*} (tile : W → WangTile H V)
    (Coupled : W → Prop) [DecidablePred Coupled] :
    {u : W // Coupled u} → WangTile H V := fun u => tile u.1

def coupledOpenEmbedding {W H V : Type*} [Fintype W]
    (tile : W → WangTile H V) (Coupled : W → Prop) [DecidablePred Coupled]
    (w h : ℕ) :
    OpenWangTiling (coupledWangTile tile Coupled) w h ↪ OpenWangTiling tile w h where
  toFun f := by
    refine ⟨fun i j => (f.1 i j).1, ?_⟩
    exact f.2
  inj' := by
    intro f g heq
    apply Subtype.ext
    funext i j
    apply Subtype.ext
    exact congrFun (congrFun (congrArg Subtype.val heq) i) j

theorem coupledOpenCount_le {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V) (Coupled : W → Prop) [DecidablePred Coupled]
    (w h : ℕ) :
    openWangCount (coupledWangTile tile Coupled) w h ≤ openWangCount tile w h := by
  unfold openWangCount
  exact Fintype.card_le_of_injective _ (coupledOpenEmbedding tile Coupled w h).injective

def WangRectangleBound.coupled {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V) (Coupled : W → Prop) [DecidablePred Coupled]
    {R : ℕ} (C : WangRectangleBound R tile) :
    WangRectangleBound R (coupledWangTile tile Coupled) where
  bound w h := (coupledOpenCount_le tile Coupled w h).trans (C.bound w h)

/-! ## The explicit ripple-counter track -/

abbrev RippleTile := Bool × Bool

/-- The four ripple tiles `tau_(b,c)` from accepted Fact
`d35ba7ae99e1de23`. -/
def rippleTile : RippleTile → WangTile Bool Bool := fun u =>
  { west := u.1
    east := xor u.1 u.2
    south := u.2
    north := u.1 && u.2 }

/-- The west column and south row are a complete code for a ripple tiling. -/
def rippleBoundaryCode (w h : ℕ) := (Fin h → RippleTile) × (Fin w → RippleTile)

instance (w h : ℕ) : Fintype (rippleBoundaryCode w h) := by
  unfold rippleBoundaryCode
  infer_instance

def encodeRippleBoundary {w h : ℕ} (hw : 0 < w) (hh : 0 < h)
    (f : OpenWangTiling rippleTile w h) :
    rippleBoundaryCode w h :=
  (fun j => f.1 ⟨0, hw⟩ j, fun i => f.1 i ⟨0, hh⟩)

private theorem ripple_tiling_ext_of_boundary {w h : ℕ}
    (hw : 0 < w) (hh : 0 < h)
    (f g : OpenWangTiling rippleTile w h)
    (hb : encodeRippleBoundary hw hh f = encodeRippleBoundary hw hh g) : f = g := by
  apply Subtype.ext
  funext i j
  have hwest : ∀ j : Fin h, f.1 ⟨0, hw⟩ j = g.1 ⟨0, hw⟩ j := by
    intro y
    exact congrFun (congrArg Prod.fst hb) y
  have hsouth : ∀ i : Fin w, f.1 i ⟨0, hh⟩ = g.1 i ⟨0, hh⟩ := by
    intro x
    exact congrFun (congrArg Prod.snd hb) x
  induction s : i.1 + j.1 using Nat.strong_induction_on generalizing i j with
  | h s ih =>
      by_cases hi : i.1 = 0
      · have ieq : i = ⟨0, hw⟩ := Fin.eq_of_val_eq hi
        simpa [ieq] using hwest j
      by_cases hj : j.1 = 0
      · have jeq : j = ⟨0, hh⟩ := Fin.eq_of_val_eq hj
        simpa [jeq] using hsouth i
      · have ipos : 0 < i.1 := Nat.pos_of_ne_zero hi
        have jpos : 0 < j.1 := Nat.pos_of_ne_zero hj
        let il : Fin w := ⟨i.1 - 1, by omega⟩
        let jb : Fin h := ⟨j.1 - 1, by omega⟩
        have hleft : f.1 il j = g.1 il j := by
          apply ih (il.1 + j.1)
          · dsimp [il]; omega
          · rfl
        have hbelow : f.1 i jb = g.1 i jb := by
          apply ih (i.1 + jb.1)
          · dsimp [jb]; omega
          · rfl
        have hfhor := f.2.1 il j (by dsimp [il]; omega)
        have hghor := g.2.1 il j (by dsimp [il]; omega)
        have hfver := f.2.2 i jb (by dsimp [jb]; omega)
        have hgver := g.2.2 i jb (by dsimp [jb]; omega)
        have hil : (⟨il.1 + 1, by dsimp [il]; omega⟩ : Fin w) = i := by
          apply Fin.ext
          dsimp [il]
          omega
        have hjb : (⟨jb.1 + 1, by dsimp [jb]; omega⟩ : Fin h) = j := by
          apply Fin.ext
          dsimp [jb]
          omega
        rw [hil] at hfhor hghor
        rw [hjb] at hfver hgver
        apply Prod.ext
        · change (f.1 i j).1 = (g.1 i j).1
          calc
            (f.1 i j).1 = (rippleTile (f.1 il j)).east := hfhor.symm
            _ = (rippleTile (g.1 il j)).east := by rw [hleft]
            _ = (g.1 i j).1 := hghor
        · change (f.1 i j).2 = (g.1 i j).2
          calc
            (f.1 i j).2 = (rippleTile (f.1 i jb)).north := hfver.symm
            _ = (rippleTile (g.1 i jb)).north := by rw [hbelow]
            _ = (g.1 i j).2 := hgver

theorem encodeRippleBoundary_injective (w h : ℕ) (hw : 0 < w) (hh : 0 < h) :
    Function.Injective (encodeRippleBoundary (w := w) (h := h) hw hh) :=
  fun f g hfg => ripple_tiling_ext_of_boundary hw hh f g hfg

/-- A kernel-checked (slightly non-sharp) arbitrary-rectangle perimeter bound
for the concrete four-tile ripple system. -/
def rippleRectangleBound : WangRectangleBound 4 rippleTile where
  bound w h := by
    by_cases hw : 0 < w
    swap
    · have hw0 : w = 0 := Nat.eq_zero_of_not_pos hw
      subst w
      calc
        openWangCount rippleTile 0 h ≤ 1 := by
          unfold openWangCount
          rw [Fintype.card_le_one_iff]
          intro f g
          apply Subtype.ext
          funext i
          exact Fin.elim0 i
        _ ≤ 4 ^ (0 + h) := Nat.one_le_pow (0 + h) 4 (by decide)
    by_cases hh : 0 < h
    swap
    · have hh0 : h = 0 := Nat.eq_zero_of_not_pos hh
      subst h
      calc
        openWangCount rippleTile w 0 ≤ 1 := by
          unfold openWangCount
          rw [Fintype.card_le_one_iff]
          intro f g
          apply Subtype.ext
          funext i j
          exact Fin.elim0 j
        _ ≤ 4 ^ (w + 0) := Nat.one_le_pow (w + 0) 4 (by decide)
    unfold openWangCount
    calc
      Fintype.card (OpenWangTiling rippleTile w h)
          ≤ Fintype.card (rippleBoundaryCode w h) :=
            Fintype.card_le_of_injective _ (encodeRippleBoundary_injective w h hw hh)
      _ = 4 ^ (w + h) := by
        simp [rippleBoundaryCode, pow_add, Nat.mul_comm]

/-! ## The explicit east-diode scanner track -/

/-- `none` is the unique idle scanner tile; `some (s,t)` is a marked
east-column tile with south state `s` and north state `t`. -/
abbrev ScannerTile (S : Type*) := Option (S × S)

def scannerTile {S : Type*} : ScannerTile S → WangTile Bool (Option S)
  | none => { west := false, east := false, south := none, north := none }
  | some st => { west := false, east := true, south := some st.1, north := some st.2 }

private theorem scanner_interior_idle {S : Type*} [Fintype S]
    {w h : ℕ} (f : OpenWangTiling (scannerTile (S := S)) w h)
    (i : Fin w) (j : Fin h) (hi : i.1 + 1 < w) : f.1 i j = none := by
  have hm := f.2.1 i j hi
  cases htile : f.1 i j with
  | none => rfl
  | some st =>
      cases hnext : f.1 ⟨i.1 + 1, hi⟩ j <;>
        simp [scannerTile, htile, hnext] at hm

def scannerEastCode {S : Type*} [Fintype S] {w h : ℕ}
    (f : OpenWangTiling (scannerTile (S := S)) w h) : Fin h → ScannerTile S :=
  if hw : 0 < w then fun j => f.1 ⟨w - 1, by omega⟩ j else fun _ => none

theorem scannerEastCode_injective {S : Type*} [Fintype S] (w h : ℕ) :
    Function.Injective (scannerEastCode (S := S) (w := w) (h := h)) := by
  intro f g heq
  apply Subtype.ext
  funext i j
  by_cases hw : 0 < w
  · by_cases hi : i.1 + 1 < w
    · rw [scanner_interior_idle f i j hi, scanner_interior_idle g i j hi]
    · have hval : i.1 = w - 1 := by omega
      have hieq : i = ⟨w - 1, by omega⟩ := Fin.eq_of_val_eq hval
      simpa [hieq, scannerEastCode, hw] using congrFun heq j
  · have hw0 : w = 0 := Nat.eq_zero_of_not_pos hw
    subst w
    exact Fin.elim0 i

/-- An explicit perimeter certificate for the scanner.  The base is the
number of scanner tiles plus one; unlike the paper's sharper estimate this
does not need to classify the vertical east-column word. -/
def scannerRectangleBound (S : Type*) [Fintype S] [DecidableEq S] :
    WangRectangleBound (Fintype.card (ScannerTile S) + 1) (scannerTile (S := S)) where
  bound w h := by
    unfold openWangCount
    let R := Fintype.card (ScannerTile S) + 1
    calc
      Fintype.card (OpenWangTiling (scannerTile (S := S)) w h)
          ≤ Fintype.card (Fin h → ScannerTile S) :=
            Fintype.card_le_of_injective _ (scannerEastCode_injective w h)
      _ = Fintype.card (ScannerTile S) ^ h := by simp [Fintype.card_fun]
      _ ≤ R ^ h := by
        exact Nat.pow_le_pow_left (Nat.le_add_right _ _) _
      _ ≤ R ^ (w + h) := by
        apply Nat.pow_le_pow_right
        · exact Nat.zero_lt_succ _
        · omega

/-! ## The explicit shared-q four-side amplifier -/

@[ext] structure AmpRaw (Q : ℕ) where
  westActive : Bool
  eastActive : Bool
  southActive : Bool
  northActive : Bool
  qWest : Fin Q
  qEast : Fin Q
  qSouth : Fin Q
  qNorth : Fin Q
  deriving DecidableEq

instance (Q : ℕ) : Finite (AmpRaw Q) :=
  Finite.of_injective
    (fun u : AmpRaw Q =>
      ((u.westActive, u.eastActive, u.southActive, u.northActive),
        (u.qWest, u.qEast, u.qSouth, u.qNorth))) (by
      intro u v h
      apply AmpRaw.ext <;> simp_all)

noncomputable instance (Q : ℕ) : Fintype (AmpRaw Q) := Fintype.ofFinite _

def AmpLegal {Q : ℕ} [NeZero Q] (u : AmpRaw Q) : Prop :=
  (u.westActive = false → u.qWest = ⟨0, NeZero.pos Q⟩) ∧
  (u.eastActive = false → u.qEast = ⟨0, NeZero.pos Q⟩) ∧
  (u.southActive = false → u.qSouth = ⟨0, NeZero.pos Q⟩) ∧
  (u.northActive = false → u.qNorth = ⟨0, NeZero.pos Q⟩) ∧
  (u.westActive = true → u.southActive = true → u.qWest = u.qSouth) ∧
  (u.westActive = true → u.northActive = true → u.qWest = u.qNorth) ∧
  (u.eastActive = true → u.southActive = true → u.qEast = u.qSouth) ∧
  (u.eastActive = true → u.northActive = true → u.qEast = u.qNorth)

abbrev SharedQAmpTile (Q : ℕ) [NeZero Q] := {u : AmpRaw Q // AmpLegal u}

noncomputable instance (Q : ℕ) [NeZero Q] : Fintype (SharedQAmpTile Q) :=
  Fintype.ofFinite _

@[ext] structure AmpHorizontalColour (Q : ℕ) where
  westDead : Bool
  westCode : Fin Q
  eastDead : Bool
  eastCode : Fin Q
  southChain : Bool
  northChain : Bool
  deriving DecidableEq, Fintype

@[ext] structure AmpVerticalColour (Q : ℕ) where
  westChain : Bool
  eastChain : Bool
  southDead : Bool
  southCode : Fin Q
  northDead : Bool
  northCode : Fin Q
  deriving DecidableEq, Fintype

/-- Literal colour table of the four-side dead-colour amplifier.  The Boolean
dead flag makes each outward active colour disjoint from every inward colour;
the chain flags propagate activity along the relevant geometric side. -/
def sharedQAmpWangTile (Q : ℕ) [NeZero Q] :
    SharedQAmpTile Q → WangTile (AmpHorizontalColour Q) (AmpVerticalColour Q) := fun u =>
  { west :=
      { westDead := u.1.westActive
        westCode := u.1.qWest
        eastDead := false
        eastCode := ⟨0, NeZero.pos Q⟩
        southChain := u.1.southActive
        northChain := u.1.northActive }
    east :=
      { westDead := false
        westCode := ⟨0, NeZero.pos Q⟩
        eastDead := u.1.eastActive
        eastCode := u.1.qEast
        southChain := u.1.southActive
        northChain := u.1.northActive }
    south :=
      { westChain := u.1.westActive
        eastChain := u.1.eastActive
        southDead := u.1.southActive
        southCode := u.1.qSouth
        northDead := false
        northCode := ⟨0, NeZero.pos Q⟩ }
    north :=
      { westChain := u.1.westActive
        eastChain := u.1.eastActive
        southDead := false
        southCode := ⟨0, NeZero.pos Q⟩
        northDead := u.1.northActive
        northCode := u.1.qNorth } }

private theorem amp_west_boundary {Q : ℕ} [NeZero Q]
    {w h : ℕ} (f : OpenWangTiling (sharedQAmpWangTile Q) w h)
    (i : Fin w) (j : Fin h) (ha : (f.1 i j).1.westActive = true) : i.1 = 0 := by
  by_contra hi
  let il : Fin w := ⟨i.1 - 1, by omega⟩
  have hm := f.2.1 il j (by dsimp [il]; omega)
  have hil : (⟨il.1 + 1, by dsimp [il]; omega⟩ : Fin w) = i := by
    apply Fin.ext
    dsimp [il]
    omega
  rw [hil] at hm
  have := congrArg AmpHorizontalColour.westDead hm
  simp [sharedQAmpWangTile, ha] at this

private theorem amp_east_boundary {Q : ℕ} [NeZero Q]
    {w h : ℕ} (f : OpenWangTiling (sharedQAmpWangTile Q) w h)
    (i : Fin w) (j : Fin h) (ha : (f.1 i j).1.eastActive = true) : i.1 + 1 = w := by
  by_contra hi
  have hil : i.1 + 1 < w := by omega
  have hm := f.2.1 i j hil
  have := congrArg AmpHorizontalColour.eastDead hm
  simp [sharedQAmpWangTile, ha] at this

private theorem amp_south_boundary {Q : ℕ} [NeZero Q]
    {w h : ℕ} (f : OpenWangTiling (sharedQAmpWangTile Q) w h)
    (i : Fin w) (j : Fin h) (ha : (f.1 i j).1.southActive = true) : j.1 = 0 := by
  by_contra hj
  let jb : Fin h := ⟨j.1 - 1, by omega⟩
  have hm := f.2.2 i jb (by dsimp [jb]; omega)
  have hjb : (⟨jb.1 + 1, by dsimp [jb]; omega⟩ : Fin h) = j := by
    apply Fin.ext
    dsimp [jb]
    omega
  rw [hjb] at hm
  have := congrArg AmpVerticalColour.southDead hm
  simp [sharedQAmpWangTile, ha] at this

private theorem amp_north_boundary {Q : ℕ} [NeZero Q]
    {w h : ℕ} (f : OpenWangTiling (sharedQAmpWangTile Q) w h)
    (i : Fin w) (j : Fin h) (ha : (f.1 i j).1.northActive = true) : j.1 + 1 = h := by
  by_contra hj
  have hjl : j.1 + 1 < h := by omega
  have hm := f.2.2 i j hjl
  have := congrArg AmpVerticalColour.northDead hm
  simp [sharedQAmpWangTile, ha] at this

private theorem amp_interior_unique {Q : ℕ} [NeZero Q]
    {w h : ℕ} (f g : OpenWangTiling (sharedQAmpWangTile Q) w h)
    (i : Fin w) (j : Fin h) (hi0 : i.1 ≠ 0) (hi1 : i.1 + 1 ≠ w)
    (hj0 : j.1 ≠ 0) (hj1 : j.1 + 1 ≠ h) : f.1 i j = g.1 i j := by
  apply Subtype.ext
  apply AmpRaw.ext
  · cases hf : (f.1 i j).1.westActive with
    | false =>
        cases hg : (g.1 i j).1.westActive with
        | false => rfl
        | true => exact (hi0 (amp_west_boundary g i j hg)).elim
    | true => exact (hi0 (amp_west_boundary f i j hf)).elim
  · cases hf : (f.1 i j).1.eastActive with
    | false =>
        cases hg : (g.1 i j).1.eastActive with
        | false => rfl
        | true => exact (hi1 (amp_east_boundary g i j hg)).elim
    | true => exact (hi1 (amp_east_boundary f i j hf)).elim
  · cases hf : (f.1 i j).1.southActive with
    | false =>
        cases hg : (g.1 i j).1.southActive with
        | false => rfl
        | true => exact (hj0 (amp_south_boundary g i j hg)).elim
    | true => exact (hj0 (amp_south_boundary f i j hf)).elim
  · cases hf : (f.1 i j).1.northActive with
    | false =>
        cases hg : (g.1 i j).1.northActive with
        | false => rfl
        | true => exact (hj1 (amp_north_boundary g i j hg)).elim
    | true => exact (hj1 (amp_north_boundary f i j hf)).elim
  · exact (f.1 i j).2.1 (by
      cases hact : (f.1 i j).1.westActive
      · rfl
      · exact (hi0 (amp_west_boundary f i j hact)).elim) |>.trans
        ((g.1 i j).2.1 (by
          cases hact : (g.1 i j).1.westActive
          · rfl
          · exact (hi0 (amp_west_boundary g i j hact)).elim)).symm
  · exact (f.1 i j).2.2.1 (by
      cases hact : (f.1 i j).1.eastActive
      · rfl
      · exact (hi1 (amp_east_boundary f i j hact)).elim) |>.trans
        ((g.1 i j).2.2.1 (by
          cases hact : (g.1 i j).1.eastActive
          · rfl
          · exact (hi1 (amp_east_boundary g i j hact)).elim)).symm
  · exact (f.1 i j).2.2.2.1 (by
      cases hact : (f.1 i j).1.southActive
      · rfl
      · exact (hj0 (amp_south_boundary f i j hact)).elim) |>.trans
        ((g.1 i j).2.2.2.1 (by
          cases hact : (g.1 i j).1.southActive
          · rfl
          · exact (hj0 (amp_south_boundary g i j hact)).elim)).symm
  · exact (f.1 i j).2.2.2.2.1 (by
      cases hact : (f.1 i j).1.northActive
      · rfl
      · exact (hj1 (amp_north_boundary f i j hact)).elim) |>.trans
        ((g.1 i j).2.2.2.2.1 (by
          cases hact : (g.1 i j).1.northActive
          · rfl
          · exact (hj1 (amp_north_boundary g i j hact)).elim)).symm

/-- Four literal boundary words.  `Option` makes the code total also for an
empty dimension; positive rectangles never use the `none` padding. -/
def ampBoundaryCode (Q w h : ℕ) [NeZero Q] :=
  ((Fin h → Option (SharedQAmpTile Q)) × (Fin h → Option (SharedQAmpTile Q))) ×
  ((Fin w → Option (SharedQAmpTile Q)) × (Fin w → Option (SharedQAmpTile Q)))

instance (Q w h : ℕ) [NeZero Q] : Fintype (ampBoundaryCode Q w h) := by
  unfold ampBoundaryCode
  infer_instance

def encodeAmpBoundary {Q : ℕ} [NeZero Q] {w h : ℕ}
    (f : OpenWangTiling (sharedQAmpWangTile Q) w h) : ampBoundaryCode Q w h :=
  ((if hw : 0 < w then fun j => some (f.1 ⟨0, hw⟩ j) else fun _ => none,
    if hw : 0 < w then fun j => some (f.1 ⟨w - 1, by omega⟩ j) else fun _ => none),
   (if hh : 0 < h then fun i => some (f.1 i ⟨0, hh⟩) else fun _ => none,
    if hh : 0 < h then fun i => some (f.1 i ⟨h - 1, by omega⟩) else fun _ => none))

theorem encodeAmpBoundary_injective {Q : ℕ} [NeZero Q] (w h : ℕ) :
    Function.Injective (encodeAmpBoundary (Q := Q) (w := w) (h := h)) := by
  intro f g heq
  apply Subtype.ext
  funext i j
  have hw : 0 < w := Nat.zero_lt_of_lt i.isLt
  have hh : 0 < h := Nat.zero_lt_of_lt j.isLt
  by_cases hi0 : i.1 = 0
  · have hf := congrFun (congrArg (fun z => z.1.1) heq) j
    have ieq : i = ⟨0, hw⟩ := Fin.eq_of_val_eq hi0
    have hf' : some (f.1 i j) = some (g.1 i j) := by
      simpa [encodeAmpBoundary, hw, ieq] using hf
    exact Option.some.inj hf'
  by_cases hi1 : i.1 + 1 = w
  · have hf := congrFun (congrArg (fun z => z.1.2) heq) j
    have hval : i.1 = w - 1 := by omega
    have hieq : i = ⟨w - 1, by omega⟩ := Fin.eq_of_val_eq hval
    have hf' : some (f.1 i j) = some (g.1 i j) := by
      simpa [encodeAmpBoundary, hw, hieq] using hf
    exact Option.some.inj hf'
  by_cases hj0 : j.1 = 0
  · have hf := congrFun (congrArg (fun z => z.2.1) heq) i
    have hjeq : j = ⟨0, hh⟩ := Fin.eq_of_val_eq hj0
    have hf' : some (f.1 i j) = some (g.1 i j) := by
      simpa [encodeAmpBoundary, hh, hjeq] using hf
    exact Option.some.inj hf'
  by_cases hj1 : j.1 + 1 = h
  · have hf := congrFun (congrArg (fun z => z.2.2) heq) i
    have hval : j.1 = h - 1 := by omega
    have hjeq : j = ⟨h - 1, by omega⟩ := Fin.eq_of_val_eq hval
    have hf' : some (f.1 i j) = some (g.1 i j) := by
      simpa [encodeAmpBoundary, hh, hjeq] using hf
    exact Option.some.inj hf'
  exact amp_interior_unique f g i j hi0 hi1 hj0 hj1

/-- A fully concrete arbitrary-rectangle perimeter certificate for the actual
shared-q amplifier.  Its base is intentionally coarse; only existence of a
fixed base is used by the geometric readout. -/
def sharedQAmpRectangleBound (Q : ℕ) [NeZero Q] :
    WangRectangleBound ((Fintype.card (SharedQAmpTile Q) + 1) ^ 2)
      (sharedQAmpWangTile Q) where
  bound w h := by
    unfold openWangCount
    let M := Fintype.card (SharedQAmpTile Q) + 1
    calc
      Fintype.card (OpenWangTiling (sharedQAmpWangTile Q) w h)
          ≤ Fintype.card (ampBoundaryCode Q w h) :=
            Fintype.card_le_of_injective _ (encodeAmpBoundary_injective w h)
      _ = M ^ (2 * (w + h)) := by
        simp only [ampBoundaryCode, Fintype.card_prod, Fintype.card_fun,
          Fintype.card_option, Fintype.card_fin]
        change (M ^ h * M ^ h) * (M ^ w * M ^ w) = M ^ (2 * (w + h))
        simp only [← pow_add]
        congr 1
        omega
      _ = (M ^ 2) ^ (w + h) := by rw [pow_mul]

/-! ## Converting the accepted constant-column theorem to a rectangle bound -/

/-- A vertically matching Wang column of a fixed height. -/
def WangColumn {W H V : Type*} [Fintype W]
    (tile : W → WangTile H V) (h : ℕ) :=
  {c : Fin h → W //
    ∀ (j : Fin h) (hj : j.1 + 1 < h),
      (tile (c j)).north = (tile (c ⟨j.1 + 1, hj⟩)).south}

instance {W H V : Type*} [Fintype W] [DecidableEq V]
    (tile : W → WangTile H V) (h : ℕ) : Fintype (WangColumn tile h) := by
  unfold WangColumn
  infer_instance

def WangColumn.eastWord {W H V : Type*} [Fintype W]
    (tile : W → WangTile H V) {h : ℕ} (c : WangColumn tile h) : Fin h → H :=
  fun j => (tile (c.1 j)).east

/-- The exact local input supplied by clause (D) of the accepted higher-block
tableau theorem: among columns with one prescribed east word there are at
most `K` possibilities.  Unlike `WangRectangleBound`, this is a one-column
statement, and the theorem below proves the nontrivial westward iteration. -/
structure ConstantEastColumnBound (K : ℕ)
    {W H V : Type*} [Fintype W] [DecidableEq V]
    (tile : W → WangTile H V) where
  code : ∀ h : ℕ, WangColumn tile h → Fin K
  code_injective_on_east : ∀ {h : ℕ} (c d : WangColumn tile h),
    c.eastWord tile = d.eastWord tile → code h c = code h d → c = d

def tilingColumn {W H V : Type*} [Fintype W]
    (tile : W → WangTile H V) {w h : ℕ}
    (f : OpenWangTiling tile w h) (i : Fin w) : WangColumn tile h := by
  refine ⟨fun j => f.1 i j, ?_⟩
  intro j hj
  exact f.2.2 i j hj

def eastColumnCode {W H V : Type*} [Fintype W] [DecidableEq V]
    (tile : W → WangTile H V) {K w h : ℕ}
    (C : ConstantEastColumnBound K tile) (hw : 0 < w)
    (f : OpenWangTiling tile w h) : (Fin h → H) × (Fin w → Fin K) :=
  ((tilingColumn tile f ⟨w - 1, by omega⟩).eastWord tile,
    fun i => C.code h (tilingColumn tile f i))

private theorem eastColumnCode_injective
    {W H V : Type*} [Fintype W] [DecidableEq V]
    (tile : W → WangTile H V) {K w h : ℕ}
    (C : ConstantEastColumnBound K tile) (hw : 0 < w) :
    Function.Injective (eastColumnCode (h := h) tile C hw) := by
  intro f g heq
  have heast :
      (tilingColumn tile f ⟨w - 1, by omega⟩).eastWord tile =
        (tilingColumn tile g ⟨w - 1, by omega⟩).eastWord tile :=
    congrArg Prod.fst heq
  have hcode : ∀ i : Fin w,
      C.code h (tilingColumn tile f i) = C.code h (tilingColumn tile g i) := by
    intro i
    exact congrFun (congrArg Prod.snd heq) i
  have hcols : ∀ i : Fin w, tilingColumn tile f i = tilingColumn tile g i := by
    intro i
    generalize hd : w - 1 - i.1 = d
    induction d using Nat.strong_induction_on generalizing i with
    | h d ih =>
        have heast_i : (tilingColumn tile f i).eastWord tile =
            (tilingColumn tile g i).eastWord tile := by
          by_cases hi : i.1 + 1 = w
          · have hval : i.1 = w - 1 := by omega
            have hieq : i = ⟨w - 1, by omega⟩ := Fin.eq_of_val_eq hval
            simpa [hieq] using heast
          · have hir : i.1 + 1 < w := by omega
            let ir : Fin w := ⟨i.1 + 1, hir⟩
            have hdr : w - 1 - ir.1 < d := by dsimp [ir]; omega
            have hcolr : tilingColumn tile f ir = tilingColumn tile g ir := by
              apply ih (w - 1 - ir.1) hdr ir
              rfl
            funext j
            have hfh := f.2.1 i j hir
            have hgh := g.2.1 i j hir
            change (tile (f.1 i j)).east = (tile (g.1 i j)).east
            calc
              (tile (f.1 i j)).east = (tile (f.1 ir j)).west := by
                simpa [ir] using hfh
              _ = (tile (g.1 ir j)).west := by
                have hv := congrArg Subtype.val hcolr
                have hc := congrFun hv j
                change f.1 ir j = g.1 ir j at hc
                rw [hc]
              _ = (tile (g.1 i j)).east := by
                simpa [ir] using hgh.symm
        exact C.code_injective_on_east _ _ heast_i (hcode i)
  apply Subtype.ext
  funext i j
  have hc := congrArg Subtype.val (hcols i)
  exact congrFun hc j

/-- The westward column scan converts a *constant column-successor* theorem
into the required arbitrary-rectangle perimeter theorem. -/
def rectangleBoundOfConstantEastColumns
    {W H V : Type*} [Fintype W] [Fintype H]
    [DecidableEq H] [DecidableEq V]
    (tile : W → WangTile H V) {K : ℕ}
    (C : ConstantEastColumnBound K tile) :
    WangRectangleBound ((Fintype.card H + 1) * (K + 1)) tile where
  bound w h := by
    let R := (Fintype.card H + 1) * (K + 1)
    by_cases hw : 0 < w
    swap
    · have hw0 : w = 0 := Nat.eq_zero_of_not_pos hw
      subst w
      calc
        openWangCount tile 0 h ≤ 1 := by
          unfold openWangCount
          rw [Fintype.card_le_one_iff]
          intro f g
          apply Subtype.ext
          funext i
          exact Fin.elim0 i
        _ ≤ R ^ (0 + h) := by
          apply Nat.one_le_pow
          exact Nat.mul_pos (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
    unfold openWangCount
    calc
      Fintype.card (OpenWangTiling tile w h)
          ≤ Fintype.card ((Fin h → H) × (Fin w → Fin K)) :=
            Fintype.card_le_of_injective _ (eastColumnCode_injective tile C hw)
      _ = Fintype.card H ^ h * K ^ w := by simp
      _ ≤ (Fintype.card H + 1) ^ h * (K + 1) ^ w := by
        exact Nat.mul_le_mul
          (Nat.pow_le_pow_left (Nat.le_add_right _ _) _)
          (Nat.pow_le_pow_left (Nat.le_add_right _ _) _)
      _ ≤ R ^ h * R ^ w := by
        apply Nat.mul_le_mul
        · exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ _)) _
        · exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (Nat.zero_lt_succ _)) _
      _ = R ^ (w + h) := by rw [← pow_add]; congr 1; omega

/-! ## Private-colour dummy mode -/

/-- Adjoin one private-colour dummy tile to a Wang system. -/
def withDummyWangTile {W H V : Type*} (tile : W → WangTile H V) :
    Option W → WangTile (Option H) (Option V)
  | none => { west := none, east := none, south := none, north := none }
  | some u =>
      { west := some (tile u).west
        east := some (tile u).east
        south := some (tile u).south
        north := some (tile u).north }

private theorem dummy_mode_horizontal {W H V : Type*} [Fintype W]
    (tile : W → WangTile H V) {w h : ℕ}
    (f : OpenWangTiling (withDummyWangTile tile) w h)
    (i : Fin w) (j : Fin h) (hi : i.1 + 1 < w) :
    (f.1 i j).isSome = (f.1 ⟨i.1 + 1, hi⟩ j).isSome := by
  have hm := f.2.1 i j hi
  cases ha : f.1 i j <;> cases hb : f.1 ⟨i.1 + 1, hi⟩ j <;>
    simp [withDummyWangTile, ha, hb] at hm ⊢

private theorem dummy_mode_vertical {W H V : Type*} [Fintype W]
    (tile : W → WangTile H V) {w h : ℕ}
    (f : OpenWangTiling (withDummyWangTile tile) w h)
    (i : Fin w) (j : Fin h) (hj : j.1 + 1 < h) :
    (f.1 i j).isSome = (f.1 i ⟨j.1 + 1, hj⟩).isSome := by
  have hm := f.2.2 i j hj
  cases ha : f.1 i j <;> cases hb : f.1 i ⟨j.1 + 1, hj⟩ <;>
    simp [withDummyWangTile, ha, hb] at hm ⊢

private theorem dummy_mode_eq_origin {W H V : Type*} [Fintype W]
    (tile : W → WangTile H V) {w h : ℕ} (hw : 0 < w) (hh : 0 < h)
    (f : OpenWangTiling (withDummyWangTile tile) w h) (i : Fin w) (j : Fin h) :
    (f.1 i j).isSome = (f.1 ⟨0, hw⟩ ⟨0, hh⟩).isSome := by
  have hrow : ∀ x : Fin w, (f.1 x j).isSome = (f.1 ⟨0, hw⟩ j).isSome := by
    intro x
    induction d : x.1 using Nat.strong_induction_on generalizing x with
    | h d ih =>
        by_cases hx : x.1 = 0
        · have heq : x = ⟨0, hw⟩ := Fin.eq_of_val_eq hx
          simp [heq]
        · let xl : Fin w := ⟨x.1 - 1, by omega⟩
          have hs : xl.1 + 1 < w := by dsimp [xl]; omega
          have hxl : (⟨xl.1 + 1, hs⟩ : Fin w) = x := by
            apply Fin.ext
            dsimp [xl]
            omega
          calc
            (f.1 x j).isSome = (f.1 xl j).isSome := by
              rw [← hxl]
              exact (dummy_mode_horizontal tile f xl j hs).symm
            _ = (f.1 ⟨0, hw⟩ j).isSome := by
              apply ih xl.1
              · dsimp [xl]; omega
              · rfl
  have hcol : ∀ y : Fin h,
      (f.1 ⟨0, hw⟩ y).isSome = (f.1 ⟨0, hw⟩ ⟨0, hh⟩).isSome := by
    intro y
    induction d : y.1 using Nat.strong_induction_on generalizing y with
    | h d ih =>
        by_cases hy : y.1 = 0
        · have heq : y = ⟨0, hh⟩ := Fin.eq_of_val_eq hy
          simp [heq]
        · let yb : Fin h := ⟨y.1 - 1, by omega⟩
          have hs : yb.1 + 1 < h := by dsimp [yb]; omega
          have hyb : (⟨yb.1 + 1, hs⟩ : Fin h) = y := by
            apply Fin.ext
            dsimp [yb]
            omega
          calc
            (f.1 ⟨0, hw⟩ y).isSome = (f.1 ⟨0, hw⟩ yb).isSome := by
              rw [← hyb]
              exact (dummy_mode_vertical tile f ⟨0, hw⟩ yb hs).symm
            _ = (f.1 ⟨0, hw⟩ ⟨0, hh⟩).isSome := by
              apply ih yb.1
              · dsimp [yb]; omega
              · rfl
  exact (hrow i).trans (hcol j)

def stripDummyTiling {W H V : Type*} [Fintype W]
    (tile : W → WangTile H V) {w h : ℕ}
    (f : OpenWangTiling (withDummyWangTile tile) w h)
    (hsome : ∀ i j, (f.1 i j).isSome = true) : OpenWangTiling tile w h := by
  choose val hval using fun i j => Option.isSome_iff_exists.mp (hsome i j)
  refine ⟨val, ?_⟩
  constructor
  · intro i j hi
    have hm := f.2.1 i j hi
    rw [hval i j, hval ⟨i.1 + 1, hi⟩ j] at hm
    simpa [withDummyWangTile] using hm
  · intro i j hj
    have hm := f.2.2 i j hj
    rw [hval i j, hval i ⟨j.1 + 1, hj⟩] at hm
    simpa [withDummyWangTile] using hm

/-- On a nonempty rectangle, private dummy colours give the exact disjoint
union `one dummy tiling + one computation tiling`. -/
def withDummyOpenEquiv {W H V : Type*} [Fintype W]
    (tile : W → WangTile H V) (w h : ℕ) (hw : 0 < w) (hh : 0 < h) :
    OpenWangTiling (withDummyWangTile tile) w h ≃ Option (OpenWangTiling tile w h) where
  toFun f := by
    by_cases hd : f.1 ⟨0, hw⟩ ⟨0, hh⟩ = none
    · exact none
    · apply some
      apply stripDummyTiling tile f
      intro i j
      have hm := dummy_mode_eq_origin tile hw hh f i j
      cases hc : f.1 i j with
      | none =>
          have hroot : f.1 ⟨0, hw⟩ ⟨0, hh⟩ = none := by
            cases hr : f.1 ⟨0, hw⟩ ⟨0, hh⟩ with
            | none => rfl
            | some u => simp [hc, hr] at hm
          exact (hd hroot).elim
      | some u => simp [hc]
  invFun f := match f with
    | none => ⟨fun _ _ => none, by simp [withDummyWangTile]⟩
    | some g => ⟨fun i j => some (g.1 i j), by
        constructor
        · intro i j hi
          simpa [withDummyWangTile] using g.2.1 i j hi
        · intro i j hj
          simpa [withDummyWangTile] using g.2.2 i j hj⟩
  left_inv f := by
    apply Subtype.ext
    funext i j
    by_cases hd : f.1 ⟨0, hw⟩ ⟨0, hh⟩ = none
    · have hm := dummy_mode_eq_origin tile hw hh f i j
      rw [hd] at hm
      cases hc : f.1 i j
      · simp [hd]
      · simp [hc] at hm
    · have hm := dummy_mode_eq_origin tile hw hh f i j
      cases hc : f.1 i j with
      | none =>
          cases hr : f.1 ⟨0, hw⟩ ⟨0, hh⟩ with
          | none => exact (hd hr).elim
          | some u => simp [hc, hr] at hm
      | some u =>
          simp [hd, stripDummyTiling, hc]
  right_inv f := by
    cases f with
    | none => simp
    | some g =>
        apply congrArg some
        apply Subtype.ext
        funext i j
        simp [stripDummyTiling]

theorem withDummyOpenCount_eq_add_one {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V] (tile : W → WangTile H V)
    (w h : ℕ) (hw : 0 < w) (hh : 0 < h) :
    openWangCount (withDummyWangTile tile) w h = 1 + openWangCount tile w h := by
  unfold openWangCount
  rw [Fintype.card_congr (withDummyOpenEquiv tile w h hw hh)]
  simp [Nat.add_comm]

/-- Adding the private dummy changes only the fixed perimeter base. -/
def WangRectangleBound.withDummy {W H V : Type*} [Fintype W]
    [DecidableEq H] [DecidableEq V] (tile : W → WangTile H V)
    {R : ℕ} (C : WangRectangleBound R tile) :
    WangRectangleBound (R + 1) (withDummyWangTile tile) where
  bound w h := by
    by_cases hw : 0 < w
    swap
    · have hw0 : w = 0 := Nat.eq_zero_of_not_pos hw
      subst w
      calc
        openWangCount (withDummyWangTile tile) 0 h ≤ 1 := by
          unfold openWangCount
          rw [Fintype.card_le_one_iff]
          intro f g
          apply Subtype.ext
          funext i
          exact Fin.elim0 i
        _ ≤ (R + 1) ^ (0 + h) := Nat.one_le_pow _ _ (Nat.zero_lt_succ _)
    by_cases hh : 0 < h
    swap
    · have hh0 : h = 0 := Nat.eq_zero_of_not_pos hh
      subst h
      calc
        openWangCount (withDummyWangTile tile) w 0 ≤ 1 := by
          unfold openWangCount
          rw [Fintype.card_le_one_iff]
          intro f g
          apply Subtype.ext
          funext i j
          exact Fin.elim0 j
        _ ≤ (R + 1) ^ (w + 0) := Nat.one_le_pow _ _ (Nat.zero_lt_succ _)
    rw [withDummyOpenCount_eq_add_one tile w h hw hh]
    calc
      1 + openWangCount tile w h ≤ 1 + R ^ (w + h) := Nat.add_le_add_left (C.bound w h) 1
      _ ≤ (R + 1) ^ (w + h) := by
        have he : 1 ≤ w + h := by omega
        calc
          1 + R ^ (w + h) ≤ 1 ^ (w + h) + R ^ (w + h) := by simp
          _ ≤ (1 + R) ^ (w + h) :=
            pow_add_pow_le (by omega) (by omega) (by omega)
          _ = (R + 1) ^ (w + h) := by rw [Nat.add_comm]

/-! ## The four-track locally coupled product -/

/-- The precise track inventory used by `W_prod`: shared-q amplifier,
ripple counter, higher-block tableau, and east-diode scanner. -/
abbrev WProdTracks (Q : ℕ) [NeZero Q] (Tab ScanState : Type*) :=
  ((SharedQAmpTile Q × RippleTile) × Tab) × ScannerTile ScanState

def wProdTracksTile (Q : ℕ) [NeZero Q]
    {Tab HTab VTab ScanState : Type*}
    (tabTile : Tab → WangTile HTab VTab) :
    WProdTracks Q Tab ScanState →
      WangTile
        (((AmpHorizontalColour Q × Bool) × HTab) × Bool)
        (((AmpVerticalColour Q × Bool) × VTab) × Option ScanState) :=
  wangProductTile
    (wangProductTile
      (wangProductTile (sharedQAmpWangTile Q) rippleTile)
      tabTile)
    (scannerTile (S := ScanState))

/-- The computation subset obtained by imposing all five same-cell coupling
constraints.  The predicate is explicit data, but no counting property of it
is assumed: deleting uncoupled product tiles can only decrease every open
rectangle count. -/
def wProdComputeTile (Q : ℕ) [NeZero Q]
    {Tab HTab VTab ScanState : Type*}
    (tabTile : Tab → WangTile HTab VTab)
    (Coupled : WProdTracks Q Tab ScanState → Prop) [DecidablePred Coupled] :
    {u : WProdTracks Q Tab ScanState // Coupled u} →
      WangTile
        (((AmpHorizontalColour Q × Bool) × HTab) × Bool)
        (((AmpVerticalColour Q × Bool) × VTab) × Option ScanState) :=
  coupledWangTile (wProdTracksTile Q tabTile) Coupled

/-- The actual unweighted product tile set, including the one private-colour
dummy tile. -/
def wProdWangTile (Q : ℕ) [NeZero Q]
    {Tab HTab VTab ScanState : Type*}
    (tabTile : Tab → WangTile HTab VTab)
    (Coupled : WProdTracks Q Tab ScanState → Prop) [DecidablePred Coupled] :
    Option {u : WProdTracks Q Tab ScanState // Coupled u} →
      WangTile
        (Option (((AmpHorizontalColour Q × Bool) × HTab) × Bool))
        (Option (((AmpVerticalColour Q × Bool) × VTab) × Option ScanState)) :=
  withDummyWangTile (wProdComputeTile Q tabTile Coupled)

def wProdRectangleBase (Q : ℕ) [NeZero Q]
    (TabHorizontal ScanState : Type*) [Fintype TabHorizontal] [Fintype ScanState]
    (Kcol : ℕ) : ℕ :=
  ((Fintype.card (SharedQAmpTile Q) + 1) ^ 2) * 4 *
    ((Fintype.card TabHorizontal + 1) * (Kcol + 1)) *
    (Fintype.card (ScannerTile ScanState) + 1)

/-- Concrete assembly of the arbitrary-rectangle certificate for the exact
four-track/dummy architecture of accepted Fact `ca9bbc68cbedb02f`.

The only non-geometric input is the *local* constant-column code for the
higher-block tableau.  The westward iteration, all other track bounds, product
inequality, coupling deletion, and private dummy isolation are all proved in
this file. -/
def wProdRectangleBound (Q : ℕ) [NeZero Q]
    {Tab HTab VTab ScanState : Type*}
    [Fintype Tab] [Fintype HTab] [Fintype ScanState]
    [DecidableEq HTab] [DecidableEq VTab] [DecidableEq ScanState]
    (tabTile : Tab → WangTile HTab VTab) {Kcol : ℕ}
    (TabColumns : ConstantEastColumnBound Kcol tabTile)
    (Coupled : WProdTracks Q Tab ScanState → Prop) [DecidablePred Coupled] :
    WangRectangleBound (wProdRectangleBase Q HTab ScanState Kcol + 1)
      (wProdWangTile Q tabTile Coupled) := by
  let A := sharedQAmpRectangleBound Q
  let RC := rippleRectangleBound
  let T := rectangleBoundOfConstantEastColumns tabTile TabColumns
  let S := scannerRectangleBound ScanState
  let AR := A.product (sharedQAmpWangTile Q) rippleTile RC
  let ART := AR.product
    (wangProductTile (sharedQAmpWangTile Q) rippleTile) tabTile T
  let ARTS := ART.product
    (wangProductTile (wangProductTile (sharedQAmpWangTile Q) rippleTile) tabTile)
    (scannerTile (S := ScanState)) S
  have HC : WangRectangleBound (wProdRectangleBase Q HTab ScanState Kcol)
      (wProdComputeTile Q tabTile Coupled) := by
    exact ARTS.coupled (wProdTracksTile Q tabTile) Coupled
  exact HC.withDummy (wProdComputeTile Q tabTile Coupled)

end
end PakFixedPolyomino
