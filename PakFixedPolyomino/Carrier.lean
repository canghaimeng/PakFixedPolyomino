import PakFixedPolyomino.IdentityRegister
import Mathlib.Tactic

namespace PakFixedPolyomino

noncomputable section

set_option maxHeartbeats 800000

/-- Finite numerical data of the identity-register compiler.  Colour maps are
already expressed in the chosen horizontal/vertical colour enumerations. -/
structure RegisterParams where
  tileCount : ℕ
  horizontalColours : ℕ
  verticalColours : ℕ
  perimeterBase : ℕ
  tileCount_pos : 0 < tileCount
  horizontalColours_pos : 0 < horizontalColours
  verticalColours_pos : 0 < verticalColours
  perimeterBase_ge_two : 2 ≤ perimeterBase
  west : Fin tileCount → Fin horizontalColours
  east : Fin tileCount → Fin horizontalColours
  south : Fin tileCount → Fin verticalColours
  north : Fin tileCount → Fin verticalColours

namespace RegisterParams

def amp (P : RegisterParams) : ℕ := 1024 * P.perimeterBase ^ 3
def codeSpan (P : RegisterParams) : ℕ :=
  4 * P.amp * max P.horizontalColours P.verticalColours
def pitch (P : RegisterParams) : ℕ := P.codeSpan + 4 * P.tileCount + 64
def handshake (P : RegisterParams) : ℕ := P.pitch - 8

theorem amp_pos (P : RegisterParams) : 0 < P.amp := by
  unfold amp
  have hR : 0 < P.perimeterBase := lt_of_lt_of_le (by decide) P.perimeterBase_ge_two
  exact Nat.mul_pos (by decide) (pow_pos hR 3)

theorem pitch_ge_tile_margin (P : RegisterParams) :
    4 * P.tileCount + 64 ≤ P.pitch := by
  simp [pitch]

theorem pitch_ge_sixty_eight (P : RegisterParams) : 68 ≤ P.pitch := by
  have := P.tileCount_pos
  have := P.pitch_ge_tile_margin
  omega

theorem codeSpan_pos (P : RegisterParams) : 0 < P.codeSpan := by
  unfold codeSpan
  have hmax : 0 < max P.horizontalColours P.verticalColours :=
    lt_of_lt_of_le P.horizontalColours_pos (Nat.le_max_left _ _)
  exact Nat.mul_pos (Nat.mul_pos (by decide) P.amp_pos) hmax

theorem handshake_eq (P : RegisterParams) :
    P.handshake = P.codeSpan + 4 * P.tileCount + 56 := by
  unfold handshake pitch
  omega

theorem handshake_lt_pitch (P : RegisterParams) : P.handshake < P.pitch := by
  unfold handshake
  have := P.pitch_ge_sixty_eight
  omega

end RegisterParams

/-- Four opening bits of a carrier. -/
@[ext] structure MacroState where
  west : Bool
  east : Bool
  south : Bool
  north : Bool
  deriving DecidableEq, Fintype

/-- Amplifier labels.  Closed-side labels are canonically required to be zero. -/
@[ext] structure AmpRecord (P : RegisterParams) (η : MacroState) where
  west : Fin P.amp
  east : Fin P.amp
  south : Fin P.amp
  north : Fin P.amp
  west_closed : η.west = false → west = ⟨0, P.amp_pos⟩
  east_closed : η.east = false → east = ⟨0, P.amp_pos⟩
  south_closed : η.south = false → south = ⟨0, P.amp_pos⟩
  north_closed : η.north = false → north = ⟨0, P.amp_pos⟩

theorem bool_toNat_lt_two (b : Bool) : b.toNat < 2 := by cases b <;> decide

def codeH (P : RegisterParams) (a b : Bool)
    (colour : Fin P.horizontalColours) (ell : Fin P.amp) : ℕ :=
  registerCode P.amp colour ell a.toNat b.toNat

def codeV (P : RegisterParams) (a b : Bool)
    (colour : Fin P.verticalColours) (ell : Fin P.amp) : ℕ :=
  registerCode P.amp colour ell a.toNat b.toNat

theorem codeH_bounds (P : RegisterParams) (a b : Bool)
    (colour : Fin P.horizontalColours) (ell : Fin P.amp) :
    8 ≤ codeH P a b colour ell ∧ codeH P a b colour ell ≤ P.codeSpan + 7 := by
  have h := registerCode_bounds P.amp_pos colour.isLt ell.isLt
    (bool_toNat_lt_two a) (bool_toNat_lt_two b)
  refine ⟨h.1, h.2.trans ?_⟩
  unfold RegisterParams.codeSpan
  have hc : P.horizontalColours ≤ max P.horizontalColours P.verticalColours :=
    Nat.le_max_left _ _
  have := Nat.mul_le_mul_left (4 * P.amp) hc
  simpa [Nat.mul_assoc] using Nat.add_le_add_right this 7

theorem codeV_bounds (P : RegisterParams) (a b : Bool)
    (colour : Fin P.verticalColours) (ell : Fin P.amp) :
    8 ≤ codeV P a b colour ell ∧ codeV P a b colour ell ≤ P.codeSpan + 7 := by
  have h := registerCode_bounds P.amp_pos colour.isLt ell.isLt
    (bool_toNat_lt_two a) (bool_toNat_lt_two b)
  refine ⟨h.1, h.2.trans ?_⟩
  unfold RegisterParams.codeSpan
  have hc : P.verticalColours ≤ max P.horizontalColours P.verticalColours :=
    Nat.le_max_right _ _
  have := Nat.mul_le_mul_left (4 * P.amp) hc
  simpa [Nat.mul_assoc] using Nat.add_le_add_right this 7

theorem codeH_lt_handshake (P : RegisterParams) (a b : Bool)
    (colour : Fin P.horizontalColours) (ell : Fin P.amp) :
    codeH P a b colour ell < P.handshake := by
  have hc := (codeH_bounds P a b colour ell).2
  rw [P.handshake_eq]
  have := P.tileCount_pos
  omega

theorem codeV_lt_handshake (P : RegisterParams) (a b : Bool)
    (colour : Fin P.verticalColours) (ell : Fin P.amp) :
    codeV P a b colour ell < P.handshake := by
  have hc := (codeV_bounds P a b colour ell).2
  rw [P.handshake_eq]
  have := P.tileCount_pos
  omega

theorem codeH_lt_pitch (P : RegisterParams) (a b : Bool)
    (colour : Fin P.horizontalColours) (ell : Fin P.amp) :
    codeH P a b colour ell < P.pitch :=
  (codeH_lt_handshake P a b colour ell).trans P.handshake_lt_pitch

theorem codeV_lt_pitch (P : RegisterParams) (a b : Bool)
    (colour : Fin P.verticalColours) (ell : Fin P.amp) :
    codeV P a b colour ell < P.pitch :=
  (codeV_lt_handshake P a b colour ell).trans P.handshake_lt_pitch

def cavityOrigin {P : RegisterParams} (u : Fin P.tileCount) : Cell :=
  ((16 + 4 * (u : ℕ) : ℕ), 16)

def tileCavity {P : RegisterParams} (u : Fin P.tileCount) : Polyomino := cavity (cavityOrigin u)

@[simp] theorem card_tileCavity {P : RegisterParams} (u : Fin P.tileCount) :
    (tileCavity u).card = 3 := by simp [tileCavity]

theorem tileCavity_injective (P : RegisterParams) :
    Function.Injective (tileCavity (P := P)) := by
  intro u v h
  have ho := cavity_injective h
  apply Fin.ext
  have hx := congrArg Prod.fst ho
  norm_num [cavityOrigin] at hx
  omega

def optionalCell (flag : Bool) (p : Cell) : Polyomino :=
  if flag then {p} else ∅

inductive Side where
  | west | east | south | north
  deriving DecidableEq

def allSides : Finset Side := {.west, .east, .south, .north}

def MacroState.isOpen (η : MacroState) : Side → Bool
  | .west => η.west
  | .east => η.east
  | .south => η.south
  | .north => η.north

def activeSides (η : MacroState) : Finset Side :=
  allSides.filter fun d => η.isOpen d

@[simp] theorem mem_activeSides (η : MacroState) (d : Side) :
    d ∈ activeSides η ↔ η.isOpen d = true := by
  rw [activeSides, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    cases d <;> simp [allSides]

def dentCell (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (ell : AmpRecord P η) : Side → Cell
  | .west => (0, codeH P η.south η.north (P.west u) ell.west)
  | .east => (((P.pitch - 1 : ℕ) : ℤ), P.handshake)
  | .south => (codeV P η.west η.east (P.south u) ell.south, 0)
  | .north => (P.handshake, ((P.pitch - 1 : ℕ) : ℤ))

def bumpCell (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (ell : AmpRecord P η) : Side → Cell
  | .west => (-1, P.handshake)
  | .east => (P.pitch, codeH P η.south η.north (P.east u) ell.east)
  | .south => (P.handshake, -1)
  | .north => (codeV P η.west η.east (P.north u) ell.north, P.pitch)

def dents (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (ell : AmpRecord P η) : Polyomino :=
  (activeSides η).image (dentCell P η u ell)

def bumps (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (ell : AmpRecord P η) : Polyomino :=
  (activeSides η).image (bumpCell P η u ell)

/-- The exact amplified identity-register carrier support. -/
def carrier (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (ell : AmpRecord P η) : Polyomino :=
  (square P.pitch \ (dents P η u ell ∪ tileCavity u)) ∪ bumps P η u ell

/-- The support box `{-1, ..., P_s}²`. -/
def extendedBox (P : RegisterParams) : Polyomino :=
  (Finset.Icc (-1 : ℤ) P.pitch).product (Finset.Icc (-1 : ℤ) P.pitch)

/-- Every tile-specific cavity lies safely in the body square. -/
theorem tileCavity_subset_body (P : RegisterParams) (u : Fin P.tileCount) :
    tileCavity u ⊆ square P.pitch := by
  intro z hz
  rw [tileCavity, cavity] at hz
  simp only [translate, Finset.mem_image] at hz
  rcases hz with ⟨p, hp, rfl⟩
  simp only [mem_plugL] at hp
  rcases hp with rfl | rfl | rfl
  · change (0 + (cavityOrigin u).1, 1 + (cavityOrigin u).2) ∈
      (natInterval P.pitch).product (natInterval P.pitch)
    have hu := u.isLt
    have hm := P.pitch_ge_tile_margin
    refine Finset.mem_product.mpr ⟨mem_natInterval.mpr ?_, mem_natInterval.mpr ?_⟩
    · exact ⟨16 + 4 * (u : ℕ), by omega, by norm_num [cavityOrigin]⟩
    · exact ⟨17, by omega, by norm_num [cavityOrigin]⟩
  · change (1 + (cavityOrigin u).1, 0 + (cavityOrigin u).2) ∈
      (natInterval P.pitch).product (natInterval P.pitch)
    have hu := u.isLt
    have hm := P.pitch_ge_tile_margin
    refine Finset.mem_product.mpr ⟨mem_natInterval.mpr ?_, mem_natInterval.mpr ?_⟩
    · exact ⟨17 + 4 * (u : ℕ), by omega, by norm_num [cavityOrigin]; omega⟩
    · exact ⟨16, by omega, by norm_num [cavityOrigin]⟩
  · change (1 + (cavityOrigin u).1, 1 + (cavityOrigin u).2) ∈
      (natInterval P.pitch).product (natInterval P.pitch)
    have hu := u.isLt
    have hm := P.pitch_ge_tile_margin
    refine Finset.mem_product.mpr ⟨mem_natInterval.mpr ?_, mem_natInterval.mpr ?_⟩
    · exact ⟨17 + 4 * (u : ℕ), by omega, by norm_num [cavityOrigin]; omega⟩
    · exact ⟨17, by omega, by norm_num [cavityOrigin]⟩

theorem dentCell_injective (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) :
    Function.Injective (dentCell P η u ell) := by
  intro d e h
  have hp := P.pitch_ge_sixty_eight
  have hh := P.handshake_eq
  have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
  have hHw := codeH_bounds P η.south η.north (P.west u) ell.west
  have hVs := codeV_bounds P η.west η.east (P.south u) ell.south
  cases d <;> cases e <;> simp [dentCell] at h ⊢ <;> omega

theorem bumpCell_injective (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) :
    Function.Injective (bumpCell P η u ell) := by
  intro d e h
  have hp := P.pitch_ge_sixty_eight
  have hh := P.handshake_eq
  have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
  have hHe := codeH_bounds P η.south η.north (P.east u) ell.east
  have hVn := codeV_bounds P η.west η.east (P.north u) ell.north
  cases d <;> cases e <;> simp [bumpCell] at h ⊢ <;> omega

@[simp] theorem card_dents (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) :
    (dents P η u ell).card = (activeSides η).card := by
  unfold dents
  exact Finset.card_image_of_injective _ (dentCell_injective P η u ell)

@[simp] theorem card_bumps (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) :
    (bumps P η u ell).card = (activeSides η).card := by
  unfold bumps
  exact Finset.card_image_of_injective _ (bumpCell_injective P η u ell)

theorem feature_card_balance (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) :
    (dents P η u ell).card = (bumps P η u ell).card := by simp

theorem dents_subset_body (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) :
    dents P η u ell ⊆ square P.pitch := by
  have hpitch : 0 < P.pitch := lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨d, _, rfl⟩
  cases d
  · simpa [dentCell] using
      (ofNat_pair_mem_square (x := 0) (y := codeH P η.south η.north
        (P.west u) ell.west) (n := P.pitch)).mpr
        ⟨hpitch, codeH_lt_pitch P η.south η.north (P.west u) ell.west⟩
  · simpa [dentCell] using
      (ofNat_pair_mem_square (x := P.pitch - 1) (y := P.handshake)
        (n := P.pitch)).mpr
        ⟨Nat.sub_lt hpitch (by decide), P.handshake_lt_pitch⟩
  · simpa [dentCell] using
      (ofNat_pair_mem_square (x := codeV P η.west η.east (P.south u) ell.south)
        (y := 0) (n := P.pitch)).mpr
        ⟨codeV_lt_pitch P η.west η.east (P.south u) ell.south, hpitch⟩
  · simpa [dentCell] using
      (ofNat_pair_mem_square (x := P.handshake) (y := P.pitch - 1)
        (n := P.pitch)).mpr
        ⟨P.handshake_lt_pitch, Nat.sub_lt hpitch (by decide)⟩

theorem dentCell_mem_body (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) (d : Side) :
    dentCell P η u ell d ∈ square P.pitch := by
  have hpitch : 0 < P.pitch := lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight
  cases d
  · simpa [dentCell] using
      (ofNat_pair_mem_square (x := 0) (y := codeH P η.south η.north
        (P.west u) ell.west) (n := P.pitch)).mpr
        ⟨hpitch, codeH_lt_pitch P η.south η.north (P.west u) ell.west⟩
  · simpa [dentCell] using
      (ofNat_pair_mem_square (x := P.pitch - 1) (y := P.handshake)
        (n := P.pitch)).mpr
        ⟨Nat.sub_lt hpitch (by decide), P.handshake_lt_pitch⟩
  · simpa [dentCell] using
      (ofNat_pair_mem_square (x := codeV P η.west η.east (P.south u) ell.south)
        (y := 0) (n := P.pitch)).mpr
        ⟨codeV_lt_pitch P η.west η.east (P.south u) ell.south, hpitch⟩
  · simpa [dentCell] using
      (ofNat_pair_mem_square (x := P.handshake) (y := P.pitch - 1)
        (n := P.pitch)).mpr
        ⟨P.handshake_lt_pitch, Nat.sub_lt hpitch (by decide)⟩

theorem tileCavity_bounds {P : RegisterParams} {u : Fin P.tileCount} {z : Cell}
    (hz : z ∈ tileCavity u) :
    16 ≤ z.1 ∧ z.1 ≤ (17 + 4 * (u : ℕ) : ℕ) ∧ (z.2 = 16 ∨ z.2 = 17) := by
  rw [tileCavity, cavity] at hz
  simp only [translate, Finset.mem_image] at hz
  rcases hz with ⟨p, hp, rfl⟩
  simp only [mem_plugL] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num [cavityOrigin] <;> omega

theorem dents_disjoint_cavity (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) :
    Disjoint (dents P η u ell) (tileCavity u) := by
  rw [Finset.disjoint_left]
  intro z hzD hzC
  rcases Finset.mem_image.mp hzD with ⟨d, _, hd⟩
  have hb := tileCavity_bounds hzC
  have hm := P.pitch_ge_tile_margin
  have hu := u.isLt
  cases d <;> simp [dentCell] at hd <;> subst z
  · omega
  · have : (17 + 4 * (u : ℕ) : ℕ) < P.pitch - 1 := by omega
    omega
  · omega
  · have hp := P.pitch_ge_sixty_eight
    omega

theorem bumps_disjoint_body (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) :
    Disjoint (bumps P η u ell) (square P.pitch) := by
  rw [Finset.disjoint_left]
  intro z hzB hzS
  rcases Finset.mem_image.mp hzB with ⟨d, _, hd⟩
  have hprod := Finset.mem_product.mp hzS
  have hx := mem_natInterval.mp hprod.1
  have hy := mem_natInterval.mp hprod.2
  rcases hx with ⟨x, hxlt, hxeq⟩
  rcases hy with ⟨y, hylt, hyeq⟩
  cases d <;> simp [bumpCell] at hd <;> subst z <;> norm_num at hxeq hyeq <;> omega

theorem bumpCell_not_mem_body (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) (d : Side) :
    bumpCell P η u ell d ∉ square P.pitch := by
  intro hz
  have hprod := Finset.mem_product.mp hz
  have hx := mem_natInterval.mp hprod.1
  have hy := mem_natInterval.mp hprod.2
  rcases hx with ⟨x, hxlt, hxeq⟩
  rcases hy with ⟨y, hylt, hyeq⟩
  cases d <;> simp [bumpCell] at hxeq hyeq <;> omega

theorem dentCell_not_mem_cavity (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) (d : Side) :
    dentCell P η u ell d ∉ tileCavity u := by
  intro hz
  have hb := tileCavity_bounds hz
  have hm := P.pitch_ge_tile_margin
  have hu := u.isLt
  have hp := P.pitch_ge_sixty_eight
  cases d <;> simp [dentCell] at hb <;> omega

/-- An exterior bump is present in the carrier exactly when its side is open. -/
theorem bumpCell_mem_carrier_iff (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) (d : Side) :
    bumpCell P η u ell d ∈ carrier P η u ell ↔ d ∈ activeSides η := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with hbody | hbump
    · exact (bumpCell_not_mem_body P η u ell d (Finset.mem_sdiff.mp hbody).1).elim
    · rcases Finset.mem_image.mp hbump with ⟨e, he, hed⟩
      have : e = d := bumpCell_injective P η u ell hed
      simpa [this] using he
  · intro hd
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨d, hd, rfl⟩))

/-- A body dent is absent from the carrier exactly when its side is open. -/
theorem dentCell_not_mem_carrier_iff (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) (d : Side) :
    dentCell P η u ell d ∉ carrier P η u ell ↔ d ∈ activeSides η := by
  constructor
  · intro habsent
    by_contra hactive
    apply habsent
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_sdiff.mpr
    refine ⟨dentCell_mem_body P η u ell d, ?_⟩
    intro hremoved
    rcases Finset.mem_union.mp hremoved with hdent | hcav
    · rcases Finset.mem_image.mp hdent with ⟨e, he, hed⟩
      have : e = d := dentCell_injective P η u ell hed
      exact hactive (this ▸ he)
    · exact dentCell_not_mem_cavity P η u ell d hcav
  · intro hactive hcarrier
    rcases Finset.mem_union.mp hcarrier with hbody | hbump
    · exact (Finset.mem_sdiff.mp hbody).2
        (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨d, hactive, rfl⟩)))
    · exact Finset.disjoint_left.mp (bumps_disjoint_body P η u ell)
        hbump (dentCell_mem_body P η u ell d)

private theorem bool_eq_of_true_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The four opening bits are determined by the unlabelled carrier support. -/
theorem carrier_eq_macroState
    (P : RegisterParams) (η η' : MacroState)
    (u v : Fin P.tileCount) (ell : AmpRecord P η) (ell' : AmpRecord P η')
    (hcar : carrier P η u ell = carrier P η' v ell') : η = η' := by
  have sideOpenEq : ∀ d : Side, η.isOpen d = true ↔ η'.isOpen d = true := by
    intro d
    cases d with
    | west =>
        have hp : bumpCell P η u ell .west = bumpCell P η' v ell' .west := rfl
        constructor
        · intro ho
          have hm := (bumpCell_mem_carrier_iff P η u ell .west).2
            (mem_activeSides η .west |>.2 ho)
          rw [hcar, hp] at hm
          exact mem_activeSides η' .west |>.1
            ((bumpCell_mem_carrier_iff P η' v ell' .west).1 hm)
        · intro ho
          have hm := (bumpCell_mem_carrier_iff P η' v ell' .west).2
            (mem_activeSides η' .west |>.2 ho)
          rw [← hcar, ← hp] at hm
          exact mem_activeSides η .west |>.1
            ((bumpCell_mem_carrier_iff P η u ell .west).1 hm)
    | south =>
        have hp : bumpCell P η u ell .south = bumpCell P η' v ell' .south := rfl
        constructor
        · intro ho
          have hm := (bumpCell_mem_carrier_iff P η u ell .south).2
            (mem_activeSides η .south |>.2 ho)
          rw [hcar, hp] at hm
          exact mem_activeSides η' .south |>.1
            ((bumpCell_mem_carrier_iff P η' v ell' .south).1 hm)
        · intro ho
          have hm := (bumpCell_mem_carrier_iff P η' v ell' .south).2
            (mem_activeSides η' .south |>.2 ho)
          rw [← hcar, ← hp] at hm
          exact mem_activeSides η .south |>.1
            ((bumpCell_mem_carrier_iff P η u ell .south).1 hm)
    | east =>
        have hp : dentCell P η u ell .east = dentCell P η' v ell' .east := rfl
        constructor
        · intro ho
          have hm := (dentCell_not_mem_carrier_iff P η u ell .east).2
            (mem_activeSides η .east |>.2 ho)
          have hm' : dentCell P η' v ell' .east ∉ carrier P η' v ell' := by
            simpa [hcar, hp] using hm
          exact mem_activeSides η' .east |>.1
            ((dentCell_not_mem_carrier_iff P η' v ell' .east).1 hm')
        · intro ho
          have hm := (dentCell_not_mem_carrier_iff P η' v ell' .east).2
            (mem_activeSides η' .east |>.2 ho)
          have hm' : dentCell P η u ell .east ∉ carrier P η u ell := by
            simpa [hcar, hp] using hm
          exact mem_activeSides η .east |>.1
            ((dentCell_not_mem_carrier_iff P η u ell .east).1 hm')
    | north =>
        have hp : dentCell P η u ell .north = dentCell P η' v ell' .north := rfl
        constructor
        · intro ho
          have hm := (dentCell_not_mem_carrier_iff P η u ell .north).2
            (mem_activeSides η .north |>.2 ho)
          have hm' : dentCell P η' v ell' .north ∉ carrier P η' v ell' := by
            simpa [hcar, hp] using hm
          exact mem_activeSides η' .north |>.1
            ((dentCell_not_mem_carrier_iff P η' v ell' .north).1 hm')
        · intro ho
          have hm := (dentCell_not_mem_carrier_iff P η' v ell' .north).2
            (mem_activeSides η' .north |>.2 ho)
          have hm' : dentCell P η u ell .north ∉ carrier P η u ell := by
            simpa [hcar, hp] using hm
          exact mem_activeSides η .north |>.1
            ((dentCell_not_mem_carrier_iff P η u ell .north).1 hm')
  apply MacroState.ext
  · exact bool_eq_of_true_iff (sideOpenEq .west)
  · exact bool_eq_of_true_iff (sideOpenEq .east)
  · exact bool_eq_of_true_iff (sideOpenEq .south)
  · exact bool_eq_of_true_iff (sideOpenEq .north)

/-- The small interior strip containing every identity cavity and no boundary
feature. -/
def identityWindow (P : RegisterParams) : Polyomino :=
  (Finset.Icc (16 : ℤ) (4 * P.tileCount + 13)).product (Finset.Icc (16 : ℤ) 17)

theorem identityWindow_subset_body (P : RegisterParams) :
    identityWindow P ⊆ square P.pitch := by
  intro z hz
  have hp := Finset.mem_product.mp hz
  have hx := Finset.mem_Icc.mp hp.1
  have hy := Finset.mem_Icc.mp hp.2
  have hm := P.pitch_ge_tile_margin
  have hxn : 0 ≤ z.1 := by omega
  have hyn : 0 ≤ z.2 := by omega
  obtain ⟨x, hxrep⟩ := Int.eq_ofNat_of_zero_le hxn
  obtain ⟨y, hyrep⟩ := Int.eq_ofNat_of_zero_le hyn
  have hzrep : z = ((x : ℤ), (y : ℤ)) := Prod.ext hxrep hyrep
  rw [hzrep, ofNat_pair_mem_square]
  rw [hzrep] at hx hy
  norm_num at hx hy
  omega

theorem tileCavity_subset_identityWindow (P : RegisterParams) (u : Fin P.tileCount) :
    tileCavity u ⊆ identityWindow P := by
  intro z hz
  have hb := tileCavity_bounds hz
  have hu := u.isLt
  refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ?_, Finset.mem_Icc.mpr ?_⟩
  · constructor <;> omega
  · rcases hb.2.2 with h | h <;> omega

theorem identityWindow_disjoint_dents (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) :
    Disjoint (identityWindow P) (dents P η u ell) := by
  rw [Finset.disjoint_left]
  intro z hzW hzD
  have hp := Finset.mem_product.mp hzW
  have hx := Finset.mem_Icc.mp hp.1
  have hy := Finset.mem_Icc.mp hp.2
  rcases Finset.mem_image.mp hzD with ⟨d, _, hd⟩
  have hm := P.pitch_ge_tile_margin
  have hM := P.tileCount_pos
  have hpitch := P.pitch_ge_sixty_eight
  cases d
  · simp [dentCell] at hd
    subst z
    norm_num at hx
  · simp [dentCell] at hd
    subst z
    norm_num at hx hy <;> omega
  · simp [dentCell] at hd
    subst z
    norm_num at hx hy <;> omega
  · simp [dentCell] at hd
    subst z
    norm_num at hx hy <;> omega

/-- Intersecting the missing body with the identity window recovers exactly the
tile-specific L-cavity. -/
theorem identityWindow_sdiff_carrier (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) :
    identityWindow P \ carrier P η u ell = tileCavity u := by
  ext z
  constructor
  · intro hz
    have hzW := (Finset.mem_sdiff.mp hz).1
    have hzNot := (Finset.mem_sdiff.mp hz).2
    have hzBody := identityWindow_subset_body P hzW
    have hzNoDent : z ∉ dents P η u ell := fun hd =>
      Finset.disjoint_left.mp (identityWindow_disjoint_dents P η u ell) hzW hd
    by_contra hzNoCav
    apply hzNot
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_sdiff.mpr ⟨hzBody, by simpa [hzNoDent, hzNoCav]⟩
  · intro hzC
    apply Finset.mem_sdiff.mpr
    refine ⟨tileCavity_subset_identityWindow P u hzC, ?_⟩
    intro hzCarrier
    rcases Finset.mem_union.mp hzCarrier with hzBody | hzBump
    · exact (Finset.mem_sdiff.mp hzBody).2 (Finset.mem_union.mpr (Or.inr hzC))
    · have hzBody' := tileCavity_subset_body P u hzC
      exact Finset.disjoint_left.mp (bumps_disjoint_body P η u ell) hzBump hzBody'

/-- The cavity register makes the Wang-tile identity recoverable from the
unlabelled carrier support. -/
theorem carrier_eq_tile
    (P : RegisterParams) (η η' : MacroState)
    (u v : Fin P.tileCount) (ell : AmpRecord P η) (ell' : AmpRecord P η')
    (hcar : carrier P η u ell = carrier P η' v ell') : u = v := by
  apply tileCavity_injective P
  rw [← identityWindow_sdiff_carrier P η u ell,
    ← identityWindow_sdiff_carrier P η' v ell', hcar]

theorem carrier_eq_bumps
    (P : RegisterParams) (η η' : MacroState)
    (u v : Fin P.tileCount) (ell : AmpRecord P η) (ell' : AmpRecord P η')
    (hcar : carrier P η u ell = carrier P η' v ell') :
    bumps P η u ell = bumps P η' v ell' := by
  ext z
  constructor
  · intro hz
    have hzNotBody : z ∉ square P.pitch := fun hzBody =>
      Finset.disjoint_left.mp (bumps_disjoint_body P η u ell) hz hzBody
    have hzCar : z ∈ carrier P η u ell := Finset.mem_union.mpr (Or.inr hz)
    rw [hcar] at hzCar
    rcases Finset.mem_union.mp hzCar with hbody | hbump
    · exact (hzNotBody (Finset.mem_sdiff.mp hbody).1).elim
    · exact hbump
  · intro hz
    have hzNotBody : z ∉ square P.pitch := fun hzBody =>
      Finset.disjoint_left.mp (bumps_disjoint_body P η' v ell') hz hzBody
    have hzCar : z ∈ carrier P η' v ell' := Finset.mem_union.mpr (Or.inr hz)
    rw [← hcar] at hzCar
    rcases Finset.mem_union.mp hzCar with hbody | hbump
    · exact (hzNotBody (Finset.mem_sdiff.mp hbody).1).elim
    · exact hbump

theorem carrier_eq_dents_of_tile_eq
    (P : RegisterParams) (η η' : MacroState)
    (u v : Fin P.tileCount) (ell : AmpRecord P η) (ell' : AmpRecord P η')
    (huv : u = v) (hcar : carrier P η u ell = carrier P η' v ell') :
    dents P η u ell = dents P η' v ell' := by
  subst v
  ext z
  constructor
  · intro hz
    have hzBody := dents_subset_body P η u ell hz
    have hzNoCav : z ∉ tileCavity u := fun hc =>
      Finset.disjoint_left.mp (dents_disjoint_cavity P η u ell) hz hc
    by_contra hzNot
    have hzOther : z ∈ carrier P η' u ell' := by
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_sdiff.mpr ⟨hzBody, by simpa [hzNot, hzNoCav]⟩
    rw [← hcar] at hzOther
    rcases Finset.mem_union.mp hzOther with hbody | hbump
    · exact (Finset.mem_sdiff.mp hbody).2
        (Finset.mem_union.mpr (Or.inl hz))
    · exact Finset.disjoint_left.mp (bumps_disjoint_body P η u ell) hbump hzBody
  · intro hz
    have hzBody := dents_subset_body P η' u ell' hz
    have hzNoCav : z ∉ tileCavity u := fun hc =>
      Finset.disjoint_left.mp (dents_disjoint_cavity P η' u ell') hz hc
    by_contra hzNot
    have hzOther : z ∈ carrier P η u ell := by
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_sdiff.mpr ⟨hzBody, by simpa [hzNot, hzNoCav]⟩
    rw [hcar] at hzOther
    rcases Finset.mem_union.mp hzOther with hbody | hbump
    · exact (Finset.mem_sdiff.mp hbody).2
        (Finset.mem_union.mpr (Or.inl hz))
    · exact Finset.disjoint_left.mp (bumps_disjoint_body P η' u ell') hbump hzBody

theorem removed_subset_body (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) :
    dents P η u ell ∪ tileCavity u ⊆ square P.pitch := by
  exact Finset.union_subset (dents_subset_body P η u ell) (tileCavity_subset_body P u)

theorem body_subset_extendedBox (P : RegisterParams) : square P.pitch ⊆ extendedBox P := by
  intro z hz
  have hp := Finset.mem_product.mp hz
  rcases mem_natInterval.mp hp.1 with ⟨x, hx, hxeq⟩
  rcases mem_natInterval.mp hp.2 with ⟨y, hy, hyeq⟩
  refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ?_, Finset.mem_Icc.mpr ?_⟩
  · constructor <;> omega
  · constructor <;> omega

theorem bumps_subset_extendedBox (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) :
    bumps P η u ell ⊆ extendedBox P := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨d, _, rfl⟩
  have hh0 : 0 ≤ P.handshake := by omega
  have hhp := P.handshake_lt_pitch
  have hpitch : 0 < P.pitch := lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight
  have hH0 := (codeH_bounds P η.south η.north (P.east u) ell.east).1
  have hHp := codeH_lt_pitch P η.south η.north (P.east u) ell.east
  have hV0 := (codeV_bounds P η.west η.east (P.north u) ell.north).1
  have hVp := codeV_lt_pitch P η.west η.east (P.north u) ell.north
  cases d <;> simp [bumpCell, extendedBox] <;> omega

theorem carrier_subset_extendedBox (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) :
    carrier P η u ell ⊆ extendedBox P := by
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · exact body_subset_extendedBox P (Finset.mem_sdiff.mp hz).1
  · exact bumps_subset_extendedBox P η u ell hz

/-- Widely separated macro-origins have disjoint carrier translates. -/
theorem translated_carriers_disjoint_of_x_gap
    (P : RegisterParams)
    (η η' : MacroState) (u v : Fin P.tileCount)
    (ell : AmpRecord P η) (ell' : AmpRecord P η')
    (a b : Cell) (hgap : a.1 + P.pitch + 1 < b.1) :
    Disjoint (translate (carrier P η u ell) a)
      (translate (carrier P η' v ell') b) := by
  rw [Finset.disjoint_left]
  intro z hza hzb
  have ha := mem_translate.mp hza
  have hb := mem_translate.mp hzb
  have haBox := carrier_subset_extendedBox P η u ell ha
  have hbBox := carrier_subset_extendedBox P η' v ell' hb
  have hax := (Finset.mem_product.mp haBox).1
  have hbx := (Finset.mem_product.mp hbBox).1
  simp only [extendedBox, Finset.mem_Icc] at hax hbx
  omega

/-- Generic finite-set accounting behind the carrier area calculation. -/
theorem card_remove_and_replace {body removed added : Polyomino}
    (hremoved : removed ⊆ body) (hadded : Disjoint added body) :
    ((body \ removed) ∪ added).card = body.card - removed.card + added.card := by
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hremoved]
  · exact hadded.symm.mono_left Finset.sdiff_subset

/-- Exact area follows once the four coordinate-disjointness obligations are
discharged.  This theorem is used by the later explicit feature audit. -/
theorem carrier_area_from_feature_account
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (ell : AmpRecord P η)
    (hremoved : dents P η u ell ∪ tileCavity u ⊆ square P.pitch)
    (hparts : Disjoint (dents P η u ell) (tileCavity u))
    (houtside : Disjoint (bumps P η u ell) (square P.pitch))
    (hbalance : (dents P η u ell).card = (bumps P η u ell).card) :
    (carrier P η u ell).card = P.pitch ^ 2 - 3 := by
  unfold carrier
  rw [card_remove_and_replace hremoved houtside]
  rw [Finset.card_union_of_disjoint hparts, card_tileCavity, card_square, hbalance]
  have hd : (dents P η u ell).card + 3 ≤ P.pitch ^ 2 := by
    simpa [Finset.card_union_of_disjoint hparts] using
      Finset.card_le_card hremoved
  omega

/-- Every explicitly defined carrier has the advertised area `P_s² - 3`. -/
theorem carrier_area (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) :
    (carrier P η u ell).card = P.pitch ^ 2 - 3 :=
  carrier_area_from_feature_account P η u ell
    (removed_subset_body P η u ell)
    (dents_disjoint_cavity P η u ell)
    (bumps_disjoint_body P η u ell)
    (feature_card_balance P η u ell)

theorem origin_mem_carrier (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) :
    (0, 0) ∈ carrier P η u ell := by
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_sdiff.mpr
  constructor
  · simpa using (ofNat_pair_mem_square (x := 0) (y := 0) (n := P.pitch)).mpr
      ⟨lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight,
       lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight⟩
  · intro hr
    rcases Finset.mem_union.mp hr with hd | hc
    · rcases Finset.mem_image.mp hd with ⟨d, _, h⟩
      have hH := (codeH_bounds P η.south η.north (P.west u) ell.west).1
      have hV := (codeV_bounds P η.west η.east (P.south u) ell.south).1
      have hp := P.pitch_ge_sixty_eight
      have hh := P.handshake_eq
      cases d <;> simp [dentCell] at h <;> omega
    · have hb := tileCavity_bounds hc
      omega

/-- `(0,0)` is the unique minimizer of `x+y` in every aligned carrier. -/
theorem carrier_sum_nonneg_eq_zero
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (ell : AmpRecord P η) {z : Cell} (hz : z ∈ carrier P η u ell) :
    0 ≤ z.1 + z.2 ∧ (z.1 + z.2 = 0 → z = (0, 0)) := by
  rcases Finset.mem_union.mp hz with hb | hbump
  · have hs := (Finset.mem_sdiff.mp hb).1
    have hp := Finset.mem_product.mp hs
    rcases mem_natInterval.mp hp.1 with ⟨x, _, hx⟩
    rcases mem_natInterval.mp hp.2 with ⟨y, _, hy⟩
    constructor
    · omega
    · intro hzero
      apply Prod.ext <;> simp
      · omega
      · omega
  · rcases Finset.mem_image.mp hbump with ⟨d, _, rfl⟩
    have hp := P.pitch_ge_sixty_eight
    have hh := P.handshake_eq
    have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
    have hH := (codeH_bounds P η.south η.north (P.east u) ell.east).1
    have hV := (codeV_bounds P η.west η.east (P.north u) ell.north).1
    cases d <;> simp [bumpCell] <;> omega

/-- Translation of a carrier has its unique `x+y` minimizer at the translation
vector.  This removes any hidden quotient by translation. -/
theorem translated_carrier_origin
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (ell : AmpRecord P η) (t : Cell) {z : Cell}
    (hz : z ∈ translate (carrier P η u ell) t) :
    t.1 + t.2 ≤ z.1 + z.2 ∧
      (t.1 + t.2 = z.1 + z.2 → z = t) := by
  have hc := mem_translate.mp hz
  have hm := carrier_sum_nonneg_eq_zero P η u ell hc
  constructor
  · omega
  · intro hsum
    have hzero : (z.1 - t.1) + (z.2 - t.2) = 0 := by omega
    have hcell := hm.2 hzero
    apply Prod.ext
    · have := congrArg Prod.fst hcell
      dsimp at this
      omega
    · have := congrArg Prod.snd hcell
      dsimp at this
      omega

theorem inner_row_mem_carrier
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (ell : AmpRecord P η) {x y : ℕ} (hx : x < P.pitch)
    (hy : y = 1 ∨ y = 2) : ((x : ℤ), (y : ℤ)) ∈ carrier P η u ell := by
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_sdiff.mpr
  constructor
  · have hp := P.pitch_ge_sixty_eight
    exact ofNat_pair_mem_square.mpr ⟨hx, by
      rcases hy with rfl | rfl <;> omega⟩
  · intro hr
    rcases Finset.mem_union.mp hr with hd | hc
    · rcases Finset.mem_image.mp hd with ⟨d, _, heq⟩
      have hp := P.pitch_ge_sixty_eight
      have hh := P.handshake_eq
      have hH := (codeH_bounds P η.south η.north (P.west u) ell.west).1
      have hV := (codeV_bounds P η.west η.east (P.south u) ell.south).1
      rcases hy with rfl | rfl <;> cases d <;> simp [dentCell] at heq <;> omega
    · have hb := tileCavity_bounds hc
      rcases hy with rfl | rfl <;> norm_num at hb <;> omega

theorem inner_col_mem_carrier
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (ell : AmpRecord P η) {x y : ℕ} (hy : y < P.pitch)
    (hx : x = 1 ∨ x = 2) : ((x : ℤ), (y : ℤ)) ∈ carrier P η u ell := by
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_sdiff.mpr
  constructor
  · have hp := P.pitch_ge_sixty_eight
    exact ofNat_pair_mem_square.mpr ⟨by rcases hx with rfl | rfl <;> omega, hy⟩
  · intro hr
    rcases Finset.mem_union.mp hr with hd | hc
    · rcases Finset.mem_image.mp hd with ⟨d, _, heq⟩
      have hp := P.pitch_ge_sixty_eight
      have hh := P.handshake_eq
      have hH := (codeH_bounds P η.south η.north (P.west u) ell.west).1
      have hV := (codeV_bounds P η.west η.east (P.south u) ell.south).1
      rcases hx with rfl | rfl <;> cases d <;> simp [dentCell] at heq <;> omega
    · have hb := tileCavity_bounds hc
      rcases hx with rfl | rfl <;> norm_num at hb <;> omega

def carrierSpine (P : RegisterParams) : Polyomino :=
  (natInterval P.pitch).product {(1 : ℤ)} ∪
    ({(1 : ℤ)} : Finset ℤ).product (natInterval P.pitch)

theorem carrierSpine_subset (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) :
    carrierSpine P ⊆ carrier P η u ell := by
  intro z hz
  rcases Finset.mem_union.mp hz with hr | hc
  · have hp := Finset.mem_product.mp hr
    rcases mem_natInterval.mp hp.1 with ⟨x, hx, hxeq⟩
    have hy : z.2 = 1 := by simpa using hp.2
    have hzEq : z = ((x : ℤ), (1 : ℤ)) := Prod.ext hxeq.symm hy
    rw [hzEq]
    exact inner_row_mem_carrier P η u ell hx (Or.inl rfl)
  · have hp := Finset.mem_product.mp hc
    have hx : z.1 = 1 := by simpa using hp.1
    rcases mem_natInterval.mp hp.2 with ⟨y, hy, hyeq⟩
    have hzEq : z = ((1 : ℤ), (y : ℤ)) := Prod.ext hx hyeq.symm
    rw [hzEq]
    exact inner_col_mem_carrier P η u ell hy (Or.inl rfl)

theorem carrierSpine_fourConnected (P : RegisterParams) : FourConnected (carrierSpine P) := by
  have hpitch : 1 < P.pitch := lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight
  have hhub : ((1 : ℤ), (1 : ℤ)) ∈ carrierSpine P := by
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_product.mpr
      ⟨mem_natInterval.mpr ⟨1, hpitch, rfl⟩, by simp⟩
  refine ⟨⟨_, hhub⟩, ?_⟩
  intro a ha b hb
  let toHub : ∀ ⦃z⦄, z ∈ carrierSpine P →
      Walk4In (carrierSpine P) z ((1 : ℤ), (1 : ℤ)) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hr | hc
    · have hprod := Finset.mem_product.mp hr
      rcases mem_natInterval.mp hprod.1 with ⟨x, hx, hxeq⟩
      have hyeq : z.2 = 1 := by simpa using hprod.2
      have hzEq : z = ((x : ℤ), (1 : ℤ)) := Prod.ext hxeq.symm hyeq
      rw [hzEq]
      by_cases hxl : x ≤ 1
      · have hxcase : x = 0 ∨ x = 1 := by omega
        rcases hxcase with rfl | rfl
        · exact walk4_right 0 1 1 (by
            intro i hi
            apply Finset.mem_union.mpr
            left
            exact Finset.mem_product.mpr
              ⟨mem_natInterval.mpr ⟨i, by omega, by simp⟩, by simp⟩)
        · exact Walk4In.nil hhub
      · have hx1 : 1 ≤ x := by omega
        have w := walk4_left (P := carrierSpine P) 1 1 (x - 1) (by
          intro i hi
          apply Finset.mem_union.mpr
          left
          refine Finset.mem_product.mpr ⟨mem_natInterval.mpr ?_, by simp⟩
          exact ⟨1 + i, by omega, by push_cast; ring⟩)
        convert w using 1 <;> ext <;> simp <;> push_cast <;> omega
    · have hprod := Finset.mem_product.mp hc
      have hxeq : z.1 = 1 := by simpa using hprod.1
      rcases mem_natInterval.mp hprod.2 with ⟨y, hy, hyeq⟩
      have hzEq : z = ((1 : ℤ), (y : ℤ)) := Prod.ext hxeq hyeq.symm
      rw [hzEq]
      by_cases hyl : y ≤ 1
      · have hycase : y = 0 ∨ y = 1 := by omega
        rcases hycase with rfl | rfl
        · exact walk4_up 1 0 1 (by
            intro i hi
            apply Finset.mem_union.mpr
            right
            exact Finset.mem_product.mpr
              ⟨by simp, mem_natInterval.mpr ⟨i, by omega, by simp⟩⟩)
        · exact Walk4In.nil hhub
      · have hy1 : 1 ≤ y := by omega
        have w := walk4_down (P := carrierSpine P) 1 1 (y - 1) (by
          intro i hi
          apply Finset.mem_union.mpr
          right
          refine Finset.mem_product.mpr ⟨by simp, mem_natInterval.mpr ?_⟩
          exact ⟨1 + i, by omega, by push_cast; ring⟩)
        convert w using 1 <;> ext <;> simp <;> push_cast <;> omega
  exact (toHub ha).trans (toHub hb).symm

theorem interior_mem_carrier_of_not_cavity
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (ell : AmpRecord P η) {x y : ℕ}
    (hx0 : 1 ≤ x) (hxp : x + 1 < P.pitch)
    (hy0 : 1 ≤ y) (hyp : y + 1 < P.pitch)
    (hcav : ((x : ℤ), (y : ℤ)) ∉ tileCavity u) :
    ((x : ℤ), (y : ℤ)) ∈ carrier P η u ell := by
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_sdiff.mpr
  constructor
  · exact ofNat_pair_mem_square.mpr ⟨by omega, by omega⟩
  · intro hr
    rcases Finset.mem_union.mp hr with hd | hc
    · rcases Finset.mem_image.mp hd with ⟨d, _, heq⟩
      have hp := P.pitch_ge_sixty_eight
      cases d <;> simp [dentCell] at heq <;> omega
    · exact hcav hc

/-- Every strictly interior carrier cell reaches the intact row/column spine. -/
theorem interior_route_to_spine
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (ell : AmpRecord P η) {x y : ℕ}
    (hx0 : 1 ≤ x) (hxp : x + 1 < P.pitch)
    (hy0 : 1 ≤ y) (hyp : y + 1 < P.pitch)
    (hxy : ((x : ℤ), (y : ℤ)) ∈ carrier P η u ell) :
    ∃ s ∈ carrierSpine P,
      Walk4In (carrier P η u ell) ((x : ℤ), (y : ℤ)) s := by
  let qx : ℕ := 16 + 4 * (u : ℕ)
  have hnotCav : ((x : ℤ), (y : ℤ)) ∉ tileCavity u := by
    intro hc
    have hr := Finset.mem_union.mp hxy
    rcases hr with hb | hb
    · exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_union.mpr (Or.inr hc))
    · exact Finset.disjoint_left.mp (bumps_disjoint_body P η u ell) hb
        (tileCavity_subset_body P u hc)
  have hpitch : 68 ≤ P.pitch := P.pitch_ge_sixty_eight
  have hu := u.isLt
  by_cases hy16 : y = 16
  · subst y
    by_cases hxq : x ≤ qx
    · have w := walk4_left (P := carrier P η u ell) 1 16 (x - 1) (by
        intro i hi
        have hix : 1 + i ≤ x := by omega
        have hm := interior_mem_carrier_of_not_cavity P η u ell
          (x := 1 + i) (y := 16) (by omega) (by omega) (by omega) (by omega) (by
            intro hc
            simp [tileCavity, cavity, translate, plugL, cavityOrigin, qx] at hc
            omega)
        convert hm using 1 <;> norm_num)
      have hs : ((1 : ℤ), (16 : ℤ)) ∈ carrierSpine P := by
        apply Finset.mem_union.mpr
        right
        exact Finset.mem_product.mpr ⟨by simp,
          mem_natInterval.mpr ⟨16, by omega, rfl⟩⟩
      refine ⟨(1, 16), hs, ?_⟩
      convert w using 1 <;> ext <;> norm_num <;> push_cast <;> omega
    · have hxright : qx + 2 ≤ x := by
        have hneq : x ≠ qx + 1 := by
          intro heq
          apply hnotCav
          rw [tileCavity, cavity]
          apply Finset.mem_image.mpr
          refine ⟨(1, 0), by simp [plugL], ?_⟩
          apply Prod.ext <;> norm_num [cavityOrigin, qx] <;> omega
        omega
      have w := walk4_down (P := carrier P η u ell) x 1 15 (by
        intro i hi
        have hm := interior_mem_carrier_of_not_cavity P η u ell
          (x := x) (y := 1 + i) hx0 hxp (by omega) (by omega) (by
            intro hc
            simp [tileCavity, cavity, translate, plugL, cavityOrigin, qx] at hc
            omega)
        simpa only [Nat.cast_add, Nat.cast_one] using hm)
      have hs : ((x : ℤ), (1 : ℤ)) ∈ carrierSpine P := by
        apply Finset.mem_union.mpr
        left
        exact Finset.mem_product.mpr ⟨mem_natInterval.mpr ⟨x, by omega, rfl⟩, by simp⟩
      exact ⟨(x, 1), hs, by convert w using 1 <;> ext <;> norm_num⟩
  · by_cases hy17 : y = 17
    · subst y
      have hxNotQ : x ≠ qx ∧ x ≠ qx + 1 := by
        constructor
        · intro heq
          apply hnotCav
          rw [tileCavity, cavity]
          apply Finset.mem_image.mpr
          refine ⟨(0, 1), by simp [plugL], ?_⟩
          apply Prod.ext <;> norm_num [cavityOrigin, qx] <;> omega
        · intro heq
          apply hnotCav
          rw [tileCavity, cavity]
          apply Finset.mem_image.mpr
          refine ⟨(1, 1), by simp [plugL], ?_⟩
          apply Prod.ext <;> norm_num [cavityOrigin, qx] <;> omega
      have w := walk4_down (P := carrier P η u ell) x 1 16 (by
        intro i hi
        have hm := interior_mem_carrier_of_not_cavity P η u ell
          (x := x) (y := 1 + i) hx0 hxp (by omega) (by omega) (by
            intro hc
            simp [tileCavity, cavity, translate, plugL, cavityOrigin, qx] at hc
            omega)
        simpa only [Nat.cast_add, Nat.cast_one] using hm)
      have hs : ((x : ℤ), (1 : ℤ)) ∈ carrierSpine P := by
        apply Finset.mem_union.mpr
        left
        exact Finset.mem_product.mpr ⟨mem_natInterval.mpr ⟨x, by omega, rfl⟩, by simp⟩
      exact ⟨(x, 1), hs, by convert w using 1 <;> ext <;> norm_num⟩
    · have w := walk4_left (P := carrier P η u ell) 1 y (x - 1) (by
        intro i hi
        have hix : 1 + i ≤ x := by omega
        have hm := interior_mem_carrier_of_not_cavity P η u ell
          (x := 1 + i) (y := y) (by omega) (by omega) hy0 hyp (by
            intro hc
            simp [tileCavity, cavity, translate, plugL, cavityOrigin] at hc
            omega)
        convert hm using 1 <;> norm_num)
      have hs : ((1 : ℤ), (y : ℤ)) ∈ carrierSpine P := by
        apply Finset.mem_union.mpr
        right
        exact Finset.mem_product.mpr ⟨by simp,
          mem_natInterval.mpr ⟨y, by omega, rfl⟩⟩
      refine ⟨(1, y), hs, ?_⟩
      convert w using 1 <;> ext <;> norm_num <;> push_cast <;> omega

/-- The column immediately inside the east boundary is completely intact. -/
theorem east_inner_column_mem_carrier
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (ell : AmpRecord P η) {y : ℕ} (hy : y < P.pitch) :
    (((P.pitch - 2 : ℕ) : ℤ), (y : ℤ)) ∈ carrier P η u ell := by
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_sdiff.mpr
  constructor
  · exact ofNat_pair_mem_square.mpr ⟨by
      have := P.pitch_ge_sixty_eight; omega, hy⟩
  · intro hr
    rcases Finset.mem_union.mp hr with hd | hc
    · rcases Finset.mem_image.mp hd with ⟨d, _, heq⟩
      have hp := P.pitch_ge_sixty_eight
      have hh := P.handshake_eq
      have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
      have hH := codeH_bounds P η.south η.north (P.west u) ell.west
      have hV := codeV_bounds P η.west η.east (P.south u) ell.south
      cases d <;> simp [dentCell] at heq <;> omega
    · have hb := tileCavity_bounds hc
      have hm := P.pitch_ge_tile_margin
      have hu := u.isLt
      omega

/-- The row immediately inside the north boundary is completely intact. -/
theorem north_inner_row_mem_carrier
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (ell : AmpRecord P η) {x : ℕ} (hx : x < P.pitch) :
    ((x : ℤ), ((P.pitch - 2 : ℕ) : ℤ)) ∈ carrier P η u ell := by
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_sdiff.mpr
  constructor
  · exact ofNat_pair_mem_square.mpr ⟨hx, by
      have := P.pitch_ge_sixty_eight; omega⟩
  · intro hr
    rcases Finset.mem_union.mp hr with hd | hc
    · rcases Finset.mem_image.mp hd with ⟨d, _, heq⟩
      have hp := P.pitch_ge_sixty_eight
      have hh := P.handshake_eq
      have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
      have hH := codeH_bounds P η.south η.north (P.west u) ell.west
      have hV := codeV_bounds P η.west η.east (P.south u) ell.south
      cases d <;> simp [dentCell] at heq <;> omega
    · have hb := tileCavity_bounds hc
      have hm := P.pitch_ge_tile_margin
      have hu := u.isLt
      omega

/-- Every body cell of a carrier reaches the intact spine. -/
theorem carrier_body_route_to_spine
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (ell : AmpRecord P η) {z : Cell}
    (hz : z ∈ square P.pitch \ (dents P η u ell ∪ tileCavity u)) :
    ∃ s ∈ carrierSpine P, Walk4In (carrier P η u ell) z s := by
  have hsquare := (Finset.mem_sdiff.mp hz).1
  have hcarr : z ∈ carrier P η u ell := Finset.mem_union.mpr (Or.inl hz)
  have hp := Finset.mem_product.mp hsquare
  rcases mem_natInterval.mp hp.1 with ⟨x, hx, hxeq⟩
  rcases mem_natInterval.mp hp.2 with ⟨y, hy, hyeq⟩
  have hzEq : z = ((x : ℤ), (y : ℤ)) := Prod.ext hxeq.symm hyeq.symm
  subst z
  by_cases hx0 : x = 0
  · subst x
    have hs : ((1 : ℤ), (y : ℤ)) ∈ carrierSpine P := by
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_product.mpr ⟨by simp, mem_natInterval.mpr ⟨y, hy, rfl⟩⟩
    have hnext := inner_col_mem_carrier P η u ell hy (Or.inl rfl)
    refine ⟨(1, y), hs, ?_⟩
    exact Walk4In.cons hcarr (by left; rfl) (.nil hnext)
  · by_cases hxE : x = P.pitch - 1
    · subst x
      have hnext := east_inner_column_mem_carrier P η u ell hy
      have hadj : Adj4 (((P.pitch - 1 : ℕ) : ℤ), (y : ℤ))
          (((P.pitch - 2 : ℕ) : ℤ), (y : ℤ)) := by
        right; left
        apply Prod.ext
        · push_cast
          have := P.pitch_ge_sixty_eight
          omega
        · rfl
      by_cases hy0 : y = 0
      · subst y
        have hsp := inner_row_mem_carrier P η u ell
          (x := P.pitch - 2) (y := 1) (by omega) (Or.inl rfl)
        have hs : (((P.pitch - 2 : ℕ) : ℤ), (1 : ℤ)) ∈ carrierSpine P := by
          apply Finset.mem_union.mpr
          left
          exact Finset.mem_product.mpr
            ⟨mem_natInterval.mpr ⟨P.pitch - 2, by omega, rfl⟩, by simp⟩
        refine ⟨_, hs, Walk4In.cons hcarr hadj ?_⟩
        exact Walk4In.cons hnext (by right; right; left; rfl) (.nil hsp)
      · by_cases hyE : y = P.pitch - 1
        · subst y
          have hpitch := P.pitch_ge_sixty_eight
          have hdown : (((P.pitch - 2 : ℕ) : ℤ), ((P.pitch - 2 : ℕ) : ℤ)) ∈
              carrier P η u ell := east_inner_column_mem_carrier P η u ell (by omega)
          have route := interior_route_to_spine P η u ell
            (x := P.pitch - 2) (y := P.pitch - 2)
            (by omega) (by omega) (by omega) (by omega) hdown
          rcases route with ⟨s, hs, w⟩
          have hdownAdj : Adj4
              (((P.pitch - 2 : ℕ) : ℤ), ((P.pitch - 1 : ℕ) : ℤ))
              (((P.pitch - 2 : ℕ) : ℤ), ((P.pitch - 2 : ℕ) : ℤ)) := by
            right; right; right
            apply Prod.ext
            · rfl
            · push_cast
              have := P.pitch_ge_sixty_eight
              omega
          refine ⟨s, hs, Walk4In.cons hcarr hadj ?_⟩
          exact Walk4In.cons hnext hdownAdj w
        · have hy0' : 1 ≤ y := by omega
          have hyE' : y + 1 < P.pitch := by omega
          have route := interior_route_to_spine P η u ell
            (x := P.pitch - 2) (y := y)
            (by omega) (by omega) hy0' hyE' hnext
          rcases route with ⟨s, hs, w⟩
          exact ⟨s, hs, Walk4In.cons hcarr hadj w⟩
    · by_cases hy0 : y = 0
      · subst y
        have hnext := inner_row_mem_carrier P η u ell hx (Or.inl rfl)
        have hs : ((x : ℤ), (1 : ℤ)) ∈ carrierSpine P := by
          apply Finset.mem_union.mpr
          left
          exact Finset.mem_product.mpr ⟨mem_natInterval.mpr ⟨x, hx, rfl⟩, by simp⟩
        exact ⟨_, hs, Walk4In.cons hcarr (by right; right; left; rfl) (.nil hnext)⟩
      · by_cases hyE : y = P.pitch - 1
        · subst y
          have hxI : 1 ≤ x := by omega
          have hxIp : x + 1 < P.pitch := by omega
          have hdown : ((x : ℤ), ((P.pitch - 2 : ℕ) : ℤ)) ∈ carrier P η u ell := by
            apply interior_mem_carrier_of_not_cavity P η u ell hxI hxIp (by omega) (by omega)
            intro hc
            have hb := tileCavity_bounds hc
            have hm := P.pitch_ge_tile_margin
            omega
          rcases interior_route_to_spine P η u ell hxI hxIp (by omega) (by omega) hdown with
            ⟨s, hs, w⟩
          have hadj : Adj4 ((x : ℤ), ((P.pitch - 1 : ℕ) : ℤ))
              ((x : ℤ), ((P.pitch - 2 : ℕ) : ℤ)) := by
            right; right; right
            apply Prod.ext
            · rfl
            · push_cast
              have := P.pitch_ge_sixty_eight
              omega
          exact ⟨s, hs, Walk4In.cons hcarr hadj w⟩
        · exact interior_route_to_spine P η u ell (by omega) (by omega)
            (by omega) (by omega) hcarr
/- Superseded long east-detour proof (the direct safe-column route below is
shorter and avoids an unnecessary endpoint conversion).
    · have hxright : qx + 2 ≤ x := by
        have hneq : x ≠ qx + 1 := by
          intro heq
          apply hnotCav
          rw [tileCavity, cavity]
          apply Finset.mem_image.mpr
          refine ⟨(1, 0), by simp [plugL], ?_⟩
          apply Prod.ext <;> norm_num [cavityOrigin, qx] <;> omega
        omega
      let stop := P.pitch - 2
      have hxstop : x ≤ stop := by dsimp [stop]; omega
      have w₁ := walk4_right (P := carrier P η u ell) x 16 (stop - x) (by
        intro i hi
        have hxi : x + i ≤ stop := by omega
        have hm := interior_mem_carrier_of_not_cavity P η u ell
          (x := x + i) (y := 16) (by omega) (by dsimp [stop] at hxi ⊢; omega)
          (by omega) (by omega) (by
            intro hc
            simp [tileCavity, cavity, translate, plugL, cavityOrigin, qx] at hc
            omega)
        convert hm using 1 <;> norm_num)
      have w₂ := walk4_down (P := carrier P η u ell) stop 1 15 (by
        intro i hi
        have hm := interior_mem_carrier_of_not_cavity P η u ell
          (x := stop) (y := 1 + i) (by dsimp [stop]; omega)
          (by dsimp [stop]; omega) (by omega) (by omega) (by
            intro hc
            simp [tileCavity, cavity, translate, plugL, cavityOrigin, stop, qx] at hc
            omega)
        simpa only [Nat.cast_add, Nat.cast_one] using hm)
      have hs : ((stop : ℤ), (1 : ℤ)) ∈ carrierSpine P := by
        apply Finset.mem_union.mpr
        left
        exact Finset.mem_product.mpr
          ⟨mem_natInterval.mpr ⟨stop, by dsimp [stop]; omega, rfl⟩, by simp⟩
      refine ⟨(stop, 1), hs, ?_⟩
      have w₂' : Walk4In (carrier P η u ell)
          ((x + (stop - x) : ℕ), (16 : ℕ)) ((stop : ℕ), (1 : ℕ)) := by
        convert w₂ using 1 <;> ext <;> norm_num <;> push_cast <;> dsimp [stop] <;> omega
      have w := w₁.trans w₂'
      convert w using 1 <;> ext <;> norm_num <;> push_cast <;> dsimp [stop] <;> omega
  · by_cases hy17 : y = 17
    · subst y
      by_cases hxq : x ≤ qx
      · have hxstrict : x < qx := by
          by_contra hn
          have : x = qx := by omega
          apply hnotCav
          rw [tileCavity, cavity]
          apply Finset.mem_image.mpr
          refine ⟨(0, 1), by simp [plugL], ?_⟩
          apply Prod.ext <;> norm_num [cavityOrigin, qx] <;> omega
        have w := walk4_left (P := carrier P η u ell) 1 17 (x - 1) (by
          intro i hi
          have hix : 1 + i ≤ x := by omega
          have hm := interior_mem_carrier_of_not_cavity P η u ell
            (x := 1 + i) (y := 17) (by omega) (by omega) (by omega) (by omega) (by
              intro hc
              simp [tileCavity, cavity, translate, plugL, cavityOrigin, qx] at hc
              omega)
          convert hm using 1 <;> norm_num)
        have hs : ((1 : ℤ), (17 : ℤ)) ∈ carrierSpine P := by
          apply Finset.mem_union.mpr
          right
          exact Finset.mem_product.mpr ⟨by simp,
            mem_natInterval.mpr ⟨17, by omega, rfl⟩⟩
        refine ⟨(1, 17), hs, ?_⟩
        convert w using 1 <;> ext <;> norm_num <;> push_cast <;> omega
      · have hxright : qx + 2 ≤ x := by
          have hneq : x ≠ qx + 1 := by
            intro heq
            apply hnotCav
            rw [tileCavity, cavity]
            apply Finset.mem_image.mpr
            refine ⟨(1, 1), by simp [plugL], ?_⟩
            apply Prod.ext <;> norm_num [cavityOrigin, qx] <;> omega
          omega
        let stop := P.pitch - 2
        have w₁ := walk4_right (P := carrier P η u ell) x 17 (stop - x) (by
          intro i hi
          have hxi : x + i ≤ stop := by omega
          have hm := interior_mem_carrier_of_not_cavity P η u ell
            (x := x + i) (y := 17) (by omega) (by dsimp [stop] at hxi ⊢; omega)
            (by omega) (by omega) (by
              intro hc
              simp [tileCavity, cavity, translate, plugL, cavityOrigin, qx] at hc
              omega)
          convert hm using 1 <;> norm_num)
        have w₂ := walk4_down (P := carrier P η u ell) stop 1 16 (by
          intro i hi
          have hm := interior_mem_carrier_of_not_cavity P η u ell
            (x := stop) (y := 1 + i) (by dsimp [stop]; omega)
            (by dsimp [stop]; omega) (by omega) (by omega) (by
              intro hc
              simp [tileCavity, cavity, translate, plugL, cavityOrigin, stop, qx] at hc
              omega)
          simpa only [Nat.cast_add, Nat.cast_one] using hm)
        have hs : ((stop : ℤ), (1 : ℤ)) ∈ carrierSpine P := by
          apply Finset.mem_union.mpr
          left
          exact Finset.mem_product.mpr
            ⟨mem_natInterval.mpr ⟨stop, by dsimp [stop]; omega, rfl⟩, by simp⟩
        refine ⟨(stop, 1), hs, ?_⟩
        have w₂' : Walk4In (carrier P η u ell)
            ((x + (stop - x) : ℕ), (17 : ℕ)) ((stop : ℕ), (1 : ℕ)) := by
          convert w₂ using 1 <;> ext <;> norm_num <;> push_cast <;> dsimp [stop] <;> omega
        have w := w₁.trans w₂'
        convert w using 1 <;> ext <;> norm_num <;> push_cast <;> dsimp [stop] <;> omega
    · have w := walk4_left (P := carrier P η u ell) 1 y (x - 1) (by
        intro i hi
        have hix : 1 + i ≤ x := by omega
        have hm := interior_mem_carrier_of_not_cavity P η u ell
          (x := 1 + i) (y := y) (by omega) (by omega) (by omega) (by omega) (by
            intro hc
            simp [tileCavity, cavity, translate, plugL, cavityOrigin] at hc
            omega)
        simpa only [Nat.cast_add, Nat.cast_one] using hm)
      have hs : ((1 : ℤ), (y : ℤ)) ∈ carrierSpine P := by
        apply Finset.mem_union.mpr
        right
        exact Finset.mem_product.mpr ⟨by simp,
          mem_natInterval.mpr ⟨y, by omega, rfl⟩⟩
      refine ⟨(1, y), hs, ?_⟩
      convert w using 1 <;> ext <;> norm_num <;> push_cast <;> omega
-/

private theorem carrier_not_at_forbidden_corner
    (P : RegisterParams) (η : MacroState) (u : Fin P.tileCount)
    (ell : AmpRecord P η) {z : Cell}
    (hshape : z = (-1, -1) ∨ z = ((P.pitch : ℤ), (P.pitch : ℤ)) ∨
      z = ((P.pitch : ℤ), (P.pitch : ℤ) - 1) ∨
      z = ((P.pitch : ℤ) - 1, (P.pitch : ℤ))) :
    z ∉ carrier P η u ell := by
  intro hz
  rcases Finset.mem_union.mp hz with hb | hbump
  · have hc := mem_square_coord_bounds (Finset.mem_sdiff.mp hb).1
    rcases hshape with rfl | rfl | rfl | rfl <;> norm_num at hc <;> omega
  · rcases Finset.mem_image.mp hbump with ⟨d, _, hd⟩
    have hp := P.pitch_ge_sixty_eight
    have hh := P.handshake_eq
    have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
    have hH0 := (codeH_bounds P η.south η.north (P.east u) ell.east).1
    have hHp := codeH_lt_handshake P η.south η.north (P.east u) ell.east
    have hV0 := (codeV_bounds P η.west η.east (P.north u) ell.north).1
    have hVp := codeV_lt_handshake P η.west η.east (P.north u) ell.north
    rcases hshape with rfl | rfl | rfl | rfl <;>
      cases d <;> simp [bumpCell] at hd <;> omega

theorem carrier_not_neg_corner (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) :
    (-1, -1) ∉ carrier P η u ell :=
  carrier_not_at_forbidden_corner P η u ell (Or.inl rfl)

theorem carrier_not_far_corner (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) :
    ((P.pitch : ℤ), (P.pitch : ℤ)) ∉ carrier P η u ell :=
  carrier_not_at_forbidden_corner P η u ell (Or.inr (Or.inl rfl))

theorem carrier_not_east_top_fringe (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) :
    ((P.pitch : ℤ), (P.pitch : ℤ) - 1) ∉ carrier P η u ell :=
  carrier_not_at_forbidden_corner P η u ell (Or.inr (Or.inr (Or.inl rfl)))

theorem carrier_not_north_right_fringe (P : RegisterParams) (η : MacroState)
    (u : Fin P.tileCount) (ell : AmpRecord P η) :
    ((P.pitch : ℤ) - 1, (P.pitch : ℤ)) ∉ carrier P η u ell :=
  carrier_not_at_forbidden_corner P η u ell (Or.inr (Or.inr (Or.inr rfl)))

/-- Diagonally adjacent southeast/northwest carriers are disjoint despite their
extended boxes meeting in a `2 × 2` corner window. -/
theorem diagonal_carriers_disjoint
    (P : RegisterParams) (η η' : MacroState)
    (u v : Fin P.tileCount) (ell : AmpRecord P η) (ell' : AmpRecord P η') :
    Disjoint (carrier P η u ell)
      (translate (carrier P η' v ell') ((P.pitch : ℤ), (P.pitch : ℤ))) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  have hb := mem_translate.mp hz'
  have hbox := carrier_subset_extendedBox P η u ell hz
  have hbox' := carrier_subset_extendedBox P η' v ell' hb
  have hx := Finset.mem_Icc.mp (Finset.mem_product.mp hbox).1
  have hy := Finset.mem_Icc.mp (Finset.mem_product.mp hbox).2
  have hx' := Finset.mem_Icc.mp (Finset.mem_product.mp hbox').1
  have hy' := Finset.mem_Icc.mp (Finset.mem_product.mp hbox').2
  have hp := P.pitch_ge_sixty_eight
  have hxcases : z.1 = (P.pitch : ℤ) - 1 ∨ z.1 = P.pitch := by omega
  have hycases : z.2 = (P.pitch : ℤ) - 1 ∨ z.2 = P.pitch := by omega
  rcases hxcases with hxz | hxz <;> rcases hycases with hyz | hyz
  · have : (z.1 - P.pitch, z.2 - P.pitch) = (-1, -1) := by
      apply Prod.ext <;> simp <;> omega
    rw [this] at hb
    exact carrier_not_neg_corner P η' v ell' hb
  · have : z = ((P.pitch : ℤ) - 1, (P.pitch : ℤ)) := Prod.ext hxz hyz
    rw [this] at hz
    exact carrier_not_north_right_fringe P η u ell hz
  · have : z = ((P.pitch : ℤ), (P.pitch : ℤ) - 1) := Prod.ext hxz hyz
    rw [this] at hz
    exact carrier_not_east_top_fringe P η u ell hz
  · have : z = ((P.pitch : ℤ), (P.pitch : ℤ)) := Prod.ext hxz hyz
    rw [this] at hz
    exact carrier_not_far_corner P η u ell hz

end
end PakFixedPolyomino
