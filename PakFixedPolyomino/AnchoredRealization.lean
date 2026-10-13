import PakFixedPolyomino.ResidualExtraction
import PakFixedPolyomino.MacroBijection

namespace PakFixedPolyomino

noncomputable section
set_option maxHeartbeats 2400000

local instance realizationDecidableEqRegisterTile (P : RegisterParams) :
    DecidableEq (RegisterTile P) := Classical.decEq _

theorem translated_carriers_disjoint_of_y_gap
    (P : RegisterParams)
    (η η' : MacroState) (u v : Fin P.tileCount)
    (l : AmpRecord P η) (l' : AmpRecord P η')
    (a b : Cell) (hgap : a.2 + P.pitch + 1 < b.2) :
    Disjoint (translate (carrier P η u l) a)
      (translate (carrier P η' v l') b) := by
  rw [Finset.disjoint_left]
  intro z hza hzb
  have ha := carrier_subset_extendedBox P η u l (mem_translate.mp hza)
  have hb := carrier_subset_extendedBox P η' v l' (mem_translate.mp hzb)
  have hay := Finset.mem_Icc.mp (Finset.mem_product.mp ha).2
  have hby := Finset.mem_Icc.mp (Finset.mem_product.mp hb).2
  omega

/-- The other diagonal orientation, omitted by the base carrier file. -/
theorem antiDiagonal_carriers_disjoint
    (P : RegisterParams) (η η' : MacroState)
    (u v : Fin P.tileCount) (l : AmpRecord P η) (l' : AmpRecord P η') :
    Disjoint (carrier P η u l)
      (translate (carrier P η' v l') ((P.pitch : ℤ), -(P.pitch : ℤ))) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  have hr := mem_translate.mp hz'
  have ha := carrier_subset_extendedBox P η u l hz
  have hb := carrier_subset_extendedBox P η' v l' hr
  have hax := Finset.mem_Icc.mp (Finset.mem_product.mp ha).1
  have hay := Finset.mem_Icc.mp (Finset.mem_product.mp ha).2
  have hbx := Finset.mem_Icc.mp (Finset.mem_product.mp hb).1
  have hby := Finset.mem_Icc.mp (Finset.mem_product.mp hb).2
  have hp := P.pitch_ge_sixty_eight
  have hxcases : z.1 = (P.pitch : ℤ) - 1 ∨ z.1 = P.pitch := by omega
  have hycases : z.2 = (-1 : ℤ) ∨ z.2 = 0 := by omega
  rcases hxcases with hx | hx <;> rcases hycases with hy | hy
  · have hzeq : z = ((P.pitch : ℤ) - 1, (-1 : ℤ)) := Prod.ext hx hy
    rw [hzeq] at hz
    have hs : ((P.pitch : ℤ) - 1, (-1 : ℤ)) ∈ carrier P η u l := hz
    obtain ⟨_, hcoord⟩ := carrier_south_outer_cell P η u l hs
    have hh := P.handshake_eq
    have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
    omega
  · have hw : ((-1 : ℤ), (P.pitch : ℤ)) ∈ carrier P η' v l' := by
      convert hr using 1 <;> apply Prod.ext <;> simp <;> omega
    obtain ⟨_, hcoord⟩ := carrier_west_outer_cell P η' v l' hw
    have hh := P.handshake_eq
    have hpit : P.pitch = P.codeSpan + 4 * P.tileCount + 64 := rfl
    omega
  · have hzeq : z = ((P.pitch : ℤ), (-1 : ℤ)) := Prod.ext hx hy
    rw [hzeq] at hz
    have he : ((P.pitch : ℤ), (-1 : ℤ)) ∈ carrier P η u l := hz
    obtain ⟨_, hcoord⟩ := carrier_east_outer_cell P η u l he
    have hc := codeH_bounds P η.south η.north (P.east u) l.east
    omega
  · have hn : ((0 : ℤ), (P.pitch : ℤ)) ∈ carrier P η' v l' := by
      convert hr using 1 <;> apply Prod.ext <;> simp <;> omega
    obtain ⟨_, hcoord⟩ := carrier_north_outer_cell P η' v l' hn
    have hc := codeV_bounds P η'.west η'.east (P.north v) l'.north
    omega

def anchoredCarrierSupport {P : RegisterParams} {n : ℕ}
    (A : AnchoredGrid P n) (q : Fin n × Fin n) : Polyomino :=
  translate (CarrierDatum.support P (A.cell q.1 q.2))
    (macroCorner P q.1.1 q.2.1)

private theorem anchoredCarrier_disjoint_col_lt
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (a b : Fin n × Fin n) (hcol : a.1.1 < b.1.1) :
    Disjoint (anchoredCarrierSupport A a) (anchoredCarrierSupport A b) := by
  let da := A.cell a.1 a.2
  let db := A.cell b.1 b.2
  by_cases hnext : a.1.1 + 1 = b.1.1
  · rcases lt_trichotomy a.2.1 b.2.1 with hrow | hrow | hrow
    · by_cases hvnext : a.2.1 + 1 = b.2.1
      · have hbEq : b =
            ((⟨a.1.1 + 1, by omega⟩ : Fin n),
             (⟨a.2.1 + 1, by omega⟩ : Fin n)) := by
          apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega
        have hd := diagonal_carriers_disjoint P da.state db.state da.tile db.tile
          da.labels db.labels
        have hdt := disjoint_translate_both
          (v := macroCorner P a.1.1 a.2.1) hd
        simpa [anchoredCarrierSupport, da, db, macroCorner, translate_translate,
          hbEq, CarrierDatum.support, Nat.add_mul, add_comm, add_left_comm,
          add_assoc] using hdt
      · have hfar : a.2.1 + 1 < b.2.1 := by omega
        apply translated_carriers_disjoint_of_y_gap P da.state db.state da.tile db.tile
          da.labels db.labels (macroCorner P a.1.1 a.2.1)
          (macroCorner P b.1.1 b.2.1)
        dsimp [macroCorner]
        have hstep := Nat.mul_le_mul_right P.pitch
          (show a.2.1 + 2 ≤ b.2.1 by omega)
        have hp := P.pitch_ge_sixty_eight
        push_cast at hstep
        nlinarith
    · have hbEq : b = ((⟨a.1.1 + 1, by omega⟩ : Fin n), a.2) := by
        apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega
      have hc : HorizontalCompatibleDatum P da db := by
        simpa [da, db, hbEq] using A.horizontal a.1 a.2 (by omega)
      have hd := (horizontal_carriers_disjoint_iff P da.state db.state da.tile db.tile
        da.labels db.labels).2 hc
      have hdt := disjoint_translate_both
        (v := macroCorner P a.1.1 a.2.1) hd
      simpa [anchoredCarrierSupport, da, db, macroCorner, translate_translate,
        hbEq, CarrierDatum.support, Nat.add_mul, add_comm, add_left_comm,
        add_assoc] using hdt
    · by_cases hvnext : b.2.1 + 1 = a.2.1
      · have hbEq : b =
            ((⟨a.1.1 + 1, by omega⟩ : Fin n),
             (⟨a.2.1 - 1, by omega⟩ : Fin n)) := by
          apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega
        have hd := antiDiagonal_carriers_disjoint P da.state db.state da.tile db.tile
          da.labels db.labels
        have hdt := disjoint_translate_both
          (v := macroCorner P a.1.1 a.2.1) hd
        have hsub : a.2.1 - 1 + 1 = a.2.1 := Nat.sub_add_cancel (by omega)
        have hsubMul : (a.2.1 - 1) * P.pitch + P.pitch =
            a.2.1 * P.pitch := by
          calc
            (a.2.1 - 1) * P.pitch + P.pitch =
                (a.2.1 - 1 + 1) * P.pitch := by rw [Nat.add_mul, one_mul]
            _ = _ := by rw [hsub]
        have hyZ : ((((a.2.1 - 1) * P.pitch : ℕ) : ℤ)) =
            ((a.2.1 * P.pitch : ℕ) : ℤ) - (P.pitch : ℤ) := by
          have hz : ((((a.2.1 - 1) * P.pitch : ℕ) : ℤ)) + (P.pitch : ℤ) =
              ((a.2.1 * P.pitch : ℕ) : ℤ) := by exact_mod_cast hsubMul
          omega
        simpa [anchoredCarrierSupport, da, db, macroCorner, translate_translate,
          hbEq, hyZ, sub_eq_add_neg, CarrierDatum.support, Nat.add_mul, hsub,
          add_comm, add_left_comm,
          add_assoc] using hdt
      · have hfar : b.2.1 + 1 < a.2.1 := by omega
        apply (translated_carriers_disjoint_of_y_gap P db.state da.state db.tile da.tile
          db.labels da.labels (macroCorner P b.1.1 b.2.1)
          (macroCorner P a.1.1 a.2.1) (by
            dsimp [macroCorner]
            have hstep := Nat.mul_le_mul_right P.pitch
              (show b.2.1 + 2 ≤ a.2.1 by omega)
            have hp := P.pitch_ge_sixty_eight
            push_cast at hstep
            nlinarith)).symm
  · have hfar : a.1.1 + 1 < b.1.1 := by omega
    apply translated_carriers_disjoint_of_x_gap P da.state db.state da.tile db.tile
      da.labels db.labels (macroCorner P a.1.1 a.2.1)
      (macroCorner P b.1.1 b.2.1)
    dsimp [macroCorner]
    have hstep := Nat.mul_le_mul_right P.pitch
      (show a.1.1 + 2 ≤ b.1.1 by omega)
    have hp := P.pitch_ge_sixty_eight
    push_cast at hstep
    nlinarith

private theorem anchoredCarrier_disjoint_same_col
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (a b : Fin n × Fin n) (hcol : a.1 = b.1) (hrow : a.2.1 < b.2.1) :
    Disjoint (anchoredCarrierSupport A a) (anchoredCarrierSupport A b) := by
  rcases a with ⟨ai, aj⟩
  rcases b with ⟨bi, bj⟩
  dsimp at hcol hrow ⊢
  subst bi
  let da := A.cell ai aj
  let db := A.cell ai bj
  by_cases hnext : aj.1 + 1 = bj.1
  · have hbj : bj = (⟨aj.1 + 1, by omega⟩ : Fin n) := Fin.ext hnext.symm
    have hc : VerticalCompatibleDatum P da db := by
      simpa [da, db, hbj] using A.vertical ai aj (by omega)
    have hd := (vertical_carriers_disjoint_iff P da.state db.state da.tile db.tile
      da.labels db.labels).2 hc
    have hdt := disjoint_translate_both
      (v := macroCorner P ai.1 aj.1) hd
    simpa [anchoredCarrierSupport, da, db, macroCorner, translate_translate,
      hbj, CarrierDatum.support, Nat.add_mul, add_comm, add_left_comm,
      add_assoc] using hdt
  · apply translated_carriers_disjoint_of_y_gap P da.state db.state da.tile db.tile
      da.labels db.labels (macroCorner P ai.1 aj.1)
      (macroCorner P ai.1 bj.1)
    dsimp [macroCorner]
    have hstep := Nat.mul_le_mul_right P.pitch
      (show aj.1 + 2 ≤ bj.1 by omega)
    have hp := P.pitch_ge_sixty_eight
    push_cast at hstep
    nlinarith

theorem anchoredCarriers_pairwise_disjoint
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) :
    Set.Pairwise (Set.univ : Set (Fin n × Fin n))
      fun a b => Disjoint (anchoredCarrierSupport A a) (anchoredCarrierSupport A b) := by
  intro a _ b _ hab
  rcases lt_trichotomy a.1.1 b.1.1 with hcol | hcol | hcol
  · exact anchoredCarrier_disjoint_col_lt A a b hcol
  · have hfin : a.1 = b.1 := Fin.ext hcol
    rcases lt_trichotomy a.2.1 b.2.1 with hrow | hrow | hrow
    · exact anchoredCarrier_disjoint_same_col A a b hfin hrow
    · exact (hab (Prod.ext hfin (Fin.ext hrow))).elim
    · exact (anchoredCarrier_disjoint_same_col A b a hfin.symm hrow).symm
  · exact (anchoredCarrier_disjoint_col_lt A b a hcol).symm

theorem mem_square_of_coord_bounds {N : ℕ} {z : Cell}
    (hx0 : 0 ≤ z.1) (hxN : z.1 < N) (hy0 : 0 ≤ z.2) (hyN : z.2 < N) :
    z ∈ square N := by
  obtain ⟨x, hx⟩ := Int.eq_ofNat_of_zero_le hx0
  obtain ⟨y, hy⟩ := Int.eq_ofNat_of_zero_le hy0
  have hz : z = ((x : ℤ), (y : ℤ)) := Prod.ext hx hy
  rw [hz] at hxN hyN
  change (x : ℤ) < (N : ℤ) at hxN
  change (y : ℤ) < (N : ℤ) at hyN
  rw [hz]
  apply ofNat_pair_mem_square.mpr
  constructor
  · exact_mod_cast hxN
  · exact_mod_cast hyN

theorem anchoredCarrier_subset_square
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (q : Fin n × Fin n) :
    anchoredCarrierSupport A q ⊆ square (P.pitch * n) := by
  intro z hz
  let d := A.cell q.1 q.2
  have hr := mem_translate.mp hz
  have hix : q.1.1 * P.pitch + P.pitch ≤ n * P.pitch := by
    simpa [Nat.add_mul] using Nat.mul_le_mul_right P.pitch
      (Nat.succ_le_iff.mpr q.1.isLt)
  have hjy : q.2.1 * P.pitch + P.pitch ≤ n * P.pitch := by
    simpa [Nat.add_mul] using Nat.mul_le_mul_right P.pitch
      (Nat.succ_le_iff.mpr q.2.isLt)
  have hcomm : n * P.pitch = P.pitch * n := Nat.mul_comm _ _
  rw [hcomm] at hix hjy
  rcases Finset.mem_union.mp hr with hb | hb
  · have hs := mem_square_coord_bounds (Finset.mem_sdiff.mp hb).1
    dsimp [macroCorner, CarrierDatum.support] at hs hr
    push_cast at hix hjy
    apply mem_square_of_coord_bounds <;> omega
  · rcases Finset.mem_image.mp hb with ⟨side, hopen, hEq⟩
    have hmem := (mem_activeSides d.state side).1 hopen
    have hxEq := congrArg Prod.fst hEq
    have hyEq := congrArg Prod.snd hEq
    dsimp [d] at hmem hxEq hyEq
    dsimp [macroCorner, CarrierDatum.support] at hr
    cases side with
    | west =>
        by_cases hq0 : q.1.1 = 0
        · have hfin : q.1 = ⟨0, by omega⟩ := Fin.ext hq0
          have hclosed := A.westClosed q.2
          have hdclosed : (A.cell q.1 q.2).state.west = false := by
            simpa [hfin] using hclosed
          simp [MacroState.isOpen, hdclosed] at hmem
        · have hpos : 0 < q.1.1 := Nat.pos_of_ne_zero hq0
          dsimp [bumpCell, macroCorner] at hxEq hyEq
          have hh := P.handshake_lt_pitch
          have hp0 : 0 < P.pitch := lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight
          have hmulpos : 0 < q.1.1 * P.pitch := Nat.mul_pos hpos hp0
          push_cast at hix hjy
          apply mem_square_of_coord_bounds <;> omega
    | east =>
        by_cases hlast : q.1.1 = n - 1
        · have hfin : q.1 = ⟨n - 1, by omega⟩ := Fin.ext hlast
          have hclosed := A.eastClosed q.2
          have hdclosed : (A.cell q.1 q.2).state.east = false := by
            simpa [hfin] using hclosed
          simp [MacroState.isOpen, hdclosed] at hmem
        · have hnext : q.1.1 + 1 < n := by omega
          have hp0 : 0 < P.pitch := lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight
          have hxStrict : q.1.1 * P.pitch + P.pitch < P.pitch * n := by
            have := Nat.mul_lt_mul_of_pos_right hnext hp0
            simpa [Nat.add_mul, Nat.mul_comm] using this
          have hc := codeH_lt_pitch P d.state.south d.state.north
            (P.east d.tile) d.labels.east
          dsimp [d] at hc
          dsimp [bumpCell, macroCorner] at hxEq hyEq
          push_cast at hix hjy
          apply mem_square_of_coord_bounds <;> omega
    | south =>
        by_cases hq0 : q.2.1 = 0
        · have hfin : q.2 = ⟨0, by omega⟩ := Fin.ext hq0
          have hclosed := A.southClosed q.1
          have hdclosed : (A.cell q.1 q.2).state.south = false := by
            simpa [hfin] using hclosed
          simp [MacroState.isOpen, hdclosed] at hmem
        · have hpos : 0 < q.2.1 := Nat.pos_of_ne_zero hq0
          have hp0 : 0 < P.pitch := lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight
          have hmulpos : 0 < q.2.1 * P.pitch := Nat.mul_pos hpos hp0
          have hh := P.handshake_lt_pitch
          dsimp [bumpCell, macroCorner] at hxEq hyEq
          push_cast at hix hjy
          apply mem_square_of_coord_bounds <;> omega
    | north =>
        by_cases hlast : q.2.1 = n - 1
        · have hfin : q.2 = ⟨n - 1, by omega⟩ := Fin.ext hlast
          have hclosed := A.northClosed q.1
          have hdclosed : (A.cell q.1 q.2).state.north = false := by
            simpa [hfin] using hclosed
          simp [MacroState.isOpen, hdclosed] at hmem
        · have hnext : q.2.1 + 1 < n := by omega
          have hp0 : 0 < P.pitch := lt_of_lt_of_le (by decide) P.pitch_ge_sixty_eight
          have hyStrict : q.2.1 * P.pitch + P.pitch < P.pitch * n := by
            have := Nat.mul_lt_mul_of_pos_right hnext hp0
            simpa [Nat.add_mul, Nat.mul_comm] using this
          have hc := codeV_lt_pitch P d.state.west d.state.east
            (P.north d.tile) d.labels.north
          dsimp [d] at hc
          dsimp [bumpCell, macroCorner] at hxEq hyEq
          push_cast at hix hjy
          apply mem_square_of_coord_bounds <;> omega

def anchoredCavitySupport {P : RegisterParams} {n : ℕ}
    (A : AnchoredGrid P n) (q : Fin n × Fin n) : Polyomino :=
  macroCavity P q.1.1 q.2.1 (A.cell q.1 q.2).tile

def anchoredCarrierUnion {P : RegisterParams} {n : ℕ}
    (A : AnchoredGrid P n) : Polyomino :=
  Finset.univ.biUnion (anchoredCarrierSupport A)

def anchoredCavityUnion {P : RegisterParams} {n : ℕ}
    (A : AnchoredGrid P n) : Polyomino :=
  Finset.univ.biUnion (anchoredCavitySupport A)

theorem anchoredCavity_disjoint_carrier
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (a b : Fin n × Fin n) :
    Disjoint (anchoredCavitySupport A a) (anchoredCarrierSupport A b) := by
  by_cases hab : a = b
  · subst b
    rw [show anchoredCavitySupport A a =
        translate (tileCavity (A.cell a.1 a.2).tile)
          (macroCorner P a.1.1 a.2.1) by
      exact macroCavity_eq_translate_tileCavity P a.1.1 a.2.1 _]
    exact disjoint_translate_both
      (tileCavity_disjoint_carrier P (A.cell a.1 a.2).state
        (A.cell a.1 a.2).tile (A.cell a.1 a.2).labels)
  · exact macroCavity_disjoint_other_alignedCarrier P
      (A.cell a.1 a.2).tile (A.cell b.1 b.2).state
      (A.cell b.1 b.2).tile (A.cell b.1 b.2).labels (by
        intro h
        apply hab
        exact Prod.ext (Fin.ext (congrArg Prod.fst h))
          (Fin.ext (congrArg Prod.snd h)))

theorem anchoredCarrierUnion_disjoint_cavityUnion
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) :
    Disjoint (anchoredCarrierUnion A) (anchoredCavityUnion A) := by
  rw [Finset.disjoint_left]
  intro z hzK hzC
  rcases Finset.mem_biUnion.mp hzK with ⟨b, _, hb⟩
  rcases Finset.mem_biUnion.mp hzC with ⟨a, _, ha⟩
  exact Finset.disjoint_left.mp (anchoredCavity_disjoint_carrier A a b) ha hb

theorem anchoredCarrierUnion_subset_square
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) :
    anchoredCarrierUnion A ⊆ square (P.pitch * n) := by
  intro z hz
  rcases Finset.mem_biUnion.mp hz with ⟨q, _, hq⟩
  exact anchoredCarrier_subset_square A q hq

theorem anchoredCavityUnion_subset_square
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) :
    anchoredCavityUnion A ⊆ square (P.pitch * n) := by
  intro z hz
  rcases Finset.mem_biUnion.mp hz with ⟨q, _, hq⟩
  exact macroCavity_subset_square P q.1 q.2 (A.cell q.1 q.2).tile hq

@[simp] theorem card_anchoredCarrierUnion
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) :
    (anchoredCarrierUnion A).card = n ^ 2 * (P.pitch ^ 2 - 3) := by
  rw [anchoredCarrierUnion, Finset.card_biUnion]
  · simp [anchoredCarrierSupport, CarrierDatum.support, carrier_area, pow_two]
  · intro a _ b _ hab
    exact anchoredCarriers_pairwise_disjoint A (Set.mem_univ a) (Set.mem_univ b) hab

@[simp] theorem card_anchoredCavityUnion
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) :
    (anchoredCavityUnion A).card = 3 * n ^ 2 := by
  rw [anchoredCavityUnion, Finset.card_biUnion]
  · simp [anchoredCavitySupport, pow_two, Nat.mul_comm]
  · intro a _ b _ hab
    exact macroCavities_pairwise_disjoint P (by
      intro h
      apply hab
      exact Prod.ext (Fin.ext (congrArg Prod.fst h))
        (Fin.ext (congrArg Prod.snd h))) _ _

theorem anchoredCarrier_cavity_cover
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) :
    anchoredCarrierUnion A ∪ anchoredCavityUnion A = square (P.pitch * n) := by
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.union_subset (anchoredCarrierUnion_subset_square A)
      (anchoredCavityUnion_subset_square A)
  · rw [Finset.card_union_of_disjoint (anchoredCarrierUnion_disjoint_cavityUnion A),
      card_anchoredCarrierUnion, card_anchoredCavityUnion, card_square]
    have hp2 : 3 ≤ P.pitch ^ 2 := by
      have hp := P.pitch_ge_sixty_eight
      nlinarith
    have hsq : (P.pitch * n) ^ 2 = n ^ 2 * P.pitch ^ 2 := by ring
    rw [hsq, Nat.mul_sub_left_distrib]
    have hle : n ^ 2 * 3 ≤ n ^ 2 * P.pitch ^ 2 := Nat.mul_le_mul_left _ hp2
    omega

def anchoredCarrierPlacement {P : RegisterParams} {n : ℕ}
    (A : AnchoredGrid P n) (q : Fin n × Fin n) : Placement (RegisterTile P) :=
  ⟨some ⟨(A.cell q.1 q.2).state, (A.cell q.1 q.2).tile,
    (A.cell q.1 q.2).labels⟩, macroCorner P q.1.1 q.2.1⟩

def anchoredPlugPlacement {P : RegisterParams} {n : ℕ}
    (A : AnchoredGrid P n) (q : Fin n × Fin n) : Placement (RegisterTile P) :=
  ⟨none, macroCavityOrigin P q.1.1 q.2.1 (A.cell q.1 q.2).tile⟩

def anchoredRealizationPlacements {P : RegisterParams} {n : ℕ}
    (A : AnchoredGrid P n) : Finset (Placement (RegisterTile P)) :=
  Finset.univ.image (anchoredCarrierPlacement A) ∪
    Finset.univ.image (anchoredPlugPlacement A)

@[simp] theorem anchoredCarrierPlacement_cells {P : RegisterParams} {n : ℕ}
    (A : AnchoredGrid P n) (q : Fin n × Fin n) :
    Placement.cells (registerTileSupport P) (anchoredCarrierPlacement A q) =
      anchoredCarrierSupport A q := rfl

@[simp] theorem anchoredPlugPlacement_cells {P : RegisterParams} {n : ℕ}
    (A : AnchoredGrid P n) (q : Fin n × Fin n) :
    Placement.cells (registerTileSupport P) (anchoredPlugPlacement A q) =
      anchoredCavitySupport A q := by
  simp [anchoredPlugPlacement, anchoredCavitySupport, Placement.cells,
    registerTileSupport, macroCavity, cavity]

theorem anchoredRealization_pairwise
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) :
    Set.Pairwise (↑(anchoredRealizationPlacements A) : Set (Placement (RegisterTile P)))
      fun p q => Disjoint (Placement.cells (registerTileSupport P) p)
        (Placement.cells (registerTileSupport P) q) := by
  intro p hp q hq hpq
  change p ∈ anchoredRealizationPlacements A at hp
  change q ∈ anchoredRealizationPlacements A at hq
  simp only [anchoredRealizationPlacements, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hp hq
  rcases hp with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases hq with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · apply anchoredCarriers_pairwise_disjoint A (Set.mem_univ a) (Set.mem_univ b)
    intro hab
    subst b
    exact hpq rfl
  · exact (anchoredCavity_disjoint_carrier A b a).symm
  · exact anchoredCavity_disjoint_carrier A a b
  · apply macroCavities_pairwise_disjoint P
    intro hab
    apply hpq
    exact congrArg (anchoredPlugPlacement A)
      (Prod.ext (Fin.ext (congrArg Prod.fst hab))
        (Fin.ext (congrArg Prod.snd hab)))

theorem anchoredRealization_covers
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) :
    (anchoredRealizationPlacements A).biUnion
      (Placement.cells (registerTileSupport P)) = square (P.pitch * n) := by
  rw [← anchoredCarrier_cavity_cover A]
  ext z
  constructor
  · intro hz
    rcases Finset.mem_biUnion.mp hz with ⟨p, hp, hzp⟩
    simp only [anchoredRealizationPlacements, Finset.mem_union,
      Finset.mem_image, Finset.mem_univ, true_and] at hp
    rcases hp with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨q, Finset.mem_univ _, by simpa using hzp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨q, Finset.mem_univ _, by simpa using hzp⟩)
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_biUnion.mp hz with ⟨q, _, hzq⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨anchoredCarrierPlacement A q, ?_, by simpa using hzq⟩
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨q, Finset.mem_univ _, rfl⟩)
    · rcases Finset.mem_biUnion.mp hz with ⟨q, _, hzq⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨anchoredPlugPlacement A q, ?_, by simpa using hzq⟩
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨q, Finset.mem_univ _, rfl⟩)

/-- The reverse physical geometry: every compatible anchored grid expands to
an actual exact tiling by its carrier occurrences and one PlugL per cavity. -/
def realizeAnchoredGrid {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) :
    Tiling (registerTileSupport P) (square (P.pitch * n)) where
  placements := anchoredRealizationPlacements A
  disjoint := anchoredRealization_pairwise A
  covers := anchoredRealization_covers A

theorem cornerPlacement_realizeAnchoredGrid
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (i j : Fin n) :
    cornerPlacement P (realizeAnchoredGrid A) i j =
      anchoredCarrierPlacement A (i, j) := by
  apply (realizeAnchoredGrid A).cover_unique
  · exact cornerPlacement_mem P (realizeAnchoredGrid A) i j
  · apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩
  · exact cornerPlacement_covers P (realizeAnchoredGrid A) i j
  · change macroCorner P i.1 j.1 ∈ anchoredCarrierSupport A (i, j)
    apply Finset.mem_image.mpr
    refine ⟨(0, 0), origin_mem_carrier P (A.cell i j).state
      (A.cell i j).tile (A.cell i j).labels, ?_⟩
    apply Prod.ext <;> simp [macroCorner]

def carrierDatumOfIndex {P : RegisterParams} : CarrierIndex P → CarrierDatum P
  | ⟨η, u, l⟩ => ⟨η, u, l⟩

@[simp] theorem carrierDatumOfIndex_mk {P : RegisterParams} (d : CarrierDatum P) :
    carrierDatumOfIndex (⟨d.state, d.tile, d.labels⟩ : CarrierIndex P) = d := by
  cases d
  rfl

theorem carrierDatumTile_injective {P : RegisterParams} :
    Function.Injective (fun d : CarrierDatum P =>
      (some ⟨d.state, d.tile, d.labels⟩ : RegisterTile P)) := by
  intro a b h
  have hs : (⟨a.state, a.tile, a.labels⟩ : CarrierIndex P) =
      ⟨b.state, b.tile, b.labels⟩ := Option.some.inj h
  have hd := congrArg carrierDatumOfIndex hs
  simpa using hd

theorem AnchoredGrid.eq_of_cell_eq {P : RegisterParams} {n : ℕ}
    (A B : AnchoredGrid P n) (h : A.cell = B.cell) : A = B := by
  cases A
  cases B
  cases h
  rfl

theorem Tiling.eq_of_placements_eq {ι : Type*} [DecidableEq ι]
    {tiles : ι → Polyomino} {region : Polyomino}
    (A B : Tiling tiles region) (h : A.placements = B.placements) : A = B := by
  cases A
  cases B
  cases h
  rfl

theorem extractedDatum_realizeAnchoredGrid
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n)
    (i j : Fin n) :
    extractedDatum P (realizeAnchoredGrid A) i j = A.cell i j := by
  apply carrierDatumTile_injective
  have hs := (extractedDatum_spec P (realizeAnchoredGrid A) i j).1
  rw [cornerPlacement_realizeAnchoredGrid A i j] at hs
  exact hs.symm

theorem extractedAnchoredGrid_realizeAnchoredGrid
    {P : RegisterParams} {n : ℕ} (A : AnchoredGrid P n) :
    extractedAnchoredGrid P (realizeAnchoredGrid A) = A := by
  have hcell : (extractedAnchoredGrid P (realizeAnchoredGrid A)).cell = A.cell := by
    funext i j
    exact extractedDatum_realizeAnchoredGrid A i j
  exact AnchoredGrid.eq_of_cell_eq _ _ hcell

theorem anchoredCarrierPlacement_extracted
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    (q : Fin n × Fin n) :
    anchoredCarrierPlacement (extractedAnchoredGrid P T) q =
      cornerPlacement P T q.1 q.2 := by
  apply congrArg₂ Placement.mk
  · exact (extractedDatum_spec P T q.1 q.2).1.symm
  · exact (extractedDatum_spec P T q.1 q.2).2.symm

theorem anchoredPlugPlacement_extracted
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n)))
    (q : Fin n × Fin n) :
    anchoredPlugPlacement (extractedAnchoredGrid P T) q =
      cavityPlugPlacement P T q := rfl

theorem realizeAnchoredGrid_extractedAnchoredGrid
    (P : RegisterParams) {n : ℕ}
    (T : Tiling (registerTileSupport P) (square (P.pitch * n))) :
    realizeAnchoredGrid (extractedAnchoredGrid P T) = T := by
  have hplacements :
      (realizeAnchoredGrid (extractedAnchoredGrid P T)).placements = T.placements := by
      dsimp [realizeAnchoredGrid]
      rw [anchoredRealizationPlacements]
      have hcar : Finset.univ.image
          (anchoredCarrierPlacement (extractedAnchoredGrid P
            T)) = selectedCarrierPlacements P T := by
        unfold selectedCarrierPlacements
        apply Finset.image_congr
        intro q _
        exact anchoredCarrierPlacement_extracted P T q
      have hplug : Finset.univ.image
          (anchoredPlugPlacement (extractedAnchoredGrid P T)) =
          residualPlacements P T := by
        rw [residualPlacements_eq_plugs]
        apply Finset.image_congr
        intro q _
        exact anchoredPlugPlacement_extracted P T q
      rw [hcar, hplug]
      exact Finset.union_sdiff_of_subset
        (selectedCarrierPlacements_subset P T)
  exact Tiling.eq_of_placements_eq _ _ hplacements

/-- Complete occurrence-level geometric equivalence.  Neither direction has
any residual placement, anchoring, or hostability hypothesis. -/
def physicalTilingEquivAnchoredGrid (P : RegisterParams) (n : ℕ) :
    Tiling (registerTileSupport P) (square (P.pitch * n)) ≃ AnchoredGrid P n where
  toFun := extractedAnchoredGrid P
  invFun := realizeAnchoredGrid
  left_inv := realizeAnchoredGrid_extractedAnchoredGrid P
  right_inv := extractedAnchoredGrid_realizeAnchoredGrid

/-- Relation-level packaging of the now unconditional physical equivalence. -/
def physicalTilingAnchoredCertificate (P : RegisterParams) (n : ℕ) :
    LatticeAnchored
      (Tiling (registerTileSupport P) (square (P.pitch * n)))
      (AnchoredGrid P n) :=
  LatticeAnchored.ofEquiv (physicalTilingEquivAnchoredGrid P n)

end
end PakFixedPolyomino
