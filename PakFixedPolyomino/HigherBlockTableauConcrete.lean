import PakFixedPolyomino.WangRectangleBoundConcrete
import Mathlib.Tactic

/-!
# The concrete higher-block tableau and its constant-column theorem

This is the tile inventory of accepted Fact `b9df6c5fdbe1516b`, separated from
the full-frame machine simulation because the arbitrary-rectangle perimeter
bound uses only the local Case H/A/B/Q rules.
-/

namespace PakFixedPolyomino

noncomputable section

inductive TableauCell (State Tape : Type*) where
  | plain : Tape → TableauCell State Tape
  | head : State → Tape → TableauCell State Tape
  deriving DecidableEq, Fintype

namespace TableauCell

def isHead {State Tape : Type*} : TableauCell State Tape → Bool
  | .plain _ => false
  | .head _ _ => true

def headSource? {State Tape : Type*} : TableauCell State Tape → Option (State × Tape)
  | .plain _ => none
  | .head q a => some (q, a)

def headSourceOf {State Tape : Type*} (z : TableauCell State Tape)
    (h : z.isHead = true) : State × Tape := by
  cases z with
  | plain a => simp [isHead] at h
  | head q a => exact (q, a)

end TableauCell

@[ext] structure CellTriple (Cell : Type*) where
  minus : Cell
  center : Cell
  plus : Cell
  deriving DecidableEq, Fintype

def tripleHeadCount {State Tape : Type*}
    (X : CellTriple (TableauCell State Tape)) : ℕ :=
  X.minus.isHead.toNat + X.center.isHead.toNat + X.plus.isHead.toNat

def tableauOrdBit {State Tape : Type*}
    (a b : Bool) (z : TableauCell State Tape) : Prop :=
  if z.isHead then a = false ∧ b = true else a = b

theorem tableauOrdBit_right_unique {State Tape : Type*}
    {a b c : Bool} {z : TableauCell State Tape}
    (hb : tableauOrdBit a b z) (hc : tableauOrdBit a c z) : b = c := by
  unfold tableauOrdBit at hb hc
  split at hb <;> split at hc <;> simp_all

/-- Finite local data of a one-tape machine.  `theta`, `leftUpdate`, and
`rightUpdate` are the literal three-cell update maps used by the four cases;
their computational meaning is irrelevant to the column bound. -/
structure TableauMachineData (State Tape Arrow : Type*) where
  source : Arrow → State × Tape
  theta : Arrow → CellTriple (TableauCell State Tape) →
    Option (CellTriple (TableauCell State Tape))
  leftUpdate : Arrow → TableauCell State Tape → TableauCell State Tape
  rightUpdate : Arrow → TableauCell State Tape → TableauCell State Tape

@[ext] structure TableauRaw (State Tape Arrow : Type*) where
  old : CellTriple (TableauCell State Tape)
  new : CellTriple (TableauCell State Tape)
  oldMinusBit : Bool
  oldPlusBit : Bool
  newMinusBit : Bool
  newPlusBit : Bool
  southToken : Option Arrow
  northToken : Option Arrow
  deriving DecidableEq

instance (State Tape Arrow : Type*) [Fintype State] [Fintype Tape] [Fintype Arrow] :
    Finite (TableauRaw State Tape Arrow) :=
  Finite.of_injective
    (fun u : TableauRaw State Tape Arrow =>
      ((u.old, u.new),
        ((u.oldMinusBit, u.oldPlusBit, u.newMinusBit, u.newPlusBit),
          (u.southToken, u.northToken)))) (by
      intro u v h
      apply TableauRaw.ext <;> simp_all)

noncomputable instance (State Tape Arrow : Type*)
    [Fintype State] [Fintype Tape] [Fintype Arrow] :
    Fintype (TableauRaw State Tape Arrow) := Fintype.ofFinite _

def TableauAdmissible {State Tape Arrow : Type*}
    (M : TableauMachineData State Tape Arrow)
    (u : TableauRaw State Tape Arrow) : Prop :=
  tripleHeadCount u.old ≤ 1 ∧
  tripleHeadCount u.new ≤ 1 ∧
  tableauOrdBit u.oldMinusBit u.oldPlusBit u.old.center ∧
  tableauOrdBit u.newMinusBit u.newPlusBit u.new.center ∧
  if hc : u.old.center.isHead then
    ∃ arr : Arrow, u.southToken = none ∧ u.northToken = some arr ∧
      M.source arr = u.old.center.headSourceOf hc ∧
      M.theta arr u.old = some u.new
  else if hm : u.old.minus.isHead then
    ∃ arr : Arrow, u.southToken = some arr ∧ u.northToken = none ∧
      M.source arr = u.old.minus.headSourceOf hm ∧
      u.new.center = M.rightUpdate arr u.old.center
  else if hp : u.old.plus.isHead then
    u.southToken = none ∧ u.northToken = none ∧
      ∃ arr : Arrow, M.source arr = u.old.plus.headSourceOf hp ∧
        u.new.center = M.leftUpdate arr u.old.center
  else
    u.southToken = none ∧ u.northToken = none ∧
      u.new.center = u.old.center

abbrev HigherBlockTableauTile (State Tape Arrow : Type*)
    (M : TableauMachineData State Tape Arrow) :=
  {u : TableauRaw State Tape Arrow // TableauAdmissible M u}

noncomputable instance (State Tape Arrow : Type*)
    [Fintype State] [Fintype Tape] [Fintype Arrow]
    (M : TableauMachineData State Tape Arrow) :
    Fintype (HigherBlockTableauTile State Tape Arrow M) := Fintype.ofFinite _

abbrev TableauHorizontalColour (State Tape : Type*) :=
  CellTriple (TableauCell State Tape)

noncomputable instance (State Tape : Type*) :
    DecidableEq (TableauHorizontalColour State Tape) := Classical.decEq _

abbrev TableauVerticalColour (State Tape Arrow : Type*) :=
  ((TableauCell State Tape × TableauCell State Tape) ×
    (TableauCell State Tape × TableauCell State Tape)) ×
      ((Bool × Bool) × Option Arrow)

noncomputable instance (State Tape Arrow : Type*) :
    DecidableEq (TableauVerticalColour State Tape Arrow) := Classical.decEq _

/-- Literal `hcol`/`vcol` table from the accepted proof. -/
def higherBlockTableauWangTile
    {State Tape Arrow : Type*} (M : TableauMachineData State Tape Arrow) :
    HigherBlockTableauTile State Tape Arrow M →
      WangTile (TableauHorizontalColour State Tape)
        (TableauVerticalColour State Tape Arrow) := fun u =>
  { east := u.1.old
    west := u.1.new
    south := (((u.1.old.minus, u.1.old.center),
      (u.1.new.minus, u.1.new.center)),
      ((u.1.oldMinusBit, u.1.newMinusBit), u.1.southToken))
    north := (((u.1.old.center, u.1.old.plus),
      (u.1.new.center, u.1.new.plus)),
      ((u.1.oldPlusBit, u.1.newPlusBit), u.1.northToken)) }

namespace HigherBlockTableau

variable {State Tape Arrow : Type*}
variable [Fintype State] [Fintype Tape] [Fintype Arrow]
variable [DecidableEq State] [DecidableEq Tape] [DecidableEq Arrow]
variable (M : TableauMachineData State Tape Arrow)

abbrev Tile := HigherBlockTableauTile State Tape Arrow M
abbrev TileMap := higherBlockTableauWangTile M

theorem vertical_old_overlap {h : ℕ} (c : WangColumn (TileMap M) h)
    (j : Fin h) (hj : j.1 + 1 < h) :
    (c.1 j).1.old.center = (c.1 ⟨j.1 + 1, hj⟩).1.old.minus ∧
    (c.1 j).1.old.plus = (c.1 ⟨j.1 + 1, hj⟩).1.old.center := by
  have hm := c.2 j hj
  exact ⟨congrArg (fun z => z.1.1.1) hm, congrArg (fun z => z.1.1.2) hm⟩

theorem vertical_new_overlap {h : ℕ} (c : WangColumn (TileMap M) h)
    (j : Fin h) (hj : j.1 + 1 < h) :
    (c.1 j).1.new.center = (c.1 ⟨j.1 + 1, hj⟩).1.new.minus ∧
    (c.1 j).1.new.plus = (c.1 ⟨j.1 + 1, hj⟩).1.new.center := by
  have hm := c.2 j hj
  exact ⟨congrArg (fun z => z.1.2.1) hm, congrArg (fun z => z.1.2.2) hm⟩

theorem vertical_bits_tokens {h : ℕ} (c : WangColumn (TileMap M) h)
    (j : Fin h) (hj : j.1 + 1 < h) :
    (c.1 j).1.oldPlusBit = (c.1 ⟨j.1 + 1, hj⟩).1.oldMinusBit ∧
    (c.1 j).1.newPlusBit = (c.1 ⟨j.1 + 1, hj⟩).1.newMinusBit ∧
    (c.1 j).1.northToken = (c.1 ⟨j.1 + 1, hj⟩).1.southToken := by
  have hm := c.2 j hj
  exact ⟨congrArg (fun z => z.2.1.1) hm,
    congrArg (fun z => z.2.1.2) hm,
    congrArg (fun z => z.2.2) hm⟩

theorem old_visible_head_unique {h : ℕ} (c : WangColumn (TileMap M) h)
    {i j : Fin h}
    (hi : (c.1 i).1.old.center.isHead = true)
    (hj : (c.1 j).1.old.center.isHead = true) : i = j := by
  apply Fin.eq_of_val_eq
  by_contra hne
  have hiBits : (c.1 i).1.oldMinusBit = false ∧
      (c.1 i).1.oldPlusBit = true := by
    have ho := (c.1 i).2.2.2.1
    unfold tableauOrdBit at ho
    simpa [hi] using ho
  have hjBits : (c.1 j).1.oldMinusBit = false ∧
      (c.1 j).1.oldPlusBit = true := by
    have ho := (c.1 j).2.2.2.1
    unfold tableauOrdBit at ho
    simpa [hj] using ho
  have chain_mono : ∀ (a b : Fin h), a.1 < b.1 →
      (c.1 a).1.oldPlusBit = true → (c.1 b).1.oldMinusBit = true := by
    intro a b hab ha
    induction d : b.1 - a.1 using Nat.strong_induction_on generalizing b with
    | h d ih =>
        by_cases hs : a.1 + 1 = b.1
        · have hov := (vertical_bits_tokens M c a (by omega)).1
          have heq : (⟨a.1 + 1, by omega⟩ : Fin h) = b := Fin.eq_of_val_eq hs
          simpa [heq, ha] using hov.symm
        · let bp : Fin h := ⟨b.1 - 1, by omega⟩
          have hbp : bp.1 + 1 < h := by dsimp [bp]; omega
          have hprev : (c.1 bp).1.oldMinusBit = true := by
            apply ih (bp.1 - a.1)
            · dsimp [bp]; omega
            · dsimp [bp]; omega
            · rfl
          have hord := (c.1 bp).2.2.2.1
          have hplus : (c.1 bp).1.oldPlusBit = true := by
            unfold tableauOrdBit at hord
            split at hord <;> simp_all
          have hov := (vertical_bits_tokens M c bp hbp).1
          have heq : (⟨bp.1 + 1, hbp⟩ : Fin h) = b := by
            apply Fin.ext
            dsimp [bp]
            omega
          simpa [heq, hplus] using hov.symm
  rcases lt_or_gt_of_ne hne with hij | hji
  · have bad := chain_mono i j hij hiBits.2
    simp [hjBits.1] at bad
  · have bad := chain_mono j i hji hjBits.2
    simp [hiBits.1] at bad

theorem northToken_none_of_center_plain (u : Tile M)
    (hc : u.1.old.center.isHead = false) : u.1.northToken = none := by
  have hcase := u.2.2.2.2.2
  simp only [hc, Bool.false_eq_true, ↓reduceDIte] at hcase
  by_cases hm : u.1.old.minus.isHead = true
  · simp [hm] at hcase
    exact hcase.choose_spec.2.1
  · have hm' : u.1.old.minus.isHead = false := by
      cases h : u.1.old.minus.isHead <;> simp_all
    simp only [hm', Bool.false_eq_true, ↓reduceDIte] at hcase
    by_cases hp : u.1.old.plus.isHead = true
    · simp [hp] at hcase
      exact hcase.2.1
    · have hp' : u.1.old.plus.isHead = false := by
        cases h : u.1.old.plus.isHead <;> simp_all
      simp [hp'] at hcase
      exact hcase.2.1

theorem new_center_eq_old_of_no_head (u : Tile M)
    (hm : u.1.old.minus.isHead = false)
    (hc : u.1.old.center.isHead = false)
    (hp : u.1.old.plus.isHead = false) :
    u.1.new.center = u.1.old.center := by
  have hcase := u.2.2.2.2.2
  simp [hc, hm, hp] at hcase
  exact hcase.2.2

def visibleHeadIndex {h : ℕ} (c : WangColumn (TileMap M) h) : Option (Fin h) :=
  if hex : ∃ j : Fin h, (c.1 j).1.old.center.isHead = true then
    some (Classical.choose hex)
  else none

theorem visibleHeadIndex_spec {h : ℕ} (c : WangColumn (TileMap M) h)
    {j : Fin h} (hj : (c.1 j).1.old.center.isHead = true) :
    visibleHeadIndex M c = some j := by
  unfold visibleHeadIndex
  split
  next hex =>
    have hchosen := Classical.choose_spec hex
    have heq := old_visible_head_unique M c hchosen hj
    simp [heq]
  next hex => exact (hex ⟨j, hj⟩).elim

/-- Three actual tile slots suffice to code a column once its east word is
fixed: the bottom tile, top tile, and the unique visible old-head tile. -/
@[ext] structure TableauColumnSummary (State Tape Arrow : Type*)
    (M : TableauMachineData State Tape Arrow) where
  bottom : Option (HigherBlockTableauTile State Tape Arrow M)
  top : Option (HigherBlockTableauTile State Tape Arrow M)
  visibleHead : Option (HigherBlockTableauTile State Tape Arrow M)

instance (State Tape Arrow : Type*) [Fintype State] [Fintype Tape] [Fintype Arrow]
    (M : TableauMachineData State Tape Arrow) :
    Fintype (TableauColumnSummary State Tape Arrow M) := by
  letI : Fintype (HigherBlockTableauTile State Tape Arrow M) := Fintype.ofFinite _
  let e : TableauColumnSummary State Tape Arrow M ≃
      Option (HigherBlockTableauTile State Tape Arrow M) ×
      Option (HigherBlockTableauTile State Tape Arrow M) ×
      Option (HigherBlockTableauTile State Tape Arrow M) :=
    { toFun := fun s => (s.bottom, s.top, s.visibleHead)
      invFun := fun s => ⟨s.1, s.2.1, s.2.2⟩
      left_inv := by intro s; cases s; rfl
      right_inv := by intro s; rcases s with ⟨a,b,c⟩; rfl }
  exact Fintype.ofEquiv _ e.symm

def columnSummary {h : ℕ} (c : WangColumn (TileMap M) h) :
    TableauColumnSummary State Tape Arrow M where
  bottom := if hh : 0 < h then some (c.1 ⟨0, hh⟩) else none
  top := if hh : 0 < h then some (c.1 ⟨h - 1, by omega⟩) else none
  visibleHead := (visibleHeadIndex M c).map fun j => c.1 j

theorem old_eq_of_east_eq {h : ℕ} (c d : WangColumn (TileMap M) h)
    (heast : c.eastWord (TileMap M) = d.eastWord (TileMap M)) (j : Fin h) :
    (c.1 j).1.old = (d.1 j).1.old := by
  exact congrFun heast j

theorem bottom_eq_of_summary_eq {h : ℕ} (c d : WangColumn (TileMap M) h)
    (hs : columnSummary M c = columnSummary M d) (hh : 0 < h) :
    c.1 ⟨0, hh⟩ = d.1 ⟨0, hh⟩ := by
  have hb := congrArg TableauColumnSummary.bottom hs
  have hb' : some (c.1 ⟨0, hh⟩) = some (d.1 ⟨0, hh⟩) := by
    simpa [columnSummary, hh] using hb
  exact Option.some.inj hb'

theorem top_eq_of_summary_eq {h : ℕ} (c d : WangColumn (TileMap M) h)
    (hs : columnSummary M c = columnSummary M d) (hh : 0 < h) :
    c.1 ⟨h - 1, by omega⟩ = d.1 ⟨h - 1, by omega⟩ := by
  have ht := congrArg TableauColumnSummary.top hs
  have ht' : some (c.1 ⟨h - 1, by omega⟩) = some (d.1 ⟨h - 1, by omega⟩) := by
    simpa [columnSummary, hh] using ht
  exact Option.some.inj ht'

theorem head_tile_eq_of_summary_eq {h : ℕ} (c d : WangColumn (TileMap M) h)
    (heast : c.eastWord (TileMap M) = d.eastWord (TileMap M))
    (hs : columnSummary M c = columnSummary M d)
    (j : Fin h) (hj : (c.1 j).1.old.center.isHead = true) : c.1 j = d.1 j := by
  have hold := old_eq_of_east_eq M c d heast j
  have hjd : (d.1 j).1.old.center.isHead = true := by rw [← hold]; exact hj
  have hic := visibleHeadIndex_spec M c hj
  have hid := visibleHeadIndex_spec M d hjd
  have hs' := congrArg TableauColumnSummary.visibleHead hs
  simp [columnSummary, hic, hid] at hs'
  exact hs'

theorem new_center_eq_of_east_summary {h : ℕ}
    (c d : WangColumn (TileMap M) h)
    (heast : c.eastWord (TileMap M) = d.eastWord (TileMap M))
    (hs : columnSummary M c = columnSummary M d) (j : Fin h) :
    (c.1 j).1.new.center = (d.1 j).1.new.center := by
  have hold := old_eq_of_east_eq M c d heast j
  by_cases hc : (c.1 j).1.old.center.isHead = true
  · have ht := head_tile_eq_of_summary_eq M c d heast hs j hc
    exact congrArg (fun u : Tile M => u.1.new.center) ht
  · have hc0 : (c.1 j).1.old.center.isHead = false := by
      cases hz : (c.1 j).1.old.center.isHead <;> simp_all
    by_cases hm : (c.1 j).1.old.minus.isHead = true
    · by_cases hj0 : j.1 = 0
      · have hh : 0 < h := Nat.zero_lt_of_lt j.isLt
        have jeq : j = ⟨0, hh⟩ := Fin.eq_of_val_eq hj0
        have hb := bottom_eq_of_summary_eq M c d hs hh
        exact congrArg (fun u : Tile M => u.1.new.center) (by simpa [jeq] using hb)
      · let jb : Fin h := ⟨j.1 - 1, by omega⟩
        have hjb : jb.1 + 1 < h := by dsimp [jb]; omega
        have heqj : (⟨jb.1 + 1, hjb⟩ : Fin h) = j := by
          apply Fin.ext
          dsimp [jb]
          omega
        have hov := vertical_old_overlap M c jb hjb
        have hheadb : (c.1 jb).1.old.center.isHead = true := by
          rw [hov.1, heqj]
          exact hm
        have htb := head_tile_eq_of_summary_eq M c d heast hs jb hheadb
        have hnew := vertical_new_overlap M c jb hjb
        have hnewd := vertical_new_overlap M d jb hjb
        calc
          (c.1 j).1.new.center = (c.1 jb).1.new.plus := by
            rw [← heqj]
            exact hnew.2.symm
          _ = (d.1 jb).1.new.plus :=
            congrArg (fun u : Tile M => u.1.new.plus) htb
          _ = (d.1 j).1.new.center := by
            rw [← heqj]
            exact hnewd.2
    · have hm0 : (c.1 j).1.old.minus.isHead = false := by
        cases hz : (c.1 j).1.old.minus.isHead <;> simp_all
      by_cases hp : (c.1 j).1.old.plus.isHead = true
      · by_cases hj1 : j.1 + 1 = h
        · have hh : 0 < h := Nat.zero_lt_of_lt j.isLt
          have hval : j.1 = h - 1 := by omega
          have jeq : j = ⟨h - 1, by omega⟩ := Fin.eq_of_val_eq hval
          have ht := top_eq_of_summary_eq M c d hs hh
          exact congrArg (fun u : Tile M => u.1.new.center) (by simpa [jeq] using ht)
        · have hjr : j.1 + 1 < h := by omega
          let jr : Fin h := ⟨j.1 + 1, hjr⟩
          have hov := vertical_old_overlap M c j hjr
          have hheadr : (c.1 jr).1.old.center.isHead = true := by
            rw [← hov.2]
            exact hp
          have htr := head_tile_eq_of_summary_eq M c d heast hs jr hheadr
          have hnew := vertical_new_overlap M c j hjr
          have hnewd := vertical_new_overlap M d j hjr
          calc
            (c.1 j).1.new.center = (c.1 jr).1.new.minus := hnew.1
            _ = (d.1 jr).1.new.minus :=
              congrArg (fun u : Tile M => u.1.new.minus) htr
            _ = (d.1 j).1.new.center := hnewd.1.symm
      · have hp0 : (c.1 j).1.old.plus.isHead = false := by
          cases hz : (c.1 j).1.old.plus.isHead <;> simp_all
        have hdc : (d.1 j).1.old = (c.1 j).1.old := hold.symm
        calc
          (c.1 j).1.new.center = (c.1 j).1.old.center :=
            new_center_eq_old_of_no_head M (c.1 j) hm0 hc0 hp0
          _ = (d.1 j).1.old.center := congrArg CellTriple.center hold
          _ = (d.1 j).1.new.center := by
            symm
            apply new_center_eq_old_of_no_head M (d.1 j)
            · simpa [hdc] using hm0
            · simpa [hdc] using hc0
            · simpa [hdc] using hp0

theorem new_triple_eq_of_east_summary {h : ℕ}
    (c d : WangColumn (TileMap M) h)
    (heast : c.eastWord (TileMap M) = d.eastWord (TileMap M))
    (hs : columnSummary M c = columnSummary M d) (j : Fin h) :
    (c.1 j).1.new = (d.1 j).1.new := by
  apply CellTriple.ext
  · by_cases hj0 : j.1 = 0
    · have hh : 0 < h := Nat.zero_lt_of_lt j.isLt
      have jeq : j = ⟨0, hh⟩ := Fin.eq_of_val_eq hj0
      have hb := bottom_eq_of_summary_eq M c d hs hh
      exact congrArg (fun u : Tile M => u.1.new.minus) (by simpa [jeq] using hb)
    · let jb : Fin h := ⟨j.1 - 1, by omega⟩
      have hjb : jb.1 + 1 < h := by dsimp [jb]; omega
      have heqj : (⟨jb.1 + 1, hjb⟩ : Fin h) = j := by
        apply Fin.ext
        dsimp [jb]
        omega
      have hc := new_center_eq_of_east_summary M c d heast hs jb
      have hov := vertical_new_overlap M c jb hjb
      have hovd := vertical_new_overlap M d jb hjb
      calc
        (c.1 j).1.new.minus = (c.1 jb).1.new.center := by rw [← heqj]; exact hov.1.symm
        _ = (d.1 jb).1.new.center := hc
        _ = (d.1 j).1.new.minus := by rw [← heqj]; exact hovd.1
  · exact new_center_eq_of_east_summary M c d heast hs j
  · by_cases hj1 : j.1 + 1 = h
    · have hh : 0 < h := Nat.zero_lt_of_lt j.isLt
      have hval : j.1 = h - 1 := by omega
      have jeq : j = ⟨h - 1, by omega⟩ := Fin.eq_of_val_eq hval
      have ht := top_eq_of_summary_eq M c d hs hh
      exact congrArg (fun u : Tile M => u.1.new.plus) (by simpa [jeq] using ht)
    · have hjr : j.1 + 1 < h := by omega
      let jr : Fin h := ⟨j.1 + 1, hjr⟩
      have hc := new_center_eq_of_east_summary M c d heast hs jr
      have hov := vertical_new_overlap M c j hjr
      have hovd := vertical_new_overlap M d j hjr
      calc
        (c.1 j).1.new.plus = (c.1 jr).1.new.center := hov.2
        _ = (d.1 jr).1.new.center := hc
        _ = (d.1 j).1.new.plus := hovd.2.symm

theorem old_bits_eq_of_east_summary {h : ℕ}
    (c d : WangColumn (TileMap M) h)
    (heast : c.eastWord (TileMap M) = d.eastWord (TileMap M))
    (hs : columnSummary M c = columnSummary M d) (j : Fin h) :
    (c.1 j).1.oldMinusBit = (d.1 j).1.oldMinusBit ∧
      (c.1 j).1.oldPlusBit = (d.1 j).1.oldPlusBit := by
  induction k : j.1 using Nat.strong_induction_on generalizing j with
  | h k ih =>
      have hminus : (c.1 j).1.oldMinusBit = (d.1 j).1.oldMinusBit := by
        by_cases hj0 : j.1 = 0
        · have hh : 0 < h := Nat.zero_lt_of_lt j.isLt
          have jeq : j = ⟨0, hh⟩ := Fin.eq_of_val_eq hj0
          have hb := bottom_eq_of_summary_eq M c d hs hh
          exact congrArg (fun u : Tile M => u.1.oldMinusBit) (by simpa [jeq] using hb)
        · let jb : Fin h := ⟨j.1 - 1, by omega⟩
          have hjb : jb.1 + 1 < h := by dsimp [jb]; omega
          have heqj : (⟨jb.1 + 1, hjb⟩ : Fin h) = j := by
            apply Fin.ext
            dsimp [jb]
            omega
          have hp := (ih jb.1 (by dsimp [jb]; omega) jb rfl).2
          have hv := (vertical_bits_tokens M c jb hjb).1
          have hvd := (vertical_bits_tokens M d jb hjb).1
          calc
            (c.1 j).1.oldMinusBit = (c.1 jb).1.oldPlusBit := by
              rw [← heqj]
              exact hv.symm
            _ = (d.1 jb).1.oldPlusBit := hp
            _ = (d.1 j).1.oldMinusBit := by rw [← heqj]; exact hvd
      refine ⟨hminus, ?_⟩
      have hold := old_eq_of_east_eq M c d heast j
      exact tableauOrdBit_right_unique
        (c.1 j).2.2.2.1
        (hminus ▸ (by simpa [hold] using (d.1 j).2.2.2.1))

theorem new_bits_eq_of_east_summary {h : ℕ}
    (c d : WangColumn (TileMap M) h)
    (heast : c.eastWord (TileMap M) = d.eastWord (TileMap M))
    (hs : columnSummary M c = columnSummary M d) (j : Fin h) :
    (c.1 j).1.newMinusBit = (d.1 j).1.newMinusBit ∧
      (c.1 j).1.newPlusBit = (d.1 j).1.newPlusBit := by
  induction k : j.1 using Nat.strong_induction_on generalizing j with
  | h k ih =>
      have hminus : (c.1 j).1.newMinusBit = (d.1 j).1.newMinusBit := by
        by_cases hj0 : j.1 = 0
        · have hh : 0 < h := Nat.zero_lt_of_lt j.isLt
          have jeq : j = ⟨0, hh⟩ := Fin.eq_of_val_eq hj0
          have hb := bottom_eq_of_summary_eq M c d hs hh
          exact congrArg (fun u : Tile M => u.1.newMinusBit) (by simpa [jeq] using hb)
        · let jb : Fin h := ⟨j.1 - 1, by omega⟩
          have hjb : jb.1 + 1 < h := by dsimp [jb]; omega
          have heqj : (⟨jb.1 + 1, hjb⟩ : Fin h) = j := by
            apply Fin.ext
            dsimp [jb]
            omega
          have hp := (ih jb.1 (by dsimp [jb]; omega) jb rfl).2
          have hv := (vertical_bits_tokens M c jb hjb).2.1
          have hvd := (vertical_bits_tokens M d jb hjb).2.1
          calc
            (c.1 j).1.newMinusBit = (c.1 jb).1.newPlusBit := by
              rw [← heqj]
              exact hv.symm
            _ = (d.1 jb).1.newPlusBit := hp
            _ = (d.1 j).1.newMinusBit := by rw [← heqj]; exact hvd
      refine ⟨hminus, ?_⟩
      have hnew := new_triple_eq_of_east_summary M c d heast hs j
      exact tableauOrdBit_right_unique
        (c.1 j).2.2.2.2.1
        (hminus ▸ (by simpa [hnew] using (d.1 j).2.2.2.2.1))

theorem north_token_eq_of_east_summary {h : ℕ}
    (c d : WangColumn (TileMap M) h)
    (heast : c.eastWord (TileMap M) = d.eastWord (TileMap M))
    (hs : columnSummary M c = columnSummary M d) (j : Fin h) :
    (c.1 j).1.northToken = (d.1 j).1.northToken := by
  have hold := old_eq_of_east_eq M c d heast j
  by_cases hc : (c.1 j).1.old.center.isHead = true
  · have ht := head_tile_eq_of_summary_eq M c d heast hs j hc
    exact congrArg (fun u : Tile M => u.1.northToken) ht
  · have hc0 : (c.1 j).1.old.center.isHead = false := by
      cases hz : (c.1 j).1.old.center.isHead <;> simp_all
    have hcd0 : (d.1 j).1.old.center.isHead = false := by simpa [← hold] using hc0
    exact (northToken_none_of_center_plain M (c.1 j) hc0).trans
      (northToken_none_of_center_plain M (d.1 j) hcd0).symm

theorem south_token_eq_of_east_summary {h : ℕ}
    (c d : WangColumn (TileMap M) h)
    (heast : c.eastWord (TileMap M) = d.eastWord (TileMap M))
    (hs : columnSummary M c = columnSummary M d) (j : Fin h) :
    (c.1 j).1.southToken = (d.1 j).1.southToken := by
  by_cases hj0 : j.1 = 0
  · have hh : 0 < h := Nat.zero_lt_of_lt j.isLt
    have jeq : j = ⟨0, hh⟩ := Fin.eq_of_val_eq hj0
    have hb := bottom_eq_of_summary_eq M c d hs hh
    exact congrArg (fun u : Tile M => u.1.southToken) (by simpa [jeq] using hb)
  · let jb : Fin h := ⟨j.1 - 1, by omega⟩
    have hjb : jb.1 + 1 < h := by dsimp [jb]; omega
    have heqj : (⟨jb.1 + 1, hjb⟩ : Fin h) = j := by
      apply Fin.ext
      dsimp [jb]
      omega
    have hn := north_token_eq_of_east_summary M c d heast hs jb
    have hv := (vertical_bits_tokens M c jb hjb).2.2
    have hvd := (vertical_bits_tokens M d jb hjb).2.2
    calc
      (c.1 j).1.southToken = (c.1 jb).1.northToken := by rw [← heqj]; exact hv.symm
      _ = (d.1 jb).1.northToken := hn
      _ = (d.1 j).1.southToken := by rw [← heqj]; exact hvd

theorem columnSummary_injective_on_east {h : ℕ}
    (c d : WangColumn (TileMap M) h)
    (heast : c.eastWord (TileMap M) = d.eastWord (TileMap M))
    (hs : columnSummary M c = columnSummary M d) : c = d := by
  apply Subtype.ext
  funext j
  apply Subtype.ext
  apply TableauRaw.ext
  · exact old_eq_of_east_eq M c d heast j
  · exact new_triple_eq_of_east_summary M c d heast hs j
  · exact (old_bits_eq_of_east_summary M c d heast hs j).1
  · exact (old_bits_eq_of_east_summary M c d heast hs j).2
  · exact (new_bits_eq_of_east_summary M c d heast hs j).1
  · exact (new_bits_eq_of_east_summary M c d heast hs j).2
  · exact south_token_eq_of_east_summary M c d heast hs j
  · exact north_token_eq_of_east_summary M c d heast hs j

def tableauColumnCode : TableauColumnSummary State Tape Arrow M ≃
    Fin (Fintype.card (TableauColumnSummary State Tape Arrow M)) :=
  Fintype.equivFin _

/-- Kernel-checked clause (D): a prescribed east word has a constant number
of vertically matching higher-block columns, independently of the height. -/
def constantEastColumnBound :
    ConstantEastColumnBound
      (Fintype.card (TableauColumnSummary State Tape Arrow M)) (TileMap M) where
  code := fun _ c => tableauColumnCode M (columnSummary M c)
  code_injective_on_east := by
    intro h c d heast hcode
    apply columnSummary_injective_on_east M c d heast
    exact (tableauColumnCode M).injective hcode

/-- The concrete higher-block tableau has a fixed arbitrary-rectangle
perimeter base. -/
def rectangleBound : WangRectangleBound
    ((Fintype.card (TableauHorizontalColour State Tape) + 1) *
      (Fintype.card (TableauColumnSummary State Tape Arrow M) + 1))
    (TileMap M) :=
  rectangleBoundOfConstantEastColumns (TileMap M) (constantEastColumnBound M)

end HigherBlockTableau

end
end PakFixedPolyomino
