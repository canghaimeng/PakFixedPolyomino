import PakFixedPolyomino.PakScannerTerminal
import PakFixedPolyomino.PakMStarCouplingCorrectness
import PakFixedPolyomino.PakFullFrameRippleClassify
import PakFixedPolyomino.PakFullFrameTableauReadback

/-! # Baseline scanner paths -/

namespace PakFixedPolyomino.PakScannerBaselineAutomaton

open ConcretePakScanner PakMStarCouplingCorrectness PakFullFrameRippleClassify
  PakFullFrameTableauReadback

structure ScannerPath (n : ℕ) where
  pos : 0 < n
  states : Fin (n + 1) → ConcretePakScanner.State
  bottom : states ⟨0, Nat.zero_lt_succ _⟩ = PakCouplingGenerated.scannerBottom
  top : states ⟨n, Nat.lt_succ_self _⟩ = ConcretePakScanner.topNorth
  legal : ∀ j : Fin n,
    ConcretePakScanner.LegalScan (states ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
      (states ⟨j.1 + 1, by omega⟩) (n.testBit j.1)

def ScannerPath.column {n : ℕ} (P : ScannerPath n) (j : Fin n) :
    ConcretePakScanner.Tile := some
      (P.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩,
       P.states ⟨j.1 + 1, by omega⟩)

def ScannerPath.toEastTiling {n : ℕ} (P : ScannerPath n) :
    OpenWangTiling (scannerTile (S := ConcretePakScanner.State)) n n :=
  PakCanonicalScanner.eastColumnTiling P.pos P.column (by
    intro j hj
    rfl)

theorem ScannerPath.toEastTiling_east {n : ℕ} (P : ScannerPath n) (j : Fin n) :
    P.toEastTiling.1 ⟨n - 1, by have := P.pos; omega⟩ j = P.column j := by
  have hn : n - 1 + 1 = n := by have := P.pos; omega
  simp [ScannerPath.toEastTiling, PakCanonicalScanner.eastColumnTiling,
    PakCanonicalScanner.eastColumnCell, hn]

theorem ScannerPath.toEastTiling_nonEast {n : ℕ} (P : ScannerPath n)
    (i : Fin n) (j : Fin n) (hi : i.1 + 1 < n) :
    P.toEastTiling.1 i j = none := by
  simp [ScannerPath.toEastTiling, PakCanonicalScanner.eastColumnTiling,
    PakCanonicalScanner.eastColumnCell, Nat.ne_of_lt hi]

/-- A scanner tiling together with its exact east-column path readback. -/
structure ScannerColumnReadback (n : ℕ) where
  path : ScannerPath n
  tiling : OpenWangTiling (scannerTile (S := ConcretePakScanner.State)) n n
  east : ∀ j : Fin n, tiling.1 ⟨n - 1, by have := path.pos; omega⟩ j = path.column j
  nonEast : ∀ (i : Fin n) (j : Fin n), i.1 + 1 < n → tiling.1 i j = none

def ScannerColumnReadback.canonical {n : ℕ} (P : ScannerPath n) :
    ScannerColumnReadback n where
  path := P
  tiling := P.toEastTiling
  east := P.toEastTiling_east
  nonEast := P.toEastTiling_nonEast

theorem ScannerColumnReadback.tiling_eq_pathTiling {n : ℕ}
    (R : ScannerColumnReadback n) : R.tiling = R.path.toEastTiling := by
  apply Subtype.ext
  funext i j
  by_cases hi : i.1 + 1 = n
  · have hilast : i = ⟨n - 1, by have := R.path.pos; omega⟩ := by
      apply Fin.ext
      change i.1 = n - 1
      have := R.path.pos
      omega
    rw [hilast, R.east, R.path.toEastTiling_east]
  · have hilt : i.1 + 1 < n := by omega
    rw [R.nonEast i j hilt, R.path.toEastTiling_nonEast i j hilt]

def isHeadBuffer : ConcretePakScanner.Buffer → Bool
  | .headZero | .headOne => true
  | _ => false

theorem isHeadBuffer_iff_bufferCell_isHead (b : ConcretePakScanner.Buffer) :
    isHeadBuffer b = true ↔
      (PakCouplingGenerated.bufferCell MStarULogAssembly.boundaryData b).isHead = true := by
  cases b <;> rfl

def ScannerPath.headCount {n : ℕ} (P : ScannerPath n) : ℕ :=
  ∑ j : Fin n,
    if isHeadBuffer (P.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩).centre then 1 else 0

abbrev HeadedScannerPath (n : ℕ) := {P : ScannerPath n // P.headCount = 1}

abbrev SlotZeroScannerPaths (n : ℕ) := HeadedScannerPath n

instance scannerPathFinite (n : ℕ) : Finite (ScannerPath n) :=
  Finite.of_injective (fun P : ScannerPath n => P.states) (by
    intro P Q h
    cases P
    cases Q
    cases h
    rfl)

noncomputable instance scannerPathFintype (n : ℕ) : Fintype (ScannerPath n) :=
  Fintype.ofFinite _

noncomputable instance headedScannerPathFintype (n : ℕ) :
    Fintype (HeadedScannerPath n) := Fintype.ofFinite _

noncomputable def baselineCount (n : ℕ) : ℕ :=
  Fintype.card (SlotZeroScannerPaths n)

/-- The finite successor set used by a bottom-to-top scanner DP layer. -/
def scannerSuccessors (bit : Bool) (s : ConcretePakScanner.State) :
    Finset ConcretePakScanner.State :=
  Finset.univ.filter (fun t => decide (ConcretePakScanner.LegalScan s t bit))

theorem mem_scannerSuccessors_iff (bit : Bool) (s t : ConcretePakScanner.State) :
    t ∈ scannerSuccessors bit s ↔ ConcretePakScanner.LegalScan s t bit := by
  simp [scannerSuccessors]

/-- One finite transfer layer on state-count vectors.  It is the direct
dynamic-programming interface for scanner-path enumeration. -/
def scannerTransfer (bit : Bool)
    (v : ConcretePakScanner.State → ℕ) : ConcretePakScanner.State → ℕ :=
  fun t => ∑ s : ConcretePakScanner.State,
    if ConcretePakScanner.LegalScan s t bit then v s else 0

def scannerDP (n : ℕ) : Fin (n + 1) → ConcretePakScanner.State → ℕ :=
  fun k => Nat.rec (fun s => if s = PakCouplingGenerated.scannerBottom then 1 else 0)
    (fun i v => scannerTransfer (n.testBit i) v) k.1

theorem scannerTransfer_zero (bit : Bool) :
    scannerTransfer bit (fun _ => 0) = fun _ => 0 := by
  funext t
  simp [scannerTransfer]

noncomputable def FullFrame.eastPair {n : ℕ} (F : FullFrame n n) (j : Fin n) :
    ConcretePakScanner.State × ConcretePakScanner.State :=
  let hex := FullFrame.east_emits_tableau_window F j
  let s := Classical.choose hex
  let t := Classical.choose (Classical.choose_spec hex)
  (s, t)

theorem FullFrame.eastPair_spec {n : ℕ} (F : FullFrame n n) (j : Fin n) :
    scannerAt F.tiling (eastIndex F.width_pos) j = some (eastPair F j) := by
  unfold eastPair
  dsimp only
  exact (Classical.choose_spec
    (Classical.choose_spec (FullFrame.east_emits_tableau_window F j))).1

theorem FullFrame.eastPair_overlap {n : ℕ} (F : FullFrame n n)
    (j : Fin n) (hj : j.1 + 1 < n) :
    (eastPair F j).2 = (eastPair F ⟨j.1 + 1, hj⟩).1 := by
  have hmatch := (scannerProjection F.tiling).2.2 (eastIndex F.width_pos) j hj
  have hleft := eastPair_spec F j
  have hright := eastPair_spec F ⟨j.1 + 1, hj⟩
  change (scannerTile (scannerAt F.tiling (eastIndex F.width_pos) j)).north =
    (scannerTile (scannerAt F.tiling (eastIndex F.width_pos) ⟨j.1 + 1, hj⟩)).south at hmatch
  rw [hleft, hright] at hmatch
  simpa [scannerTile] using hmatch

noncomputable def FullFrame.eastScannerStates {n : ℕ} (F : FullFrame n n) :
    Fin (n + 1) → ConcretePakScanner.State := fun k =>
  if hk : k.1 < n then (eastPair F ⟨k.1, hk⟩).1
  else (eastPair F ⟨n - 1, by have := F.width_pos; omega⟩).2

theorem FullFrame.eastPair_eq_states {n : ℕ} (F : FullFrame n n) (j : Fin n) :
    eastPair F j =
      (eastScannerStates F ⟨j.1, Nat.lt_succ_of_lt j.2⟩,
       eastScannerStates F ⟨j.1 + 1, by omega⟩) := by
  apply Prod.ext
  · simp [eastScannerStates, j.2]
  · by_cases hj : j.1 + 1 < n
    · rw [eastPair_overlap F j hj]
      simp [eastScannerStates, hj]
    · have hlast : j.1 + 1 = n := by omega
      let last : Fin n := ⟨n - 1, Nat.pred_lt (Nat.ne_of_gt F.width_pos)⟩
      have hjlast : j = last := Fin.ext (by
        dsimp [last]
        omega)
      have heq := congrArg (fun k : Fin n => (eastPair F k).2) hjlast
      simpa [eastScannerStates, hlast, last] using heq

theorem FullFrame.size_ge_two {n : ℕ} (F : FullFrame n n) : 2 ≤ n :=
  F.height_ge_two

theorem FullFrame.east_top_second {n : ℕ} (F : FullFrame n n) :
    (eastPair F ⟨n - 1, Nat.pred_lt (Nat.ne_of_gt F.height_pos)⟩).2 =
      ConcretePakScanner.topNorth := by
  let j : Fin n := ⟨n - 1, Nat.pred_lt (Nat.ne_of_gt F.height_pos)⟩
  have heast := F.boundary.2.1 j
  have hnorth0 := F.boundary.2.2.2 (eastIndex F.width_pos)
  have hnorth : (ampAt F.tiling (eastIndex F.width_pos) j).1.northActive = true := by
    simpa [j, northIndex] using hnorth0
  have hsouth : (ampAt F.tiling (eastIndex F.width_pos) j).1.southActive = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hs
    have hbottom := southActive_on_south_boundary F.tiling
      (eastIndex F.width_pos) j hs
    have hsize := FullFrame.height_ge_two F
    dsimp [j] at hbottom
    omega
  have hactivity := ((coupledAt_iff F.tiling (eastIndex F.width_pos) j).2.1 heast).1
  change ConcretePakScanner.ActivityCoupledStep
    (ampAt F.tiling (eastIndex F.width_pos) j).1.southActive
    (ampAt F.tiling (eastIndex F.width_pos) j).1.northActive
    (scannerAt F.tiling (eastIndex F.width_pos) j) _ at hactivity
  rw [hsouth, hnorth, eastPair_spec F j] at hactivity
  have hcap := ConcretePakScanner.activityCoupled_top_forces_cap
    (some (eastPair F j)) _ (eastPair F j).1 (eastPair F j).2 rfl hactivity
  exact hcap.2

theorem FullFrame.east_ripple_bit {n : ℕ} (F : FullFrame n n) (j : Fin n) :
    Bool.xor (rippleAt F.tiling (eastIndex F.width_pos) j).1
      (rippleAt F.tiling (eastIndex F.width_pos) j).2 = n.testBit j.1 := by
  have hr := congrFun (congrFun
    (congrArg Subtype.val (FullFrame.rippleProjection_eq_canonical F))
    (eastIndex F.width_pos)) j
  change (rippleTile (rippleAt F.tiling (eastIndex F.width_pos) j)).east = _
  rw [show rippleAt F.tiling (eastIndex F.width_pos) j =
      (PakRippleCanonical.canonicalTiling n n).1 (eastIndex F.width_pos) j by
        simpa only [rippleProjection_cell] using hr]
  exact PakRippleCanonical.canonicalTiling_east n n F.width_pos j

/-- Every full frame determines the literal bottom-to-top scanner path on its
east boundary.  The bit label is not an extra hypothesis: it is read from the
canonical ripple projection forced by the full-frame boundary. -/
noncomputable def FullFrame.toScannerPath {n : ℕ} (F : FullFrame n n) :
    ScannerPath n where
  pos := F.height_pos
  states := eastScannerStates F
  bottom := by
    have hp := eastPair_spec F ⟨0, F.height_pos⟩
    rcases FullFrame.east_bottom_scanner F with ⟨t, hb⟩
    have hpair : eastPair F ⟨0, F.height_pos⟩ =
        (PakCouplingGenerated.scannerBottom, t) :=
      Option.some.inj (hp.symm.trans hb)
    simpa [eastScannerStates, F.height_pos] using congrArg Prod.fst hpair
  top := by
    simp [eastScannerStates, FullFrame.east_top_second F]
  legal := by
    intro j
    have hactivity :=
      ((coupledAt_iff F.tiling (eastIndex F.width_pos) j).2.1
        (F.boundary.2.1 j)).1
    change ConcretePakScanner.ActivityCoupledStep
      (ampAt F.tiling (eastIndex F.width_pos) j).1.southActive
      (ampAt F.tiling (eastIndex F.width_pos) j).1.northActive
      (scannerAt F.tiling (eastIndex F.width_pos) j)
      (Bool.xor (rippleAt F.tiling (eastIndex F.width_pos) j).1
        (rippleAt F.tiling (eastIndex F.width_pos) j).2) at hactivity
    rw [eastPair_spec F j, east_ripple_bit F j] at hactivity
    rcases hactivity with ⟨s, t, hpair, hlegal, _⟩
    have hp :
        (eastScannerStates F ⟨j.1, Nat.lt_succ_of_lt j.2⟩,
          eastScannerStates F ⟨j.1 + 1, by omega⟩) = (s, t) := by
      rw [← eastPair_eq_states F j]
      exact Option.some.inj hpair
    cases hp
    exact hlegal

noncomputable def FullFrame.scannerColumnReadback {n : ℕ} (F : FullFrame n n) :
    ScannerColumnReadback n where
  path := FullFrame.toScannerPath F
  tiling := scannerProjection F.tiling
  east := by
    intro j
    have hi : (⟨n - 1, by have := F.height_pos; omega⟩ : Fin n) =
        eastIndex F.width_pos := Fin.ext (by simp [eastIndex])
    rw [hi]
    rw [scannerProjection_cell, eastPair_spec F j]
    exact congrArg Option.some (eastPair_eq_states F j)
  nonEast := by
    intro i j hi
    exact scannerAt_interior_idle F.tiling i j hi

theorem FullFrame.toScannerPath_state_head_iff {n : ℕ} (F : FullFrame n n)
    (j : Fin n) :
    isHeadBuffer
        (((FullFrame.toScannerPath F).states
          ⟨j.1, Nat.lt_succ_of_lt j.2⟩).centre) = true ↔
      ((tableauAt F.tiling (eastIndex F.width_pos) j).1.old.center.isHead = true) := by
  rcases F.east_emits_tableau_window j with ⟨s, t, hscan, hold⟩
  have hpair : eastPair F j = (s, t) :=
    Option.some.inj ((eastPair_spec F j).symm.trans hscan)
  have hstates := eastPair_eq_states F j
  have hs : eastScannerStates F ⟨j.1, Nat.lt_succ_of_lt j.2⟩ = s :=
    congrArg Prod.fst (hstates.symm.trans hpair)
  change isHeadBuffer
      (eastScannerStates F ⟨j.1, Nat.lt_succ_of_lt j.2⟩).centre = true ↔ _
  rw [hs]
  have hcenter := congrArg CellTriple.center hold
  rw [hcenter]
  exact isHeadBuffer_iff_bufferCell_isHead s.centre

theorem FullFrame.toScannerPath_headCount {n : ℕ} (F : FullFrame n n) :
    (FullFrame.toScannerPath F).headCount = 1 := by
  classical
  let R :=
    PakFixedPolyomino.PakFullFrameTableauReadback.FullFrame.tableau_column_readback
      F (eastIndex F.width_pos)
  unfold ScannerPath.headCount
  rw [Finset.sum_eq_single R.head]
  · have hhead : isHeadBuffer
        (((FullFrame.toScannerPath F).states
          ⟨R.head.1, Nat.lt_succ_of_lt R.head.2⟩).centre) = true :=
      (FullFrame.toScannerPath_state_head_iff F R.head).2 R.head_is_head
    simp [hhead]
  · intro j _ hj
    have hnot : isHeadBuffer
        (((FullFrame.toScannerPath F).states
          ⟨j.1, Nat.lt_succ_of_lt j.2⟩).centre) ≠ true := by
      intro hhead
      exact hj (R.head_unique j
        ((FullFrame.toScannerPath_state_head_iff F j).1 hhead))
    simp [hnot]
  · simp

noncomputable def FullFrame.toHeadedScannerPath {n : ℕ} (F : FullFrame n n) :
    HeadedScannerPath n :=
  ⟨FullFrame.toScannerPath F, FullFrame.toScannerPath_headCount F⟩

end PakFixedPolyomino.PakScannerBaselineAutomaton
