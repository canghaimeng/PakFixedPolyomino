import PakFixedPolyomino.ULogSourceObliviousScanExecution
import Mathlib.Tactic

/-!
# Literal update/return sweeps on a delimited oblivious window

Physical layout: left blank at coordinate `0`, encoded marked cells at `1`
through `W := w.encode.length`, right blank at `W+1`.  The overlay is an
explicit finite list; coordinates outside `[0, W+1]` read an exterior
function.
-/

namespace PakFixedPolyomino.ULogSourceObliviousUpdateExecution

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics
open ULogCompiler
open ULogSourceOneHotReader (zero one tapeOfBit)
open ULogSourceOneHotBlocks (encodeOneHot)
open ULogSourceObliviousWindow
open ULogSourceObliviousScanProgram
open ULogSourceObliviousScanExecution

variable {ns nt : ℕ}

abbrev Phys := Fin 3
abbrev physBlank : Phys := ULogSourceOneHotReader.blank

abbrev ScanArrow (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt) :=
  Arrow (ULogSourceObliviousScanProgram.program p hnt blank)

abbrev ScanCfg (ns nt : ℕ) :=
  FiniteOneTapeSemantics.Config (State ns nt) Phys

def windowWidth {nt : ℕ} (w : LogicalWindow nt) : ℕ := w.encode.length

theorem windowWidth_eq {nt : ℕ} (w : LogicalWindow nt) :
    windowWidth w = w.cells.length * (nt + 1) := by
  simp [windowWidth]

theorem window_cells_pos {nt : ℕ} (w : LogicalWindow nt) :
    0 < w.cells.length := by
  have := w.head.isLt
  omega

theorem windowWidth_pos {nt : ℕ} (w : LogicalWindow nt) :
    0 < windowWidth w := by
  have hcells := window_cells_pos w
  have hnt : 0 < nt + 1 := Nat.succ_pos _
  simpa [windowWidth] using Nat.mul_pos hcells hnt

/-! ## Finite-list overlay -/

def overlayTape (cells : List Phys) (exterior : Int → Phys) : Int → Phys :=
  fun z =>
    if hz : 0 ≤ z then
      if hn : z.toNat < cells.length then cells[z.toNat]
      else exterior z
    else exterior z

def delimitedCells {nt : ℕ} (w : LogicalWindow nt) : List Phys :=
  physBlank :: (w.encode ++ [physBlank])

@[simp] theorem delimitedCells_length {nt : ℕ} (w : LogicalWindow nt) :
    (delimitedCells w).length = windowWidth w + 2 := by
  simp [delimitedCells, windowWidth]

def windowTape {nt : ℕ} (w : LogicalWindow nt) (exterior : Int → Phys) :
    Int → Phys :=
  overlayTape (delimitedCells w) exterior

theorem overlayTape_ofNat (cells : List Phys) (exterior : Int → Phys)
    (i : ℕ) (hi : i < cells.length) :
    overlayTape cells exterior (i : Int) = cells[i] := by
  unfold overlayTape
  have hnn : 0 ≤ (i : Int) := Int.natCast_nonneg i
  have hto : (i : Int).toNat = i := Int.toNat_natCast i
  simp [hnn, hto, hi]

theorem overlayTape_neg (cells : List Phys) (exterior : Int → Phys)
    (z : Int) (hz : z < 0) :
    overlayTape cells exterior z = exterior z := by
  unfold overlayTape
  have : ¬ 0 ≤ z := not_le.mpr hz
  simp [this]

theorem overlayTape_ge (cells : List Phys) (exterior : Int → Phys)
    (z : Int) (hz : 0 ≤ z) (hge : cells.length ≤ z.toNat) :
    overlayTape cells exterior z = exterior z := by
  unfold overlayTape
  simp [hz, Nat.not_lt.mpr hge]

theorem overlayTape_update (cells : List Phys) (exterior : Int → Phys)
    (i : ℕ) (hi : i < cells.length) (x : Phys) :
    Function.update (overlayTape cells exterior) (i : Int) x =
      overlayTape (cells.set i x) exterior := by
  funext z
  unfold Function.update overlayTape
  have hlen : (cells.set i x).length = cells.length := by simp
  by_cases hzi : z = (i : Int)
  · subst z
    have hnn : 0 ≤ (i : Int) := Int.natCast_nonneg i
    have hto : (i : Int).toNat = i := Int.toNat_natCast i
    simp [hnn, hto, hi, hlen]
  · by_cases hz : 0 ≤ z
    · simp [hzi, hz, hlen]
      split_ifs with hzlt
      · have hneNat : z.toNat ≠ i := by
          intro h
          apply hzi
          have hz' : z = (z.toNat : Int) := (Int.toNat_of_nonneg hz).symm
          simpa [h] using hz'
        simp [List.getElem_set_ne (Ne.symm hneNat)]
      · rfl
    · simp [hzi, hz]

theorem writtenTape_id {ns nt : ℕ} (c : ScanCfg ns nt) :
    FiniteOneTapeSemantics.writtenTape c (c.tape c.head) = c.tape := by
  funext z
  by_cases hz : z = c.head
  · subst z
    simp [FiniteOneTapeSemantics.writtenTape]
  · simp [FiniteOneTapeSemantics.writtenTape, Function.update_of_ne hz]

/-! ## Encode cells are physical bits, never blank -/

theorem tapeOfBit_ne_blank (b : Bool) : tapeOfBit b ≠ physBlank := by
  cases b <;> simp [tapeOfBit, zero, one, physBlank, ULogSourceOneHotReader.blank]

theorem validBit_tapeOfBit (b : Bool) :
    ULogSourceObliviousScanProgram.validBit (tapeOfBit b) = true := by
  cases b <;> simp [validBit, tapeOfBit, zero, one]

theorem encodeMarkedCell_mem_tapeOfBit {nt : ℕ} (c : MarkedCell nt)
    {x : Phys} (hx : x ∈ encodeMarkedCell c) : ∃ b, x = tapeOfBit b := by
  unfold encodeMarkedCell at hx
  rw [List.mem_cons] at hx
  cases hx with
  | inl h => exact ⟨c.head, h⟩
  | inr h =>
      rw [List.mem_map] at h
      rcases h with ⟨b, _, rfl⟩
      exact ⟨b, rfl⟩

theorem encodeWindow_mem_tapeOfBit {nt : ℕ} (cells : List (MarkedCell nt))
    {x : Phys} (hx : x ∈ encodeWindow cells) : ∃ b, x = tapeOfBit b := by
  induction cells with
  | nil =>
      simp [encodeWindow] at hx
  | cons c cs ih =>
      simp [encodeWindow, List.flatMap_cons, List.mem_append] at hx
      rcases hx with hx | hx
      · exact encodeMarkedCell_mem_tapeOfBit c hx
      · exact ih (by simpa [encodeWindow] using hx)

theorem encode_mem_tapeOfBit {nt : ℕ} (w : LogicalWindow nt) {x : Phys}
    (hx : x ∈ w.encode) : ∃ b, x = tapeOfBit b :=
  encodeWindow_mem_tapeOfBit w.markedCells (by simpa [LogicalWindow.encode] using hx)

theorem encode_mem_ne_blank {nt : ℕ} (w : LogicalWindow nt) {x : Phys}
    (hx : x ∈ w.encode) : x ≠ physBlank := by
  rcases encode_mem_tapeOfBit w hx with ⟨b, hb⟩
  simpa [hb] using tapeOfBit_ne_blank b

theorem encode_get_ne_blank {nt : ℕ} (w : LogicalWindow nt)
    (i : Fin w.encode.length) : w.encode[i.val] ≠ physBlank :=
  encode_mem_ne_blank w (List.getElem_mem _)

theorem encode_get_validBit {nt : ℕ} (w : LogicalWindow nt)
    (i : Fin w.encode.length) :
    ULogSourceObliviousScanProgram.validBit w.encode[i.val] = true := by
  rcases encode_mem_tapeOfBit w (List.getElem_mem _) with ⟨b, hb⟩
  rw [hb]
  exact validBit_tapeOfBit b

theorem delimitedCells_get_zero {nt : ℕ} (w : LogicalWindow nt) :
    (delimitedCells w)[0] = physBlank := rfl

theorem delimitedCells_get_last {nt : ℕ} (w : LogicalWindow nt) :
    (delimitedCells w)[windowWidth w + 1]'(by
      simp [delimitedCells, windowWidth]) = physBlank := by
  have hW : windowWidth w = w.encode.length := rfl
  simp [delimitedCells, hW, List.getElem_cons_succ, List.getElem_append_right']

theorem delimitedCells_get_encode {nt : ℕ} (w : LogicalWindow nt)
    (i : ℕ) (hi : i < windowWidth w) :
    (delimitedCells w)[i + 1]'(by
      rw [delimitedCells_length]; omega) =
      w.encode[i]'(by exact hi) := by
  have hi' : i < w.encode.length := hi
  simp only [delimitedCells, List.getElem_cons_succ]
  exact (List.getElem_append_left' hi' [physBlank]).symm

theorem windowTape_left {nt : ℕ} (w : LogicalWindow nt)
    (exterior : Int → Phys) : windowTape w exterior (0 : Int) = physBlank := by
  have h0 : (0 : Int) = ((0 : ℕ) : Int) := rfl
  rw [windowTape, h0, overlayTape_ofNat (delimitedCells w) exterior 0 (by simp),
    delimitedCells_get_zero]

theorem windowTape_right {nt : ℕ} (w : LogicalWindow nt)
    (exterior : Int → Phys) :
    windowTape w exterior (windowWidth w + 1 : Int) = physBlank := by
  have hlen : windowWidth w + 1 < (delimitedCells w).length := by
    simp [delimitedCells, windowWidth]
  have hcast : (windowWidth w + 1 : Int) = ((windowWidth w + 1 : ℕ) : Int) := by
    simp
  rw [windowTape, hcast, overlayTape_ofNat (delimitedCells w) exterior _ hlen,
    delimitedCells_get_last]

theorem windowTape_encode {nt : ℕ} (w : LogicalWindow nt)
    (exterior : Int → Phys) (i : ℕ) (hi : i < windowWidth w) :
    windowTape w exterior (i + 1 : Int) = w.encode[i]'(by simpa [windowWidth] using hi) := by
  have hlen : i + 1 < (delimitedCells w).length := by
    rw [delimitedCells_length]
    omega
  have hcast : (i + 1 : Int) = ((i + 1 : ℕ) : Int) := by simp
  rw [windowTape, hcast, overlayTape_ofNat (delimitedCells w) exterior _ hlen,
    delimitedCells_get_encode w i hi]
  rfl

theorem windowTape_exterior {nt : ℕ} (w : LogicalWindow nt)
    (exterior : Int → Phys) (z : Int)
    (hz : z < 0 ∨ (windowWidth w + 1 : Int) < z) :
    windowTape w exterior z = exterior z := by
  rcases hz with hz | hz
  · simp [windowTape, overlayTape_neg (delimitedCells w) exterior z hz]
  · have hnn : 0 ≤ z :=
      le_trans (Int.natCast_nonneg (windowWidth w + 1)) (le_of_lt hz)
    have hge : (delimitedCells w).length ≤ z.toNat := by
      have : (windowWidth w + 2 : Int) ≤ z := by omega
      have hcast : windowWidth w + 2 ≤ z.toNat :=
        (Int.le_toNat (n := windowWidth w + 2) hnn).mpr this
      simpa [delimitedCells_length] using hcast
    simp [windowTape, overlayTape_ge (delimitedCells w) exterior z hnn hge]

/-! ## applyAction? on stay / internal right / internal left -/

theorem applyAction?_isSome_of_stay {ns nt : ℕ} (w : LogicalWindow nt)
    (a : BoundedAction ns nt) (h : a.move = .stay) :
    (w.applyAction? a).isSome := by
  rw [LogicalWindow.applyAction_stay w a h]
  simp

theorem applyAction?_right {ns nt : ℕ} (w : LogicalWindow nt)
    (a : BoundedAction ns nt) (h : a.move = .right) :
    (w.applyAction? a).isSome ↔ w.head.val + 1 < w.cells.length := by
  rcases a with ⟨write, target, move⟩
  simp only at h
  subst move
  simp [LogicalWindow.applyAction?, moveIndex]
  split <;> simp_all

theorem applyAction?_left {ns nt : ℕ} (w : LogicalWindow nt)
    (a : BoundedAction ns nt) (h : a.move = .left) :
    (w.applyAction? a).isSome ↔ 0 < w.head.val := by
  rcases a with ⟨write, target, move⟩
  simp only at h
  subst move
  simp [LogicalWindow.applyAction?, moveIndex]
  split <;> simp_all

/-! ## Generic successor on the existing deterministic table -/

def phaseNext (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (c : ScanCfg ns nt) : ScanCfg ns nt :=
  match deterministicAction p hnt blank c.state (c.tape c.head) with
  | none => c
  | some act =>
      { state := act.target
        head := moveHead act.move c.head
        tape := FiniteOneTapeSemantics.writtenTape c act.write }

def phaseArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt) :
    ScanCfg ns nt → ℕ → List (ScanArrow p hnt blank)
  | _, 0 => []
  | c, k + 1 =>
      match hact : deterministicAction p hnt blank c.state (c.tape c.head) with
      | none => []
      | some act =>
          deterministicArrow p hnt blank c.state (c.tape c.head) act hact ::
            phaseArrows p hnt blank (phaseNext p hnt blank c) k

theorem phaseNext_of_some (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (c : ScanCfg ns nt)
    (act : Action (State ns nt) Phys)
    (hact : deterministicAction p hnt blank c.state (c.tape c.head) = some act) :
    phaseNext p hnt blank c =
      { state := act.target
        head := moveHead act.move c.head
        tape := FiniteOneTapeSemantics.writtenTape c act.write } := by
  simp [phaseNext, hact]

theorem phaseNext_step (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (c : ScanCfg ns nt)
    (act : Action (State ns nt) Phys)
    (hact : deterministicAction p hnt blank c.state (c.tape c.head) = some act) :
    FiniteOneTapeSemantics.step
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      c (deterministicArrow p hnt blank c.state (c.tape c.head) act hact) =
        some (phaseNext p hnt blank c) := by
  have hs := deterministicArrow_step p hnt blank c c.state (c.tape c.head)
    act rfl rfl hact
  simpa [phaseNext_of_some p hnt blank c act hact] using hs

theorem phaseArrows_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (c : ScanCfg ns nt) (k : ℕ)
    (hok : ∀ j, j < k →
      (deterministicAction p hnt blank
        ((phaseNext p hnt blank)^[j] c).state
        (((phaseNext p hnt blank)^[j] c).tape
          ((phaseNext p hnt blank)^[j] c).head)).isSome) :
    FiniteOneTapeSemantics.run
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      (phaseArrows p hnt blank c k) c =
        some ((phaseNext p hnt blank)^[k] c) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
      have h0 := hok 0 (Nat.zero_lt_succ k)
      simp only [Function.iterate_zero] at h0
      cases hact : deterministicAction p hnt blank c.state (c.tape c.head) with
      | none =>
          simp [hact] at h0
      | some act =>
          have hok' : ∀ j, j < k →
              (deterministicAction p hnt blank
                ((phaseNext p hnt blank)^[j] (phaseNext p hnt blank c)).state
                (((phaseNext p hnt blank)^[j] (phaseNext p hnt blank c)).tape
                  ((phaseNext p hnt blank)^[j]
                    (phaseNext p hnt blank c)).head)).isSome := by
            intro j hj
            simpa [Function.iterate_succ_apply] using
              hok (j + 1) (Nat.succ_lt_succ hj)
          have hstep := phaseNext_step p hnt blank c act hact
          have harrows :
              phaseArrows p hnt blank c (k + 1) =
                deterministicArrow p hnt blank c.state (c.tape c.head) act hact ::
                  phaseArrows p hnt blank (phaseNext p hnt blank c) k := by
            dsimp [phaseArrows]
            split
            · next hnone => simp [hnone] at hact
            · next act' hact' =>
                obtain rfl := Option.some.inj (hact'.symm.trans hact)
                rfl
          rw [harrows, FiniteOneTapeSemantics.run_cons, hstep, Option.bind_some]
          simpa [Function.iterate_succ_apply] using
            ih (phaseNext p hnt blank c) hok'

theorem phaseArrows_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (c : ScanCfg ns nt) (k : ℕ)
    (hok : ∀ j, j < k →
      (deterministicAction p hnt blank
        ((phaseNext p hnt blank)^[j] c).state
        (((phaseNext p hnt blank)^[j] c).tape
          ((phaseNext p hnt blank)^[j] c).head)).isSome) :
    (phaseArrows p hnt blank c k).length = k := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
      have h0 := hok 0 (Nat.zero_lt_succ k)
      simp only [Function.iterate_zero] at h0
      cases hact : deterministicAction p hnt blank c.state (c.tape c.head) with
      | none =>
          simp [hact] at h0
      | some act =>
          have hok' : ∀ j, j < k →
              (deterministicAction p hnt blank
                ((phaseNext p hnt blank)^[j] (phaseNext p hnt blank c)).state
                (((phaseNext p hnt blank)^[j] (phaseNext p hnt blank c)).tape
                  ((phaseNext p hnt blank)^[j]
                    (phaseNext p hnt blank c)).head)).isSome := by
            intro j hj
            simpa [Function.iterate_succ_apply] using
              hok (j + 1) (Nat.succ_lt_succ hj)
          have harrows :
              phaseArrows p hnt blank c (k + 1) =
                deterministicArrow p hnt blank c.state (c.tape c.head) act hact ::
                  phaseArrows p hnt blank (phaseNext p hnt blank c) k := by
            dsimp [phaseArrows]
            split
            · next hnone => simp [hnone] at hact
            · next act' hact' =>
                obtain rfl := Option.some.inj (hact'.symm.trans hact)
                rfl
          simp [harrows, ih (phaseNext p hnt blank c) hok']

theorem run_append (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (xs ys : List (ScanArrow p hnt blank)) (c : ScanCfg ns nt) :
    FiniteOneTapeSemantics.run
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      (xs ++ ys) c =
      (FiniteOneTapeSemantics.run
        (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
        xs c).bind
        (FiniteOneTapeSemantics.run
          (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
          ys) := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, FiniteOneTapeSemantics.run_cons]
      cases hstep :
        FiniteOneTapeSemantics.step
          (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
          c x with
      | none => simp [hstep]
      | some c' => simp [hstep, ih]

def iteratedHeads (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (c : ScanCfg ns nt) (k : ℕ) : List Int :=
  List.ofFn fun i : Fin k => ((phaseNext p hnt blank)^[i.val + 1] c).head

def pathHeads (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (c : ScanCfg ns nt) (k : ℕ) : List Int :=
  c.head :: iteratedHeads p hnt blank c k

@[simp] theorem pathHeads_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (c : ScanCfg ns nt) (k : ℕ) :
    (pathHeads p hnt blank c k).length = k + 1 := by
  simp [pathHeads, iteratedHeads]

/-! ## Explicit return-to-left arrows -/

def returnLeftInteriorArrow (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (x : Phys)
    (hx : x ≠ ULogSourceOneHotReader.blank) :
    ScanArrow p hnt blank :=
  deterministicArrow p hnt blank (.returnLeft a) x
    ⟨x, .returnLeft a, .left⟩
    (by
      simp [deterministicAction]
      intro hblank
      exact (hx hblank).elim)

theorem returnLeftInteriorArrow_step (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (a : BoundedAction ns nt) (x : Phys)
    (hx : x ≠ ULogSourceOneHotReader.blank) (c : ScanCfg ns nt)
    (hstate : c.state = .returnLeft a) (hread : c.tape c.head = x) :
    FiniteOneTapeSemantics.step
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      c (returnLeftInteriorArrow p hnt blank a x hx) = some {
        state := .returnLeft a
        head := c.head - 1
        tape := c.tape } := by
  have hact : deterministicAction p hnt blank (.returnLeft a) x =
      some ⟨x, .returnLeft a, .left⟩ := by
    simp [deterministicAction]
    intro hblank
    exact (hx hblank).elim
  have harrow : returnLeftInteriorArrow p hnt blank a x hx =
      deterministicArrow p hnt blank (.returnLeft a) x
        ⟨x, .returnLeft a, .left⟩ hact := Subtype.ext rfl
  rw [harrow]
  have htape : FiniteOneTapeSemantics.writtenTape c x = c.tape := by
    simpa [hread] using writtenTape_id (c := c)
  have hs := deterministicArrow_step p hnt blank c (.returnLeft a) x
    ⟨x, .returnLeft a, .left⟩ hstate hread hact
  simpa [htape, moveHead] using hs

def returnLeftInteriorArrows (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (xs : List Phys)
    (hxs : ∀ x ∈ xs, x ≠ ULogSourceOneHotReader.blank) :
    List (ScanArrow p hnt blank) :=
  xs.reverse.attach.map fun ⟨x, hx⟩ =>
    returnLeftInteriorArrow p hnt blank a x (hxs x (List.mem_reverse.mp hx))

@[simp] theorem returnLeftInteriorArrows_length (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (a : BoundedAction ns nt)
    (xs : List Phys) (hxs : ∀ x ∈ xs, x ≠ ULogSourceOneHotReader.blank) :
    (returnLeftInteriorArrows p hnt blank a xs hxs).length = xs.length := by
  simp [returnLeftInteriorArrows]

def returnLeftArrows (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt)
    (w : LogicalWindow nt) : List (ScanArrow p hnt blank) :=
  postScanBoundaryArrow p hnt blank q a ::
    (returnLeftInteriorArrows p hnt blank a w.encode
      (fun x hx => encode_mem_ne_blank w hx) ++
    [returnLeftBoundaryArrow p hnt blank a])

@[simp] theorem returnLeftArrows_length (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt)
    (w : LogicalWindow nt) :
    (returnLeftArrows p hnt blank q a w).length = windowWidth w + 2 := by
  simp [returnLeftArrows, windowWidth]

def startConfig (q : Fin ns) (a : BoundedAction ns nt)
    (w : LogicalWindow nt) (exterior : Int → Phys) : ScanCfg ns nt :=
  { state := .flag q (some a)
    head := (windowWidth w + 1 : Int)
    tape := windowTape w exterior }

theorem returnLeftInterior_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (xs : List Phys)
    (hxs : ∀ x ∈ xs, x ≠ ULogSourceOneHotReader.blank)
    (c : ScanCfg ns nt) (hstate : c.state = .returnLeft a)
    (hhead : c.head = (xs.length : Int))
    (htape : ∀ i : Fin xs.length, c.tape (i.val + 1 : Int) = xs[i.val]) :
    FiniteOneTapeSemantics.run
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      (returnLeftInteriorArrows p hnt blank a xs hxs) c = some {
        state := .returnLeft a
        head := 0
        tape := c.tape } := by
  induction xs using List.reverseRecOn generalizing c with
  | nil =>
      simp [returnLeftInteriorArrows]
      rcases c with ⟨s, hd, tp⟩
      simp at hstate hhead ⊢
      subst s
      simpa using hhead
  | append_singleton xs x ih =>
      have hx : x ≠ ULogSourceOneHotReader.blank := hxs x (by simp)
      have hxs' : ∀ y ∈ xs, y ≠ ULogSourceOneHotReader.blank :=
        fun y hy => hxs y (by simp [hy])
      have hlen : (xs ++ [x]).length = xs.length + 1 := by simp
      have hread : c.tape c.head = x := by
        have := htape ⟨xs.length, by simp⟩
        simpa [hhead, hlen, List.getElem_append_right'] using this
      have hfirst :
          returnLeftInteriorArrows p hnt blank a (xs ++ [x]) hxs =
            returnLeftInteriorArrow p hnt blank a x hx ::
              returnLeftInteriorArrows p hnt blank a xs hxs' := by
        simp [returnLeftInteriorArrows, List.reverse_append]
      rw [hfirst, FiniteOneTapeSemantics.run_cons]
      have hstep :=
        returnLeftInteriorArrow_step p hnt blank a x hx c hstate hread
      rw [hstep, Option.bind_some]
      exact ih hxs'
        (c := { state := .returnLeft a, head := c.head - 1, tape := c.tape })
        rfl (by simp [hhead]) (fun i => by
          have hi := htape ⟨i.val, by simp⟩
          simpa [List.getElem_append_left'] using hi)

theorem returnLeft_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt)
    (w : LogicalWindow nt) (exterior : Int → Phys) :
    FiniteOneTapeSemantics.run
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      (returnLeftArrows p hnt blank q a w)
      (startConfig q a w exterior) = some {
        state := .updateLRFlag a false
        head := 1
        tape := windowTape w exterior } := by
  have hflag := postScanBoundaryArrow_step p hnt blank q a
    (startConfig q a w exterior) rfl (by
      simpa [startConfig] using windowTape_right w exterior)
  have hinter := returnLeftInterior_run p hnt blank a w.encode
    (fun x hx => encode_mem_ne_blank w hx)
    { state := .returnLeft a
      head := (windowWidth w : Int)
      tape := windowTape w exterior }
    rfl (by simp [windowWidth]) (by
      intro i
      exact windowTape_encode w exterior i.val (by simpa [windowWidth] using i.isLt))
  have hbound := returnLeftBoundaryArrow_step p hnt blank a
    { state := .returnLeft a, head := 0, tape := windowTape w exterior }
    rfl (windowTape_left w exterior)
  unfold returnLeftArrows
  rw [FiniteOneTapeSemantics.run_cons, hflag, Option.bind_some]
  have hcfg :
      ({ state := .returnLeft a
         head := (startConfig q a w exterior).head - 1
         tape := (startConfig q a w exterior).tape } : ScanCfg ns nt) =
        { state := .returnLeft a
          head := (windowWidth w : Int)
          tape := windowTape w exterior } := by
    simp [startConfig]
  rw [hcfg, run_append, hinter, Option.bind_some]
  simp [hbound]

theorem returnLeft_visits_zero (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt)
    (w : LogicalWindow nt) (exterior : Int → Phys) :
    ∃ c : ScanCfg ns nt,
      FiniteOneTapeSemantics.run
        (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
        (returnLeftInteriorArrows p hnt blank a w.encode
          (fun x hx => encode_mem_ne_blank w hx))
        { state := .returnLeft a
          head := (windowWidth w : Int)
          tape := windowTape w exterior } = some c ∧
      c.head = 0 ∧
      c.state = .returnLeft a ∧
      c.tape = windowTape w exterior := by
  refine ⟨{ state := .returnLeft a, head := 0, tape := windowTape w exterior },
    ?_, rfl, rfl, rfl⟩
  exact returnLeftInterior_run p hnt blank a w.encode
    (fun x hx => encode_mem_ne_blank w hx)
    { state := .returnLeft a
      head := (windowWidth w : Int)
      tape := windowTape w exterior }
    rfl (by simp [windowWidth]) (by
      intro i
      exact windowTape_encode w exterior i.val
        (by simpa [windowWidth] using i.isLt))

theorem returnLeft_visits_right_delimiter (q : Fin ns)
    (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (exterior : Int → Phys) :
    (startConfig q a w exterior).head = (windowWidth w + 1 : Int) := rfl

theorem returnLeft_endpoint (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt)
    (w : LogicalWindow nt) (exterior : Int → Phys) :
    ∃ c : ScanCfg ns nt,
      FiniteOneTapeSemantics.run
        (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
        (returnLeftArrows p hnt blank q a w)
        (startConfig q a w exterior) = some c ∧
      c.state = .updateLRFlag a false ∧
      c.head = 1 ∧
      c.tape = windowTape w exterior ∧
      (returnLeftArrows p hnt blank q a w).length = windowWidth w + 2 := by
  refine ⟨{ state := .updateLRFlag a false
            head := 1
            tape := windowTape w exterior }, ?_⟩
  exact ⟨returnLeft_run p hnt blank q a w exterior, rfl, rfl, rfl, by simp⟩

/-! ## Explicit LR constructors from the transition table -/

def skipLRWrite {ns nt : ℕ} (a : BoundedAction ns nt) (rewrite : Bool)
    (i : Fin nt) (x : Phys) : Phys :=
  if rewrite then
    tapeOfBit ((encodeOneHot a.write)[i.val]'(by simpa using i.isLt))
  else x

theorem skipLR_last (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed rewrite : Bool)
    (i : Fin nt) (x : Phys)
    (hvalid : ULogSourceObliviousScanProgram.validBit x = true)
    (hlast : i.val + 1 = nt) :
    deterministicAction p hnt blank (.skipLR a armed rewrite i) x =
      some ⟨skipLRWrite a rewrite i x, .updateLRFlag a armed, .right⟩ := by
  simp [deterministicAction, hvalid, hlast, skipLRWrite]

theorem skipLR_not_last (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed rewrite : Bool)
    (i : Fin nt) (x : Phys)
    (hvalid : ULogSourceObliviousScanProgram.validBit x = true)
    (hlast : i.val + 1 ≠ nt) :
    deterministicAction p hnt blank (.skipLR a armed rewrite i) x =
      some ⟨skipLRWrite a rewrite i x,
        .skipLR a armed rewrite ⟨i.val + 1, by omega⟩, .right⟩ := by
  simp [deterministicAction, hvalid, skipLRWrite]
  split
  · rename_i h
    exact (hlast h).elim
  · rfl

def skipLRArrow (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed rewrite : Bool) (i : Fin nt) (x : Phys)
    (hvalid : ULogSourceObliviousScanProgram.validBit x = true) :
    ScanArrow p hnt blank :=
  if hlast : i.val + 1 = nt then
    deterministicArrow p hnt blank (.skipLR a armed rewrite i) x
      ⟨skipLRWrite a rewrite i x, .updateLRFlag a armed, .right⟩
      (skipLR_last p hnt blank a armed rewrite i x hvalid hlast)
  else
    deterministicArrow p hnt blank (.skipLR a armed rewrite i) x
      ⟨skipLRWrite a rewrite i x,
        .skipLR a armed rewrite ⟨i.val + 1, by omega⟩, .right⟩
      (skipLR_not_last p hnt blank a armed rewrite i x hvalid hlast)

def skipLRArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed rewrite : Bool) (bits : List Phys)
    (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, ULogSourceObliviousScanProgram.validBit x = true) :
    List (ScanArrow p hnt blank) :=
  List.ofFn fun i : Fin nt =>
    skipLRArrow p hnt blank a armed rewrite i
      (bits.get ⟨i.val, by omega⟩)
      (hvalid _ (List.get_mem _ _))

@[simp] theorem skipLRArrows_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed rewrite : Bool)
    (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, ULogSourceObliviousScanProgram.validBit x = true) :
    (skipLRArrows p hnt blank a armed rewrite bits hbits hvalid).length = nt := by
  simp [skipLRArrows]

theorem updateLR_isSome {ns nt : ℕ} (a : BoundedAction ns nt)
    (armed : Bool) (x : Phys)
    (hvalid : ULogSourceObliviousScanProgram.validBit x = true)
    (hplace : armed = true → x = zero) :
    (updateLR a armed x).isSome := by
  unfold updateLR
  simp [hvalid]
  split_ifs with hmove harmed hx0 hx1
  · simp
  · have hx := hplace (by simp [harmed])
    simp [hx] at hx0
  · simp
  · simp
  · simp

def updateLRFlagInteriorArrow (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed : Bool) (x : Phys)
    (hne : x ≠ ULogSourceOneHotReader.blank)
    (write : Phys) (armed' : Bool)
    (hupd : updateLR a armed x = some (write, armed')) :
    ScanArrow p hnt blank :=
  deterministicArrow p hnt blank (.updateLRFlag a armed) x
    ⟨write, .skipLR a armed' (x = one) ⟨0, hnt⟩, .right⟩
    (by
      simp [deterministicAction, hupd]
      intro hblank
      exact (hne hblank).elim)

def updateLRFlagRightBoundaryArrow (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) :
    ScanArrow p hnt blank :=
  deterministicArrow p hnt blank (.updateLRFlag a false) physBlank
    ⟨physBlank, .skipRL a false ⟨nt - 1, by omega⟩, .left⟩
    (by simp [deterministicAction])

theorem updateLRFlagRightBoundaryArrow_step (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (a : BoundedAction ns nt)
    (c : ScanCfg ns nt)
    (hstate : c.state = .updateLRFlag a false)
    (hread : c.tape c.head = physBlank) :
    FiniteOneTapeSemantics.step
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      c (updateLRFlagRightBoundaryArrow p hnt blank a) = some {
        state := .skipRL a false ⟨nt - 1, by omega⟩
        head := c.head - 1
        tape := c.tape } := by
  let act : Action (State ns nt) Phys :=
    ⟨physBlank, .skipRL a false ⟨nt - 1, by omega⟩, .left⟩
  have hact : deterministicAction p hnt blank (.updateLRFlag a false) physBlank =
      some act := by
    simp [act, deterministicAction]
  have harrow : updateLRFlagRightBoundaryArrow p hnt blank a =
      deterministicArrow p hnt blank (.updateLRFlag a false) physBlank act hact :=
    Subtype.ext rfl
  rw [harrow]
  have htape : FiniteOneTapeSemantics.writtenTape c physBlank = c.tape := by
    simpa [hread] using writtenTape_id (c := c)
  have hs := deterministicArrow_step p hnt blank c (.updateLRFlag a false)
    physBlank act hstate hread hact
  simpa [act, htape, moveHead] using hs

def lrArmed {ns nt : ℕ} (w : LogicalWindow nt) (a : BoundedAction ns nt)
    (cellIdx : ℕ) : Bool :=
  decide (a.move = .right ∧ cellIdx = w.head.val + 1)

def lrRewrite {nt : ℕ} (w : LogicalWindow nt) (cellIdx : ℕ) : Bool :=
  decide (cellIdx = w.head.val)

theorem markedCell_symbol_bits_valid {nt : ℕ} (c : MarkedCell nt)
    {x : Phys} (hx : x ∈ (encodeOneHot c.symbol).map tapeOfBit) :
    ULogSourceObliviousScanProgram.validBit x = true := by
  rw [List.mem_map] at hx
  rcases hx with ⟨b, _, rfl⟩
  exact validBit_tapeOfBit b

/-! ## Explicit RL constructors from the transition table -/

theorem skipRL_first (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed : Bool)
    (i : Fin nt) (x : Phys)
    (hvalid : ULogSourceObliviousScanProgram.validBit x = true)
    (hne : x ≠ ULogSourceOneHotReader.blank) (hfirst : i.val = 0) :
    deterministicAction p hnt blank (.skipRL a armed i) x =
      some ⟨x, .updateRLFlag a armed, .left⟩ := by
  simp [deterministicAction, hne, hvalid, hfirst]

theorem skipRL_not_first (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed : Bool)
    (i : Fin nt) (x : Phys)
    (hvalid : ULogSourceObliviousScanProgram.validBit x = true)
    (hne : x ≠ ULogSourceOneHotReader.blank) (hfirst : i.val ≠ 0) :
    deterministicAction p hnt blank (.skipRL a armed i) x =
      some ⟨x, .skipRL a armed ⟨i.val - 1, by omega⟩, .left⟩ := by
  simp [deterministicAction, hne, hvalid]
  exact hfirst

def skipRLArrow (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed : Bool) (i : Fin nt) (x : Phys)
    (hvalid : ULogSourceObliviousScanProgram.validBit x = true)
    (hne : x ≠ ULogSourceOneHotReader.blank) : ScanArrow p hnt blank :=
  if hfirst : i.val = 0 then
    deterministicArrow p hnt blank (.skipRL a armed i) x
      ⟨x, .updateRLFlag a armed, .left⟩
      (skipRL_first p hnt blank a armed i x hvalid hne hfirst)
  else
    deterministicArrow p hnt blank (.skipRL a armed i) x
      ⟨x, .skipRL a armed ⟨i.val - 1, by omega⟩, .left⟩
      (skipRL_not_first p hnt blank a armed i x hvalid hne hfirst)

def skipRLBitArrows (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed : Bool) (bits : List Phys)
    (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, ULogSourceObliviousScanProgram.validBit x = true)
    (hne : ∀ x ∈ bits, x ≠ ULogSourceOneHotReader.blank) :
    List (ScanArrow p hnt blank) :=
  List.ofFn fun k : Fin nt =>
    let i : Fin nt := ⟨nt - 1 - k.val, by omega⟩
    skipRLArrow p hnt blank a armed i (bits.get ⟨i.val, by omega⟩)
      (hvalid _ (List.get_mem _ _)) (hne _ (List.get_mem _ _))

@[simp] theorem skipRLBitArrows_length (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (a : BoundedAction ns nt)
    (armed : Bool) (bits : List Phys) (hbits : bits.length = nt)
    (hvalid : ∀ x ∈ bits, ULogSourceObliviousScanProgram.validBit x = true)
    (hne : ∀ x ∈ bits, x ≠ ULogSourceOneHotReader.blank) :
    (skipRLBitArrows p hnt blank a armed bits hbits hvalid hne).length = nt := by
  simp [skipRLBitArrows]

def updateRLFlagArrow (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (armed : Bool) (x : Phys)
    (write : Phys) (armed' : Bool)
    (hupd : updateRL a armed x = some (write, armed')) :
    ScanArrow p hnt blank :=
  deterministicArrow p hnt blank (.updateRLFlag a armed) x
    ⟨write, .skipRL a armed' ⟨nt - 1, by omega⟩, .left⟩
    (by simp [deterministicAction, hupd])

def skipRLLeftBoundaryArrow (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) :
    ScanArrow p hnt blank :=
  deterministicArrow p hnt blank (.skipRL a false ⟨nt - 1, by omega⟩) physBlank
    ⟨physBlank, .atLeft a.target, .stay⟩
    (by simp [deterministicAction])

theorem skipRLLeftBoundaryArrow_step (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (blank : Fin nt) (a : BoundedAction ns nt)
    (c : ScanCfg ns nt)
    (hstate : c.state = .skipRL a false ⟨nt - 1, by omega⟩)
    (hread : c.tape c.head = physBlank) :
    FiniteOneTapeSemantics.step
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      c (skipRLLeftBoundaryArrow p hnt blank a) = some {
        state := .atLeft a.target
        head := c.head
        tape := c.tape } := by
  let act : Action (State ns nt) Phys := ⟨physBlank, .atLeft a.target, .stay⟩
  have hact : deterministicAction p hnt blank
      (.skipRL a false ⟨nt - 1, by omega⟩) physBlank = some act := by
    simp [act, deterministicAction]
  have harrow : skipRLLeftBoundaryArrow p hnt blank a =
      deterministicArrow p hnt blank
        (.skipRL a false ⟨nt - 1, by omega⟩) physBlank act hact :=
    Subtype.ext rfl
  rw [harrow]
  have htape : FiniteOneTapeSemantics.writtenTape c physBlank = c.tape := by
    simpa [hread] using writtenTape_id (c := c)
  have hs := deterministicArrow_step p hnt blank c
    (.skipRL a false ⟨nt - 1, by omega⟩) physBlank act hstate hread hact
  simpa [act, htape, moveHead] using hs

def rlArmed {ns nt : ℕ} (w : LogicalWindow nt) (a : BoundedAction ns nt)
    (cellIdx : ℕ) : Bool :=
  decide (a.move = .left ∧ cellIdx + 1 = w.head.val)

/-! ## Suffix cost ledger -/

def suffixCost (W : ℕ) : ℕ := 3 * W + 4

theorem suffixCost_ledger (W : ℕ) :
    suffixCost W = (W + 2) + (W + 1) + (W + 1) := by
  simp [suffixCost]; omega

theorem suffixCost_phases (W : ℕ) :
    suffixCost W = 1 + W + 1 + W + 1 + W + 1 := by
  simp [suffixCost]; omega

/-- Residual fuel after the compiled return-to-left pass. -/
def residualSuffixFuel (w : LogicalWindow nt) : ℕ :=
  2 * windowWidth w + 2

theorem residualSuffixFuel_eq (w : LogicalWindow nt) :
    suffixCost (windowWidth w) =
      (windowWidth w + 2) + residualSuffixFuel w := by
  simp [suffixCost, residualSuffixFuel]; omega

/-- Compiled operational prefix: the complete return-to-left pass, ending at
`.updateLRFlag a false` on coordinate `1` with the original encoded tape. -/
def updateSuffixPrefixArrows (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt)
    (w : LogicalWindow nt) : List (ScanArrow p hnt blank) :=
  returnLeftArrows p hnt blank q a w

theorem updateSuffixPrefix_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt)
    (w : LogicalWindow nt) (exterior : Int → Phys) :
    FiniteOneTapeSemantics.run
      (ULogSourceObliviousScanProgram.program p hnt blank) (fun _ => true)
      (updateSuffixPrefixArrows p hnt blank q a w)
      (startConfig q a w exterior) = some {
        state := .updateLRFlag a false
        head := 1
        tape := windowTape w exterior } ∧
    (updateSuffixPrefixArrows p hnt blank q a w).length =
      windowWidth w + 2 :=
  ⟨returnLeft_run p hnt blank q a w exterior, by simp [updateSuffixPrefixArrows]⟩

end PakFixedPolyomino.ULogSourceObliviousUpdateExecution
