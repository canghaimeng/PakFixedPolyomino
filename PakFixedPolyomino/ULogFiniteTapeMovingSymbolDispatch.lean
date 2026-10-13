import PakFixedPolyomino.ULogFiniteTapeSymbolDispatch
import PakFixedPolyomino.ULogFiniteTapeGrowthLedger

/-! One-tick moving tape-symbol dispatch into an arbitrary finite labelled
parent. The read symbol is cleared and a real Move is applied, including
blank allocation at empty exteriors. Compact loader composition remains
separate. -/
namespace PakFixedPolyomino.ULogFiniteTapeMovingSymbolDispatch

open ULogCompiler ULogFiniteTapeZipperRun
open ULogFiniteTapeStageComposition (rightState rightConfig rightAction apply_right)
open ULogFiniteTapeStageCompositionRuns (right_halted right_accepts_iff)
open ULogFiniteTapeSymbolDispatch (RawAccepting RawAcceptingWords)
open ULogFiniteTapeGrowthLedger
open FiniteOneTapeSemantics (moveHead)

variable {ms nt : Nat}

abbrev stateCount (ms : Nat) := ULogFiniteTapeStageComposition.stateCount 3 ms

def program (q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear : Fin nt) (movement : OneTapeTableau.Move) :
    BoundedProgram (stateCount ms) nt where
  rule state read slot :=
    if state.val = 2 then
      if slot then none
      else some ⟨clear, rightState (ns := 3) (entry read), movement⟩
    else if hright : 3 + 2 ≤ state.val ∧ state.val < 3 + ms then
      (q.rule ⟨state.val - 3, by omega⟩ read slot).map (rightAction (ns := 3))
    else none

def initial (symbol : Fin nt) (left right : List (Fin nt)) :
    BoundedConfig (stateCount ms) nt :=
  ⟨⟨2, by unfold stateCount ULogFiniteTapeStageComposition.stateCount; omega⟩,
    left, symbol, right⟩

def moved (entry : Fin nt → Fin ms) (clear blank : Fin nt)
    (movement : OneTapeTableau.Move) (symbol : Fin nt)
    (left right : List (Fin nt)) : BoundedConfig ms nt :=
  applyBounded blank
    { state := entry symbol, leftRev := left, focus := symbol, right := right }
    { write := clear, target := entry symbol, move := movement }

def growL (movement : OneTapeTableau.Move) (left : List (Fin nt)) : Nat :=
  match movement, left with
  | .left, [] => 1
  | _, _ => 0

def growR (movement : OneTapeTableau.Move) (right : List (Fin nt)) : Nat :=
  match movement, right with
  | .right, [] => 1
  | _, _ => 0

def dispatchAction (_q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear : Fin nt) (movement : OneTapeTableau.Move) (symbol : Fin nt) :
    BoundedAction (stateCount ms) nt :=
  ⟨clear, rightState (ns := 3) (entry symbol), movement⟩

theorem program_falseOnly (q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear : Fin nt) (movement : OneTapeTableau.Move)
    (hq : ULogFiniteAlphabetDeterministicRuns.FalseOnly q) :
    ULogFiniteAlphabetDeterministicRuns.FalseOnly
      (program q entry clear movement) := by
  dsimp [ULogFiniteAlphabetDeterministicRuns.FalseOnly] at hq ⊢
  intro state read
  simp [program, hq]

theorem initial_not_halt (symbol : Fin nt) (left right : List (Fin nt)) :
    boundedHalted (initial (ms := ms) symbol left right) = false := by
  simp [boundedHalted, initial]

theorem rule_entry (q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear : Fin nt) (movement : OneTapeTableau.Move) (symbol : Fin nt)
    (left right : List (Fin nt)) :
    (program q entry clear movement).rule
        (initial (ms := ms) symbol left right).state
        (initial (ms := ms) symbol left right).focus false =
      some (dispatchAction q entry clear movement symbol) := by
  simp [program, initial, dispatchAction]

theorem apply_dispatch (entry : Fin nt → Fin ms) (clear blank : Fin nt)
    (movement : OneTapeTableau.Move) (symbol : Fin nt)
    (left right : List (Fin nt)) :
    applyBounded blank (initial (ms := ms) symbol left right)
        ⟨clear, rightState (ns := 3) (entry symbol), movement⟩ =
      rightConfig (ns := 3)
        (moved entry clear blank movement symbol left right) := by
  cases movement <;> cases left <;> cases right <;>
    simp [applyBounded, initial, moved, rightConfig]

theorem leftCharge_entry (_q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear : Fin nt) (movement : OneTapeTableau.Move) (symbol : Fin nt)
    (left right : List (Fin nt)) :
    leftCharge (initial (ms := ms) symbol left right)
        ⟨clear, rightState (ns := 3) (entry symbol), movement⟩ =
      growL movement left := by
  cases movement <;> cases left <;> simp [leftCharge, initial, growL]

theorem rightCharge_entry (_q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear : Fin nt) (movement : OneTapeTableau.Move) (symbol : Fin nt)
    (left right : List (Fin nt)) :
    rightCharge (initial (ms := ms) symbol left right)
        ⟨clear, rightState (ns := 3) (entry symbol), movement⟩ =
      growR movement right := by
  cases movement <;> cases right <;> simp [rightCharge, initial, growR]

theorem rule_right (q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear : Fin nt) (movement : OneTapeTableau.Move) (z : BoundedConfig ms nt)
    (slot : Bool) (live : boundedHalted z = false) :
    (program q entry clear movement).rule (rightState (ns := 3) z.state) z.focus slot =
      (q.rule z.state z.focus slot).map (rightAction (ns := 3)) := by
  have hq : 2 ≤ z.state.val := by
    have h : 1 < z.state.val := by simpa [boundedHalted] using live
    omega
  have hz := z.state.isLt
  simp [program, rightState, show ¬ z.state.val < 2 by omega,
    show 3 + z.state.val ≠ 2 by omega,
    show 3 + 2 ≤ 3 + z.state.val by omega,
    show 3 + z.state.val < 3 + ms by omega]

theorem run_right_map (q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear blank : Fin nt) (movement : OneTapeTableau.Move) (w : List Bool)
    (head : Int) (z : BoundedConfig ms nt) :
    run (program q entry clear movement) blank w head (rightConfig (ns := 3) z) =
      (run q blank w head z).map (fun hz => (hz.1, rightConfig (ns := 3) hz.2)) := by
  induction w generalizing head z with
  | nil => rfl
  | cons slot rest ih =>
      cases hh : boundedHalted z with
      | true => simp [run, right_halted, hh]
      | false =>
          cases hr : q.rule z.state z.focus slot with
          | none =>
              simp only [run, right_halted, hh, Bool.false_eq_true, ↓reduceIte]
              rw [show (rightConfig z).state = rightState z.state by rfl,
                show (rightConfig (ns := 3) z).focus = z.focus by rfl,
                rule_right q entry clear movement z slot hh, hr]
              rfl
          | some a =>
              simp only [run, right_halted, hh, Bool.false_eq_true, ↓reduceIte]
              rw [show (rightConfig z).state = rightState z.state by rfl,
                show (rightConfig (ns := 3) z).focus = z.focus by rfl,
                rule_right q entry clear movement z slot hh, hr]
              change run (program q entry clear movement) blank rest
                (moveHead a.move head)
                (applyBounded blank (rightConfig z) (rightAction a)) = _
              rw [apply_right]
              exact ih _ _

theorem run_dispatch_cons (q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear blank : Fin nt) (movement : OneTapeTableau.Move) (symbol : Fin nt)
    (left right : List (Fin nt)) (head : Int) (slot : Bool) (rest : List Bool) :
    run (program q entry clear movement) blank (slot :: rest) head
        (initial symbol left right) =
      if slot then none else
        (run q blank rest (moveHead movement head)
          (moved entry clear blank movement symbol left right)).map
          (fun hz => (hz.1, rightConfig (ns := 3) hz.2)) := by
  cases slot with
  | true => simp [run, initial, boundedHalted, program]
  | false =>
      have hnh := initial_not_halt (ms := ms) symbol left right
      have hr := rule_entry q entry clear movement symbol left right
      simp [run, hnh, hr, dispatchAction, apply_dispatch]
      exact run_right_map q entry clear blank movement rest
        (moveHead movement head)
        (moved entry clear blank movement symbol left right)

theorem every_raw_run_splits (q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear blank : Fin nt) (movement : OneTapeTableau.Move) (symbol : Fin nt)
    (left right : List (Fin nt)) (head hf : Int) (w : List Bool)
    (zf : BoundedConfig (stateCount ms) nt) :
    run (program q entry clear movement) blank w head (initial symbol left right) =
        some (hf, zf) ↔
      (w = [] ∧ hf = head ∧ zf = initial symbol left right) ∨
      ∃ rest out, w = false :: rest ∧
        run q blank rest (moveHead movement head)
          (moved entry clear blank movement symbol left right) = some (hf, out) ∧
        zf = rightConfig (ns := 3) out := by
  cases w with
  | nil => simp [run, eq_comm]
  | cons slot rest =>
      rw [run_dispatch_cons]
      cases slot with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, List.cons_ne_nil, false_and, false_or]
        constructor
        · intro h
          obtain ⟨⟨h, out⟩, run, eq⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
          exact ⟨rest, out, rfl, run, rfl⟩
        · rintro ⟨v, out, word, run, rfl⟩
          have hv : v = rest := (List.cons.inj word).2.symm
          subst v
          rw [run]
          rfl
      | true => simp

theorem every_raw_accepting_splits (q : BoundedProgram ms nt)
    (entry : Fin nt → Fin ms) (clear blank : Fin nt)
    (movement : OneTapeTableau.Move) (symbol : Fin nt)
    (left right : List (Fin nt)) (head : Int) (w : List Bool) :
    RawAccepting (program q entry clear movement) blank head
        (initial symbol left right) w ↔
      ∃ rest, w = false :: rest ∧
        RawAccepting q blank (moveHead movement head)
          (moved entry clear blank movement symbol left right) rest := by
  constructor
  · rintro ⟨hf, out, raw, accepts⟩
    rcases (every_raw_run_splits q entry clear blank movement symbol left right
        head hf w out).1 raw with ⟨rfl, rfl, rfl⟩ | ⟨rest, out, word, run, rfl⟩
    · simp [initial] at accepts
    · exact ⟨rest, word, hf, out, run, (right_accepts_iff out).1 accepts⟩
  · rintro ⟨rest, rfl, hf, out, run, accepts⟩
    refine ⟨hf, rightConfig out, ?_, (right_accepts_iff out).2 accepts⟩
    rw [run_dispatch_cons]
    simp [run]

noncomputable def acceptingWordsEquiv (q : BoundedProgram ms nt)
    (entry : Fin nt → Fin ms) (clear blank : Fin nt)
    (movement : OneTapeTableau.Move) (symbol : Fin nt)
    (left right : List (Fin nt)) (head : Int) (T : Nat) :
    RawAcceptingWords (program q entry clear movement) blank head
        (initial symbol left right) (T + 1) ≃
      RawAcceptingWords q blank (moveHead movement head)
        (moved entry clear blank movement symbol left right) T := by
  classical
  let split := fun word : RawAcceptingWords (program q entry clear movement) blank head
      (initial symbol left right) (T + 1) =>
    (every_raw_accepting_splits q entry clear blank movement symbol left right
      head word.val).1 word.property.2
  refine
    { toFun := fun word => ⟨Classical.choose (split word), ?_,
        (Classical.choose_spec (split word)).2⟩
      invFun := fun word => ⟨false :: word.val, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have length := word.property.1
    rw [(Classical.choose_spec (split word)).1, List.length_cons] at length
    omega
  · simpa only [List.length_cons] using Nat.add_le_add_right word.property.1 1
  · exact (every_raw_accepting_splits q entry clear blank movement symbol left right
      head _).2 ⟨word.val, rfl, word.property.2⟩
  · intro word
    apply Subtype.ext
    exact (Classical.choose_spec (split word)).1.symm
  · intro word
    apply Subtype.ext
    exact (List.cons.inj (Classical.choose_spec (split ⟨false :: word.val,
      by simpa only [List.length_cons] using Nat.add_le_add_right word.property.1 1,
      (every_raw_accepting_splits q entry clear blank movement symbol left right
        head _).2 ⟨word.val, rfl, word.property.2⟩⟩)).1).2.symm

theorem all_cutoff_counts (q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear blank : Fin nt) (movement : OneTapeTableau.Move) (symbol : Fin nt)
    (left right : List (Fin nt)) (head : Int) (T : Nat) :
    Nat.card (RawAcceptingWords (program q entry clear movement) blank head
      (initial symbol left right) (T + 1)) =
    Nat.card (RawAcceptingWords q blank (moveHead movement head)
      (moved entry clear blank movement symbol left right) T) :=
  Nat.card_congr (acceptingWordsEquiv q entry clear blank movement symbol left right head T)

theorem one_tick_growth (q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear blank : Fin nt) (movement : OneTapeTableau.Move) (symbol : Fin nt)
    (left right : List (Fin nt)) (H : Int) :
    GrowthRun (program q entry clear movement) blank [false] H
      (initial symbol left right) (moveHead movement H)
      (rightConfig (ns := 3)
        (moved entry clear blank movement symbol left right))
      (growL movement left) (growR movement right) := by
  have tail :
      GrowthRun (program q entry clear movement) blank []
        (moveHead movement H)
        (applyBounded blank (initial symbol left right)
          (dispatchAction q entry clear movement symbol))
        (moveHead movement H)
        (applyBounded blank (initial symbol left right)
          (dispatchAction q entry clear movement symbol)) 0 0 :=
    GrowthRun.nil _ _
  have hcons := GrowthRun.cons (initial_not_halt (ms := ms) symbol left right)
    (rule_entry q entry clear movement symbol left right) tail
  simp [dispatchAction] at hcons
  rw [apply_dispatch] at hcons
  convert hcons
  · exact leftCharge_entry q entry clear movement symbol left right
  · exact rightCharge_entry q entry clear movement symbol left right

theorem allocated_no_growth (q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear blank : Fin nt) (movement : OneTapeTableau.Move) (symbol : Fin nt)
    (left right : List (Fin nt)) (H : Int)
    (hL : movement = .left → left ≠ [])
    (hR : movement = .right → right ≠ []) :
    GrowthRun (program q entry clear movement) blank [false] H
      (initial symbol left right) (moveHead movement H)
      (rightConfig (ns := 3)
        (moved entry clear blank movement symbol left right)) 0 0 := by
  have h := one_tick_growth q entry clear blank movement symbol left right H
  have hl : growL movement left = 0 := by
    cases movement with
    | left =>
        have : left ≠ [] := hL rfl
        cases left <;> simp [growL] at this ⊢
    | stay => simp [growL]
    | right => simp [growL]
  have hr : growR movement right = 0 := by
    cases movement with
    | right =>
        have : right ≠ [] := hR rfl
        cases right <;> simp [growR] at this ⊢
    | stay => simp [growR]
    | left => simp [growR]
  simpa [hl, hr] using h

theorem compiled_symbols (q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear : Fin nt) (movement : OneTapeTableau.Move) :
    ∀ r ∈ compile (program q entry clear movement),
      r.read < nt ∧ r.action.write < nt := by
  intro r hr
  have hb := compile_rule_bounded (program q entry clear movement) hr
  exact ⟨hb.2.1, hb.2.2.1⟩

theorem moving_symbol_dispatch_spec (q : BoundedProgram ms nt)
    (entry : Fin nt → Fin ms) (clear blank : Fin nt)
    (movement : OneTapeTableau.Move) (symbol : Fin nt)
    (left right : List (Fin nt)) (H : Int) :
    (∀ w hf out,
      run (program q entry clear movement) blank w H (initial symbol left right) =
          some (hf, out) ↔
        (w = [] ∧ hf = H ∧ out = initial symbol left right) ∨
          ∃ rest z, w = false :: rest ∧
            run q blank rest (moveHead movement H)
              (moved entry clear blank movement symbol left right) =
                some (hf, z) ∧
            out = rightConfig (ns := 3) z) ∧
    (∀ w,
      RawAccepting (program q entry clear movement) blank H
          (initial symbol left right) w ↔
        ∃ rest, w = false :: rest ∧
          RawAccepting q blank (moveHead movement H)
            (moved entry clear blank movement symbol left right) rest) ∧
    (∀ T,
      Nat.card (RawAcceptingWords (program q entry clear movement) blank H
          (initial symbol left right) (T + 1)) =
        Nat.card (RawAcceptingWords q blank (moveHead movement H)
          (moved entry clear blank movement symbol left right) T)) ∧
    (GrowthRun (program q entry clear movement) blank [false] H
        (initial symbol left right) (moveHead movement H)
        (rightConfig (ns := 3)
          (moved entry clear blank movement symbol left right))
        (growL movement left) (growR movement right) ∧
      ((movement = .left → left ≠ []) → (movement = .right → right ≠ []) →
        GrowthRun (program q entry clear movement) blank [false] H
          (initial symbol left right) (moveHead movement H)
          (rightConfig (ns := 3)
            (moved entry clear blank movement symbol left right)) 0 0)) :=
  ⟨fun w hf out =>
      every_raw_run_splits q entry clear blank movement symbol left right H hf w out,
    every_raw_accepting_splits q entry clear blank movement symbol left right H,
    all_cutoff_counts q entry clear blank movement symbol left right H,
    ⟨one_tick_growth q entry clear blank movement symbol left right H,
      allocated_no_growth q entry clear blank movement symbol left right H⟩⟩

end PakFixedPolyomino.ULogFiniteTapeMovingSymbolDispatch
