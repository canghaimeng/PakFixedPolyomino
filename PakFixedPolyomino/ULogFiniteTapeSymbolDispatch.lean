import PakFixedPolyomino.ULogFiniteTapeStageCompositionRuns

/-! One real deterministic tape-symbol dispatch into an arbitrary finite
labelled source program. Every subsequent label and accepting endpoint is
preserved, including immediate source acceptance. This structural primitive
is not a compact loader or a source-hardness certificate. -/
namespace PakFixedPolyomino.ULogFiniteTapeSymbolDispatch
open ULogCompiler ULogFiniteTapeZipperRun
open ULogFiniteTapeStageComposition (rightState rightConfig rightAction apply_right right_live)
open ULogFiniteTapeStageCompositionRuns (right_halted right_accepts_iff)
open FiniteOneTapeSemantics (moveHead)

variable {ms nt : Nat}

abbrev stateCount (ms : Nat) := ULogFiniteTapeStageComposition.stateCount 3 ms

def program (q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear : Fin nt) : BoundedProgram (stateCount ms) nt where
  rule state read slot :=
    if state.val = 2 then
      if slot then none else some ⟨clear, rightState (ns := 3) (entry read), .stay⟩
    else if hright : 3 + 2 ≤ state.val ∧ state.val < 3 + ms then
      (q.rule ⟨state.val - 3, by omega⟩ read slot).map (rightAction (ns := 3))
    else none

def initial (symbol : Fin nt) (left right : List (Fin nt)) :
    BoundedConfig (stateCount ms) nt :=
  ⟨⟨2, by unfold stateCount ULogFiniteTapeStageComposition.stateCount; omega⟩,
    left, symbol, right⟩

def dispatched (entry : Fin nt → Fin ms) (clear symbol : Fin nt)
    (left right : List (Fin nt)) : BoundedConfig ms nt :=
  ⟨entry symbol, left, clear, right⟩

theorem program_falseOnly (q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear : Fin nt) (hq : ULogFiniteAlphabetDeterministicRuns.FalseOnly q) :
    ULogFiniteAlphabetDeterministicRuns.FalseOnly (program q entry clear) := by
  dsimp [ULogFiniteAlphabetDeterministicRuns.FalseOnly] at hq ⊢
  intro state read
  simp [program, hq]

theorem rule_right (q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear : Fin nt) (z : BoundedConfig ms nt) (slot : Bool)
    (live : boundedHalted z = false) :
    (program q entry clear).rule (rightState (ns := 3) z.state) z.focus slot =
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
    (clear blank : Fin nt) (w : List Bool) (head : Int) (z : BoundedConfig ms nt) :
    run (program q entry clear) blank w head (rightConfig (ns := 3) z) =
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
                rule_right q entry clear z slot hh, hr]
              rfl
          | some a =>
              simp only [run, right_halted, hh, Bool.false_eq_true, ↓reduceIte]
              rw [show (rightConfig z).state = rightState z.state by rfl,
                show (rightConfig (ns := 3) z).focus = z.focus by rfl,
                rule_right q entry clear z slot hh, hr]
              change run (program q entry clear) blank rest
                (moveHead a.move head) (applyBounded blank (rightConfig z) (rightAction a)) = _
              rw [apply_right]
              exact ih _ _

theorem run_dispatch_cons (q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear blank symbol : Fin nt) (left right : List (Fin nt))
    (head : Int) (slot : Bool) (rest : List Bool) :
    run (program q entry clear) blank (slot :: rest) head
        (initial symbol left right) =
      if slot then none else
        (run q blank rest head (dispatched entry clear symbol left right)).map
          (fun hz => (hz.1, rightConfig (ns := 3) hz.2)) := by
  cases slot with
  | true => simp [run, initial, boundedHalted, program]
  | false =>
      change run (program q entry clear) blank rest head
        (rightConfig (ns := 3) (dispatched entry clear symbol left right)) = _
      exact run_right_map q entry clear blank rest head _

theorem every_raw_run_splits (q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear blank symbol : Fin nt) (left right : List (Fin nt))
    (head hf : Int) (w : List Bool) (zf : BoundedConfig (stateCount ms) nt) :
    run (program q entry clear) blank w head (initial symbol left right) = some (hf, zf) ↔
      (w = [] ∧ hf = head ∧ zf = initial symbol left right) ∨
      ∃ rest out, w = false :: rest ∧
        run q blank rest head (dispatched entry clear symbol left right) = some (hf, out) ∧
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

def RawAccepting (q : BoundedProgram ms nt) (blank : Fin nt)
    (head : Int) (start : BoundedConfig ms nt) (w : List Bool) : Prop :=
  ∃ hf out, run q blank w head start = some (hf, out) ∧ out.state.val = 0

theorem every_raw_accepting_splits (q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear blank symbol : Fin nt) (left right : List (Fin nt))
    (head : Int) (w : List Bool) :
    RawAccepting (program q entry clear) blank head (initial symbol left right) w ↔
      ∃ rest, w = false :: rest ∧
        RawAccepting q blank head (dispatched entry clear symbol left right) rest := by
  constructor
  · rintro ⟨hf, out, raw, accepts⟩
    rcases (every_raw_run_splits q entry clear blank symbol left right head hf w out).1 raw with
      ⟨rfl, rfl, rfl⟩ | ⟨rest, out, word, run, rfl⟩
    · simp [initial] at accepts
    · exact ⟨rest, word, hf, out, run, (right_accepts_iff out).1 accepts⟩
  · rintro ⟨rest, rfl, hf, out, run, accepts⟩
    refine ⟨hf, rightConfig out, ?_, (right_accepts_iff out).2 accepts⟩
    rw [run_dispatch_cons]
    simp [run]

theorem symbol_dispatch_spec (q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear blank symbol : Fin nt) (left right : List (Fin nt)) (head : Int) :
    (∀ w hf out,
      run (program q entry clear) blank w head (initial symbol left right) = some (hf, out) ↔
        (w = [] ∧ hf = head ∧ out = initial symbol left right) ∨
          ∃ rest z, w = false :: rest ∧
            run q blank rest head (dispatched entry clear symbol left right) = some (hf, z) ∧
            out = rightConfig (ns := 3) z) ∧
    (∀ w, RawAccepting (program q entry clear) blank head (initial symbol left right) w ↔
      ∃ rest, w = false :: rest ∧
        RawAccepting q blank head (dispatched entry clear symbol left right) rest) :=
  ⟨fun w hf out => every_raw_run_splits q entry clear blank symbol left right head hf w out,
    every_raw_accepting_splits q entry clear blank symbol left right head⟩

def RawAcceptingWords (q : BoundedProgram ms nt) (blank : Fin nt)
    (head : Int) (start : BoundedConfig ms nt) (T : Nat) : Type :=
  {w : List Bool // w.length ≤ T ∧ RawAccepting q blank head start w}

noncomputable def acceptingWordsEquiv (q : BoundedProgram ms nt)
    (entry : Fin nt → Fin ms) (clear blank symbol : Fin nt)
    (left right : List (Fin nt)) (head : Int) (T : Nat) :
    RawAcceptingWords (program q entry clear) blank head (initial symbol left right) (T + 1) ≃
      RawAcceptingWords q blank head (dispatched entry clear symbol left right) T := by
  classical
  let split := fun word : RawAcceptingWords (program q entry clear) blank head
      (initial symbol left right) (T + 1) =>
    (every_raw_accepting_splits q entry clear blank symbol left right head word.val).1 word.property.2
  refine
    { toFun := fun word => ⟨Classical.choose (split word), ?_, (Classical.choose_spec (split word)).2⟩
      invFun := fun word => ⟨false :: word.val, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have length := word.property.1
    rw [(Classical.choose_spec (split word)).1, List.length_cons] at length
    omega
  · simpa only [List.length_cons] using Nat.add_le_add_right word.property.1 1
  · exact (every_raw_accepting_splits q entry clear blank symbol left right head _).2
      ⟨word.val, rfl, word.property.2⟩
  · intro word
    apply Subtype.ext
    exact (Classical.choose_spec (split word)).1.symm
  · intro word
    apply Subtype.ext
    exact (List.cons.inj (Classical.choose_spec (split ⟨false :: word.val,
      by simpa only [List.length_cons] using Nat.add_le_add_right word.property.1 1,
      (every_raw_accepting_splits q entry clear blank symbol left right head _).2
        ⟨word.val, rfl, word.property.2⟩⟩)).1).2.symm

theorem all_cutoff_counts (q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear blank symbol : Fin nt) (left right : List (Fin nt)) (head : Int) (T : Nat) :
    Nat.card (RawAcceptingWords (program q entry clear) blank head
      (initial symbol left right) (T + 1)) =
    Nat.card (RawAcceptingWords q blank head (dispatched entry clear symbol left right) T) :=
  Nat.card_congr (acceptingWordsEquiv q entry clear blank symbol left right head T)

theorem symbol_dispatch_count_spec (q : BoundedProgram ms nt) (entry : Fin nt → Fin ms)
    (clear blank symbol : Fin nt) (left right : List (Fin nt)) (head : Int) :
    (∀ w, RawAccepting (program q entry clear) blank head (initial symbol left right) w ↔
      ∃ rest, w = false :: rest ∧
        RawAccepting q blank head (dispatched entry clear symbol left right) rest) ∧
    (∀ T, Nat.card (RawAcceptingWords (program q entry clear) blank head
        (initial symbol left right) (T + 1)) =
      Nat.card (RawAcceptingWords q blank head (dispatched entry clear symbol left right) T)) :=
  ⟨every_raw_accepting_splits q entry clear blank symbol left right head,
    all_cutoff_counts q entry clear blank symbol left right head⟩

end PakFixedPolyomino.ULogFiniteTapeSymbolDispatch
