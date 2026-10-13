import PakFixedPolyomino.ULogFiniteTapeGrowthLedger
import PakFixedPolyomino.ULogFiniteAlphabetDeterministicRuns

/-! Literal ternary source loop with first-iteration raw-word inversion. -/
namespace PakFixedPolyomino.ULogTernarySourceLoop

open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open FiniteOneTapeSemantics (moveHead)

variable {ms : Nat}

def stateCount (ms : Nat) : Nat := ms + 4

def bodyState (z : Fin ms) : Fin (stateCount ms) :=
  if h0 : z.val = 0 then ⟨3, by unfold stateCount; omega⟩
  else if h1 : z.val = 1 then ⟨1, by unfold stateCount; omega⟩
  else ⟨z.val + 2, by unfold stateCount; have := z.isLt; omega⟩

def bodyConfig (z : BoundedConfig ms 3) : BoundedConfig (stateCount ms) 3 :=
  ⟨bodyState z.state, z.leftRev, z.focus, z.right⟩

def bodyAction (a : BoundedAction ms 3) : BoundedAction (stateCount ms) 3 :=
  ⟨a.write, bodyState a.target, a.move⟩

def initial (symbol : Fin 3) (left right : List (Fin 3)) :
    BoundedConfig (stateCount ms) 3 :=
  ⟨⟨2, by unfold stateCount; omega⟩, left, symbol, right⟩

def loopAt (z : BoundedConfig ms 3) : BoundedConfig (stateCount ms) 3 :=
  initial z.focus z.leftRev z.right

def selected (entry : Fin 3 → Fin ms) (symbol : Fin 3)
    (left right : List (Fin 3)) : BoundedConfig ms 3 :=
  ⟨entry symbol, left, 2, right⟩

def sentinelFinal (symbol : Fin 3) (left right : List (Fin 3)) :
    BoundedConfig (stateCount ms) 3 :=
  ⟨⟨0, by unfold stateCount; omega⟩, left, symbol, right⟩

def program (q : BoundedProgram ms 3) (entry : Fin 3 → Fin ms) :
    BoundedProgram (stateCount ms) 3 where
  rule state read slot :=
    if state.val = 2 then
      if slot then none
      else if read.val = 2 then
        some ⟨read, ⟨0, by unfold stateCount; omega⟩, .stay⟩
      else some ⟨2, bodyState (entry read), .stay⟩
    else if state.val = 3 then
      if slot then none
      else some ⟨read, ⟨2, by unfold stateCount; omega⟩, .stay⟩
    else if hbody : 4 ≤ state.val ∧ state.val < ms + 2 then
      (q.rule ⟨state.val - 2, by omega⟩ read slot).map bodyAction
    else none

theorem apply_body (z : BoundedConfig ms 3) (a : BoundedAction ms 3) :
    applyBounded (2 : Fin 3) (bodyConfig z) (bodyAction a) =
      bodyConfig (applyBounded 2 z a) := by
  cases hm : a.move <;> cases hl : z.leftRev <;> cases hr : z.right <;>
    simp [applyBounded, bodyConfig, bodyAction, hm, hl, hr]

theorem body_reject_halted (z : BoundedConfig ms 3) (hz : z.state.val = 1) :
    boundedHalted (bodyConfig z) = true := by
  simp [boundedHalted, bodyConfig, bodyState, hz]

theorem body_accept_live (z : BoundedConfig ms 3) (hz : z.state.val = 0) :
    boundedHalted (bodyConfig z) = false := by
  simp [boundedHalted, bodyConfig, bodyState, hz]

theorem body_live (z : BoundedConfig ms 3) (hl : boundedHalted z = false) :
    boundedHalted (bodyConfig z) = false := by
  have h : 1 < z.state.val := by simpa [boundedHalted] using hl
  simp [boundedHalted, bodyConfig, bodyState, show z.state.val ≠ 0 by omega,
    show z.state.val ≠ 1 by omega]

theorem body_not_accept (z : BoundedConfig ms 3) :
    (bodyConfig z).state.val ≠ 0 := by
  by_cases h0 : z.state.val = 0 <;> by_cases h1 : z.state.val = 1 <;>
    simp [bodyConfig, bodyState, *]

theorem rule_body (q : BoundedProgram ms 3) (entry : Fin 3 → Fin ms)
    (z : BoundedConfig ms 3) (slot : Bool) (hl : boundedHalted z = false) :
    (program q entry).rule (bodyState z.state) z.focus slot =
      (q.rule z.state z.focus slot).map bodyAction := by
  have h : 1 < z.state.val := by simpa [boundedHalted] using hl
  simp [program, bodyState, show z.state.val ≠ 0 by omega,
    show z.state.val ≠ 1 by omega, show z.state.val + 2 ≠ 3 by omega,
    show 4 ≤ z.state.val + 2 by omega, show z.state.val + 2 < ms + 2 by omega]

theorem rule_handoff (q : BoundedProgram ms 3) (entry : Fin 3 → Fin ms)
    (z : BoundedConfig ms 3) (hz : z.state.val = 0) (slot : Bool) :
    (program q entry).rule (bodyState z.state) z.focus slot =
      if slot then none
      else some ⟨z.focus, ⟨2, by unfold stateCount; omega⟩, .stay⟩ := by
  simp [program, bodyState, hz]

theorem initial_not_halt (symbol : Fin 3) (left right : List (Fin 3)) :
    boundedHalted (initial (ms := ms) symbol left right) = false := by
  simp [boundedHalted, initial]

theorem run_body_prefix (q : BoundedProgram ms 3) (entry : Fin 3 → Fin ms)
    (w : List Bool) (head hf : Int) (z zp : BoundedConfig ms 3)
    (hp : run q 2 w head z = some (hf, zp)) :
    run (program q entry) 2 w head (bodyConfig z) = some (hf, bodyConfig zp) := by
  induction w generalizing head z with
  | nil =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at hp
      rcases hp with ⟨rfl, rfl⟩
      rfl
  | cons slot rest ih =>
      cases hh : boundedHalted z with
      | true => simp [run, hh] at hp
      | false =>
          cases hr : q.rule z.state z.focus slot with
          | none => simp [run, hh, hr] at hp
          | some a =>
              have ht : run q 2 rest (moveHead a.move head) (applyBounded 2 z a) =
                  some (hf, zp) := by simpa [run, hh, hr] using hp
              simp only [run, body_live z hh, Bool.false_eq_true, ↓reduceIte]
              rw [show (bodyConfig z).state = bodyState z.state by rfl,
                show (bodyConfig z).focus = z.focus by rfl,
                rule_body q entry z slot hh, hr, Option.map_some]
              change run (program q entry) 2 rest (moveHead a.move head)
                (applyBounded 2 (bodyConfig z) (bodyAction a)) = _
              rw [apply_body]
              exact ih _ _ ht

theorem handoff_run (q : BoundedProgram ms 3) (entry : Fin 3 → Fin ms)
    (head : Int) (z : BoundedConfig ms 3) (hz : z.state.val = 0) :
    run (program q entry) 2 [false] head (bodyConfig z) = some (head, loopAt z) := by
  simp only [run, body_accept_live z hz, Bool.false_eq_true, ↓reduceIte]
  rw [show (bodyConfig z).state = bodyState z.state by rfl,
    show (bodyConfig z).focus = z.focus by rfl, rule_handoff q entry z hz]
  simp [applyBounded, loopAt, initial, moveHead, bodyConfig]

theorem sequential_body (q : BoundedProgram ms 3) (entry : Fin 3 → Fin ms)
    (u v : List Bool) (head mid hf : Int) (z zp : BoundedConfig ms 3)
    (out : BoundedConfig (stateCount ms) 3)
    (hp : run q 2 u head z = some (mid, zp)) (ha : zp.state.val = 0)
    (hr : run (program q entry) 2 v mid (loopAt zp) = some (hf, out)) :
    run (program q entry) 2 (u ++ false :: v) head (bodyConfig z) =
      some (hf, out) := by
  have hw : u ++ false :: v = (u ++ [false]) ++ v := by simp [List.append_assoc]
  rw [hw, run_append, run_append, run_body_prefix q entry u head mid z zp hp,
    Option.bind_some, handoff_run q entry mid zp ha, Option.bind_some]
  exact hr

theorem every_raw_body_of_run (q : BoundedProgram ms 3) (entry : Fin 3 → Fin ms)
    (w : List Bool) (head hf : Int) (z : BoundedConfig ms 3)
    (out : BoundedConfig (stateCount ms) 3)
    (hw : run (program q entry) 2 w head (bodyConfig z) = some (hf, out)) :
    (∃ zp, run q 2 w head z = some (hf, zp) ∧ out = bodyConfig zp) ∨
      ∃ u v mid zp, w = u ++ false :: v ∧
        run q 2 u head z = some (mid, zp) ∧ zp.state.val = 0 ∧
        run (program q entry) 2 v mid (loopAt zp) = some (hf, out) := by
  induction w generalizing head z with
  | nil =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at hw
      rcases hw with ⟨rfl, rfl⟩
      exact Or.inl ⟨z, rfl, rfl⟩
  | cons slot rest ih =>
      by_cases hzero : z.state.val = 0
      · cases slot with
        | true =>
            simp only [run, body_accept_live z hzero, Bool.false_eq_true,
              ↓reduceIte] at hw
            rw [show (bodyConfig z).state = bodyState z.state by rfl,
              show (bodyConfig z).focus = z.focus by rfl,
              rule_handoff q entry z hzero] at hw
            cases hw
        | false =>
            have htail : run (program q entry) 2 rest head (loopAt z) =
                some (hf, out) := by
              simp only [run, body_accept_live z hzero, Bool.false_eq_true,
                ↓reduceIte] at hw
              rw [show (bodyConfig z).state = bodyState z.state by rfl,
                show (bodyConfig z).focus = z.focus by rfl,
                rule_handoff q entry z hzero] at hw
              simpa [applyBounded, loopAt, initial, moveHead, bodyConfig] using hw
            exact Or.inr ⟨[], rest, head, z, rfl, rfl, hzero, htail⟩
      · by_cases hone : z.state.val = 1
        · simp [run, body_reject_halted z hone] at hw
        · have hlive : boundedHalted z = false := by
            simp [boundedHalted]
            omega
          cases hrule : q.rule z.state z.focus slot with
          | none =>
              simp only [run, body_live z hlive, Bool.false_eq_true, ↓reduceIte] at hw
              rw [show (bodyConfig z).state = bodyState z.state by rfl,
                show (bodyConfig z).focus = z.focus by rfl,
                rule_body q entry z slot hlive, hrule] at hw
              cases hw
          | some a =>
              have htail : run (program q entry) 2 rest (moveHead a.move head)
                  (bodyConfig (applyBounded 2 z a)) = some (hf, out) := by
                simp only [run, body_live z hlive, Bool.false_eq_true, ↓reduceIte] at hw
                rw [show (bodyConfig z).state = bodyState z.state by rfl,
                  show (bodyConfig z).focus = z.focus by rfl,
                  rule_body q entry z slot hlive, hrule] at hw
                change run (program q entry) 2 rest (moveHead a.move head)
                  (applyBounded 2 (bodyConfig z) (bodyAction a)) = _ at hw
                rw [apply_body] at hw
                exact hw
              rcases ih _ _ htail with hfirst | hsecond
              · obtain ⟨zp, hp, hfz⟩ := hfirst
                refine Or.inl ⟨zp, ?_, hfz⟩
                simpa [run, hlive, hrule] using hp
              · obtain ⟨u, v, mid, zp, he, hp, ha, hloop⟩ := hsecond
                refine Or.inr ⟨slot :: u, v, mid, zp, ?_, ?_, ha, hloop⟩
                · simpa using congrArg (List.cons slot) he
                · simpa [run, hlive, hrule] using hp

theorem every_raw_body_splits (q : BoundedProgram ms 3) (entry : Fin 3 → Fin ms)
    (w : List Bool) (head hf : Int) (z : BoundedConfig ms 3)
    (out : BoundedConfig (stateCount ms) 3) :
    run (program q entry) 2 w head (bodyConfig z) = some (hf, out) ↔
      (∃ zp, run q 2 w head z = some (hf, zp) ∧ out = bodyConfig zp) ∨
        ∃ u v mid zp, w = u ++ false :: v ∧
          run q 2 u head z = some (mid, zp) ∧ zp.state.val = 0 ∧
          run (program q entry) 2 v mid (loopAt zp) = some (hf, out) := by
  constructor
  · exact every_raw_body_of_run q entry w head hf z out
  · rintro (⟨zp, hp, rfl⟩ | ⟨u, v, mid, zp, rfl, hp, ha, hloop⟩)
    · exact run_body_prefix q entry w head hf z zp hp
    · exact sequential_body q entry u v head mid hf z zp out hp ha hloop

theorem run_true_none (q : BoundedProgram ms 3) (entry : Fin 3 → Fin ms)
    (symbol : Fin 3) (left right : List (Fin 3)) (head : Int) (rest : List Bool) :
    run (program q entry) 2 (true :: rest) head
      (initial (ms := ms) symbol left right) = none := by
  simp [run, initial, boundedHalted, program]

theorem run_entry_sentinel (q : BoundedProgram ms 3) (entry : Fin 3 → Fin ms)
    (symbol : Fin 3) (left right : List (Fin 3)) (head : Int) (rest : List Bool)
    (hs : symbol.val = 2) :
    run (program q entry) 2 (false :: rest) head
        (initial (ms := ms) symbol left right) =
      match rest with
      | [] => some (head, sentinelFinal (ms := ms) symbol left right)
      | _ => none := by
  cases rest with
  | nil =>
      simp [run, initial, boundedHalted, program, hs, applyBounded, moveHead,
        sentinelFinal]
  | cons _ _ =>
      simp [run, initial, boundedHalted, program, hs, applyBounded]

theorem run_entry_select (q : BoundedProgram ms 3) (entry : Fin 3 → Fin ms)
    (symbol : Fin 3) (left right : List (Fin 3)) (head : Int) (rest : List Bool)
    (hs : symbol.val ≠ 2) :
    run (program q entry) 2 (false :: rest) head
        (initial (ms := ms) symbol left right) =
      run (program q entry) 2 rest head
        (bodyConfig (selected entry symbol left right)) := by
  simp [run, initial, boundedHalted, program, hs, applyBounded, bodyConfig,
    selected, moveHead]

theorem every_raw_entry_splits (q : BoundedProgram ms 3) (entry : Fin 3 → Fin ms)
    (symbol : Fin 3) (left right : List (Fin 3)) (w : List Bool)
    (head hf : Int) (out : BoundedConfig (stateCount ms) 3) :
    run (program q entry) 2 w head (initial (ms := ms) symbol left right) =
        some (hf, out) ↔
      (w = [] ∧ hf = head ∧ out = initial (ms := ms) symbol left right) ∨
        (symbol.val = 2 ∧ w = [false] ∧ hf = head ∧
          out = sentinelFinal (ms := ms) symbol left right) ∨
        (symbol.val ≠ 2 ∧
          ((∃ v zp, w = false :: v ∧
              run q 2 v head (selected entry symbol left right) = some (hf, zp) ∧
              out = bodyConfig zp) ∨
            ∃ u v mid zp, w = false :: (u ++ false :: v) ∧
              run q 2 u head (selected entry symbol left right) =
                some (mid, zp) ∧ zp.state.val = 0 ∧
              run (program q entry) 2 v mid (loopAt zp) = some (hf, out))) := by
  cases w with
  | nil =>
      simp [run, eq_comm]
  | cons slot rest =>
      cases slot with
      | true =>
          simp [run_true_none]
      | false =>
          by_cases hs : symbol.val = 2
          · rw [run_entry_sentinel q entry symbol left right head rest hs]
            cases rest <;> simp [hs, eq_comm]
          · rw [run_entry_select q entry symbol left right head rest hs,
              every_raw_body_splits]
            simp [hs]

theorem every_raw_entry_accepting (q : BoundedProgram ms 3)
    (entry : Fin 3 → Fin ms) (symbol : Fin 3) (left right : List (Fin 3))
    (w : List Bool) (head hf : Int) (out : BoundedConfig (stateCount ms) 3) :
    run (program q entry) 2 w head (initial (ms := ms) symbol left right) =
        some (hf, out) ∧ out.state.val = 0 ↔
      (symbol.val = 2 ∧ w = [false] ∧ hf = head ∧
          out = sentinelFinal (ms := ms) symbol left right) ∨
        (symbol.val ≠ 2 ∧ ∃ u v mid zp,
          w = false :: (u ++ false :: v) ∧
            run q 2 u head (selected entry symbol left right) = some (mid, zp) ∧
            zp.state.val = 0 ∧
            run (program q entry) 2 v mid (loopAt zp) = some (hf, out) ∧
            out.state.val = 0) := by
  constructor
  · rintro ⟨hw, ha⟩
    rcases (every_raw_entry_splits q entry symbol left right w head hf out).1 hw with
      hnil | hsen | hsel
    · rcases hnil with ⟨rfl, _, rfl⟩
      simp [initial] at ha
    · exact Or.inl hsen
    · rcases hsel with ⟨hs, hpre | hho⟩
      · obtain ⟨v, zp, _, _, rfl⟩ := hpre
        exact (body_not_accept zp ha).elim
      · obtain ⟨u, v, mid, zp, he, hp, hap, hloop⟩ := hho
        exact Or.inr ⟨hs, u, v, mid, zp, he, hp, hap, hloop, ha⟩
  · rintro (⟨hs, rfl, rfl, rfl⟩ | ⟨hs, u, v, mid, zp, rfl, hp, hap, hloop, ha⟩)
    · refine ⟨?_, by simp [sentinelFinal]⟩
      simp [run_entry_sentinel q entry symbol left right hf [] hs]
    · refine ⟨?_, ha⟩
      exact (every_raw_entry_splits q entry symbol left right
          (false :: (u ++ false :: v)) head hf out).2
        (Or.inr (Or.inr ⟨hs, Or.inr ⟨u, v, mid, zp, rfl, hp, hap, hloop⟩⟩))

theorem program_falseOnly (q : BoundedProgram ms 3) (entry : Fin 3 → Fin ms)
    (hq : ULogFiniteAlphabetDeterministicRuns.FalseOnly q) :
    ULogFiniteAlphabetDeterministicRuns.FalseOnly (program q entry) := by
  dsimp [ULogFiniteAlphabetDeterministicRuns.FalseOnly] at hq ⊢
  intro state read; simp [program, hq]

theorem compiled_symbols (q : BoundedProgram ms 3) (entry : Fin 3 → Fin ms) :
    ∀ r ∈ compile (program q entry), r.read < 3 ∧ r.action.write < 3 :=
  fun _ hr => ⟨(compile_rule_bounded (program q entry) hr).2.1,
    (compile_rule_bounded (program q entry) hr).2.2.1⟩

theorem sentinel_growth (q : BoundedProgram ms 3) (entry : Fin 3 → Fin ms)
    (symbol : Fin 3) (left right : List (Fin 3)) (H : Int)
    (hs : symbol.val = 2) :
    GrowthRun (program q entry) 2 [false] H
      (initial (ms := ms) symbol left right) H
      (sentinelFinal (ms := ms) symbol left right) 0 0 := by
  have rule : (program q entry).rule
      (initial (ms := ms) symbol left right).state
      (initial (ms := ms) symbol left right).focus false =
      some ⟨symbol, ⟨0, by unfold stateCount; omega⟩, .stay⟩ := by
    simp [program, initial, hs]
  simpa [applyBounded, leftCharge, rightCharge, initial, sentinelFinal, moveHead]
    using GrowthRun.cons (initial_not_halt (ms := ms) symbol left right) rule
      (GrowthRun.nil (p := program q entry) (blank := (2 : Fin 3)) H _)

theorem entry_growth (q : BoundedProgram ms 3) (entry : Fin 3 → Fin ms)
    (symbol : Fin 3) (left right : List (Fin 3)) (H : Int)
    (hs : symbol.val ≠ 2) :
    GrowthRun (program q entry) 2 [false] H
      (initial (ms := ms) symbol left right) H
      (bodyConfig (selected entry symbol left right)) 0 0 := by
  have rule : (program q entry).rule
      (initial (ms := ms) symbol left right).state
      (initial (ms := ms) symbol left right).focus false =
      some ⟨2, bodyState (entry symbol), .stay⟩ := by
    simp [program, initial, hs]
  simpa [applyBounded, bodyConfig, selected, leftCharge, rightCharge, initial,
    moveHead] using
    GrowthRun.cons (initial_not_halt (ms := ms) symbol left right) rule
      (GrowthRun.nil (p := program q entry) (blank := (2 : Fin 3)) H _)

theorem handoff_growth (q : BoundedProgram ms 3) (entry : Fin 3 → Fin ms)
    (z : BoundedConfig ms 3) (H : Int) (hz : z.state.val = 0) :
    GrowthRun (program q entry) 2 [false] H (bodyConfig z) H (loopAt z) 0 0 := by
  have rule : (program q entry).rule (bodyConfig z).state (bodyConfig z).focus
      false = some ⟨z.focus, ⟨2, by unfold stateCount; omega⟩, .stay⟩ := by
    simpa [bodyConfig] using rule_handoff q entry z hz false
  simpa [applyBounded, loopAt, initial, leftCharge, rightCharge, bodyConfig,
    moveHead] using GrowthRun.cons (body_accept_live z hz) rule
      (GrowthRun.nil (p := program q entry) (blank := (2 : Fin 3)) H _)

theorem source_loop_spec (q : BoundedProgram ms 3) (entry : Fin 3 → Fin ms)
    (symbol : Fin 3) (left right : List (Fin 3)) (H : Int)
    (z : BoundedConfig ms 3) :
    (∀ w hf out, run (program q entry) 2 w H (bodyConfig z) = some (hf, out) ↔
      (∃ zp, run q 2 w H z = some (hf, zp) ∧ out = bodyConfig zp) ∨
        ∃ u v mid zp, w = u ++ false :: v ∧ run q 2 u H z = some (mid, zp) ∧
          zp.state.val = 0 ∧ run (program q entry) 2 v mid (loopAt zp) = some (hf, out)) ∧
    (∀ w hf out, run (program q entry) 2 w H (initial (ms := ms) symbol left right) =
        some (hf, out) ↔
      (w = [] ∧ hf = H ∧ out = initial (ms := ms) symbol left right) ∨
        (symbol.val = 2 ∧ w = [false] ∧ hf = H ∧
          out = sentinelFinal (ms := ms) symbol left right) ∨
        (symbol.val ≠ 2 ∧
          ((∃ v zp, w = false :: v ∧
              run q 2 v H (selected entry symbol left right) = some (hf, zp) ∧
              out = bodyConfig zp) ∨
            ∃ u v mid zp, w = false :: (u ++ false :: v) ∧
              run q 2 u H (selected entry symbol left right) = some (mid, zp) ∧
              zp.state.val = 0 ∧
              run (program q entry) 2 v mid (loopAt zp) = some (hf, out)))) ∧
    (∀ w hf out, run (program q entry) 2 w H (initial (ms := ms) symbol left right) =
        some (hf, out) ∧ out.state.val = 0 ↔
      (symbol.val = 2 ∧ w = [false] ∧ hf = H ∧
          out = sentinelFinal (ms := ms) symbol left right) ∨
        (symbol.val ≠ 2 ∧ ∃ u v mid zp, w = false :: (u ++ false :: v) ∧
          run q 2 u H (selected entry symbol left right) = some (mid, zp) ∧
          zp.state.val = 0 ∧
          run (program q entry) 2 v mid (loopAt zp) = some (hf, out) ∧
          out.state.val = 0)) ∧
    ((symbol.val = 2 → GrowthRun (program q entry) 2 [false] H
        (initial (ms := ms) symbol left right) H
        (sentinelFinal (ms := ms) symbol left right) 0 0) ∧
      (symbol.val ≠ 2 → GrowthRun (program q entry) 2 [false] H
        (initial (ms := ms) symbol left right) H
        (bodyConfig (selected entry symbol left right)) 0 0) ∧
      (z.state.val = 0 →
        GrowthRun (program q entry) 2 [false] H (bodyConfig z) H (loopAt z) 0 0)) :=
  ⟨fun w hf out => every_raw_body_splits q entry w H hf z out,
    fun w hf out => every_raw_entry_splits q entry symbol left right w H hf out,
    fun w hf out => every_raw_entry_accepting q entry symbol left right w H hf out,
    ⟨sentinel_growth q entry symbol left right H,
      entry_growth q entry symbol left right H, handoff_growth q entry z H⟩⟩

end PakFixedPolyomino.ULogTernarySourceLoop
