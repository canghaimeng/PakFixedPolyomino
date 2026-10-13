import PakFixedPolyomino.ULogFiniteAlphabetDeterministicRuns

/-! Literal finite bytecode sequencing. The first accept state becomes a
live handoff state; reject1 remains terminal. One real deterministic tick
enters the second program, optionally moving the head. Configurations keep
all tape cells. These are structural forward lemmas, not an all-run inverse
or a closed source normalization/counting theorem. -/

namespace PakFixedPolyomino.ULogFiniteTapeStageComposition

open ULogCompiler ULogFiniteTapeZipperRun
open FiniteOneTapeSemantics (moveHead)

variable {ns ms nt : Nat}

def stateCount (ns ms : Nat) : Nat := ns + ms + 1

def leftState (q : Fin ns) : Fin (stateCount ns ms) :=
  if q.val = 0 then ⟨ns, by unfold stateCount; omega⟩
  else ⟨q.val, by have h := q.isLt; unfold stateCount; omega⟩

def rightState (q : Fin ms) : Fin (stateCount ns ms) :=
  if q.val < 2 then ⟨q.val, by have h := q.isLt; unfold stateCount; omega⟩
  else ⟨ns + q.val, by have h := q.isLt; unfold stateCount; omega⟩

def leftConfig (z : BoundedConfig ns nt) : BoundedConfig (stateCount ns ms) nt :=
  ⟨leftState z.state, z.leftRev, z.focus, z.right⟩

def rightConfig (z : BoundedConfig ms nt) : BoundedConfig (stateCount ns ms) nt :=
  ⟨rightState z.state, z.leftRev, z.focus, z.right⟩

def leftAction (a : BoundedAction ns nt) : BoundedAction (stateCount ns ms) nt :=
  ⟨a.write, leftState a.target, a.move⟩

def rightAction (a : BoundedAction ms nt) : BoundedAction (stateCount ns ms) nt :=
  ⟨a.write, rightState a.target, a.move⟩

def program (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (handoff : OneTapeTableau.Move) :
    BoundedProgram (stateCount ns ms) nt where
  rule state read slot :=
    if state.val = ns then
      if slot then none else some ⟨read, rightState (⟨2, by omega⟩ : Fin ms), handoff⟩
    else if hleft : state.val < ns then
      (p.rule ⟨state.val, hleft⟩ read slot).map leftAction
    else if hright : ns + 2 ≤ state.val ∧ state.val < ns + ms then
      (q.rule ⟨state.val - ns, by omega⟩ read slot).map rightAction
    else none

theorem apply_left (blank : Fin nt) (z : BoundedConfig ns nt) (a : BoundedAction ns nt) :
    applyBounded blank (leftConfig (ms := ms) z) (leftAction a) =
      leftConfig (applyBounded blank z a) := by
  cases hm : a.move <;> cases hl : z.leftRev <;> cases hr : z.right <;>
    simp [applyBounded, leftConfig, leftAction, hm, hl, hr]

theorem apply_right (blank : Fin nt) (z : BoundedConfig ms nt) (a : BoundedAction ms nt) :
    applyBounded blank (rightConfig (ns := ns) z) (rightAction a) =
      rightConfig (applyBounded blank z a) := by
  cases hm : a.move <;> cases hl : z.leftRev <;> cases hr : z.right <;>
    simp [applyBounded, rightConfig, rightAction, hm, hl, hr]

theorem left_live (z : BoundedConfig ns nt) (hl : boundedHalted z = false) :
    boundedHalted (leftConfig (ms := ms) z) = false := by
  have hq : 2 ≤ z.state.val := by
    have h : 1 < z.state.val := by simpa [boundedHalted] using hl
    omega
  have hne : z.state.val ≠ 0 := by omega
  simpa [boundedHalted, leftConfig, leftState, hne] using hl

theorem right_live (z : BoundedConfig ms nt) (hl : boundedHalted z = false) :
    boundedHalted (rightConfig (ns := ns) z) = false := by
  have hq : 2 ≤ z.state.val := by
    have h : 1 < z.state.val := by simpa [boundedHalted] using hl
    omega
  simp [boundedHalted, rightConfig, rightState, show ¬ z.state.val < 2 by omega]
  omega

theorem rule_left (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (handoff : OneTapeTableau.Move)
    (z : BoundedConfig ns nt) (slot : Bool) (hl : boundedHalted z = false) :
    (program p q hns hms handoff).rule (leftState z.state) z.focus slot =
      (p.rule z.state z.focus slot).map leftAction := by
  have hz := z.state.isLt
  have hq : 2 ≤ z.state.val := by
    have h : 1 < z.state.val := by simpa [boundedHalted] using hl
    omega
  have hne : z.state.val ≠ 0 := by omega
  simp [program, leftState, hne, show z.state.val ≠ ns by omega, hz]

theorem rule_right (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (handoff : OneTapeTableau.Move)
    (z : BoundedConfig ms nt) (slot : Bool) (hl : boundedHalted z = false) :
    (program p q hns hms handoff).rule (rightState z.state) z.focus slot =
      (q.rule z.state z.focus slot).map rightAction := by
  have hz := z.state.isLt
  have hq : 2 ≤ z.state.val := by
    have h : 1 < z.state.val := by simpa [boundedHalted] using hl
    omega
  simp [program, rightState, show ¬ z.state.val < 2 by omega,
    show z.state.val ≠ 0 by omega,
    show ns + z.state.val ≠ ns by omega, show ¬ ns + z.state.val < ns by omega,
    show ns + 2 ≤ ns + z.state.val by omega, show ns + z.state.val < ns + ms by omega]

theorem run_left (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (handoff : OneTapeTableau.Move)
    (blank : Fin nt) (w : List Bool) (head hf : Int) (z zf : BoundedConfig ns nt)
    (hrun : run p blank w head z = some (hf, zf)) :
    run (program p q hns hms handoff) blank w head (leftConfig z) =
      some (hf, leftConfig zf) := by
  induction w generalizing head z with
  | nil =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at hrun
      rcases hrun with ⟨rfl, rfl⟩
      rfl
  | cons slot rest ih =>
      cases hh : boundedHalted z with
      | true => simp [run, hh] at hrun
      | false =>
          cases hr : p.rule z.state z.focus slot with
          | none => simp [run, hh, hr] at hrun
          | some a =>
              have ht : run p blank rest (moveHead a.move head) (applyBounded blank z a) =
                  some (hf, zf) := by simpa [run, hh, hr] using hrun
              simp only [run, left_live z hh, Bool.false_eq_true, ↓reduceIte]
              rw [show (leftConfig z).state = leftState z.state by rfl,
                show (leftConfig z).focus = z.focus by rfl, rule_left p q hns hms handoff z slot hh,
                hr, Option.map_some]
              change run (program p q hns hms handoff) blank rest
                (moveHead a.move head) (applyBounded blank (leftConfig z) (leftAction a)) = _
              rw [apply_left]
              exact ih _ _ ht

theorem run_right (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (handoff : OneTapeTableau.Move)
    (blank : Fin nt) (w : List Bool) (head hf : Int) (z zf : BoundedConfig ms nt)
    (hrun : run q blank w head z = some (hf, zf)) :
    run (program p q hns hms handoff) blank w head (rightConfig z) =
      some (hf, rightConfig zf) := by
  induction w generalizing head z with
  | nil =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at hrun
      rcases hrun with ⟨rfl, rfl⟩
      rfl
  | cons slot rest ih =>
      cases hh : boundedHalted z with
      | true => simp [run, hh] at hrun
      | false =>
          cases hr : q.rule z.state z.focus slot with
          | none => simp [run, hh, hr] at hrun
          | some a =>
              have ht : run q blank rest (moveHead a.move head) (applyBounded blank z a) =
                  some (hf, zf) := by simpa [run, hh, hr] using hrun
              simp only [run, right_live z hh, Bool.false_eq_true, ↓reduceIte]
              rw [show (rightConfig z).state = rightState z.state by rfl,
                show (rightConfig z).focus = z.focus by rfl, rule_right p q hns hms handoff z slot hh,
                hr, Option.map_some]
              change run (program p q hns hms handoff) blank rest
                (moveHead a.move head) (applyBounded blank (rightConfig z) (rightAction a)) = _
              rw [apply_right]
              exact ih _ _ ht

def secondStart (hms : 3 ≤ ms) (blank : Fin nt) (handoff : OneTapeTableau.Move)
    (z : BoundedConfig ns nt) : BoundedConfig ms nt :=
  applyBounded blank ⟨⟨2, by omega⟩, z.leftRev, z.focus, z.right⟩
    ⟨z.focus, ⟨2, by omega⟩, handoff⟩

theorem handoff_run (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (handoff : OneTapeTableau.Move)
    (blank : Fin nt) (head : Int) (z : BoundedConfig ns nt) (hz : z.state.val = 0) :
    run (program p q hns hms handoff) blank [false] head (leftConfig z) =
      some (moveHead handoff head, rightConfig (secondStart hms blank handoff z)) := by
  have hnsLive : ¬ ns < 2 := by omega
  cases hm : handoff <;> cases hl : z.leftRev <;> cases hr : z.right <;>
    simp [run, program, boundedHalted, leftConfig, leftState, hz, hnsLive,
      rightConfig, rightState, secondStart, applyBounded, hm, hl, hr]

theorem sequential_run (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (handoff : OneTapeTableau.Move)
    (blank : Fin nt) (w v : List Bool) (head mid hf : Int)
    (z zp : BoundedConfig ns nt) (zq : BoundedConfig ms nt)
    (hp : run p blank w head z = some (mid, zp)) (ha : zp.state.val = 0)
    (hq : run q blank v (moveHead handoff mid) (secondStart hms blank handoff zp) =
      some (hf, zq)) :
    run (program p q hns hms handoff) blank (w ++ false :: v) head (leftConfig z) =
      some (hf, rightConfig zq) := by
  have hw : w ++ false :: v = (w ++ [false]) ++ v := by simp [List.append_assoc]
  rw [hw, run_append, run_append, run_left p q hns hms handoff blank w head mid z zp hp,
    Option.bind_some, handoff_run p q hns hms handoff blank mid zp ha, Option.bind_some]
  exact run_right p q hns hms handoff blank v _ hf _ zq hq

end PakFixedPolyomino.ULogFiniteTapeStageComposition
