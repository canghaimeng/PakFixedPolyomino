import PakFixedPolyomino.ULogFiniteTapeStageCompositionRuns

/-! Literal finite test/body feedback. Test accept0 enters the body; test
reject1 ends the whole loop at accept0. Body accept0 returns to the test;
body reject1 stays reject1. Each transfer is one real false STAY tick.
Concrete margin termination/count/time must instantiate this controller. -/
namespace PakFixedPolyomino.ULogFiniteTapeTestBodyLoop
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open FiniteOneTapeSemantics (moveHead)
variable {ns ms nt : Nat}

def stateCount (ns ms : Nat) := ns + ms + 2
def testState (q : Fin ns) : Fin (stateCount ns ms) :=
  if q.val = 0 then ⟨ns + ms, by unfold stateCount; omega⟩
  else if q.val = 1 then ⟨0, by unfold stateCount; omega⟩
  else ⟨q.val, by have := q.isLt; unfold stateCount; omega⟩
def bodyState (q : Fin ms) : Fin (stateCount ns ms) :=
  if q.val = 0 then ⟨ns + ms + 1, by unfold stateCount; omega⟩
  else if q.val = 1 then ⟨1, by unfold stateCount; omega⟩
  else ⟨ns + q.val, by have := q.isLt; unfold stateCount; omega⟩
def testConfig (z : BoundedConfig ns nt) : BoundedConfig (stateCount ns ms) nt :=
  ⟨testState z.state, z.leftRev, z.focus, z.right⟩
def bodyConfig (z : BoundedConfig ms nt) : BoundedConfig (stateCount ns ms) nt :=
  ⟨bodyState z.state, z.leftRev, z.focus, z.right⟩
def testAction (a : BoundedAction ns nt) : BoundedAction (stateCount ns ms) nt :=
  ⟨a.write, testState a.target, a.move⟩
def bodyAction (a : BoundedAction ms nt) : BoundedAction (stateCount ns ms) nt :=
  ⟨a.write, bodyState a.target, a.move⟩
def program (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) : BoundedProgram (stateCount ns ms) nt where
  rule state read slot :=
    if state.val = ns + ms then
      if slot then none else some ⟨read, bodyState ⟨2, by omega⟩, .stay⟩
    else if state.val = ns + ms + 1 then
      if slot then none else some ⟨read, testState ⟨2, by omega⟩, .stay⟩
    else if h : state.val < ns then
      (p.rule ⟨state.val, h⟩ read slot).map testAction
    else if h : ns + 2 ≤ state.val ∧ state.val < ns + ms then
      (q.rule ⟨state.val - ns, by omega⟩ read slot).map bodyAction
    else none

theorem apply_test (blank : Fin nt) (z : BoundedConfig ns nt) (a : BoundedAction ns nt) :
    applyBounded blank (testConfig (ms := ms) z) (testAction a) =
      testConfig (applyBounded blank z a) := by
  cases hm : a.move <;> cases hl : z.leftRev <;> cases hr : z.right <;>
    simp [applyBounded, testConfig, testAction, hm, hl, hr]
theorem apply_body (blank : Fin nt) (z : BoundedConfig ms nt) (a : BoundedAction ms nt) :
    applyBounded blank (bodyConfig (ns := ns) z) (bodyAction a) =
      bodyConfig (applyBounded blank z a) := by
  cases hm : a.move <;> cases hl : z.leftRev <;> cases hr : z.right <;>
    simp [applyBounded, bodyConfig, bodyAction, hm, hl, hr]
theorem test_live (z : BoundedConfig ns nt) (hz : boundedHalted z = false) :
    boundedHalted (testConfig (ms := ms) z) = false := by
  have hq : 2 ≤ z.state.val := by
    have : 1 < z.state.val := by simpa [boundedHalted] using hz
    omega
  simp [boundedHalted, testConfig, testState, show z.state.val ≠ 0 by omega,
    show z.state.val ≠ 1 by omega]; omega
theorem body_live (z : BoundedConfig ms nt) (hz : boundedHalted z = false) :
    boundedHalted (bodyConfig (ns := ns) z) = false := by
  have hq : 2 ≤ z.state.val := by
    have : 1 < z.state.val := by simpa [boundedHalted] using hz
    omega
  simp [boundedHalted, bodyConfig, bodyState, show z.state.val ≠ 0 by omega,
    show z.state.val ≠ 1 by omega]; omega

theorem rule_test (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (z : BoundedConfig ns nt) (slot : Bool)
    (live : boundedHalted z = false) :
    (program p q hns hms).rule (testState z.state) z.focus slot =
      (p.rule z.state z.focus slot).map testAction := by
  have hq : 2 ≤ z.state.val := by
    have : 1 < z.state.val := by simpa [boundedHalted] using live
    omega
  have hz := z.state.isLt
  simp [program, testState, show z.state.val ≠ 0 by omega, show z.state.val ≠ 1 by omega,
    show z.state.val ≠ ns + ms by omega, show z.state.val ≠ ns + ms + 1 by omega, hz]
theorem rule_body (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (z : BoundedConfig ms nt) (slot : Bool)
    (live : boundedHalted z = false) :
    (program p q hns hms).rule (bodyState z.state) z.focus slot =
      (q.rule z.state z.focus slot).map bodyAction := by
  have hq : 2 ≤ z.state.val := by
    have : 1 < z.state.val := by simpa [boundedHalted] using live
    omega
  have hz := z.state.isLt
  simp [program, bodyState, show z.state.val ≠ 0 by omega, show z.state.val ≠ 1 by omega,
    show z.state.val ≠ ms by omega, show z.state.val ≠ ms + 1 by omega,
    show ns + z.state.val ≠ ns + ms by omega, show ns + z.state.val ≠ ns + ms + 1 by omega,
    show ¬ ns + z.state.val < ns by omega,
    show ns + 2 ≤ ns + z.state.val by omega, show ns + z.state.val < ns + ms by omega]

theorem run_test (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (blank : Fin nt) (w : List Bool)
    (H hf : Int) (z out : BoundedConfig ns nt)
    (hw : run p blank w H z = some (hf, out)) :
    run (program p q hns hms) blank w H (testConfig z) = some (hf, testConfig out) := by
  induction w generalizing H z with
  | nil =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at hw
      rcases hw with ⟨rfl, rfl⟩; rfl
  | cons slot rest ih =>
      cases hh : boundedHalted z with
      | true => simp [run, hh] at hw
      | false =>
          cases hr : p.rule z.state z.focus slot with
          | none => simp [run, hh, hr] at hw
          | some a =>
              have ht : run p blank rest (moveHead a.move H) (applyBounded blank z a) =
                  some (hf, out) := by simpa [run, hh, hr] using hw
              simp only [run, test_live z hh, Bool.false_eq_true, ↓reduceIte]
              rw [show (testConfig z).state = testState (ms := ms) z.state by rfl,
                show (testConfig (ms := ms) z).focus = z.focus by rfl,
                rule_test p q hns hms z slot hh, hr, Option.map_some]
              change run (program p q hns hms) blank rest (moveHead a.move H)
                (applyBounded blank (testConfig z) (testAction a)) = _
              rw [apply_test]
              exact ih _ _ ht

theorem run_body (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (blank : Fin nt) (w : List Bool)
    (H hf : Int) (z out : BoundedConfig ms nt)
    (hw : run q blank w H z = some (hf, out)) :
    run (program p q hns hms) blank w H (bodyConfig z) = some (hf, bodyConfig out) := by
  induction w generalizing H z with
  | nil =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at hw
      rcases hw with ⟨rfl, rfl⟩; rfl
  | cons slot rest ih =>
      cases hh : boundedHalted z with
      | true => simp [run, hh] at hw
      | false =>
          cases hr : q.rule z.state z.focus slot with
          | none => simp [run, hh, hr] at hw
          | some a =>
              have ht : run q blank rest (moveHead a.move H) (applyBounded blank z a) =
                  some (hf, out) := by simpa [run, hh, hr] using hw
              simp only [run, body_live z hh, Bool.false_eq_true, ↓reduceIte]
              rw [show (bodyConfig z).state = bodyState (ns := ns) z.state by rfl,
                show (bodyConfig (ns := ns) z).focus = z.focus by rfl,
                rule_body p q hns hms z slot hh, hr, Option.map_some]
              change run (program p q hns hms) blank rest (moveHead a.move H)
                (applyBounded blank (bodyConfig z) (bodyAction a)) = _
              rw [apply_body]
              exact ih _ _ ht

def bodyStart (hms : 3 ≤ ms) (z : BoundedConfig ns nt) : BoundedConfig ms nt :=
  ⟨⟨2, by omega⟩, z.leftRev, z.focus, z.right⟩
def testStart (hns : 3 ≤ ns) (z : BoundedConfig ms nt) : BoundedConfig ns nt :=
  ⟨⟨2, by omega⟩, z.leftRev, z.focus, z.right⟩

theorem test_handoff (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (blank : Fin nt) (H : Int)
    (z : BoundedConfig ns nt) (ha : z.state.val = 0) :
    run (program p q hns hms) blank [false] H (testConfig z) =
      some (H, bodyConfig (bodyStart hms z)) := by
  have hsum : ¬ ns + ms < 2 := by omega
  simp [run, program, testConfig, testState, ha, boundedHalted, hsum,
    applyBounded, moveHead, bodyConfig, bodyStart]
theorem body_handoff (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (blank : Fin nt) (H : Int)
    (z : BoundedConfig ms nt) (ha : z.state.val = 0) :
    run (program p q hns hms) blank [false] H (bodyConfig z) =
      some (H, testConfig (testStart hns z)) := by
  have hsum : ¬ ns + ms + 1 < 2 := by omega
  simp [run, program, bodyConfig, bodyState, ha, boundedHalted, hsum,
    applyBounded, moveHead, testConfig, testStart]

theorem test_stop_accepts (z : BoundedConfig ns nt) (ha : z.state.val = 1) :
    (testConfig (ms := ms) z).state.val = 0 := by simp [testConfig, testState, ha]
theorem body_rejects (z : BoundedConfig ms nt) (ha : z.state.val = 1) :
    (bodyConfig (ns := ns) z).state.val = 1 := by simp [bodyConfig, bodyState, ha]

theorem cycle_run (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (blank : Fin nt) (u v : List Bool)
    (H mid hf : Int) (z zp : BoundedConfig ns nt) (zq : BoundedConfig ms nt)
    (hp : run p blank u H z = some (mid, zp)) (ha : zp.state.val = 0)
    (hq : run q blank v mid (bodyStart hms zp) = some (hf, zq)) (hb : zq.state.val = 0) :
    run (program p q hns hms) blank ((u ++ [false]) ++ (v ++ [false])) H (testConfig z) =
      some (hf, testConfig (testStart hns zq)) := by
  rw [run_append, run_append, run_test p q hns hms blank u H mid z zp hp, Option.bind_some,
    test_handoff p q hns hms blank mid zp ha, Option.bind_some,
    run_append, run_body p q hns hms blank v mid hf _ zq hq, Option.bind_some,
    body_handoff p q hns hms blank hf zq hb]

theorem program_falseOnly (p : BoundedProgram ns nt) (q : BoundedProgram ms nt)
    (hns : 3 ≤ ns) (hms : 3 ≤ ms) (hp : FalseOnly p) (hq : FalseOnly q) :
    FalseOnly (program p q hns hms) := by
  dsimp [FalseOnly] at hp hq ⊢
  intro state read
  simp [program, hp, hq]

end PakFixedPolyomino.ULogFiniteTapeTestBodyLoop
