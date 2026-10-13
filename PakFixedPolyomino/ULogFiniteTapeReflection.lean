import PakFixedPolyomino.ULogFiniteTapeSymbolDispatch
import PakFixedPolyomino.ULogFiniteTapeGrowthLedger

/-! Literal reflection of finite tape programs. It preserves each raw label,
including coincident transition effects, and exchanges the physical head
coordinate H with -H. Used for left and right loader movements. -/
namespace PakFixedPolyomino.ULogFiniteTapeReflection
open ULogCompiler ULogFiniteTapeZipperRun
open ULogFiniteTapeGrowthLedger
open ULogFiniteTapeSymbolDispatch (RawAccepting RawAcceptingWords)
open FiniteOneTapeSemantics (moveHead)

variable {ns nt : Nat}

def reflectMove : OneTapeTableau.Move → OneTapeTableau.Move
  | .stay => .stay
  | .left => .right
  | .right => .left

def reflectAction (a : BoundedAction ns nt) : BoundedAction ns nt :=
  ⟨a.write, a.target, reflectMove a.move⟩

def reflectConfig (z : BoundedConfig ns nt) : BoundedConfig ns nt :=
  ⟨z.state, z.right, z.focus, z.leftRev⟩

def program (p : BoundedProgram ns nt) : BoundedProgram ns nt where
  rule q read slot := (p.rule q read slot).map reflectAction

theorem program_falseOnly (p : BoundedProgram ns nt)
    (hp : ULogFiniteAlphabetDeterministicRuns.FalseOnly p) :
    ULogFiniteAlphabetDeterministicRuns.FalseOnly (program p) := by
  dsimp [ULogFiniteAlphabetDeterministicRuns.FalseOnly] at hp ⊢
  intro q read
  simp [program, hp]

theorem config_involutive (z : BoundedConfig ns nt) :
    reflectConfig (reflectConfig z) = z := by cases z; rfl

theorem action_involutive (a : BoundedAction ns nt) :
    reflectAction (reflectAction a) = a := by
  cases a with
  | mk write target move => cases move <;> rfl

theorem move_head (move : OneTapeTableau.Move) (H : Int) :
    moveHead (reflectMove move) (-H) = -(moveHead move H) := by
  cases move <;> simp [reflectMove, moveHead] <;> omega

theorem halted_reflect (z : BoundedConfig ns nt) :
    boundedHalted (reflectConfig z) = boundedHalted z := rfl

theorem accepts_reflect (z : BoundedConfig ns nt) :
    (reflectConfig z).state.val = 0 ↔ z.state.val = 0 := Iff.rfl

theorem cellCount_reflect (z : BoundedConfig ns nt) :
    cellCount (reflectConfig z) = cellCount z := by
  simp [cellCount, reflectConfig]
  omega

theorem apply_reflect (blank : Fin nt) (z : BoundedConfig ns nt) (a : BoundedAction ns nt) :
    applyBounded blank (reflectConfig z) (reflectAction a) =
      reflectConfig (applyBounded blank z a) := by
  cases hm : a.move <;> cases hl : z.leftRev <;> cases hr : z.right <;>
    simp [applyBounded, reflectConfig, reflectAction, reflectMove, hm, hl, hr]

theorem run_reflect (p : BoundedProgram ns nt) (blank : Fin nt)
    (w : List Bool) (H : Int) (z : BoundedConfig ns nt) :
    run (program p) blank w (-H) (reflectConfig z) =
      (run p blank w H z).map (fun hz => (-hz.1, reflectConfig hz.2)) := by
  induction w generalizing H z with
  | nil => rfl
  | cons slot rest ih =>
      cases hh : boundedHalted z with
      | true => simp [run, halted_reflect, hh]
      | false =>
          cases ha : p.rule z.state z.focus slot with
          | none => simp [run, halted_reflect, hh, program, reflectConfig, ha]
          | some a =>
              simp only [run, halted_reflect, hh, Bool.false_eq_true, ↓reduceIte]
              rw [show (program p).rule (reflectConfig z).state (reflectConfig z).focus slot =
                some (reflectAction a) by simp [program, reflectConfig, ha], ha]
              change run (program p) blank rest
                (moveHead (reflectMove a.move) (-H))
                (applyBounded blank (reflectConfig z) (reflectAction a)) = _
              rw [move_head, apply_reflect]
              exact ih _ _

theorem every_raw_inverse (p : BoundedProgram ns nt) (blank : Fin nt)
    (w : List Bool) (H hf : Int) (z out : BoundedConfig ns nt) :
    run (program p) blank w H z = some (hf, out) ↔
      run p blank w (-H) (reflectConfig z) = some (-hf, reflectConfig out) := by
  have transfer := run_reflect p blank w (-H) (reflectConfig z)
  simp only [neg_neg, config_involutive] at transfer
  rw [transfer]
  cases hr : run p blank w (-H) (reflectConfig z) with
  | none => simp
  | some hz =>
      cases hz with
      | mk h c =>
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
          constructor
          · rintro ⟨hh, hc⟩
            refine ⟨by omega, ?_⟩
            have h := congrArg reflectConfig hc
            simpa only [config_involutive] using h
          · rintro ⟨rfl, rfl⟩
            simp [config_involutive]

theorem every_raw_accepting (p : BoundedProgram ns nt) (blank : Fin nt)
    (H : Int) (z : BoundedConfig ns nt) (w : List Bool) :
    RawAccepting (program p) blank H z w ↔
      RawAccepting p blank (-H) (reflectConfig z) w := by
  constructor
  · rintro ⟨hf, out, raw, accepts⟩
    exact ⟨-hf, reflectConfig out, (every_raw_inverse p blank w H hf z out).1 raw, accepts⟩
  · rintro ⟨hf, out, raw, accepts⟩
    refine ⟨-hf, reflectConfig out, ?_, accepts⟩
    apply (every_raw_inverse p blank w H (-hf) z (reflectConfig out)).2
    simpa only [neg_neg, config_involutive] using raw

noncomputable def acceptingWordsEquiv (p : BoundedProgram ns nt) (blank : Fin nt)
    (H : Int) (z : BoundedConfig ns nt) (T : Nat) :
    RawAcceptingWords (program p) blank H z T ≃
      RawAcceptingWords p blank (-H) (reflectConfig z) T where
  toFun w := ⟨w.val, w.property.1, (every_raw_accepting p blank H z w.val).1 w.property.2⟩
  invFun w := ⟨w.val, w.property.1, (every_raw_accepting p blank H z w.val).2 w.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem all_cutoff_counts (p : BoundedProgram ns nt) (blank : Fin nt)
    (H : Int) (z : BoundedConfig ns nt) (T : Nat) :
    Nat.card (RawAcceptingWords (program p) blank H z T) =
      Nat.card (RawAcceptingWords p blank (-H) (reflectConfig z) T) :=
  Nat.card_congr (acceptingWordsEquiv p blank H z T)

theorem reflection_spec (p : BoundedProgram ns nt) (blank : Fin nt)
    (H : Int) (z : BoundedConfig ns nt) :
    (∀ w hf out, run (program p) blank w H z = some (hf, out) ↔
      run p blank w (-H) (reflectConfig z) = some (-hf, reflectConfig out)) ∧
    (∀ w, RawAccepting (program p) blank H z w ↔
      RawAccepting p blank (-H) (reflectConfig z) w) ∧
    (∀ T, Nat.card (RawAcceptingWords (program p) blank H z T) =
      Nat.card (RawAcceptingWords p blank (-H) (reflectConfig z) T)) :=
  ⟨(fun w hf out => every_raw_inverse p blank w H hf z out),
    every_raw_accepting p blank H z, all_cutoff_counts p blank H z⟩

end PakFixedPolyomino.ULogFiniteTapeReflection
