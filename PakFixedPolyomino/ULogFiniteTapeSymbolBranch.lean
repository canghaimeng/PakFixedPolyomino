import PakFixedPolyomino.ULogFiniteTapeSymbolDispatch
import Mathlib.Tactic.FinCases

/-! A literal ternary symbol selects one of three finite programs. The
selected live state copy remembers that symbol throughout the parent run.
Every subsequent label is retained, including duplicate rule effects and
immediate acceptance. This is a finite controller, not a bit-cost compiler
or a complete compact loader. -/
namespace PakFixedPolyomino.ULogFiniteTapeSymbolBranch
open ULogCompiler ULogFiniteTapeZipperRun
open ULogFiniteTapeSymbolDispatch (RawAccepting RawAcceptingWords)
open FiniteOneTapeSemantics (moveHead)

variable {ms nt : Nat}

def stateCount (ms : Nat) : Nat := 2 + 3 * ms

def branchState (symbol : Fin 3) (q : Fin ms) : Fin (stateCount ms) :=
  if h : q.val < 2 then ⟨q.val, by unfold stateCount; omega⟩
  else ⟨2 + symbol.val * ms + q.val, by
    have hq := q.isLt
    have hs : symbol.val * ms ≤ 2 * ms := Nat.mul_le_mul_right ms (by omega)
    unfold stateCount; omega⟩

def branchConfig (symbol : Fin 3) (z : BoundedConfig ms nt) :
    BoundedConfig (stateCount ms) nt :=
  ⟨branchState symbol z.state, z.leftRev, z.focus, z.right⟩

def branchAction (symbol : Fin 3) (a : BoundedAction ms nt) :
    BoundedAction (stateCount ms) nt :=
  ⟨a.write, branchState symbol a.target, a.move⟩

def program (parents : Fin 3 → BoundedProgram ms nt) :
    BoundedProgram (stateCount ms) nt where
  rule state read slot :=
    if hzero : 2 ≤ state.val ∧ state.val < 2 + ms then
      ((parents 0).rule ⟨state.val - 2, by omega⟩ read slot).map (branchAction 0)
    else if hone : 2 + ms ≤ state.val ∧ state.val < 2 + 2 * ms then
      ((parents 1).rule ⟨state.val - (2 + ms), by omega⟩ read slot).map (branchAction 1)
    else if htwo : 2 + 2 * ms ≤ state.val ∧ state.val < 2 + 3 * ms then
      ((parents 2).rule ⟨state.val - (2 + 2 * ms), by omega⟩ read slot).map (branchAction 2)
    else none

theorem program_falseOnly (parents : Fin 3 → BoundedProgram ms nt)
    (hp : ∀ symbol, ULogFiniteAlphabetDeterministicRuns.FalseOnly (parents symbol)) :
    ULogFiniteAlphabetDeterministicRuns.FalseOnly (program parents) := by
  dsimp [ULogFiniteAlphabetDeterministicRuns.FalseOnly] at hp ⊢
  intro state read
  dsimp [program]
  split_ifs <;> simp [hp]

theorem branch_halted (symbol : Fin 3) (z : BoundedConfig ms nt) :
    boundedHalted (branchConfig symbol z) = boundedHalted z := by
  by_cases h : z.state.val < 2
  · simp [boundedHalted, branchConfig, branchState, h]
  · simp [boundedHalted, branchConfig, branchState, h]
    omega

theorem branch_accepts (symbol : Fin 3) (z : BoundedConfig ms nt) :
    (branchConfig symbol z).state.val = 0 ↔ z.state.val = 0 := by
  by_cases h : z.state.val < 2
  · simp [branchConfig, branchState, h]
  · simp [branchConfig, branchState, h]
    omega

theorem apply_branch (symbol : Fin 3) (blank : Fin nt)
    (z : BoundedConfig ms nt) (a : BoundedAction ms nt) :
    applyBounded blank (branchConfig symbol z) (branchAction symbol a) =
      branchConfig symbol (applyBounded blank z a) := by
  cases hm : a.move <;> cases hl : z.leftRev <;> cases hr : z.right <;>
    simp [applyBounded, branchConfig, branchAction, hm, hl, hr]

theorem rule_branch (parents : Fin 3 → BoundedProgram ms nt)
    (symbol : Fin 3) (z : BoundedConfig ms nt) (slot : Bool)
    (live : boundedHalted z = false) :
    (program parents).rule (branchState symbol z.state) z.focus slot =
      ((parents symbol).rule z.state z.focus slot).map (branchAction symbol) := by
  have hz := z.state.isLt
  have hq : 2 ≤ z.state.val := by
    have : 1 < z.state.val := by simpa [boundedHalted] using live
    omega
  have hsmall : ¬ z.state.val < 2 := by omega
  fin_cases symbol <;>
    simp [program, branchState, hsmall,
      show 2 ≤ 2 + z.state.val by omega,
      show 2 + z.state.val < 2 + ms by omega,
      show ¬ 2 + ms + z.state.val < 2 + ms by omega,
      show 2 + ms ≤ 2 + ms + z.state.val by omega,
      show 2 + ms + z.state.val < 2 + 2 * ms by omega,
      show ¬ 2 + 2 * ms + z.state.val < 2 + ms by omega,
      show ¬ 2 + 2 * ms + z.state.val < 2 + 2 * ms by omega,
      show 2 + 2 * ms ≤ 2 + 2 * ms + z.state.val by omega,
      show 2 + 2 * ms + z.state.val < 2 + 3 * ms by omega]

theorem run_branch_map (parents : Fin 3 → BoundedProgram ms nt)
    (symbol : Fin 3) (blank : Fin nt) (word : List Bool)
    (head : Int) (z : BoundedConfig ms nt) :
    run (program parents) blank word head (branchConfig symbol z) =
      (run (parents symbol) blank word head z).map
        (fun hz => (hz.1, branchConfig symbol hz.2)) := by
  induction word generalizing head z with
  | nil => rfl
  | cons slot rest ih =>
      cases hh : boundedHalted z with
      | true => simp [run, branch_halted, hh]
      | false =>
          cases hr : (parents symbol).rule z.state z.focus slot with
          | none =>
              simp only [run, branch_halted, hh, Bool.false_eq_true, ↓reduceIte]
              rw [show (branchConfig symbol z).state = branchState symbol z.state by rfl,
                show (branchConfig symbol z).focus = z.focus by rfl,
                rule_branch parents symbol z slot hh, hr]
              rfl
          | some a =>
              simp only [run, branch_halted, hh, Bool.false_eq_true, ↓reduceIte]
              rw [show (branchConfig symbol z).state = branchState symbol z.state by rfl,
                show (branchConfig symbol z).focus = z.focus by rfl,
                rule_branch parents symbol z slot hh, hr]
              change run (program parents) blank rest (moveHead a.move head)
                (applyBounded blank (branchConfig symbol z) (branchAction symbol a)) = _
              rw [apply_branch]
              exact ih _ _

theorem every_raw_accepting (parents : Fin 3 → BoundedProgram ms nt)
    (symbol : Fin 3) (blank : Fin nt) (head : Int)
    (z : BoundedConfig ms nt) (word : List Bool) :
    RawAccepting (program parents) blank head (branchConfig symbol z) word ↔
      RawAccepting (parents symbol) blank head z word := by
  unfold RawAccepting
  constructor
  · rintro ⟨hf, out, hrun, accepts⟩
    rw [run_branch_map] at hrun
    obtain ⟨⟨h, zp⟩, raw, eq⟩ := Option.map_eq_some_iff.mp hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
    exact ⟨h, zp, raw, (branch_accepts symbol zp).1 accepts⟩
  · rintro ⟨hf, out, raw, accepts⟩
    refine ⟨hf, branchConfig symbol out, ?_, (branch_accepts symbol out).2 accepts⟩
    rw [run_branch_map, raw]
    rfl

noncomputable def acceptingWordsEquiv (parents : Fin 3 → BoundedProgram ms nt)
    (symbol : Fin 3) (blank : Fin nt) (head : Int)
    (z : BoundedConfig ms nt) (T : Nat) :
    RawAcceptingWords (program parents) blank head (branchConfig symbol z) T ≃
      RawAcceptingWords (parents symbol) blank head z T where
  toFun word := ⟨word.val, word.property.1,
    (every_raw_accepting parents symbol blank head z word.val).1 word.property.2⟩
  invFun word := ⟨word.val, word.property.1,
    (every_raw_accepting parents symbol blank head z word.val).2 word.property.2⟩
  left_inv word := by apply Subtype.ext; rfl
  right_inv word := by apply Subtype.ext; rfl

def dispatch (parents : Fin 3 → BoundedProgram ms 3)
    (entry : Fin 3 → Fin ms) (clear : Fin 3) :=
  ULogFiniteTapeSymbolDispatch.program (program parents)
    (fun symbol => branchState symbol (entry symbol)) clear

def selectedStart (entry : Fin 3 → Fin ms) (clear symbol : Fin 3)
    (left right : List (Fin 3)) : BoundedConfig ms 3 :=
  ⟨entry symbol, left, clear, right⟩

theorem dispatch_every_raw_accepting (parents : Fin 3 → BoundedProgram ms 3)
    (entry : Fin 3 → Fin ms) (clear blank symbol : Fin 3)
    (left right : List (Fin 3)) (head : Int) (word : List Bool) :
    RawAccepting (dispatch parents entry clear) blank head
      (ULogFiniteTapeSymbolDispatch.initial symbol left right) word ↔
      ∃ rest, word = false :: rest ∧ RawAccepting (parents symbol) blank head
        (selectedStart entry clear symbol left right) rest := by
  unfold dispatch
  rw [ULogFiniteTapeSymbolDispatch.every_raw_accepting_splits]
  change (∃ rest, word = false :: rest ∧
    RawAccepting (program parents) blank head
      (branchConfig symbol (selectedStart entry clear symbol left right)) rest) ↔ _
  simp_rw [every_raw_accepting]

noncomputable def dispatchWordsEquiv (parents : Fin 3 → BoundedProgram ms 3)
    (entry : Fin 3 → Fin ms) (clear blank symbol : Fin 3)
    (left right : List (Fin 3)) (head : Int) (T : Nat) :
    RawAcceptingWords (dispatch parents entry clear) blank head
      (ULogFiniteTapeSymbolDispatch.initial symbol left right) (T + 1) ≃
      RawAcceptingWords (parents symbol) blank head
        (selectedStart entry clear symbol left right) T :=
  (ULogFiniteTapeSymbolDispatch.acceptingWordsEquiv (program parents)
    (fun symbol => branchState symbol (entry symbol)) clear blank symbol left right head T).trans
    (acceptingWordsEquiv parents symbol blank head
      (selectedStart entry clear symbol left right) T)

theorem all_dispatch_cutoff_counts (parents : Fin 3 → BoundedProgram ms 3)
    (entry : Fin 3 → Fin ms) (clear blank symbol : Fin 3)
    (left right : List (Fin 3)) (head : Int) (T : Nat) :
    Nat.card (RawAcceptingWords (dispatch parents entry clear) blank head
      (ULogFiniteTapeSymbolDispatch.initial symbol left right) (T + 1)) =
      Nat.card (RawAcceptingWords (parents symbol) blank head
        (selectedStart entry clear symbol left right) T) :=
  Nat.card_congr (dispatchWordsEquiv parents entry clear blank symbol left right head T)

theorem dispatch_falseOnly (parents : Fin 3 → BoundedProgram ms 3)
    (entry : Fin 3 → Fin ms) (clear : Fin 3)
    (hp : ∀ symbol, ULogFiniteAlphabetDeterministicRuns.FalseOnly (parents symbol)) :
    ULogFiniteAlphabetDeterministicRuns.FalseOnly (dispatch parents entry clear) :=
  ULogFiniteTapeSymbolDispatch.program_falseOnly _ _ _ (program_falseOnly parents hp)

theorem symbol_branch_spec (parents : Fin 3 → BoundedProgram ms 3)
    (entry : Fin 3 → Fin ms) (clear blank symbol : Fin 3)
    (left right : List (Fin 3)) (head : Int) :
    (∀ (word : List Bool) (z : BoundedConfig ms 3),
      run (program parents) blank word head (branchConfig symbol z) =
        (run (parents symbol) blank word head z).map
          (fun hz => (hz.1, branchConfig symbol hz.2))) ∧
    (∀ word, RawAccepting (dispatch parents entry clear) blank head
      (ULogFiniteTapeSymbolDispatch.initial symbol left right) word ↔
        ∃ rest, word = false :: rest ∧ RawAccepting (parents symbol) blank head
          (selectedStart entry clear symbol left right) rest) ∧
    (∀ T, Nat.card (RawAcceptingWords (dispatch parents entry clear) blank head
      (ULogFiniteTapeSymbolDispatch.initial symbol left right) (T + 1)) =
        Nat.card (RawAcceptingWords (parents symbol) blank head
          (selectedStart entry clear symbol left right) T)) :=
  ⟨fun word z => run_branch_map parents symbol blank word head z,
    dispatch_every_raw_accepting parents entry clear blank symbol left right head,
    all_dispatch_cutoff_counts parents entry clear blank symbol left right head⟩

end PakFixedPolyomino.ULogFiniteTapeSymbolBranch
