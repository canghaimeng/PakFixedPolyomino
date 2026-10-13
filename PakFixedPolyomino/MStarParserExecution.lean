import PakFixedPolyomino.MStarParserMicrocode
import Mathlib.Tactic

/-!
# Executable trace semantics for the parser microcode

The parser never needs to cross the marked low endpoint and stops while
focused on the high-zero cell.  A finite zipper therefore suffices for its
complete trace.  This module is the concrete semantics used by the forthcoming
arbitrary-length crossing-off invariant.
-/

namespace PakFixedPolyomino.MStarParserExecution

open OneTapeTableau MStarOuterProgram MStarParserMicrocode

@[ext] structure Zipper (A : Type*) where
  leftRev : List A
  focus : A
  right : List A
  deriving DecidableEq, Repr

def applyAction {A State : Type*} (z : Zipper A)
    (a : FiniteOneTapeProgram.Action State A) : Option (Zipper A) :=
  match a.move with
  | .stay => some { z with focus := a.write }
  | .right =>
      match z.right with
      | [] => none
      | y :: ys => some { leftRev := a.write :: z.leftRev, focus := y, right := ys }
  | .left =>
      match z.leftRev with
      | [] => none
      | y :: ys => some { leftRev := ys, focus := y, right := a.write :: z.right }

inductive Result (UTape : Type*) where
  | running : ParserState → Zipper (Tape UTape) → Result UTape
  | copyReady : Zipper (Tape UTape) → Result UTape
  | rejected : Result UTape
  | stuck : Result UTape
  deriving DecidableEq, Repr

variable {UTape : Type*}
variable [Fintype UTape] [DecidableEq UTape]

def oneStep (zero one work : UTape) : Result UTape → Result UTape
  | .running p z =>
      if p = copyStart then .copyReady z
      else
        match MStarParserMicrocode.step (UState := Unit) zero one work p z.focus with
        | none => .stuck
        | some a =>
            match applyAction z a with
            | none => .stuck
            | some z' =>
                match a.target with
                | .parser p' => .running p' z'
                | .reject => .rejected
                | _ => .stuck
  | r => r

def run (zero one work : UTape) : ℕ → Result UTape → Result UTape
  | 0, r => r
  | fuel + 1, r => run zero one work fuel (oneStep zero one work r)

@[simp] theorem run_zero (zero one work : UTape) (r : Result UTape) :
    run zero one work 0 r = r := rfl

@[simp] theorem run_succ (zero one work : UTape) (fuel : ℕ) (r : Result UTape) :
    run zero one work (fuel + 1) r =
      run zero one work fuel (oneStep zero one work r) := rfl

theorem run_add (zero one work : UTape) (a b : ℕ) (r : Result UTape) :
    run zero one work (a + b) r =
      run zero one work b (run zero one work a r) := by
  induction a generalizing r with
  | zero => simp [run]
  | succ a ih =>
      simpa only [Nat.succ_add, run] using ih (oneStep zero one work r)

def Reaches (zero one work : UTape) (r s : Result UTape) : Prop :=
  ∃ fuel, run zero one work fuel r = s

theorem reaches_refl (zero one work : UTape) (r : Result UTape) :
    Reaches zero one work r r := ⟨0, rfl⟩

theorem reaches_of_oneStep (zero one work : UTape) {r s : Result UTape}
    (h : oneStep zero one work r = s) : Reaches zero one work r s := by
  exact ⟨1, h⟩

theorem reaches_trans (zero one work : UTape) {r s t : Result UTape}
    (hrs : Reaches zero one work r s) (hst : Reaches zero one work s t) :
    Reaches zero one work r t := by
  rcases hrs with ⟨a, ha⟩
  rcases hst with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  rw [run_add, ha, hb]

def beforeRightRepeat (n : ℕ) (symbol : Tape UTape)
    (left : List (Tape UTape)) (y : Tape UTape) (right : List (Tape UTape)) :
    Zipper (Tape UTape) :=
  match n with
  | 0 => ⟨left, y, right⟩
  | k + 1 => ⟨left, symbol, List.replicate k symbol ++ y :: right⟩

def afterRightRepeat (n : ℕ) (symbol : Tape UTape)
    (left : List (Tape UTape)) (y : Tape UTape) (right : List (Tape UTape)) :
    Zipper (Tape UTape) :=
  ⟨List.replicate n symbol ++ left, y, right⟩

/-- Generic zipper loop: a state that moves right over one distinguished
symbol moves over an arbitrary finite block in exactly its length. -/
theorem run_right_repeat_of
    (zero one work : UTape) (p : ParserState) (symbol : Tape UTape)
    (hstep : ∀ (left : List (Tape UTape)) (y : Tape UTape)
      (right : List (Tape UTape)),
      oneStep zero one work (.running p ⟨left, symbol, y :: right⟩) =
        .running p ⟨symbol :: left, y, right⟩)
    (n : ℕ) (left : List (Tape UTape)) (y : Tape UTape)
    (right : List (Tape UTape)) :
    run zero one work n
      (.running p (beforeRightRepeat n symbol left y right)) =
      .running p (afterRightRepeat n symbol left y right) := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      rw [run_succ]
      have hone : oneStep zero one work
          (.running p (beforeRightRepeat (n + 1) symbol left y right)) =
          .running p (beforeRightRepeat n symbol (symbol :: left) y right) := by
        cases n <;> simp [beforeRightRepeat, List.replicate_succ, hstep]
      rw [hone, ih]
      rw [show afterRightRepeat n symbol (symbol :: left) y right =
          afterRightRepeat (n + 1) symbol left y right by
        apply Zipper.ext <;>
          simp [afterRightRepeat, List.replicate_succ', List.append_assoc]]

def beforeLeftRepeat (n : ℕ) (symbol : Tape UTape)
    (left : List (Tape UTape)) (y : Tape UTape) (right : List (Tape UTape)) :
    Zipper (Tape UTape) :=
  match n with
  | 0 => ⟨left, y, right⟩
  | k + 1 => ⟨List.replicate k symbol ++ y :: left, symbol, right⟩

def afterLeftRepeat (n : ℕ) (symbol : Tape UTape)
    (left : List (Tape UTape)) (y : Tape UTape) (right : List (Tape UTape)) :
    Zipper (Tape UTape) :=
  ⟨left, y, List.replicate n symbol ++ right⟩

/-- Left-moving counterpart of `run_right_repeat_of`. -/
theorem run_left_repeat_of
    (zero one work : UTape) (p : ParserState) (symbol : Tape UTape)
    (hstep : ∀ (left : List (Tape UTape)) (y : Tape UTape)
      (right : List (Tape UTape)),
      oneStep zero one work (.running p ⟨y :: left, symbol, right⟩) =
        .running p ⟨left, y, symbol :: right⟩)
    (n : ℕ) (left : List (Tape UTape)) (y : Tape UTape)
    (right : List (Tape UTape)) :
    run zero one work n
      (.running p (beforeLeftRepeat n symbol left y right)) =
      .running p (afterLeftRepeat n symbol left y right) := by
  induction n generalizing right with
  | zero => rfl
  | succ n ih =>
      rw [run_succ]
      have hone : oneStep zero one work
          (.running p (beforeLeftRepeat (n + 1) symbol left y right)) =
          .running p (beforeLeftRepeat n symbol left y (symbol :: right)) := by
        cases n <;> simp [beforeLeftRepeat, List.replicate_succ, hstep,
          List.append_assoc]
      rw [hone, ih]
      rw [show afterLeftRepeat n symbol left y (symbol :: right) =
          afterLeftRepeat (n + 1) symbol left y right by
        apply Zipper.ext <;>
          simp [afterLeftRepeat, List.replicate_succ', List.append_assoc]]

def beforeRightList (f : Bool → Tape UTape) (xs : List Bool)
    (left : List (Tape UTape)) (y : Tape UTape) (right : List (Tape UTape)) :
    Zipper (Tape UTape) :=
  match xs with
  | [] => ⟨left, y, right⟩
  | b :: bs => ⟨left, f b, bs.map f ++ y :: right⟩

def afterRightList (f : Bool → Tape UTape) (xs : List Bool)
    (left : List (Tape UTape)) (y : Tape UTape) (right : List (Tape UTape)) :
    Zipper (Tape UTape) := ⟨xs.reverse.map f ++ left, y, right⟩

theorem run_right_bool_list_of
    (zero one work : UTape) (p : ParserState) (f : Bool → Tape UTape)
    (hstep : ∀ b left y right,
      oneStep zero one work (.running p ⟨left, f b, y :: right⟩) =
        .running p ⟨f b :: left, y, right⟩)
    (xs : List Bool) (left : List (Tape UTape)) (y : Tape UTape)
    (right : List (Tape UTape)) :
    run zero one work xs.length
      (.running p (beforeRightList f xs left y right)) =
      .running p (afterRightList f xs left y right) := by
  induction xs generalizing left with
  | nil => rfl
  | cons b bs ih =>
      cases bs with
      | nil => simp [run, beforeRightList, afterRightList, hstep]
      | cons c cs =>
          rw [show (b :: c :: cs).length = (c :: cs).length + 1 by simp, run_succ]
          simp only [beforeRightList, List.map_cons, List.cons_append]
          rw [hstep]
          change run zero one work (c :: cs).length
            (.running p (beforeRightList f (c :: cs) (f b :: left) y right)) = _
          rw [ih]
          simp [beforeRightList, afterRightList, List.map_reverse,
            List.append_assoc]

def beforeLeftList (f : Bool → Tape UTape) (xs : List Bool)
    (left : List (Tape UTape)) (y : Tape UTape) (right : List (Tape UTape)) :
    Zipper (Tape UTape) :=
  match xs with
  | [] => ⟨left, y, right⟩
  | b :: bs => ⟨bs.map f ++ y :: left, f b, right⟩

def afterLeftList (f : Bool → Tape UTape) (xs : List Bool)
    (left : List (Tape UTape)) (y : Tape UTape) (right : List (Tape UTape)) :
    Zipper (Tape UTape) := ⟨left, y, xs.reverse.map f ++ right⟩

theorem run_left_bool_list_of
    (zero one work : UTape) (p : ParserState) (f : Bool → Tape UTape)
    (hstep : ∀ b left y right,
      oneStep zero one work (.running p ⟨y :: left, f b, right⟩) =
        .running p ⟨left, y, f b :: right⟩)
    (xs : List Bool) (left : List (Tape UTape)) (y : Tape UTape)
    (right : List (Tape UTape)) :
    run zero one work xs.length
      (.running p (beforeLeftList f xs left y right)) =
      .running p (afterLeftList f xs left y right) := by
  induction xs generalizing right with
  | nil => rfl
  | cons b bs ih =>
      cases bs with
      | nil => simp [run, beforeLeftList, afterLeftList, hstep]
      | cons c cs =>
          rw [show (b :: c :: cs).length = (c :: cs).length + 1 by simp, run_succ]
          simp only [beforeLeftList, List.map_cons, List.cons_append]
          rw [hstep]
          change run zero one work (c :: cs).length
            (.running p (beforeLeftList f (c :: cs) left y (f b :: right))) = _
          rw [ih]
          simp [beforeLeftList, afterLeftList, List.map_reverse,
            List.append_assoc]

def bitCell (zero one : UTape) : Bool → Tape UTape
  | false => .core zero
  | true => .core one

/-- LSB-first physical row followed by the required high-zero lookahead. -/
def inputCells (zero one work : UTape) (w : ConcretePakSide.Word) :
    List (Tape UTape) :=
  w.reverse.map (bitCell zero one) ++ [.core work]

def initial (zero one work : UTape) (w : ConcretePakSide.Word) : Result UTape :=
  match inputCells zero one work w with
  | [] => .stuck
  | y :: ys => .running (fixed 0) { leftRev := [], focus := y, right := ys }

theorem inputCells_encodedWord (zero one work : UTape)
    (x : ConcretePakSide.Word) :
    inputCells zero one work (ConcretePakSide.encodedWord x) =
      List.replicate (ConcretePakSide.paddingLength x.length) (.core zero) ++
      [.core one] ++
      List.replicate x.length (.core zero) ++
      [.core one] ++
      x.reverse.map (bitCell zero one) ++
      [.core one, .core work] := by
  simp [inputCells, ConcretePakSide.encodedWord, List.reverse_append,
    List.map_append, List.map_reverse, List.append_assoc, bitCell]

theorem inputCells_ne_nil (zero one work : UTape) (w : ConcretePakSide.Word) :
    inputCells zero one work w ≠ [] := by
  simp [inputCells]

theorem initial_is_running (zero one work : UTape) (w : ConcretePakSide.Word) :
    ∃ z, initial zero one work w = .running (fixed 0) z := by
  unfold initial
  have h := inputCells_ne_nil zero one work w
  cases hc : inputCells zero one work w with
  | nil => exact (h hc).elim
  | cons y ys => exact ⟨⟨[], y, ys⟩, rfl⟩

def Accepts (zero one work : UTape) (w : ConcretePakSide.Word) : Prop :=
  ∃ fuel z, run zero one work fuel (initial zero one work w) = .copyReady z

theorem result_absorbing_rejected (zero one work : UTape) (fuel : ℕ) :
    run zero one work fuel (.rejected : Result UTape) = .rejected := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [run, oneStep] using ih

theorem result_absorbing_stuck (zero one work : UTape) (fuel : ℕ) :
    run zero one work fuel (.stuck : Result UTape) = .stuck := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [run, oneStep] using ih

theorem result_absorbing_copyReady (zero one work : UTape)
    (fuel : ℕ) (z : Zipper (Tape UTape)) :
    run zero one work fuel (.copyReady z) = .copyReady z := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [run, oneStep] using ih

/-- Determinism plus absorption makes the successful parser output unique,
even when the two witnesses use different fuel bounds. -/
theorem copyReady_output_unique (zero one work : UTape)
    (r : Result UTape) (fuel₁ fuel₂ : ℕ)
    (z₁ z₂ : Zipper (Tape UTape))
    (h₁ : run zero one work fuel₁ r = .copyReady z₁)
    (h₂ : run zero one work fuel₂ r = .copyReady z₂) : z₁ = z₂ := by
  rcases le_total fuel₁ fuel₂ with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [run_add, h₁, result_absorbing_copyReady] at h₂
    exact Result.copyReady.inj h₂
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [run_add, h₂, result_absorbing_copyReady] at h₁
    exact (Result.copyReady.inj h₁).symm

/-- Append cells at the far right end of a finite zipper.  Every successful
parser step is local, so a successful trace is stable under this operation. -/
def extendRight (z : Zipper (Tape UTape)) (tail : List (Tape UTape)) :
    Zipper (Tape UTape) :=
  ⟨z.leftRev, z.focus, z.right ++ tail⟩

def extendResultRight (r : Result UTape) (tail : List (Tape UTape)) :
    Result UTape :=
  match r with
  | .running p z => .running p (extendRight z tail)
  | .copyReady z => .copyReady (extendRight z tail)
  | .rejected => .rejected
  | .stuck => .stuck

theorem applyAction_extendRight_of_some {State : Type*}
    (z z' : Zipper (Tape UTape))
    (a : FiniteOneTapeProgram.Action State (Tape UTape))
    (tail : List (Tape UTape)) (h : applyAction z a = some z') :
    applyAction (extendRight z tail) a = some (extendRight z' tail) := by
  rcases z with ⟨left, focus, right⟩
  rcases a with ⟨write, target, move⟩
  cases move with
  | stay =>
      simp only [applyAction] at h
      have hz := Option.some.inj h
      subst z'
      rfl
  | right =>
      cases right with
      | nil => simp [applyAction] at h
      | cons y ys =>
          simp only [applyAction] at h
          have hz := Option.some.inj h
          subst z'
          rfl
  | left =>
      cases left with
      | nil => simp [applyAction] at h
      | cons y ys =>
          simp only [applyAction] at h
          have hz := Option.some.inj h
          subst z'
          rfl

theorem oneStep_extendResultRight_of_not_stuck (zero one work : UTape)
    (r : Result UTape) (tail : List (Tape UTape))
    (hgood : oneStep zero one work r ≠ .stuck) :
    oneStep zero one work (extendResultRight r tail) =
      extendResultRight (oneStep zero one work r) tail := by
  cases r with
  | copyReady z => rfl
  | rejected => rfl
  | stuck => exact (hgood rfl).elim
  | running p z =>
      by_cases hp : p = copyStart
      · subst p
        rfl
      · cases hs : MStarParserMicrocode.step (UState := Unit)
            zero one work p z.focus with
        | none =>
            exfalso
            apply hgood
            rw [oneStep, if_neg hp, hs]
        | some a =>
            cases ha : applyAction z a with
            | none =>
                exfalso
                apply hgood
                rw [oneStep, if_neg hp]
                simp only [hs, ha]
            | some z' =>
                have ha' := applyAction_extendRight_of_some z z' a tail ha
                dsimp only [extendResultRight]
                rw [oneStep, if_neg hp]
                have hfocus : (extendRight z tail).focus = z.focus := rfl
                rw [hfocus, hs]
                change (match applyAction (extendRight z tail) a with
                  | none => (Result.stuck : Result UTape)
                  | some z'' =>
                      match a.target with
                      | .parser p' => Result.running p' z''
                      | .reject => Result.rejected
                      | _ => Result.stuck) = _
                rw [ha']
                have horig : oneStep zero one work (.running p z) =
                    match a.target with
                    | .parser p' => Result.running p' z'
                    | .reject => Result.rejected
                    | _ => Result.stuck := by
                  rw [oneStep, if_neg hp, hs]
                  change (match applyAction z a with
                    | none => (Result.stuck : Result UTape)
                    | some z'' =>
                        match a.target with
                        | .parser p' => Result.running p' z''
                        | .reject => Result.rejected
                        | _ => Result.stuck) = _
                  rw [ha]
                rw [horig]
                change (match a.target with
                  | .parser p' => Result.running p' (extendRight z' tail)
                  | .reject => Result.rejected
                  | _ => Result.stuck) =
                    extendResultRight
                      (match a.target with
                      | .parser p' => Result.running p' z'
                      | .reject => Result.rejected
                      | _ => Result.stuck) tail
                cases a.target <;> rfl

theorem run_extendResultRight_to_copyReady (zero one work : UTape)
    (fuel : ℕ) (r : Result UTape) (z : Zipper (Tape UTape))
    (tail : List (Tape UTape))
    (h : run zero one work fuel r = .copyReady z) :
    run zero one work fuel (extendResultRight r tail) =
      .copyReady (extendRight z tail) := by
  induction fuel generalizing r with
  | zero =>
      simp only [run_zero] at h ⊢
      subst r
      rfl
  | succ fuel ih =>
      rw [run_succ] at h ⊢
      have hgood : oneStep zero one work r ≠ .stuck := by
        intro hs
        rw [hs, result_absorbing_stuck] at h
        cases h
      rw [oneStep_extendResultRight_of_not_stuck zero one work r tail hgood]
      exact ih (oneStep zero one work r) h

theorem reaches_extendResultRight_to_copyReady (zero one work : UTape)
    (r : Result UTape) (z : Zipper (Tape UTape))
    (tail : List (Tape UTape))
    (h : Reaches zero one work r (.copyReady z)) :
    Reaches zero one work (extendResultRight r tail)
      (.copyReady (extendRight z tail)) := by
  rcases h with ⟨fuel, hfuel⟩
  exact ⟨fuel, run_extendResultRight_to_copyReady zero one work
    fuel r z tail hfuel⟩

end PakFixedPolyomino.MStarParserExecution
