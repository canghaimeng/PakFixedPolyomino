import PakFixedPolyomino.MStarCopierMicrocode
import PakFixedPolyomino.MStarParserCopySpec
import Mathlib.Tactic

/-!
# Executable zipper semantics for the concrete copier

This is the operational layer used to prove the unary-doubling kernel and,
later, the full `copiedWorkspace` refinement.  It executes the literal
`copierStep` table; no macro transition is built into the semantics.
-/

namespace PakFixedPolyomino.MStarCopierExecution

open OneTapeTableau MStarOuterProgram MStarParserExecution
open MStarCopierMicrocode

inductive Result where
  | running : CopierState → Zipper ConcreteTape → Result
  | groupReady : Zipper ConcreteTape → Result
  | rejected
  | stuck
  deriving DecidableEq, Repr

def oneStep : Result → Result
  | .running q z =>
      match copierStep (UState := Unit) () q z.focus with
      | none => .stuck
      | some a =>
          match applyAction z a with
          | none => .stuck
          | some z' =>
              match a.target with
              | .parser (.inr q') => .running q' z'
              | .sim _ => .groupReady z'
              | .reject => .rejected
              | _ => .stuck
  | r => r

def run : ℕ → Result → Result
  | 0, r => r
  | fuel + 1, r => run fuel (oneStep r)

@[simp] theorem run_zero (r : Result) : run 0 r = r := rfl

@[simp] theorem run_succ (fuel : ℕ) (r : Result) :
    run (fuel + 1) r = run fuel (oneStep r) := rfl

theorem run_add (a b : ℕ) (r : Result) :
    run (a + b) r = run b (run a r) := by
  induction a generalizing r with
  | zero => simp [run]
  | succ a ih => simpa only [Nat.succ_add, run] using ih (oneStep r)

def Reaches (r s : Result) : Prop := ∃ fuel, run fuel r = s

theorem reaches_refl (r : Result) : Reaches r r := ⟨0, rfl⟩

theorem reaches_of_oneStep {r s : Result} (h : oneStep r = s) : Reaches r s :=
  ⟨1, h⟩

theorem reaches_trans {r s t : Result} (hrs : Reaches r s)
    (hst : Reaches s t) : Reaches r t := by
  rcases hrs with ⟨a, ha⟩
  rcases hst with ⟨b, hb⟩
  exact ⟨a + b, by rw [run_add, ha, hb]⟩

def beforeRightRepeat (n : ℕ) (symbol : ConcreteTape)
    (left : List ConcreteTape) (y : ConcreteTape) (right : List ConcreteTape) :
    Zipper ConcreteTape :=
  match n with
  | 0 => ⟨left, y, right⟩
  | k + 1 => ⟨left, symbol, List.replicate k symbol ++ y :: right⟩

def afterRightRepeat (n : ℕ) (symbol : ConcreteTape)
    (left : List ConcreteTape) (y : ConcreteTape) (right : List ConcreteTape) :
    Zipper ConcreteTape :=
  ⟨List.replicate n symbol ++ left, y, right⟩

theorem run_right_repeat_of (q : CopierState) (symbol : ConcreteTape)
    (hstep : ∀ left y right,
      oneStep (.running q ⟨left, symbol, y :: right⟩) =
        .running q ⟨symbol :: left, y, right⟩)
    (n : ℕ) (left : List ConcreteTape) (y : ConcreteTape)
    (right : List ConcreteTape) :
    run n (.running q (beforeRightRepeat n symbol left y right)) =
      .running q (afterRightRepeat n symbol left y right) := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      rw [run_succ]
      have hone : oneStep
          (.running q (beforeRightRepeat (n + 1) symbol left y right)) =
          .running q (beforeRightRepeat n symbol (symbol :: left) y right) := by
        cases n <;> simp [beforeRightRepeat, List.replicate_succ, hstep]
      rw [hone, ih]
      rw [show afterRightRepeat n symbol (symbol :: left) y right =
          afterRightRepeat (n + 1) symbol left y right by
        apply Zipper.ext <;>
          simp [afterRightRepeat, List.replicate_succ', List.append_assoc]]

def beforeLeftRepeat (n : ℕ) (symbol : ConcreteTape)
    (left : List ConcreteTape) (y : ConcreteTape) (right : List ConcreteTape) :
    Zipper ConcreteTape :=
  match n with
  | 0 => ⟨left, y, right⟩
  | k + 1 => ⟨List.replicate k symbol ++ y :: left, symbol, right⟩

def afterLeftRepeat (n : ℕ) (symbol : ConcreteTape)
    (left : List ConcreteTape) (y : ConcreteTape) (right : List ConcreteTape) :
    Zipper ConcreteTape :=
  ⟨left, y, List.replicate n symbol ++ right⟩

theorem run_left_repeat_of (q : CopierState) (symbol : ConcreteTape)
    (hstep : ∀ left y right,
      oneStep (.running q ⟨y :: left, symbol, right⟩) =
        .running q ⟨left, y, symbol :: right⟩)
    (n : ℕ) (left : List ConcreteTape) (y : ConcreteTape)
    (right : List ConcreteTape) :
    run n (.running q (beforeLeftRepeat n symbol left y right)) =
      .running q (afterLeftRepeat n symbol left y right) := by
  induction n generalizing right with
  | zero => rfl
  | succ n ih =>
      rw [run_succ]
      have hone : oneStep
          (.running q (beforeLeftRepeat (n + 1) symbol left y right)) =
          .running q (beforeLeftRepeat n symbol left y (symbol :: right)) := by
        cases n <;>
          simp [beforeLeftRepeat, List.replicate_succ, hstep,
            List.append_assoc]
      rw [hone, ih]
      rw [show afterLeftRepeat n symbol left y (symbol :: right) =
          afterLeftRepeat (n + 1) symbol left y right by
        apply Zipper.ext <;>
          simp [afterLeftRepeat, List.replicate_succ', List.append_assoc]]

def beforeRightList (xs : List ConcreteTape) (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) : Zipper ConcreteTape :=
  match xs with
  | [] => ⟨left, y, right⟩
  | x :: xs => ⟨left, x, xs ++ y :: right⟩

def afterRightList (xs : List ConcreteTape) (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) : Zipper ConcreteTape :=
  ⟨xs.reverse ++ left, y, right⟩

theorem run_right_list_of (q : CopierState) (xs : List ConcreteTape)
    (hstep : ∀ x, x ∈ xs → ∀ left y right,
      oneStep (.running q ⟨left, x, y :: right⟩) =
        .running q ⟨x :: left, y, right⟩)
    (left : List ConcreteTape) (y : ConcreteTape) (right : List ConcreteTape) :
    run xs.length (.running q (beforeRightList xs left y right)) =
      .running q (afterRightList xs left y right) := by
  induction xs generalizing left with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => simp [run, beforeRightList, afterRightList, hstep]
      | cons z zs =>
          rw [show (x :: z :: zs).length = (z :: zs).length + 1 by simp,
            run_succ]
          simp only [beforeRightList, List.cons_append]
          rw [hstep x (by simp)]
          change run (z :: zs).length
            (.running q (beforeRightList (z :: zs) (x :: left) y right)) = _
          rw [ih (fun a ha => hstep a (by simp [ha]))]
          simp [afterRightList, List.append_assoc]

def beforeLeftList (xs : List ConcreteTape) (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) : Zipper ConcreteTape :=
  match xs with
  | [] => ⟨left, y, right⟩
  | x :: xs => ⟨xs ++ y :: left, x, right⟩

def afterLeftList (xs : List ConcreteTape) (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) : Zipper ConcreteTape :=
  ⟨left, y, xs.reverse ++ right⟩

theorem run_left_list_of (q : CopierState) (xs : List ConcreteTape)
    (hstep : ∀ x, x ∈ xs → ∀ left y right,
      oneStep (.running q ⟨y :: left, x, right⟩) =
        .running q ⟨left, y, x :: right⟩)
    (left : List ConcreteTape) (y : ConcreteTape) (right : List ConcreteTape) :
    run xs.length (.running q (beforeLeftList xs left y right)) =
      .running q (afterLeftList xs left y right) := by
  induction xs generalizing right with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => simp [run, beforeLeftList, afterLeftList, hstep]
      | cons z zs =>
          rw [show (x :: z :: zs).length = (z :: zs).length + 1 by simp,
            run_succ]
          simp only [beforeLeftList, List.cons_append]
          rw [hstep x (by simp)]
          change run (z :: zs).length
            (.running q (beforeLeftList (z :: zs) left y (x :: right))) = _
          rw [ih (fun a ha => hstep a (by simp [ha]))]
          simp [afterLeftList, List.append_assoc]

theorem groupDone_step (left : List ConcreteTape) (y : ConcreteTape)
    (right : List ConcreteTape) :
    oneStep (.running .groupDone ⟨y :: left, .markL, right⟩) =
      .running .groupSeekLen ⟨left, y, .markL :: right⟩ := by
  rfl

theorem groupSeek_pass_step (x : ConcreteTape)
    (hx : x = MStarParserMicrocode.endpointMark ∨
      x = MStarParserMicrocode.payloadZero ∨
      x = MStarParserMicrocode.payloadOne ∨ x = MStarParserMicrocode.sepLen ∨
      x = MStarParserMicrocode.lenDone)
    (left : List ConcreteTape) (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running .groupSeekLen ⟨y :: left, x, right⟩) =
      .running .groupSeekLen ⟨left, y, x :: right⟩ := by
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem groupSeek_paired_step (left right : List ConcreteTape)
    (y : ConcreteTape) :
    oneStep (.running .groupSeekLen
      ⟨left, MStarParserMicrocode.pairedLen, y :: right⟩) =
      .running .groupReturn
        ⟨MStarParserMicrocode.lenDone :: left, y,
          right⟩ := by
  rfl

theorem groupSeek_finished_step (left right : List ConcreteTape)
    (y : ConcreteTape) :
    oneStep (.running .groupSeekLen
      ⟨left, MStarParserMicrocode.sepPad, y :: right⟩) =
      .running .finishReturn
        ⟨MStarParserMicrocode.sepPad :: left, y, right⟩ := by
  rfl

theorem groupReturn_pass_step (x : ConcreteTape)
    (hx : x = MStarParserMicrocode.lenDone ∨ x = MStarParserMicrocode.sepLen ∨
      x = MStarParserMicrocode.payloadZero ∨
      x = MStarParserMicrocode.payloadOne ∨
      x = MStarParserMicrocode.endpointMark)
    (left : List ConcreteTape) (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running .groupReturn ⟨left, x, y :: right⟩) =
      .running .groupReturn ⟨x :: left, y, right⟩ := by
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem groupReturn_mark_step (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running .groupReturn ⟨left, .markL, y :: right⟩) =
      .running (.findOld 0) ⟨.markL :: left, y, right⟩ := by
  rfl

theorem finishReturn_pass_step (x : ConcreteTape)
    (hx : x = MStarParserMicrocode.lenDone ∨ x = MStarParserMicrocode.sepLen ∨
      x = MStarParserMicrocode.payloadZero ∨
      x = MStarParserMicrocode.payloadOne ∨
      x = MStarParserMicrocode.endpointMark)
    (left : List ConcreteTape) (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running .finishReturn ⟨left, x, y :: right⟩) =
      .running .finishReturn ⟨x :: left, y, right⟩ := by
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem finishReturn_mark_step (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running .finishReturn ⟨left, .markL, y :: right⟩) =
      .running .counterToWork ⟨.markL :: left, y, right⟩ := by
  rfl

theorem counterToWork_A_step (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running .counterToWork ⟨left, cellA, y :: right⟩) =
      .running .counterToWork
        ⟨.core MStarConcreteAlphabet.work :: left, y, right⟩ := by
  rfl

theorem counterToWork_mark_step (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running .counterToWork ⟨left, .markR, y :: right⟩) =
      .running .payloadBoundary
        ⟨.core MStarConcreteAlphabet.work :: left, y, right⟩ := by
  rfl

theorem payloadBoundary_step (left : List ConcreteTape)
    (right : List ConcreteTape) :
    oneStep (.running .payloadBoundary
      ⟨left, .core MStarConcreteAlphabet.work, right⟩) =
      match left with
      | [] => .stuck
      | y :: ys => .running .payloadSeek ⟨ys, y, .markR :: right⟩ := by
  cases left <;> rfl

theorem payloadSeek_pass_step (x : ConcreteTape)
    (hx : x = .core MStarConcreteAlphabet.work ∨
      x = .core MStarConcreteAlphabet.zero ∨
      x = .core MStarConcreteAlphabet.one ∨ x = .markL ∨
      x = MStarParserMicrocode.endpointMark ∨
      x = MStarParserMicrocode.lenDone)
    (left : List ConcreteTape) (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running .payloadSeek ⟨y :: left, x, right⟩) =
      .running .payloadSeek ⟨left, y, x :: right⟩ := by
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem payloadSeek_marker_step (b : Bool) (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running .payloadSeek
      ⟨left, MStarConcreteAlphabet.payloadMarker b, y :: right⟩) =
      .running (.payloadCarry b)
        ⟨MStarParserMicrocode.lenDone :: left, y, right⟩ := by
  cases b <;> rfl

theorem payloadSeek_sep_step (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running .payloadSeek
      ⟨left, MStarParserMicrocode.sepLen, y :: right⟩) =
      .running .payloadDoneReturn
        ⟨MStarParserMicrocode.sepLen :: left, y, right⟩ := by
  rfl

theorem payloadCarry_pass_step (b : Bool) (x : ConcreteTape)
    (hx : x = MStarParserMicrocode.lenDone ∨
      x = MStarParserMicrocode.endpointMark ∨ x = .markL ∨
      x = .core MStarConcreteAlphabet.work ∨
      x = .core MStarConcreteAlphabet.zero ∨
      x = .core MStarConcreteAlphabet.one)
    (left : List ConcreteTape) (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running (.payloadCarry b) ⟨left, x, y :: right⟩) =
      .running (.payloadCarry b) ⟨x :: left, y, right⟩ := by
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> rfl

theorem payloadCarry_mark_step (b : Bool) (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running (.payloadCarry b) ⟨left, .markR, y :: right⟩) =
      .running .payloadPlace
        ⟨.core (if b then MStarConcreteAlphabet.one
          else MStarConcreteAlphabet.zero) :: left, y, right⟩ := by
  cases b <;> rfl

theorem payloadPlace_step (left : List ConcreteTape)
    (right : List ConcreteTape) :
    oneStep (.running .payloadPlace
      ⟨left, .core MStarConcreteAlphabet.work, right⟩) =
      match left with
      | [] => .stuck
      | y :: ys => .running .payloadSeek ⟨ys, y, .markR :: right⟩ := by
  cases left <;> rfl

theorem payloadDoneReturn_pass_step (x : ConcreteTape)
    (hx : x = MStarParserMicrocode.lenDone ∨
      x = MStarParserMicrocode.endpointMark)
    (left : List ConcreteTape) (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running .payloadDoneReturn ⟨left, x, y :: right⟩) =
      .running .payloadDoneReturn ⟨x :: left, y, right⟩ := by
  rcases hx with rfl | rfl <;> rfl

theorem payloadDoneReturn_mark_step (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running .payloadDoneReturn ⟨left, .markL, y :: right⟩) =
      .running .finalSeekBoundary ⟨.markL :: left, y, right⟩ := by
  rfl

theorem finalSeekBoundary_pass_step (x : ConcreteTape)
    (hx : x = .core MStarConcreteAlphabet.work ∨
      x = .core MStarConcreteAlphabet.zero ∨
      x = .core MStarConcreteAlphabet.one)
    (left : List ConcreteTape) (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running .finalSeekBoundary ⟨left, x, y :: right⟩) =
      .running .finalSeekBoundary ⟨x :: left, y, right⟩ := by
  rcases hx with rfl | rfl | rfl <;> rfl

theorem finalSeekBoundary_mark_step (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running .finalSeekBoundary ⟨left, .markR, y :: right⟩) =
      .running .rightBufferScan
        ⟨.core MStarConcreteAlphabet.work :: left, y, right⟩ := by
  rfl

theorem rightBufferScan_work_step (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running .rightBufferScan
      ⟨left, .core MStarConcreteAlphabet.work, y :: right⟩) =
      .running .rightBufferScan
        ⟨.core MStarConcreteAlphabet.work :: left, y, right⟩ := by
  rfl

theorem rightBufferScan_end_step (left : List ConcreteTape)
    (right : List ConcreteTape) :
    oneStep (.running .rightBufferScan ⟨left, rightEnd, right⟩) =
      match left with
      | [] => .stuck
      | y :: ys => .running .finalReturn ⟨ys, y, .markR :: right⟩ := by
  cases left <;> rfl

theorem finalReturn_pass_step (x : ConcreteTape)
    (hx : x = .core MStarConcreteAlphabet.work ∨
      x = .core MStarConcreteAlphabet.zero ∨
      x = .core MStarConcreteAlphabet.one)
    (left : List ConcreteTape) (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running .finalReturn ⟨y :: left, x, right⟩) =
      .running .finalReturn ⟨left, y, x :: right⟩ := by
  rcases hx with rfl | rfl | rfl <;> rfl

theorem finalReturn_mark_step (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running .finalReturn ⟨left, .markL, y :: right⟩) =
      .groupReady ⟨.markL :: left, y, right⟩ := by
  rfl

@[simp] theorem rejected_absorbing (fuel : ℕ) :
    run fuel .rejected = .rejected := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [run, oneStep] using ih

@[simp] theorem stuck_absorbing (fuel : ℕ) :
    run fuel .stuck = .stuck := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [run, oneStep] using ih

@[simp] theorem groupReady_absorbing (fuel : ℕ)
    (z : Zipper ConcreteTape) :
    run fuel (.groupReady z) = .groupReady z := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [run, oneStep] using ih

theorem seedCell_step (left : List ConcreteTape) (y : ConcreteTape)
    (right : List ConcreteTape) :
    oneStep (.running .seedCell
      ⟨left, .core MStarConcreteAlphabet.work, y :: right⟩) =
      .running .seedBoundary ⟨cellA :: left, y, right⟩ := by
  rfl

theorem seedBoundary_step (left : List ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running .seedBoundary
      ⟨left, .core MStarConcreteAlphabet.work, right⟩) =
      match left with
      | [] => .stuck
      | y :: ys => .running (.returnLeft 0) ⟨ys, y, .markR :: right⟩ := by
  cases left <;> rfl

theorem findOld_A_step (r : Fin 8) (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running (.findOld r) ⟨left, cellA, y :: right⟩) =
      .running (.seekBoundary r) ⟨cellB :: left, y, right⟩ := by
  rfl

theorem findOld_B_step (r : Fin 8) (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running (.findOld r) ⟨left, cellB, y :: right⟩) =
      .running (.findOld r) ⟨cellB :: left, y, right⟩ := by
  rfl

theorem findOld_boundary_step (r : Fin 8) (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running (.findOld r) ⟨y :: left, .markR, right⟩) =
      .running (.normalize r) ⟨left, y, .markR :: right⟩ := by
  rfl

theorem seekBoundary_cell_step (r : Fin 8) (x : ConcreteTape)
    (hx : x = cellA ∨ x = cellB) (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running (.seekBoundary r) ⟨left, x, y :: right⟩) =
      .running (.seekBoundary r) ⟨x :: left, y, right⟩ := by
  rcases hx with rfl | rfl <;> rfl

theorem seekBoundary_end_step (r : Fin 8) (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running (.seekBoundary r) ⟨left, .markR, y :: right⟩) =
      .running (.placeBoundary r) ⟨cellB :: left, y, right⟩ := by
  rfl

theorem placeBoundary_step (r : Fin 8) (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running (.placeBoundary r)
      ⟨y :: left, .core MStarConcreteAlphabet.work, right⟩) =
      .running (.returnLeft r) ⟨left, y, .markR :: right⟩ := by
  rfl

theorem returnLeft_cell_step (r : Fin 8) (x : ConcreteTape)
    (hx : x = cellA ∨ x = cellB) (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running (.returnLeft r) ⟨y :: left, x, right⟩) =
      .running (.returnLeft r) ⟨left, y, x :: right⟩ := by
  rcases hx with rfl | rfl <;> rfl

theorem returnLeft_mark_step (r : Fin 8) (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running (.returnLeft r) ⟨left, .markL, y :: right⟩) =
      .running (.findOld r) ⟨.markL :: left, y, right⟩ := by
  rfl

theorem normalize_B_step (r : Fin 8) (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    oneStep (.running (.normalize r) ⟨y :: left, cellB, right⟩) =
      .running (.normalize r) ⟨left, y, cellA :: right⟩ := by
  rfl

theorem run_findOld_B (r : Fin 8) (n : ℕ) (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    run n (.running (.findOld r)
      (beforeRightRepeat n cellB left y right)) =
      .running (.findOld r) (afterRightRepeat n cellB left y right) :=
  run_right_repeat_of (.findOld r) cellB (findOld_B_step r) n left y right

theorem run_seekBoundary_A (r : Fin 8) (n : ℕ)
    (left : List ConcreteTape) (y : ConcreteTape) (right : List ConcreteTape) :
    run n (.running (.seekBoundary r)
      (beforeRightRepeat n cellA left y right)) =
      .running (.seekBoundary r) (afterRightRepeat n cellA left y right) :=
  run_right_repeat_of (.seekBoundary r) cellA
    (fun left y right => seekBoundary_cell_step r cellA (Or.inl rfl) left y right)
    n left y right

theorem run_seekBoundary_B (r : Fin 8) (n : ℕ)
    (left : List ConcreteTape) (y : ConcreteTape) (right : List ConcreteTape) :
    run n (.running (.seekBoundary r)
      (beforeRightRepeat n cellB left y right)) =
      .running (.seekBoundary r) (afterRightRepeat n cellB left y right) :=
  run_right_repeat_of (.seekBoundary r) cellB
    (fun left y right => seekBoundary_cell_step r cellB (Or.inr rfl) left y right)
    n left y right

theorem run_returnLeft_A (r : Fin 8) (n : ℕ)
    (left : List ConcreteTape) (y : ConcreteTape) (right : List ConcreteTape) :
    run n (.running (.returnLeft r)
      (beforeLeftRepeat n cellA left y right)) =
      .running (.returnLeft r) (afterLeftRepeat n cellA left y right) :=
  run_left_repeat_of (.returnLeft r) cellA
    (fun left y right => returnLeft_cell_step r cellA (Or.inl rfl) left y right)
    n left y right

theorem run_returnLeft_B (r : Fin 8) (n : ℕ)
    (left : List ConcreteTape) (y : ConcreteTape) (right : List ConcreteTape) :
    run n (.running (.returnLeft r)
      (beforeLeftRepeat n cellB left y right)) =
      .running (.returnLeft r) (afterLeftRepeat n cellB left y right) :=
  run_left_repeat_of (.returnLeft r) cellB
    (fun left y right => returnLeft_cell_step r cellB (Or.inr rfl) left y right)
    n left y right

theorem run_normalize_B (r : Fin 8) (n : ℕ)
    (left : List ConcreteTape) (y : ConcreteTape) (right : List ConcreteTape) :
    run n (.running (.normalize r)
      (beforeLeftRepeat n cellB left y right)) =
      .running (.normalize r)
        ⟨left, y, List.replicate n cellA ++ right⟩ := by
  induction n generalizing right with
  | zero => rfl
  | succ n ih =>
      rw [run_succ]
      have hone : oneStep
          (.running (.normalize r)
            (beforeLeftRepeat (n + 1) cellB left y right)) =
          .running (.normalize r)
            (beforeLeftRepeat n cellB left y (cellA :: right)) := by
        cases n <;>
          simp [beforeLeftRepeat, List.replicate_succ,
            normalize_B_step, List.append_assoc]
      rw [hone, ih]
      apply congrArg (Result.running (.normalize r))
      apply Zipper.ext <;>
        simp [List.replicate_succ', List.append_assoc]

theorem seed_reaches_round_zero (tail : List ConcreteTape) :
    run 4
      (.running .seedCell
        ⟨[.markL], .core MStarConcreteAlphabet.work,
          .core MStarConcreteAlphabet.work :: tail⟩) =
      .running (.findOld 0) ⟨[.markL], cellA, .markR :: tail⟩ := by
  rfl

theorem seed_reaches_round_zero_source (tail source : List ConcreteTape) :
    run 4
      (.running .seedCell
        ⟨.markL :: source, .core MStarConcreteAlphabet.work,
          .core MStarConcreteAlphabet.work :: tail⟩) =
      .running (.findOld 0)
        ⟨.markL :: source, cellA, .markR :: tail⟩ := by
  rfl

/-- Home position of one doubling round after `processed` original cells have
already been duplicated and `remaining` originals are still `cellA`.  The
physical block is `B^processed A^remaining B^processed`; the head is the
first cell immediately to the right of `markL`. -/
def roundStage (r : Fin 8) (processed remaining : ℕ)
    (tail : List ConcreteTape) (source : List ConcreteTape := []) : Result :=
  match processed, remaining with
  | 0, 0 => .stuck
  | 0, u + 1 =>
      .running (.findOld r)
        ⟨.markL :: source, cellA,
          List.replicate u cellA ++ .markR ::
            List.replicate (u + 1) (.core MStarConcreteAlphabet.work) ++ tail⟩
  | k + 1, u =>
      .running (.findOld r)
        ⟨.markL :: source, cellB,
          List.replicate k cellB ++ List.replicate u cellA ++
            List.replicate (k + 1) cellB ++ .markR ::
              List.replicate u (.core MStarConcreteAlphabet.work) ++ tail⟩

theorem seeded_eq_roundStage (tail : List ConcreteTape) :
    (.running (.findOld 0)
      ⟨[.markL], cellA,
        .markR :: .core MStarConcreteAlphabet.work :: tail⟩ : Result) =
      roundStage 0 0 1 tail := by
  rfl

def atOld (r : Fin 8) (processed remaining : ℕ)
    (tail : List ConcreteTape) (source : List ConcreteTape := []) : Result :=
  .running (.findOld r)
    (afterRightRepeat processed cellB (.markL :: source) cellA
      (List.replicate remaining cellA ++ List.replicate processed cellB ++
        .markR :: List.replicate (remaining + 1)
          (.core MStarConcreteAlphabet.work) ++ tail))

theorem reaches_atOld (r : Fin 8) (processed remaining : ℕ)
    (tail source : List ConcreteTape) :
    Reaches (roundStage r processed (remaining + 1) tail source)
      (atOld r processed remaining tail source) := by
  refine ⟨processed, ?_⟩
  have hrun := run_findOld_B r processed (.markL :: source) cellA
    (List.replicate remaining cellA ++ List.replicate processed cellB ++
      .markR :: List.replicate (remaining + 1)
        (.core MStarConcreteAlphabet.work) ++ tail)
  cases processed with
  | zero => simpa [roundStage, atOld, beforeRightRepeat] using hrun
  | succ processed =>
      simpa [roundStage, atOld, beforeRightRepeat,
        List.replicate_succ, List.append_assoc] using hrun

def seekCells (processed remaining : ℕ) : List ConcreteTape :=
  List.replicate remaining cellA ++ List.replicate processed cellB

def seekStarted (r : Fin 8) (processed remaining : ℕ)
    (tail : List ConcreteTape) (source : List ConcreteTape := []) : Result :=
  .running (.seekBoundary r)
    (beforeRightList (seekCells processed remaining)
      (cellB :: List.replicate processed cellB ++ .markL :: source) .markR
      (List.replicate (remaining + 1) (.core MStarConcreteAlphabet.work) ++ tail))

theorem reaches_seekStarted (r : Fin 8) (processed remaining : ℕ)
    (tail source : List ConcreteTape) :
    Reaches (atOld r processed remaining tail source)
      (seekStarted r processed remaining tail source) := by
  apply reaches_of_oneStep
  cases processed <;> cases remaining <;>
    simp [atOld, seekStarted, seekCells, afterRightRepeat, beforeRightList,
      findOld_A_step, List.replicate_succ, List.append_assoc]

def atBoundary (r : Fin 8) (processed remaining : ℕ)
    (tail : List ConcreteTape) (source : List ConcreteTape := []) : Result :=
  .running (.seekBoundary r)
    (afterRightList (seekCells processed remaining)
      (cellB :: List.replicate processed cellB ++ .markL :: source) .markR
      (List.replicate (remaining + 1) (.core MStarConcreteAlphabet.work) ++ tail))

theorem reaches_atBoundary (r : Fin 8) (processed remaining : ℕ)
    (tail source : List ConcreteTape) :
    Reaches (seekStarted r processed remaining tail source)
      (atBoundary r processed remaining tail source) := by
  refine ⟨(seekCells processed remaining).length, ?_⟩
  apply run_right_list_of (.seekBoundary r) (seekCells processed remaining)
  intro x hx left y right
  have hcell : x = cellA ∨ x = cellB := by
    simp [seekCells] at hx
    rcases hx with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  exact seekBoundary_cell_step r x hcell left y right

def returnCells (processed remaining : ℕ) : List ConcreteTape :=
  cellB :: (seekCells processed remaining).reverse ++
    cellB :: List.replicate processed cellB

def returnStarted (r : Fin 8) (processed remaining : ℕ)
    (tail : List ConcreteTape) (source : List ConcreteTape := []) : Result :=
  .running (.returnLeft r)
    (beforeLeftList (returnCells processed remaining) source .markL
      (.markR :: List.replicate remaining (.core MStarConcreteAlphabet.work) ++ tail))

theorem reaches_returnStarted (r : Fin 8) (processed remaining : ℕ)
    (tail source : List ConcreteTape) :
    Reaches (atBoundary r processed remaining tail source)
      (returnStarted r processed remaining tail source) := by
  refine ⟨2, ?_⟩
  cases processed <;> cases remaining <;>
    simp [run, atBoundary, returnStarted, returnCells, seekCells,
      afterRightList, beforeLeftList, seekBoundary_end_step,
      placeBoundary_step, List.replicate_succ, List.append_assoc]

def returnedToMark (r : Fin 8) (processed remaining : ℕ)
    (tail : List ConcreteTape) (source : List ConcreteTape := []) : Result :=
  .running (.returnLeft r)
    (afterLeftList (returnCells processed remaining) source .markL
      (.markR :: List.replicate remaining (.core MStarConcreteAlphabet.work) ++ tail))

theorem reaches_returnedToMark (r : Fin 8) (processed remaining : ℕ)
    (tail source : List ConcreteTape) :
    Reaches (returnStarted r processed remaining tail source)
      (returnedToMark r processed remaining tail source) := by
  refine ⟨(returnCells processed remaining).length, ?_⟩
  apply run_left_list_of (.returnLeft r) (returnCells processed remaining)
  intro x hx left y right
  have hcell : x = cellA ∨ x = cellB := by
    simp [returnCells, seekCells] at hx
    aesop
  exact returnLeft_cell_step r x hcell left y right

theorem reaches_process_one (r : Fin 8) (processed remaining : ℕ)
    (tail source : List ConcreteTape) :
    Reaches (roundStage r processed (remaining + 1) tail source)
      (roundStage r (processed + 1) remaining tail source) := by
  have h₀ := reaches_atOld r processed remaining tail source
  have h₁ := reaches_seekStarted r processed remaining tail source
  have h₂ := reaches_atBoundary r processed remaining tail source
  have h₃ := reaches_returnStarted r processed remaining tail source
  have h₄ := reaches_returnedToMark r processed remaining tail source
  have h₅ : Reaches (returnedToMark r processed remaining tail source)
      (roundStage r (processed + 1) remaining tail source) := by
    apply reaches_of_oneStep
    cases processed <;>
      simp [returnedToMark, roundStage, returnCells, seekCells,
        afterLeftList, returnLeft_mark_step, List.reverse_append,
        List.replicate_succ, MStarConcreteAlphabet.replicate_cons_rotate,
        List.append_assoc]
  exact reaches_trans h₀ (reaches_trans h₁
    (reaches_trans h₂ (reaches_trans h₃ (reaches_trans h₄ h₅))))

theorem reaches_process_all (r : Fin 8) (processed remaining : ℕ)
    (tail source : List ConcreteTape) :
    Reaches (roundStage r processed remaining tail source)
      (roundStage r (processed + remaining) 0 tail source) := by
  induction remaining generalizing processed with
  | zero =>
      simpa using reaches_refl (roundStage r processed 0 tail source)
  | succ remaining ih =>
      have hstep := reaches_process_one r processed remaining tail source
      have hrest := ih (processed + 1)
      have h := reaches_trans hstep hrest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem replicate_join_middle {A : Type*} (n : ℕ) (a : A) :
    List.replicate n a ++ a :: List.replicate n a =
      List.replicate (2 * n + 1) a := by
  rw [← List.replicate_succ, ← List.replicate_add]
  congr 1
  omega

def normalizeStarted (r : Fin 8) (n : ℕ) (tail : List ConcreteTape)
    (source : List ConcreteTape := []) :
    Result :=
  .running (.normalize r)
    (beforeLeftRepeat (2 * n) cellB source .markL (.markR :: tail))

theorem reaches_normalizeStarted (r : Fin 8) (n : ℕ) (hn : 0 < n)
    (tail source : List ConcreteTape) :
    Reaches (roundStage r n 0 tail source) (normalizeStarted r n tail source) := by
  let atEnd : Result :=
    .running (.findOld r)
      (afterRightRepeat (2 * n) cellB (.markL :: source) .markR tail)
  have hfind : Reaches (roundStage r n 0 tail source) atEnd := by
    refine ⟨2 * n, ?_⟩
    have hrun := run_findOld_B r (2 * n) (.markL :: source) .markR tail
    cases n with
    | zero => omega
    | succ n =>
        have hstage' : roundStage r (n + 1) 0 tail source =
            .running (.findOld r)
              (beforeRightRepeat (2 * (n + 1)) cellB
                (.markL :: source) .markR tail) := by
          unfold roundStage beforeRightRepeat
          rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
          apply congrArg (Result.running (.findOld r))
          apply Zipper.ext <;> simp only
          simp only [List.replicate_zero, List.nil_append, List.append_nil]
          rw [← List.replicate_add]
          rw [show n + (n + 1) = 2 * n + 1 by omega]
          simp [List.append_assoc]
        rw [hstage']
        exact hrun
  have hnormalize : Reaches atEnd (normalizeStarted r n tail source) := by
    apply reaches_of_oneStep
    cases n with
    | zero => omega
    | succ n =>
        unfold atEnd normalizeStarted
        rw [show 2 * (n + 1) = (2 * (n + 1) - 1) + 1 by omega]
        simp [afterRightRepeat, beforeLeftRepeat, findOld_boundary_step,
          List.replicate_add, List.replicate_succ, List.append_assoc]
  exact reaches_trans hfind hnormalize

def normalizedAtMark (r : Fin 8) (n : ℕ) (tail : List ConcreteTape)
    (source : List ConcreteTape := []) :
    Result :=
  .running (.normalize r)
    ⟨source, .markL, List.replicate (2 * n) cellA ++ .markR :: tail⟩

theorem reaches_normalizedAtMark (r : Fin 8) (n : ℕ)
    (tail source : List ConcreteTape) :
    Reaches (normalizeStarted r n tail source) (normalizedAtMark r n tail source) := by
  exact ⟨2 * n, by
    simpa [normalizeStarted, normalizedAtMark] using
      run_normalize_B r (2 * n) source .markL (.markR :: tail)⟩

def roundCompleted (r : Fin 8) (n : ℕ) (tail : List ConcreteTape)
    (source : List ConcreteTape := []) :
    Result :=
  if h : r.1 < 7 then
    .running (.findOld (MStarCopierMicrocode.nextRound r h))
      (match 2 * n with
       | 0 => ⟨.markL :: source, .markR, tail⟩
       | k + 1 => ⟨.markL :: source, cellA,
          List.replicate k cellA ++ .markR :: tail⟩)
  else
    .running .groupDone
      ⟨source, .markL, List.replicate (2 * n) cellA ++ .markR :: tail⟩

theorem reaches_roundCompleted (r : Fin 8) (n : ℕ)
    (tail source : List ConcreteTape) :
    Reaches (normalizedAtMark r n tail source) (roundCompleted r n tail source) := by
  apply reaches_of_oneStep
  unfold normalizedAtMark roundCompleted oneStep MStarCopierMicrocode.copierStep
  by_cases hr : r.1 < 7
  · rw [dif_pos hr]
    by_cases hn : n = 0
    · subst n
      simp [hr, cellB, MStarCopierMicrocode.cellB,
        MStarCopierMicrocode.copyGo, applyAction, List.replicate_succ]
    · rw [show 2 * n = (2 * n - 1) + 1 by omega]
      simp [hr, cellB, MStarCopierMicrocode.cellB,
        MStarCopierMicrocode.copyGo, applyAction, List.replicate_succ]
  · rw [dif_neg hr]
    simp [hr, cellB, MStarCopierMicrocode.cellB,
      MStarCopierMicrocode.copyGo, applyAction, List.replicate_succ]

theorem roundCompleted_eq_next (r : Fin 8) (n : ℕ) (hn : 0 < n)
    (hr : r.1 < 7) (tail source : List ConcreteTape) :
    roundCompleted r n
        (List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail) source =
      roundStage (MStarCopierMicrocode.nextRound r hr) 0 (2 * n) tail source := by
  unfold roundCompleted
  rw [dif_pos hr]
  cases n with
  | zero => omega
  | succ n =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      simp [roundStage, List.replicate_succ, List.append_assoc]

theorem reaches_doubleRound_next (r : Fin 8) (n : ℕ) (hn : 0 < n)
    (hr : r.1 < 7) (tail source : List ConcreteTape) :
    Reaches
      (roundStage r 0 n
        (List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail) source)
      (roundStage (MStarCopierMicrocode.nextRound r hr) 0 (2 * n) tail source) := by
  have h₀ := reaches_process_all r 0 n
    (List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail) source
  have h₁ := reaches_normalizeStarted r n hn
    (List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail) source
  have h₂ := reaches_normalizedAtMark r n
    (List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail) source
  have h₃ := reaches_roundCompleted r n
    (List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail) source
  rw [roundCompleted_eq_next r n hn hr tail source] at h₃
  have h₀' : Reaches
      (roundStage r 0 n
        (List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail) source)
      (roundStage r n 0
        (List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail) source) := by
    simpa using h₀
  exact reaches_trans h₀' (reaches_trans h₁ (reaches_trans h₂ h₃))

def doubledGroupZipper (n : ℕ) (tail : List ConcreteTape)
    (source : List ConcreteTape := []) :
    Zipper ConcreteTape :=
  ⟨source, .markL,
    List.replicate (2 * n) cellA ++ .markR ::
      List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail⟩

theorem reaches_doubleRound_final (r : Fin 8) (n : ℕ) (hn : 0 < n)
    (hr : ¬ r.1 < 7) (tail source : List ConcreteTape) :
    Reaches
      (roundStage r 0 n
        (List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail) source)
      (.running .groupDone (doubledGroupZipper n tail source)) := by
  have h₀ := reaches_process_all r 0 n
    (List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail) source
  have h₁ := reaches_normalizeStarted r n hn
    (List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail) source
  have h₂ := reaches_normalizedAtMark r n
    (List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail) source
  have h₃ := reaches_roundCompleted r n
    (List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail) source
  have h₃' : Reaches
      (normalizedAtMark r n
        (List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail) source)
      (.running .groupDone (doubledGroupZipper n tail source)) := by
    simpa [roundCompleted, doubledGroupZipper, hr, List.append_assoc] using h₃
  have h₀' : Reaches
      (roundStage r 0 n
        (List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail) source)
      (roundStage r n 0
        (List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++ tail) source) := by
    simpa using h₀
  exact reaches_trans h₀' (reaches_trans h₁
    (reaches_trans h₂ h₃'))

def eightRoundReserve (n : ℕ) (tail : List ConcreteTape) : List ConcreteTape :=
  List.replicate (2 * n) (.core MStarConcreteAlphabet.work) ++
  List.replicate (4 * n) (.core MStarConcreteAlphabet.work) ++
  List.replicate (8 * n) (.core MStarConcreteAlphabet.work) ++
  List.replicate (16 * n) (.core MStarConcreteAlphabet.work) ++
  List.replicate (32 * n) (.core MStarConcreteAlphabet.work) ++
  List.replicate (64 * n) (.core MStarConcreteAlphabet.work) ++
  List.replicate (128 * n) (.core MStarConcreteAlphabet.work) ++
  List.replicate (256 * n) (.core MStarConcreteAlphabet.work) ++ tail

theorem reaches_eight_doublings (n : ℕ) (hn : 0 < n)
    (tail source : List ConcreteTape) :
    Reaches (roundStage 0 0 n (eightRoundReserve n tail) source)
      (.running .groupDone
        ⟨source, .markL,
          List.replicate (256 * n) cellA ++ .markR ::
            List.replicate (256 * n) (.core MStarConcreteAlphabet.work) ++ tail⟩) := by
  let t₁ : List ConcreteTape :=
    List.replicate (4 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (8 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (16 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (32 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (64 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (128 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (256 * n) (.core MStarConcreteAlphabet.work) ++ tail
  let t₂ : List ConcreteTape :=
    List.replicate (8 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (16 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (32 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (64 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (128 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (256 * n) (.core MStarConcreteAlphabet.work) ++ tail
  let t₃ : List ConcreteTape :=
    List.replicate (16 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (32 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (64 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (128 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (256 * n) (.core MStarConcreteAlphabet.work) ++ tail
  let t₄ : List ConcreteTape :=
    List.replicate (32 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (64 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (128 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (256 * n) (.core MStarConcreteAlphabet.work) ++ tail
  let t₅ : List ConcreteTape :=
    List.replicate (64 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (128 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (256 * n) (.core MStarConcreteAlphabet.work) ++ tail
  let t₆ : List ConcreteTape :=
    List.replicate (128 * n) (.core MStarConcreteAlphabet.work) ++
    List.replicate (256 * n) (.core MStarConcreteAlphabet.work) ++ tail
  let t₇ : List ConcreteTape :=
    List.replicate (256 * n) (.core MStarConcreteAlphabet.work) ++ tail
  have h₀ : Reaches
      (roundStage 0 0 n (List.replicate (2 * n)
        (.core MStarConcreteAlphabet.work) ++ t₁) source)
      (roundStage 1 0 (2 * n) t₁ source) := by
    simpa [MStarCopierMicrocode.nextRound] using
      reaches_doubleRound_next (0 : Fin 8) n hn (by decide) t₁ source
  have h₁ : Reaches
      (roundStage 1 0 (2 * n) (List.replicate (4 * n)
        (.core MStarConcreteAlphabet.work) ++ t₂) source)
      (roundStage 2 0 (4 * n) t₂ source) := by
    have h := reaches_doubleRound_next (1 : Fin 8) (2 * n) (by omega)
      (by decide) t₂ source
    rw [show 2 * (2 * n) = 4 * n by ring] at h
    simpa [MStarCopierMicrocode.nextRound] using h
  have h₂ : Reaches
      (roundStage 2 0 (4 * n) (List.replicate (8 * n)
        (.core MStarConcreteAlphabet.work) ++ t₃) source)
      (roundStage 3 0 (8 * n) t₃ source) := by
    have h := reaches_doubleRound_next (2 : Fin 8) (4 * n) (by omega)
      (by decide) t₃ source
    rw [show 2 * (4 * n) = 8 * n by ring] at h
    simpa [MStarCopierMicrocode.nextRound] using h
  have h₃ : Reaches
      (roundStage 3 0 (8 * n) (List.replicate (16 * n)
        (.core MStarConcreteAlphabet.work) ++ t₄) source)
      (roundStage 4 0 (16 * n) t₄ source) := by
    have h := reaches_doubleRound_next (3 : Fin 8) (8 * n) (by omega)
      (by decide) t₄ source
    rw [show 2 * (8 * n) = 16 * n by ring] at h
    simpa [MStarCopierMicrocode.nextRound] using h
  have h₄ : Reaches
      (roundStage 4 0 (16 * n) (List.replicate (32 * n)
        (.core MStarConcreteAlphabet.work) ++ t₅) source)
      (roundStage 5 0 (32 * n) t₅ source) := by
    have h := reaches_doubleRound_next (4 : Fin 8) (16 * n) (by omega)
      (by decide) t₅ source
    rw [show 2 * (16 * n) = 32 * n by ring] at h
    simpa [MStarCopierMicrocode.nextRound] using h
  have h₅ : Reaches
      (roundStage 5 0 (32 * n) (List.replicate (64 * n)
        (.core MStarConcreteAlphabet.work) ++ t₆) source)
      (roundStage 6 0 (64 * n) t₆ source) := by
    have h := reaches_doubleRound_next (5 : Fin 8) (32 * n) (by omega)
      (by decide) t₆ source
    rw [show 2 * (32 * n) = 64 * n by ring] at h
    simpa [MStarCopierMicrocode.nextRound] using h
  have h₆ : Reaches
      (roundStage 6 0 (64 * n) (List.replicate (128 * n)
        (.core MStarConcreteAlphabet.work) ++ t₇) source)
      (roundStage 7 0 (128 * n) t₇ source) := by
    have h := reaches_doubleRound_next (6 : Fin 8) (64 * n) (by omega)
      (by decide) t₇ source
    rw [show 2 * (64 * n) = 128 * n by ring] at h
    simpa [MStarCopierMicrocode.nextRound] using h
  have h₇ : Reaches (roundStage 7 0 (128 * n) t₇ source)
      (.running .groupDone
        ⟨source, .markL,
          List.replicate (256 * n) cellA ++ .markR ::
            List.replicate (256 * n) (.core MStarConcreteAlphabet.work) ++ tail⟩) := by
    have h := reaches_doubleRound_final (7 : Fin 8) (128 * n) (by omega)
      (by decide) tail source
    have hdouble : 2 * (128 * n) = 256 * n := by ring
    simp only [doubledGroupZipper] at h
    simp only [hdouble] at h
    simpa only [t₇] using h
  have hstart : roundStage 0 0 n (eightRoundReserve n tail) source =
      roundStage 0 0 n (List.replicate (2 * n)
        (.core MStarConcreteAlphabet.work) ++ t₁) source := by
    simp only [eightRoundReserve, t₁, List.append_assoc]
  have h₀₁ := reaches_trans h₀
    (by simpa only [t₁, t₂, List.append_assoc] using h₁)
  have h₀₂ := reaches_trans h₀₁
    (by simpa only [t₂, t₃, List.append_assoc] using h₂)
  have h₀₃ := reaches_trans h₀₂
    (by simpa only [t₃, t₄, List.append_assoc] using h₃)
  have h₀₄ := reaches_trans h₀₃
    (by simpa only [t₄, t₅, List.append_assoc] using h₄)
  have h₀₅ := reaches_trans h₀₄
    (by simpa only [t₅, t₆, List.append_assoc] using h₅)
  have h₀₆ := reaches_trans h₀₅
    (by simpa only [t₆, t₇, List.append_assoc] using h₆)
  have hall := reaches_trans h₀₆ h₇
  rw [hstart]
  exact hall

def groupPrefix (bits : List Bool) (done : ℕ) : List ConcreteTape :=
  MStarParserMicrocode.endpointMark ::
    bits.reverse.map MStarConcreteAlphabet.payloadMarker ++
      MStarParserMicrocode.sepLen ::
        List.replicate done MStarParserMicrocode.lenDone

theorem replicate_cons_rotate (x : ConcreteTape) (n : ℕ)
    (tail : List ConcreteTape) :
    List.replicate n x ++ x :: tail = x :: List.replicate n x ++ tail := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (x :: ·) ih

def groupSource (bits : List Bool) (done remaining : ℕ)
    (junk : List ConcreteTape) : List ConcreteTape :=
  groupPrefix bits done ++
    List.replicate remaining MStarParserMicrocode.pairedLen ++
      MStarParserMicrocode.sepPad :: junk

def groupSeekStarted (bits : List Bool) (done remaining : ℕ)
    (junk blockRight : List ConcreteTape) : Result :=
  .running .groupSeekLen
    (beforeLeftList (groupPrefix bits done)
      (List.replicate remaining MStarParserMicrocode.pairedLen ++
        MStarParserMicrocode.sepPad :: junk)
      MStarParserMicrocode.pairedLen (.markL :: blockRight))

theorem reaches_groupSeekStarted (bits : List Bool) (done remaining : ℕ)
    (junk blockRight : List ConcreteTape) :
    Reaches
      (.running .groupDone
        ⟨groupSource bits done (remaining + 1) junk, .markL, blockRight⟩)
      (groupSeekStarted bits done remaining junk blockRight) := by
  apply reaches_of_oneStep
  simp [groupSource, groupPrefix, groupSeekStarted, beforeLeftList,
    groupDone_step, List.replicate_succ, List.append_assoc]

def groupAtPaired (bits : List Bool) (done remaining : ℕ)
    (junk blockRight : List ConcreteTape) : Result :=
  .running .groupSeekLen
    (afterLeftList (groupPrefix bits done)
      (List.replicate remaining MStarParserMicrocode.pairedLen ++
        MStarParserMicrocode.sepPad :: junk)
      MStarParserMicrocode.pairedLen (.markL :: blockRight))

theorem reaches_groupAtPaired (bits : List Bool) (done remaining : ℕ)
    (junk blockRight : List ConcreteTape) :
    Reaches (groupSeekStarted bits done remaining junk blockRight)
      (groupAtPaired bits done remaining junk blockRight) := by
  refine ⟨(groupPrefix bits done).length, ?_⟩
  apply run_left_list_of .groupSeekLen (groupPrefix bits done)
  intro x hx left y right
  have hpass : x = MStarParserMicrocode.endpointMark ∨
      x = MStarParserMicrocode.payloadZero ∨
      x = MStarParserMicrocode.payloadOne ∨
      x = MStarParserMicrocode.sepLen ∨
      x = MStarParserMicrocode.lenDone := by
    simp [groupPrefix] at hx
    rcases hx with rfl | hx | rfl | ⟨-, rfl⟩
    · exact Or.inl rfl
    · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
        simp [MStarConcreteAlphabet.payloadMarker]
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  exact groupSeek_pass_step x hpass left y right

def groupReturnStarted (bits : List Bool) (done remaining : ℕ)
    (junk blockRight : List ConcreteTape) : Result :=
  .running .groupReturn
    (beforeRightList (groupPrefix bits done).reverse
      (MStarParserMicrocode.lenDone ::
        List.replicate remaining MStarParserMicrocode.pairedLen ++
          MStarParserMicrocode.sepPad :: junk)
      .markL blockRight)

theorem reaches_groupReturnStarted (bits : List Bool) (done remaining : ℕ)
    (junk blockRight : List ConcreteTape) :
    Reaches (groupAtPaired bits done remaining junk blockRight)
      (groupReturnStarted bits done remaining junk blockRight) := by
  have hne : (groupPrefix bits done).reverse ≠ [] := by
    simp [groupPrefix]
  cases hrev : (groupPrefix bits done).reverse with
  | nil => exact (hne hrev).elim
  | cons x xs =>
      apply reaches_of_oneStep
      simp [groupAtPaired, groupReturnStarted, afterLeftList,
        beforeRightList, hrev, groupSeek_paired_step]

def groupReturnedToMark (bits : List Bool) (done remaining : ℕ)
    (junk blockRight : List ConcreteTape) : Result :=
  .running .groupReturn
    (afterRightList (groupPrefix bits done).reverse
      (MStarParserMicrocode.lenDone ::
        List.replicate remaining MStarParserMicrocode.pairedLen ++
          MStarParserMicrocode.sepPad :: junk)
      .markL blockRight)

theorem reaches_groupReturnedToMark (bits : List Bool) (done remaining : ℕ)
    (junk blockRight : List ConcreteTape) :
    Reaches (groupReturnStarted bits done remaining junk blockRight)
      (groupReturnedToMark bits done remaining junk blockRight) := by
  refine ⟨(groupPrefix bits done).length, ?_⟩
  rw [show (groupPrefix bits done).length =
      (groupPrefix bits done).reverse.length by simp]
  apply run_right_list_of .groupReturn (groupPrefix bits done).reverse
  intro x hx left y right
  have hx' : x ∈ groupPrefix bits done := by
    simpa using (List.mem_reverse.mp hx)
  have hpass : x = MStarParserMicrocode.lenDone ∨
      x = MStarParserMicrocode.sepLen ∨
      x = MStarParserMicrocode.payloadZero ∨
      x = MStarParserMicrocode.payloadOne ∨
      x = MStarParserMicrocode.endpointMark := by
    simp [groupPrefix] at hx'
    rcases hx' with rfl | hx | rfl | ⟨-, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
        simp [MStarConcreteAlphabet.payloadMarker]
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  exact groupReturn_pass_step x hpass left y right

theorem reaches_restart_next_group (bits : List Bool) (done remaining : ℕ)
    (junk : List ConcreteTape) (n : ℕ) (hn : 0 < n)
    (reserve : List ConcreteTape) :
    Reaches
      (.running .groupDone
        ⟨groupSource bits done (remaining + 1) junk, .markL,
          List.replicate n cellA ++ .markR ::
            List.replicate n (.core MStarConcreteAlphabet.work) ++ reserve⟩)
      (roundStage 0 0 n reserve
        (groupSource bits (done + 1) remaining junk)) := by
  have h₀ := reaches_groupSeekStarted bits done remaining junk
    (List.replicate n cellA ++ .markR ::
      List.replicate n (.core MStarConcreteAlphabet.work) ++ reserve)
  have h₁ := reaches_groupAtPaired bits done remaining junk
    (List.replicate n cellA ++ .markR ::
      List.replicate n (.core MStarConcreteAlphabet.work) ++ reserve)
  have h₂ := reaches_groupReturnStarted bits done remaining junk
    (List.replicate n cellA ++ .markR ::
      List.replicate n (.core MStarConcreteAlphabet.work) ++ reserve)
  have h₃ := reaches_groupReturnedToMark bits done remaining junk
    (List.replicate n cellA ++ .markR ::
      List.replicate n (.core MStarConcreteAlphabet.work) ++ reserve)
  have h₄ : Reaches
      (groupReturnedToMark bits done remaining junk
        (List.replicate n cellA ++ .markR ::
          List.replicate n (.core MStarConcreteAlphabet.work) ++ reserve))
      (roundStage 0 0 n reserve
        (groupSource bits (done + 1) remaining junk)) := by
    apply reaches_of_oneStep
    cases n with
    | zero => omega
    | succ n =>
        have hrotate := replicate_cons_rotate
          MStarParserMicrocode.lenDone done
          (List.replicate remaining MStarParserMicrocode.pairedLen ++
            MStarParserMicrocode.sepPad :: junk)
        simp [groupReturnedToMark, roundStage, groupSource, groupPrefix,
          afterRightList, groupReturn_mark_step,
          List.replicate_succ, List.map_reverse, List.append_assoc,
          List.replicate_add, hrotate]
  exact reaches_trans h₀
    (reaches_trans h₁ (reaches_trans h₂ (reaches_trans h₃ h₄)))

/-- Work beyond the permanent right buffer needed for the remaining
payload-length groups.  The current block's `n`-cell right buffer is kept
separate; each successor contributes exactly the reserve consumed by its
eight concrete doubling rounds. -/
def groupExtraReserve : ℕ → ℕ → List ConcreteTape → List ConcreteTape
  | 0, _, tail => tail
  | groups + 1, n, tail =>
      eightRoundReserve n (groupExtraReserve groups (256 * n) tail)

def iteratedGroupWidth : ℕ → ℕ → ℕ
  | 0, n => n
  | groups + 1, n => iteratedGroupWidth groups (256 * n)

theorem iteratedGroupWidth_pos (groups n : ℕ) (hn : 0 < n) :
    0 < iteratedGroupWidth groups n := by
  induction groups generalizing n with
  | zero => simpa [iteratedGroupWidth] using hn
  | succ groups ih =>
      simp only [iteratedGroupWidth]
      exact ih (256 * n) (by omega)

/-- Fold the actual `groupDone/groupSeekLen/groupReturn` control loop over
all remaining paired length markers.  Each marker triggers eight literal
doubling rounds, hence replaces unary width `n` by `256*n`. -/
theorem reaches_group_fold (bits : List Bool) (done groups : ℕ)
    (junk : List ConcreteTape) (n : ℕ) (hn : 0 < n)
    (tail : List ConcreteTape) :
    Reaches
      (.running .groupDone
        ⟨groupSource bits done groups junk, .markL,
          List.replicate n cellA ++ .markR ::
            List.replicate n (.core MStarConcreteAlphabet.work) ++
              groupExtraReserve groups n tail⟩)
      (.running .groupDone
        ⟨groupSource bits (done + groups) 0 junk, .markL,
          List.replicate (iteratedGroupWidth groups n) cellA ++ .markR ::
            List.replicate (iteratedGroupWidth groups n)
              (.core MStarConcreteAlphabet.work) ++ tail⟩) := by
  induction groups generalizing done n with
  | zero =>
      simp only [groupExtraReserve, iteratedGroupWidth, Nat.add_zero]
      exact reaches_refl _
  | succ groups ih =>
      have hrestart := reaches_restart_next_group bits done groups junk n hn
        (eightRoundReserve n
          (groupExtraReserve groups (256 * n) tail))
      have height := reaches_eight_doublings n hn
        (groupExtraReserve groups (256 * n) tail)
        (groupSource bits (done + 1) groups junk)
      have hnext := ih (done + 1) (256 * n) (by omega)
      have hfirst : Reaches
          (.running .groupDone
            ⟨groupSource bits done (groups + 1) junk, .markL,
              List.replicate n cellA ++ .markR ::
                List.replicate n (.core MStarConcreteAlphabet.work) ++
                  groupExtraReserve (groups + 1) n tail⟩)
          (.running .groupDone
            ⟨groupSource bits (done + 1) groups junk, .markL,
              List.replicate (256 * n) cellA ++ .markR ::
                List.replicate (256 * n) (.core MStarConcreteAlphabet.work) ++
                  groupExtraReserve groups (256 * n) tail⟩) := by
        exact reaches_trans
          (by simpa [groupExtraReserve] using hrestart) height
      have hall := reaches_trans hfirst hnext
      simpa [iteratedGroupWidth, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hall

def finishSeekStarted (bits : List Bool) (done : ℕ)
    (junk blockRight : List ConcreteTape) : Result :=
  .running .groupSeekLen
    (beforeLeftList (groupPrefix bits done) junk
      MStarParserMicrocode.sepPad (.markL :: blockRight))

def finishAtPad (bits : List Bool) (done : ℕ)
    (junk blockRight : List ConcreteTape) : Result :=
  .running .groupSeekLen
    (afterLeftList (groupPrefix bits done) junk
      MStarParserMicrocode.sepPad (.markL :: blockRight))

theorem reaches_finishAtPad (bits : List Bool) (done : ℕ)
    (junk blockRight : List ConcreteTape) :
    Reaches
      (.running .groupDone
        ⟨groupSource bits done 0 junk, .markL, blockRight⟩)
      (finishAtPad bits done junk blockRight) := by
  have hstart : Reaches
      (.running .groupDone
        ⟨groupSource bits done 0 junk, .markL, blockRight⟩)
      (finishSeekStarted bits done junk blockRight) := by
    have hne : groupPrefix bits done ≠ [] := by simp [groupPrefix]
    cases hp : groupPrefix bits done with
    | nil => exact (hne hp).elim
    | cons x xs =>
        apply reaches_of_oneStep
        simp [groupSource, finishSeekStarted, beforeLeftList, hp,
          groupDone_step]
  have hscan : Reaches (finishSeekStarted bits done junk blockRight)
      (finishAtPad bits done junk blockRight) := by
    refine ⟨(groupPrefix bits done).length, ?_⟩
    apply run_left_list_of .groupSeekLen (groupPrefix bits done)
    intro x hx left y right
    have hpass : x = MStarParserMicrocode.endpointMark ∨
        x = MStarParserMicrocode.payloadZero ∨
        x = MStarParserMicrocode.payloadOne ∨
        x = MStarParserMicrocode.sepLen ∨
        x = MStarParserMicrocode.lenDone := by
      simp [groupPrefix] at hx
      rcases hx with rfl | hx | rfl | ⟨-, rfl⟩
      · exact Or.inl rfl
      · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
          simp [MStarConcreteAlphabet.payloadMarker]
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    exact groupSeek_pass_step x hpass left y right
  exact reaches_trans hstart hscan

def finishReturnStarted (bits : List Bool) (done : ℕ)
    (junk blockRight : List ConcreteTape) : Result :=
  .running .finishReturn
    (beforeRightList (groupPrefix bits done).reverse
      (MStarParserMicrocode.sepPad :: junk) .markL blockRight)

theorem reaches_finishReturnStarted (bits : List Bool) (done : ℕ)
    (junk blockRight : List ConcreteTape) :
    Reaches (finishAtPad bits done junk blockRight)
      (finishReturnStarted bits done junk blockRight) := by
  have hne : (groupPrefix bits done).reverse ≠ [] := by
    simp [groupPrefix]
  cases hrev : (groupPrefix bits done).reverse with
  | nil => exact (hne hrev).elim
  | cons x xs =>
      apply reaches_of_oneStep
      simp [finishAtPad, finishReturnStarted, afterLeftList,
        beforeRightList, hrev, groupSeek_finished_step]

def finishReturnedToMark (bits : List Bool) (done : ℕ)
    (junk blockRight : List ConcreteTape) : Result :=
  .running .finishReturn
    (afterRightList (groupPrefix bits done).reverse
      (MStarParserMicrocode.sepPad :: junk) .markL blockRight)

theorem reaches_finishReturnedToMark (bits : List Bool) (done : ℕ)
    (junk blockRight : List ConcreteTape) :
    Reaches (finishReturnStarted bits done junk blockRight)
      (finishReturnedToMark bits done junk blockRight) := by
  refine ⟨(groupPrefix bits done).length, ?_⟩
  rw [show (groupPrefix bits done).length =
      (groupPrefix bits done).reverse.length by simp]
  apply run_right_list_of .finishReturn (groupPrefix bits done).reverse
  intro x hx left y right
  have hx' : x ∈ groupPrefix bits done := by
    simpa using (List.mem_reverse.mp hx)
  have hpass : x = MStarParserMicrocode.lenDone ∨
      x = MStarParserMicrocode.sepLen ∨
      x = MStarParserMicrocode.payloadZero ∨
      x = MStarParserMicrocode.payloadOne ∨
      x = MStarParserMicrocode.endpointMark := by
    simp [groupPrefix] at hx'
    rcases hx' with rfl | hx | rfl | ⟨-, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
        simp [MStarConcreteAlphabet.payloadMarker]
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  exact finishReturn_pass_step x hpass left y right

theorem reaches_counterStarted (bits : List Bool) (done : ℕ)
    (junk : List ConcreteTape) (n : ℕ) (hn : 0 < n)
    (blockTail : List ConcreteTape) :
    Reaches
      (.running .groupDone
        ⟨groupSource bits done 0 junk, .markL,
          List.replicate n cellA ++ blockTail⟩)
      (.running .counterToWork
        ⟨.markL :: groupSource bits done 0 junk, cellA,
          List.replicate (n - 1) cellA ++ blockTail⟩) := by
  have h₀ := reaches_finishAtPad bits done junk
    (List.replicate n cellA ++ blockTail)
  have h₁ := reaches_finishReturnStarted bits done junk
    (List.replicate n cellA ++ blockTail)
  have h₂ := reaches_finishReturnedToMark bits done junk
    (List.replicate n cellA ++ blockTail)
  have h₃ : Reaches
      (finishReturnedToMark bits done junk
        (List.replicate n cellA ++ blockTail))
      (.running .counterToWork
        ⟨.markL :: groupSource bits done 0 junk, cellA,
          List.replicate (n - 1) cellA ++ blockTail⟩) := by
    apply reaches_of_oneStep
    cases n with
    | zero => omega
    | succ n =>
        simp [finishReturnedToMark, groupSource, afterRightList,
          finishReturn_mark_step, List.replicate_succ]
  exact reaches_trans h₀ (reaches_trans h₁ (reaches_trans h₂ h₃))

theorem run_counterToWork_A (n : ℕ) (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    run n (.running .counterToWork
      (beforeRightRepeat n cellA left y right)) =
      .running .counterToWork
        (afterRightRepeat n (.core MStarConcreteAlphabet.work) left y right) := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
      rw [run_succ]
      have hone : oneStep (.running .counterToWork
          (beforeRightRepeat (n + 1) cellA left y right)) =
          .running .counterToWork
            (beforeRightRepeat n cellA
              (.core MStarConcreteAlphabet.work :: left) y right) := by
        cases n <;> simp [beforeRightRepeat, List.replicate_succ,
          counterToWork_A_step, List.append_assoc]
      rw [hone, ih]
      apply congrArg (Result.running .counterToWork)
      apply Zipper.ext <;>
        simp [afterRightRepeat, List.replicate_succ', List.append_assoc]

theorem reaches_payloadSeekStarted (source : List ConcreteTape)
    (n : ℕ) (hn : 0 < n) (right : List ConcreteTape) :
    Reaches
      (.running .counterToWork
        ⟨.markL :: source, cellA,
          List.replicate (n - 1) cellA ++ .markR ::
            .core MStarConcreteAlphabet.work :: right⟩)
      (.running .payloadSeek
        ⟨List.replicate n (.core MStarConcreteAlphabet.work) ++
            .markL :: source,
          .core MStarConcreteAlphabet.work, .markR :: right⟩) := by
  have h₀ : Reaches
      (.running .counterToWork
        ⟨.markL :: source, cellA,
          List.replicate (n - 1) cellA ++ .markR ::
            .core MStarConcreteAlphabet.work :: right⟩)
      (.running .counterToWork
        ⟨List.replicate n (.core MStarConcreteAlphabet.work) ++
            .markL :: source,
          .markR, .core MStarConcreteAlphabet.work :: right⟩) := by
    cases n with
    | zero => omega
    | succ n =>
        refine ⟨n + 1, ?_⟩
        simpa [beforeRightRepeat, afterRightRepeat, List.replicate_succ,
          List.append_assoc] using
          (run_counterToWork_A (n + 1) (.markL :: source) .markR
            (.core MStarConcreteAlphabet.work :: right))
  have h₁ : Reaches
      (.running .counterToWork
        ⟨List.replicate n (.core MStarConcreteAlphabet.work) ++
            .markL :: source,
          .markR, .core MStarConcreteAlphabet.work :: right⟩)
      (.running .payloadBoundary
        ⟨.core MStarConcreteAlphabet.work ::
            (List.replicate n (.core MStarConcreteAlphabet.work) ++
              .markL :: source),
          .core MStarConcreteAlphabet.work, right⟩) := by
    apply reaches_of_oneStep
    exact counterToWork_mark_step _ _ _
  have h₂ : Reaches
      (.running .payloadBoundary
        ⟨.core MStarConcreteAlphabet.work ::
            (List.replicate n (.core MStarConcreteAlphabet.work) ++
              .markL :: source),
          .core MStarConcreteAlphabet.work, right⟩)
      (.running .payloadSeek
        ⟨List.replicate n (.core MStarConcreteAlphabet.work) ++
            .markL :: source,
          .core MStarConcreteAlphabet.work, .markR :: right⟩) := by
    apply reaches_of_oneStep
    exact payloadBoundary_step _ _
  exact reaches_trans h₀ (reaches_trans h₁ h₂)

def coreBit (b : Bool) : ConcreteTape :=
  .core (if b then MStarConcreteAlphabet.one else MStarConcreteAlphabet.zero)

def payloadPath (copiedRev : List Bool) (processed n : ℕ) :
    List ConcreteTape :=
  copiedRev.map coreBit ++
    List.replicate (n + 1) (.core MStarConcreteAlphabet.work) ++
      [.markL, MStarParserMicrocode.endpointMark] ++
        List.replicate processed MStarParserMicrocode.lenDone

theorem payloadPath_seek_pass (copiedRev : List Bool) (processed n : ℕ)
    (x : ConcreteTape) (hx : x ∈ payloadPath copiedRev processed n) :
    x = .core MStarConcreteAlphabet.work ∨
      x = .core MStarConcreteAlphabet.zero ∨
      x = .core MStarConcreteAlphabet.one ∨ x = .markL ∨
      x = MStarParserMicrocode.endpointMark ∨
      x = MStarParserMicrocode.lenDone := by
  simp [payloadPath] at hx
  rcases hx with hx | rfl | rfl | rfl | ⟨-, rfl⟩
  · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [coreBit]
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

theorem payloadPath_carry_pass (copiedRev : List Bool) (processed n : ℕ)
    (x : ConcreteTape) (hx : x ∈ payloadPath copiedRev processed n) :
    x = MStarParserMicrocode.lenDone ∨
      x = MStarParserMicrocode.endpointMark ∨ x = .markL ∨
      x = .core MStarConcreteAlphabet.work ∨
      x = .core MStarConcreteAlphabet.zero ∨
      x = .core MStarConcreteAlphabet.one := by
  have h := payloadPath_seek_pass copiedRev processed n x hx
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

def payloadBefore (copiedRev : List Bool) (processed n : ℕ)
    (source : List ConcreteTape) (next : ConcreteTape)
    (boundaryTail : List ConcreteTape) : Result :=
  .running .payloadSeek
    (beforeLeftList (payloadPath copiedRev processed n) source next
      (.markR :: boundaryTail))

def payloadAtSource (copiedRev : List Bool) (processed n : ℕ)
    (source : List ConcreteTape) (next : ConcreteTape)
    (boundaryTail : List ConcreteTape) : Result :=
  .running .payloadSeek
    (afterLeftList (payloadPath copiedRev processed n) source next
      (.markR :: boundaryTail))

theorem reaches_payloadAtSource (copiedRev : List Bool) (processed n : ℕ)
    (source : List ConcreteTape) (next : ConcreteTape)
    (boundaryTail : List ConcreteTape) :
    Reaches (payloadBefore copiedRev processed n source next boundaryTail)
      (payloadAtSource copiedRev processed n source next boundaryTail) := by
  refine ⟨(payloadPath copiedRev processed n).length, ?_⟩
  apply run_left_list_of .payloadSeek (payloadPath copiedRev processed n)
  intro x hx left y right
  exact payloadSeek_pass_step x
    (payloadPath_seek_pass copiedRev processed n x hx) left y right

def payloadCarryStarted (b : Bool) (copiedRev : List Bool)
    (processed n : ℕ) (source boundaryRight : List ConcreteTape) : Result :=
  .running (.payloadCarry b)
    (beforeRightList (payloadPath copiedRev processed n).reverse
      (MStarParserMicrocode.lenDone :: source) .markR boundaryRight)

theorem reaches_payloadCarryStarted (b : Bool) (copiedRev : List Bool)
    (processed n : ℕ) (source boundaryRight : List ConcreteTape) :
    Reaches
      (payloadAtSource copiedRev processed n source
        (MStarConcreteAlphabet.payloadMarker b) boundaryRight)
      (payloadCarryStarted b copiedRev processed n source boundaryRight) := by
  have hne : (payloadPath copiedRev processed n).reverse ≠ [] := by
    simp [payloadPath]
  cases hrev : (payloadPath copiedRev processed n).reverse with
  | nil => exact (hne hrev).elim
  | cons x xs =>
      apply reaches_of_oneStep
      simp [payloadAtSource, payloadCarryStarted, afterLeftList,
        beforeRightList, hrev, payloadSeek_marker_step]

def payloadAtBoundary (b : Bool) (copiedRev : List Bool)
    (processed n : ℕ) (source boundaryRight : List ConcreteTape) : Result :=
  .running (.payloadCarry b)
    (afterRightList (payloadPath copiedRev processed n).reverse
      (MStarParserMicrocode.lenDone :: source) .markR boundaryRight)

theorem reaches_payloadAtBoundary (b : Bool) (copiedRev : List Bool)
    (processed n : ℕ) (source boundaryRight : List ConcreteTape) :
    Reaches (payloadCarryStarted b copiedRev processed n source boundaryRight)
      (payloadAtBoundary b copiedRev processed n source boundaryRight) := by
  refine ⟨(payloadPath copiedRev processed n).length, ?_⟩
  rw [show (payloadPath copiedRev processed n).length =
      (payloadPath copiedRev processed n).reverse.length by simp]
  apply run_right_list_of (.payloadCarry b)
    (payloadPath copiedRev processed n).reverse
  intro x hx left y right
  have hx' : x ∈ payloadPath copiedRev processed n := by
    simpa using (List.mem_reverse.mp hx)
  exact payloadCarry_pass_step b x
    (payloadPath_carry_pass copiedRev processed n x hx') left y right

theorem payloadPath_next (b : Bool) (copiedRev : List Bool)
    (processed n : ℕ) :
    coreBit b :: payloadPath copiedRev processed n ++
        [MStarParserMicrocode.lenDone] =
      payloadPath (b :: copiedRev) (processed + 1) n := by
  simp [payloadPath, coreBit, List.replicate_succ, List.append_assoc,
    replicate_cons_rotate]

theorem reaches_payload_iteration (b : Bool) (copiedRev : List Bool)
    (processed n : ℕ) (source : List ConcreteTape)
    (next : ConcreteTape) (right : List ConcreteTape) :
    Reaches
      (payloadBefore copiedRev processed n (next :: source)
        (MStarConcreteAlphabet.payloadMarker b)
        (.core MStarConcreteAlphabet.work :: right))
      (payloadBefore (b :: copiedRev) (processed + 1) n source next right) := by
  have h₀ := reaches_payloadAtSource copiedRev processed n (next :: source)
    (MStarConcreteAlphabet.payloadMarker b)
    (.core MStarConcreteAlphabet.work :: right)
  have h₁ := reaches_payloadCarryStarted b copiedRev processed n
    (next :: source) (.core MStarConcreteAlphabet.work :: right)
  have h₂ := reaches_payloadAtBoundary b copiedRev processed n
    (next :: source) (.core MStarConcreteAlphabet.work :: right)
  have h₃ : Reaches
      (payloadAtBoundary b copiedRev processed n (next :: source)
        (.core MStarConcreteAlphabet.work :: right))
      (.running .payloadPlace
        ⟨coreBit b :: payloadPath copiedRev processed n ++
            MStarParserMicrocode.lenDone :: next :: source,
          .core MStarConcreteAlphabet.work, right⟩) := by
    apply reaches_of_oneStep
    simp only [payloadAtBoundary, afterRightList, List.reverse_reverse]
    cases b <;> rfl
  have h₄ : Reaches
      (.running .payloadPlace
        ⟨coreBit b :: payloadPath copiedRev processed n ++
            MStarParserMicrocode.lenDone :: next :: source,
          .core MStarConcreteAlphabet.work, right⟩)
      (payloadBefore (b :: copiedRev) (processed + 1) n source next right) := by
    apply reaches_of_oneStep
    unfold payloadBefore
    rw [← payloadPath_next]
    simp [beforeLeftList, payloadPlace_step, List.append_assoc]
  exact reaches_trans h₀
    (reaches_trans h₁ (reaches_trans h₂ (reaches_trans h₃ h₄)))

def payloadLoop (copiedRev : List Bool) (processed n : ℕ)
    (todo : List Bool) (source boundaryTail : List ConcreteTape) : Result :=
  match todo with
  | [] => payloadBefore copiedRev processed n source
      MStarParserMicrocode.sepLen boundaryTail
  | b :: bs => payloadBefore copiedRev processed n
      (bs.map MStarConcreteAlphabet.payloadMarker ++
        MStarParserMicrocode.sepLen :: source)
      (MStarConcreteAlphabet.payloadMarker b) boundaryTail

theorem reaches_payload_fold (todo copiedRev : List Bool)
    (processed n : ℕ) (source right : List ConcreteTape) :
    Reaches
      (payloadLoop copiedRev processed n todo source
        (List.replicate todo.length (.core MStarConcreteAlphabet.work) ++ right))
      (payloadLoop (todo.reverse ++ copiedRev) (processed + todo.length)
        n [] source right) := by
  induction todo generalizing copiedRev processed with
  | nil =>
      simp [payloadLoop]
      exact reaches_refl _
  | cons b bs ih =>
      have hstep' : Reaches
          (payloadLoop copiedRev processed n (b :: bs) source
            (List.replicate (b :: bs).length
              (.core MStarConcreteAlphabet.work) ++ right))
          (payloadLoop (b :: copiedRev) (processed + 1) n bs source
            (List.replicate bs.length
              (.core MStarConcreteAlphabet.work) ++ right)) := by
        cases bs with
        | nil =>
            simpa [payloadLoop, List.replicate_succ] using
              (reaches_payload_iteration b copiedRev processed n source
                MStarParserMicrocode.sepLen right)
        | cons c cs =>
            simpa [payloadLoop, List.replicate_succ, List.append_assoc] using
              (reaches_payload_iteration b copiedRev processed n
                (cs.map MStarConcreteAlphabet.payloadMarker ++
                  MStarParserMicrocode.sepLen :: source)
                (MStarConcreteAlphabet.payloadMarker c)
                (.core MStarConcreteAlphabet.work ::
                  (List.replicate cs.length
                    (.core MStarConcreteAlphabet.work) ++ right)))
      have hrest := ih (b :: copiedRev) (processed + 1)
      have hall := reaches_trans hstep' hrest
      have hnat : processed + 1 + bs.length =
          processed + (bs.length + 1) := by omega
      simpa [payloadLoop, List.reverse_cons, Nat.add_assoc,
        List.append_assoc, hnat] using hall

def doneReturnPrefix (processed : ℕ) : List ConcreteTape :=
  List.replicate processed MStarParserMicrocode.lenDone ++
    [MStarParserMicrocode.endpointMark]

def finalForwardPath (n : ℕ) (copiedRev : List Bool) :
    List ConcreteTape :=
  List.replicate (n + 1) (.core MStarConcreteAlphabet.work) ++
    copiedRev.reverse.map coreBit

theorem payloadPath_reverse (copiedRev : List Bool) (processed n : ℕ) :
    (payloadPath copiedRev processed n).reverse =
      doneReturnPrefix processed ++ .markL :: finalForwardPath n copiedRev := by
  simp [payloadPath, doneReturnPrefix, finalForwardPath,
    List.reverse_append, List.map_reverse, List.append_assoc]

def payloadDoneStarted (copiedRev : List Bool) (processed n : ℕ)
    (source boundaryTail : List ConcreteTape) : Result :=
  .running .payloadDoneReturn
    (beforeRightList (doneReturnPrefix processed)
      (MStarParserMicrocode.sepLen :: source) .markL
      (finalForwardPath n copiedRev ++ .markR :: boundaryTail))

theorem reaches_payloadDoneStarted (copiedRev : List Bool)
    (processed n : ℕ) (source boundaryTail : List ConcreteTape) :
    Reaches
      (payloadAtSource copiedRev processed n source
        MStarParserMicrocode.sepLen boundaryTail)
      (payloadDoneStarted copiedRev processed n source boundaryTail) := by
  have hne : doneReturnPrefix processed ≠ [] := by
    simp [doneReturnPrefix]
  cases hp : doneReturnPrefix processed with
  | nil => exact (hne hp).elim
  | cons x xs =>
      apply reaches_of_oneStep
      unfold payloadAtSource payloadDoneStarted
      simp only [afterLeftList]
      rw [payloadPath_reverse]
      simp [afterLeftList, beforeRightList, hp,
        payloadSeek_sep_step, List.append_assoc]

def payloadDoneAtMark (copiedRev : List Bool) (processed n : ℕ)
    (source boundaryTail : List ConcreteTape) : Result :=
  .running .payloadDoneReturn
    (afterRightList (doneReturnPrefix processed)
      (MStarParserMicrocode.sepLen :: source) .markL
      (finalForwardPath n copiedRev ++ .markR :: boundaryTail))

theorem reaches_payloadDoneAtMark (copiedRev : List Bool)
    (processed n : ℕ) (source boundaryTail : List ConcreteTape) :
    Reaches (payloadDoneStarted copiedRev processed n source boundaryTail)
      (payloadDoneAtMark copiedRev processed n source boundaryTail) := by
  refine ⟨(doneReturnPrefix processed).length, ?_⟩
  apply run_right_list_of .payloadDoneReturn (doneReturnPrefix processed)
  intro x hx left y right
  have hpass : x = MStarParserMicrocode.lenDone ∨
      x = MStarParserMicrocode.endpointMark := by
    simp [doneReturnPrefix] at hx
    rcases hx with ⟨-, rfl⟩ | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  exact payloadDoneReturn_pass_step x hpass left y right

def finalSeekStarted (copiedRev : List Bool) (processed n : ℕ)
    (source boundaryTail : List ConcreteTape) : Result :=
  .running .finalSeekBoundary
    (beforeRightList (finalForwardPath n copiedRev)
      (.markL :: (doneReturnPrefix processed).reverse ++
        MStarParserMicrocode.sepLen :: source)
      .markR boundaryTail)

theorem reaches_finalSeekStarted (copiedRev : List Bool)
    (processed n : ℕ) (source boundaryTail : List ConcreteTape) :
    Reaches (payloadDoneAtMark copiedRev processed n source boundaryTail)
      (finalSeekStarted copiedRev processed n source boundaryTail) := by
  have hne : finalForwardPath n copiedRev ≠ [] := by
    simp [finalForwardPath]
  cases hp : finalForwardPath n copiedRev with
  | nil => exact (hne hp).elim
  | cons x xs =>
      apply reaches_of_oneStep
      unfold payloadDoneAtMark finalSeekStarted
      simp [afterRightList, beforeRightList, hp,
        payloadDoneReturn_mark_step, List.append_assoc]

def finalAtBoundary (copiedRev : List Bool) (processed n : ℕ)
    (source boundaryTail : List ConcreteTape) : Result :=
  .running .finalSeekBoundary
    (afterRightList (finalForwardPath n copiedRev)
      (.markL :: (doneReturnPrefix processed).reverse ++
        MStarParserMicrocode.sepLen :: source)
      .markR boundaryTail)

theorem reaches_finalAtBoundary (copiedRev : List Bool)
    (processed n : ℕ) (source boundaryTail : List ConcreteTape) :
    Reaches (finalSeekStarted copiedRev processed n source boundaryTail)
      (finalAtBoundary copiedRev processed n source boundaryTail) := by
  refine ⟨(finalForwardPath n copiedRev).length, ?_⟩
  apply run_right_list_of .finalSeekBoundary (finalForwardPath n copiedRev)
  intro x hx left y right
  have hpass : x = .core MStarConcreteAlphabet.work ∨
      x = .core MStarConcreteAlphabet.zero ∨
      x = .core MStarConcreteAlphabet.one := by
    simp [finalForwardPath] at hx
    rcases hx with ⟨-, rfl⟩ | hx
    · exact Or.inl rfl
    · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
        simp [coreBit]
  exact finalSeekBoundary_pass_step x hpass left y right

theorem reaches_rightBufferStarted (copiedRev : List Bool)
    (processed n : ℕ) (source : List ConcreteTape)
    (boundaryTail : List ConcreteTape) :
    Reaches (finalAtBoundary copiedRev processed n source
      (.core MStarConcreteAlphabet.work :: boundaryTail))
      (.running .rightBufferScan
        ⟨.core MStarConcreteAlphabet.work ::
            ((finalForwardPath n copiedRev).reverse ++
              .markL :: (doneReturnPrefix processed).reverse ++
                MStarParserMicrocode.sepLen :: source),
          .core MStarConcreteAlphabet.work, boundaryTail⟩) := by
  apply reaches_of_oneStep
  simp [finalAtBoundary, afterRightList, finalSeekBoundary_mark_step,
    List.append_assoc]

theorem run_rightBuffer_work (k : ℕ) (left : List ConcreteTape)
    (y : ConcreteTape) (right : List ConcreteTape) :
    run k (.running .rightBufferScan
      (beforeRightRepeat k (.core MStarConcreteAlphabet.work) left y right)) =
      .running .rightBufferScan
        (afterRightRepeat k (.core MStarConcreteAlphabet.work) left y right) :=
  run_right_repeat_of .rightBufferScan (.core MStarConcreteAlphabet.work)
    rightBufferScan_work_step k left y right

def finalSpan (n : ℕ) (copiedRev : List Bool) : List ConcreteTape :=
  finalForwardPath n copiedRev ++
    List.replicate (n + 1) (.core MStarConcreteAlphabet.work)

def rightBufferStarted (copiedRev : List Bool) (processed n : ℕ)
    (source external : List ConcreteTape) : Result :=
  .running .rightBufferScan
    (beforeRightRepeat n (.core MStarConcreteAlphabet.work)
      (.core MStarConcreteAlphabet.work ::
        (finalForwardPath n copiedRev).reverse ++
          .markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source)
      rightEnd external)

theorem reaches_rightBufferStarted_exact (copiedRev : List Bool)
    (processed n : ℕ) (source external : List ConcreteTape) :
    Reaches
      (finalAtBoundary copiedRev processed n source
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          rightEnd :: external))
      (rightBufferStarted copiedRev processed n source external) := by
  apply reaches_of_oneStep
  cases n <;> simp [rightBufferStarted, finalAtBoundary, afterRightList,
    beforeRightRepeat, finalSeekBoundary_mark_step, List.replicate_succ,
    List.append_assoc]

theorem reaches_finalReturnStarted (copiedRev : List Bool)
    (processed n : ℕ) (source external : List ConcreteTape) :
    Reaches
      (finalAtBoundary copiedRev processed n source
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          rightEnd :: external))
      (.running .finalReturn
        (beforeLeftList (finalSpan n copiedRev).reverse
          ((doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source)
          .markL (.markR :: external))) := by
  have h₀ := reaches_rightBufferStarted_exact copiedRev processed n source external
  have h₁ : Reaches
      (rightBufferStarted copiedRev processed n source external)
      (.running .rightBufferScan
        (afterRightRepeat n (.core MStarConcreteAlphabet.work)
          (.core MStarConcreteAlphabet.work ::
            (finalForwardPath n copiedRev).reverse ++
              .markL :: (doneReturnPrefix processed).reverse ++
                MStarParserMicrocode.sepLen :: source)
          rightEnd external)) := by
    refine ⟨n, ?_⟩
    unfold rightBufferStarted
    exact run_rightBuffer_work n
      (.core MStarConcreteAlphabet.work ::
        (finalForwardPath n copiedRev).reverse ++
          .markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source)
      rightEnd external
  have h₂ : Reaches
      (.running .rightBufferScan
        (afterRightRepeat n (.core MStarConcreteAlphabet.work)
          (.core MStarConcreteAlphabet.work ::
            (finalForwardPath n copiedRev).reverse ++
              .markL :: (doneReturnPrefix processed).reverse ++
                MStarParserMicrocode.sepLen :: source)
          rightEnd external))
      (.running .finalReturn
        (beforeLeftList (finalSpan n copiedRev).reverse
          ((doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source)
          .markL (.markR :: external))) := by
    have hwalk : List.replicate n (.core MStarConcreteAlphabet.work) ++
          .core MStarConcreteAlphabet.work ::
            (finalForwardPath n copiedRev).reverse =
        (finalSpan n copiedRev).reverse := by
      simp [finalSpan, List.reverse_append, List.replicate_succ,
        replicate_cons_rotate]
    have hwalk' : List.replicate n (.core MStarConcreteAlphabet.work) ++
          (.core MStarConcreteAlphabet.work ::
            (finalForwardPath n copiedRev).reverse ++
              .markL :: (doneReturnPrefix processed).reverse ++
                MStarParserMicrocode.sepLen :: source) =
        (finalSpan n copiedRev).reverse ++
          .markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source := by
      simpa [List.append_assoc] using congrArg
        (fun xs => xs ++
          (.markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source)) hwalk
    have hne : (finalSpan n copiedRev).reverse ≠ [] := by
      simp [finalSpan, finalForwardPath]
    cases hp : (finalSpan n copiedRev).reverse with
    | nil => exact (hne hp).elim
    | cons x xs =>
        apply reaches_of_oneStep
        unfold afterRightRepeat
        rw [hwalk', hp]
        simp [beforeLeftList, hp, rightBufferScan_end_step]
  exact reaches_trans h₀ (reaches_trans h₁ h₂)

def finalAtMark (copiedRev : List Bool) (processed n : ℕ)
    (source external : List ConcreteTape) : Result :=
  .running .finalReturn
    (afterLeftList (finalSpan n copiedRev).reverse
      ((doneReturnPrefix processed).reverse ++
        MStarParserMicrocode.sepLen :: source)
      .markL (.markR :: external))

theorem reaches_finalAtMark (copiedRev : List Bool)
    (processed n : ℕ) (source external : List ConcreteTape) :
    Reaches
      (.running .finalReturn
        (beforeLeftList (finalSpan n copiedRev).reverse
          ((doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source)
          .markL (.markR :: external)))
      (finalAtMark copiedRev processed n source external) := by
  refine ⟨(finalSpan n copiedRev).length, ?_⟩
  rw [show (finalSpan n copiedRev).length =
      (finalSpan n copiedRev).reverse.length by simp]
  apply run_left_list_of .finalReturn (finalSpan n copiedRev).reverse
  intro x hx left y right
  have hx' : x ∈ finalSpan n copiedRev := by
    simpa using (List.mem_reverse.mp hx)
  have hpass : x = .core MStarConcreteAlphabet.work ∨
      x = .core MStarConcreteAlphabet.zero ∨
      x = .core MStarConcreteAlphabet.one := by
    simp [finalSpan, finalForwardPath] at hx'
    rcases hx' with ⟨-, rfl⟩ | hx | ⟨-, rfl⟩
    · exact Or.inl rfl
    · rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
        simp [coreBit]
    · exact Or.inl rfl
  exact finalReturn_pass_step x hpass left y right

theorem reaches_groupReady (copiedRev : List Bool) (processed n : ℕ)
    (source external : List ConcreteTape) :
    Reaches (finalAtMark copiedRev processed n source external)
      (.groupReady
        ⟨.markL :: (doneReturnPrefix processed).reverse ++
            MStarParserMicrocode.sepLen :: source,
          .core MStarConcreteAlphabet.work,
          List.replicate n (.core MStarConcreteAlphabet.work) ++
            copiedRev.reverse.map coreBit ++
              List.replicate (n + 1) (.core MStarConcreteAlphabet.work) ++
                .markR :: external⟩) := by
  apply reaches_of_oneStep
  simp [finalAtMark, finalSpan, finalForwardPath, afterLeftList,
    finalReturn_mark_step, List.reverse_append, List.map_reverse,
    List.replicate_succ, List.append_assoc]

theorem iteratedGroupWidth_closed (groups n : ℕ) :
    iteratedGroupWidth groups n = 256 ^ groups * n := by
  induction groups generalizing n with
  | zero => simp [iteratedGroupWidth]
  | succ groups ih =>
      simp [iteratedGroupWidth, ih, Nat.pow_succ]
      ring

theorem copier_width_eq_time_bound (m : ℕ) :
    iteratedGroupWidth m 256 = 2 ^ (8 * (m + 1)) := by
  rw [iteratedGroupWidth_closed]
  have h256 : 256 = 2 ^ 8 := by norm_num
  rw [h256, ← Nat.pow_succ]
  rw [← Nat.pow_mul]

def copierRoundReserve (m : ℕ) (external : List ConcreteTape) :
    List ConcreteTape :=
  eightRoundReserve 1
    (groupExtraReserve m 256
      (List.replicate (m + 1) (.core MStarConcreteAlphabet.work) ++
        rightEnd :: external))

def copierReserve (m : ℕ) (external : List ConcreteTape) :
    List ConcreteTape :=
  .core MStarConcreteAlphabet.work :: copierRoundReserve m external

set_option maxRecDepth 10000 in
/-- Complete concrete copier execution from the state immediately after the
parser's `copyStart` action.  The source record may have arbitrary checked
padding junk to its left; the marked segment delivered to the simulated
machine is exactly the two `(N+1)`-cell work buffers with the payload between
them, where `N = 2^(8*(|x|+1))`. -/
theorem reaches_copier_complete (x : List Bool)
    (junk external : List ConcreteTape) :
    let m := x.length
    let n := iteratedGroupWidth m 256
    Reaches
      (.running .seedCell
        ⟨.markL :: groupSource x.reverse 0 m junk,
          .core MStarConcreteAlphabet.work,
          .core MStarConcreteAlphabet.work :: copierReserve m external⟩)
      (.groupReady
        ⟨(.markL :: (doneReturnPrefix m).reverse) ++
            MStarParserMicrocode.sepLen ::
              (List.replicate m MStarParserMicrocode.lenDone ++
                MStarParserMicrocode.sepPad :: junk),
          .core MStarConcreteAlphabet.work,
          List.replicate n (.core MStarConcreteAlphabet.work) ++
            x.map coreBit ++
              List.replicate (n + 1) (.core MStarConcreteAlphabet.work) ++
                .markR :: external⟩) := by
  dsimp only
  let finalTail : List ConcreteTape :=
    List.replicate (x.length + 1) (.core MStarConcreteAlphabet.work) ++
      rightEnd :: external
  let sourceTail : List ConcreteTape :=
    List.replicate x.length MStarParserMicrocode.lenDone ++
      MStarParserMicrocode.sepPad :: junk
  let n := iteratedGroupWidth x.length 256
  have hn : 0 < n := iteratedGroupWidth_pos x.length 256 (by omega)
  have hnshape : n = (n - 1) + 1 := by omega
  have hrep : List.replicate n
        (MStarOuterProgram.Tape.core MStarConcreteAlphabet.work) =
      MStarOuterProgram.Tape.core MStarConcreteAlphabet.work ::
        List.replicate (n - 1)
          (MStarOuterProgram.Tape.core MStarConcreteAlphabet.work) := by
    rw [hnshape]
    simp [List.replicate_succ]
  have hseed : Reaches
      (.running .seedCell
        ⟨.markL :: groupSource x.reverse 0 x.length junk,
          .core MStarConcreteAlphabet.work,
          .core MStarConcreteAlphabet.work :: copierReserve x.length external⟩)
      (roundStage 0 0 1 (copierRoundReserve x.length external)
        (groupSource x.reverse 0 x.length junk)) := by
    refine ⟨4, ?_⟩
    simpa [copierReserve, roundStage] using
      (seed_reaches_round_zero_source (copierReserve x.length external)
        (groupSource x.reverse 0 x.length junk))
  have hbase := reaches_eight_doublings 1 (by omega)
    (groupExtraReserve x.length 256 finalTail)
    (groupSource x.reverse 0 x.length junk)
  have hgroups := reaches_group_fold x.reverse 0 x.length junk 256
    (by omega) finalTail
  have hcounter := reaches_counterStarted x.reverse x.length junk n hn
    (.markR :: List.replicate n (.core MStarConcreteAlphabet.work) ++ finalTail)
  have hseek := reaches_payloadSeekStarted
    (groupSource x.reverse x.length 0 junk) n hn
    (List.replicate (n - 1) (.core MStarConcreteAlphabet.work) ++ finalTail)
  have hpayload := reaches_payload_fold x [] 0 n sourceTail
    (List.replicate n (.core MStarConcreteAlphabet.work) ++
      rightEnd :: external)
  have hat := reaches_payloadAtSource x.reverse x.length n sourceTail
    MStarParserMicrocode.sepLen
    (List.replicate n (.core MStarConcreteAlphabet.work) ++
      rightEnd :: external)
  have hdone₀ := reaches_payloadDoneStarted x.reverse x.length n sourceTail
    (List.replicate n (.core MStarConcreteAlphabet.work) ++
      rightEnd :: external)
  have hdone₁ := reaches_payloadDoneAtMark x.reverse x.length n sourceTail
    (List.replicate n (.core MStarConcreteAlphabet.work) ++
      rightEnd :: external)
  have hfinal₀ := reaches_finalSeekStarted x.reverse x.length n sourceTail
    (List.replicate n (.core MStarConcreteAlphabet.work) ++
      rightEnd :: external)
  have hfinal₁ := reaches_finalAtBoundary x.reverse x.length n sourceTail
    (List.replicate n (.core MStarConcreteAlphabet.work) ++
      rightEnd :: external)
  have hfinal₂ := reaches_finalReturnStarted x.reverse x.length n sourceTail external
  have hfinal₃ := reaches_finalAtMark x.reverse x.length n sourceTail external
  have hready := reaches_groupReady x.reverse x.length n sourceTail external
  have hbase' : Reaches
      (roundStage 0 0 1 (copierRoundReserve x.length external)
        (groupSource x.reverse 0 x.length junk))
      (.running .groupDone
        ⟨groupSource x.reverse 0 x.length junk, .markL,
          List.replicate 256 cellA ++ .markR ::
            List.replicate 256 (.core MStarConcreteAlphabet.work) ++
              groupExtraReserve x.length 256 finalTail⟩) := by
    simpa only [copierRoundReserve, finalTail, Nat.mul_one] using hbase
  have hgroups' : Reaches
      (.running .groupDone
        ⟨groupSource x.reverse 0 x.length junk, .markL,
          List.replicate 256 cellA ++ .markR ::
            List.replicate 256 (.core MStarConcreteAlphabet.work) ++
              groupExtraReserve x.length 256 finalTail⟩)
      (.running .groupDone
        ⟨groupSource x.reverse x.length 0 junk, .markL,
          List.replicate n cellA ++ .markR ::
            List.replicate n (.core MStarConcreteAlphabet.work) ++ finalTail⟩) := by
    simpa only [Nat.zero_add] using hgroups
  have hcounter' : Reaches
      (.running .groupDone
        ⟨groupSource x.reverse x.length 0 junk, .markL,
          List.replicate n cellA ++ .markR ::
            List.replicate n (.core MStarConcreteAlphabet.work) ++ finalTail⟩)
      (.running .counterToWork
        ⟨.markL :: groupSource x.reverse x.length 0 junk, cellA,
          List.replicate (n - 1) cellA ++ .markR ::
            .core MStarConcreteAlphabet.work ::
              List.replicate (n - 1) (.core MStarConcreteAlphabet.work) ++
                finalTail⟩) := by
    simpa only [hrep, List.append_assoc] using hcounter
  have hright : List.replicate (n - 1)
        (.core MStarConcreteAlphabet.work) ++ finalTail =
      List.replicate x.length (.core MStarConcreteAlphabet.work) ++
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          rightEnd :: external) := by
    dsimp only [finalTail]
    have hnsub : n - 1 + (x.length + 1) = x.length + n := by omega
    simp only [← List.append_assoc, ← List.replicate_add]
    rw [hnsub, Nat.add_comm]
  have hseek' : Reaches
      (.running .counterToWork
        ⟨.markL :: groupSource x.reverse x.length 0 junk, cellA,
          List.replicate (n - 1) cellA ++ .markR ::
            .core MStarConcreteAlphabet.work ::
              List.replicate (n - 1) (.core MStarConcreteAlphabet.work) ++
                finalTail⟩)
      (payloadLoop [] 0 n x sourceTail
        (List.replicate (n - 1) (.core MStarConcreteAlphabet.work) ++
          finalTail)) := by
    cases x with
    | nil =>
        simpa [payloadLoop, payloadBefore, payloadPath, sourceTail,
          groupSource, groupPrefix, beforeLeftList,
          List.replicate_succ, List.append_assoc] using hseek
    | cons b bs =>
        simpa [payloadLoop, payloadBefore, payloadPath, sourceTail,
          groupSource, groupPrefix, beforeLeftList,
          List.map_reverse, List.replicate_succ,
          List.append_assoc] using hseek
  have hseek'' : Reaches
      (.running .counterToWork
        ⟨.markL :: groupSource x.reverse x.length 0 junk, cellA,
          List.replicate (n - 1) cellA ++ .markR ::
            .core MStarConcreteAlphabet.work ::
              List.replicate (n - 1) (.core MStarConcreteAlphabet.work) ++
                finalTail⟩)
      (payloadLoop [] 0 n x sourceTail
        (List.replicate x.length (.core MStarConcreteAlphabet.work) ++
          (List.replicate n (.core MStarConcreteAlphabet.work) ++
            rightEnd :: external))) := by
    simpa only [hright] using hseek'
  have hpayload' : Reaches
      (payloadLoop [] 0 n x sourceTail
        (List.replicate x.length (.core MStarConcreteAlphabet.work) ++
          (List.replicate n (.core MStarConcreteAlphabet.work) ++
            rightEnd :: external)))
      (payloadLoop x.reverse x.length n [] sourceTail
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          rightEnd :: external)) := by
    simpa only [List.append_nil, Nat.zero_add] using hpayload
  have hall := reaches_trans hseed
    (reaches_trans hbase'
      (reaches_trans hgroups'
        (reaches_trans hcounter'
          (reaches_trans hseek''
            (reaches_trans hpayload'
              (reaches_trans hat
                (reaches_trans hdone₀
                  (reaches_trans hdone₁
                    (reaches_trans hfinal₀
                      (reaches_trans hfinal₁
                        (reaches_trans hfinal₂
                          (reaches_trans hfinal₃ hready))))))))))))
  simpa only [sourceTail, n, List.reverse_reverse] using hall

theorem copier_marked_segment_eq (x : List Bool) :
    let n := iteratedGroupWidth x.length 256
    .markL :: .core MStarConcreteAlphabet.work ::
        (List.replicate n (.core MStarConcreteAlphabet.work) ++
          x.map coreBit ++
            List.replicate (n + 1) (.core MStarConcreteAlphabet.work) ++
              [.markR]) =
      MStarParserCopySpec.copiedWorkspace MStarConcreteAlphabet.zero
        MStarConcreteAlphabet.one MStarConcreteAlphabet.work x := by
  dsimp only
  rw [copier_width_eq_time_bound]
  simp [MStarParserCopySpec.copiedWorkspace,
    MStarParserCopySpec.workspaceRadius, MStarParserCopySpec.timeExponent,
    MStarParserCopySpec.bitLetter, coreBit, List.replicate_succ,
    List.append_assoc]

theorem reaches_copier_copiedWorkspace (x : List Bool)
    (junk : List ConcreteTape) :
    ∃ z : Zipper ConcreteTape,
      Reaches
        (.running .seedCell
          ⟨.markL :: groupSource x.reverse 0 x.length junk,
            .core MStarConcreteAlphabet.work,
            .core MStarConcreteAlphabet.work :: copierReserve x.length []⟩)
        (.groupReady z) ∧
      .markL :: z.focus :: z.right =
        MStarParserCopySpec.copiedWorkspace MStarConcreteAlphabet.zero
          MStarConcreteAlphabet.one MStarConcreteAlphabet.work x := by
  let n := iteratedGroupWidth x.length 256
  let z : Zipper ConcreteTape :=
    ⟨(.markL :: (doneReturnPrefix x.length).reverse) ++
        MStarParserMicrocode.sepLen ::
          (List.replicate x.length MStarParserMicrocode.lenDone ++
            MStarParserMicrocode.sepPad :: junk),
      .core MStarConcreteAlphabet.work,
      List.replicate n (.core MStarConcreteAlphabet.work) ++
        x.map coreBit ++
          List.replicate (n + 1) (.core MStarConcreteAlphabet.work) ++
            [.markR]⟩
  refine ⟨z, ?_, ?_⟩
  · simpa [z, n] using reaches_copier_complete x junk []
  · simpa [z, n] using copier_marked_segment_eq x

theorem groupReady_output_unique (r : Result) (fuel₁ fuel₂ : ℕ)
    (z₁ z₂ : Zipper ConcreteTape)
    (h₁ : run fuel₁ r = .groupReady z₁)
    (h₂ : run fuel₂ r = .groupReady z₂) : z₁ = z₂ := by
  rcases Nat.le_total fuel₁ fuel₂ with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [run_add, h₁, groupReady_absorbing] at h₂
    exact Result.groupReady.inj h₂
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [run_add, h₂, groupReady_absorbing] at h₁
    exact (Result.groupReady.inj h₁).symm

def parserCopierReserve (x : List Bool) : List ConcreteTape :=
  [.core MStarConcreteAlphabet.work, .core MStarConcreteAlphabet.work] ++
    copierReserve x.length []

def parserReadyWithReserve (x : List Bool) :
    Zipper ConcreteTape :=
  MStarParserExecution.extendRight
    (MStarConcreteAlphabet.finalZipper x.reverse) (parserCopierReserve x)

def copierSeedZipper (x : List Bool) : Zipper ConcreteTape :=
  ⟨.markL :: groupSource x.reverse 0 x.length
      (MStarConcreteAlphabet.pairingPad x.length),
    .core MStarConcreteAlphabet.work,
    .core MStarConcreteAlphabet.work :: copierReserve x.length []⟩

theorem parser_reaches_reserved_copyReady (x : List Bool) :
    MStarParserExecution.Reaches MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work
      (MStarParserExecution.extendResultRight
        (MStarParserExecution.initial MStarConcreteAlphabet.zero
          MStarConcreteAlphabet.one MStarConcreteAlphabet.work
          (ConcretePakSide.encodedWord x)) (parserCopierReserve x))
      (.copyReady (parserReadyWithReserve x)) := by
  simpa [parserReadyWithReserve] using
    MStarConcreteAlphabet.reaches_parser_encodedWord_with_tail x
      (parserCopierReserve x)

theorem reserved_copyReady_enters_copier (x : List Bool) :
    MStarCopierMicrocode.step (UState := Unit) ()
        (.inl MStarParserMicrocode.copyStart)
        (parserReadyWithReserve x).focus =
      some (MStarCopierMicrocode.copyGo .markL .seedCell .right) ∧
    MStarParserExecution.applyAction (parserReadyWithReserve x)
        (MStarCopierMicrocode.copyGo (UState := Unit)
          .markL .seedCell .right) =
      some (copierSeedZipper x) := by
  constructor
  · simp [parserReadyWithReserve, parserCopierReserve,
      MStarParserExecution.extendRight,
      MStarConcreteAlphabet.finalZipper,
      MStarCopierMicrocode.step]
  · simp [parserReadyWithReserve, parserCopierReserve, copierSeedZipper,
      MStarParserExecution.extendRight,
      MStarParserExecution.applyAction,
      MStarConcreteAlphabet.finalZipper, groupSource, groupPrefix,
      MStarCopierMicrocode.copyGo, List.append_assoc]

/-- End-to-end parser/copy refinement on the actual encoded input with the
finite tableau reserve appended: the real parser reaches its unique checked
output, the combined local table enters the copier, and the real copier
reaches the exact functional `copiedWorkspace`. -/
theorem parser_then_copier_refines_spec (x : List Bool) :
    MStarParserExecution.Reaches MStarConcreteAlphabet.zero
        MStarConcreteAlphabet.one MStarConcreteAlphabet.work
        (MStarParserExecution.extendResultRight
          (MStarParserExecution.initial MStarConcreteAlphabet.zero
            MStarConcreteAlphabet.one MStarConcreteAlphabet.work
            (ConcretePakSide.encodedWord x)) (parserCopierReserve x))
        (.copyReady (parserReadyWithReserve x)) ∧
      MStarCopierMicrocode.step (UState := Unit) ()
          (.inl MStarParserMicrocode.copyStart)
          (parserReadyWithReserve x).focus =
        some (MStarCopierMicrocode.copyGo .markL .seedCell .right) ∧
      MStarParserExecution.applyAction (parserReadyWithReserve x)
          (MStarCopierMicrocode.copyGo (UState := Unit)
            .markL .seedCell .right) = some (copierSeedZipper x) ∧
      ∃ z : Zipper ConcreteTape,
        Reaches (.running .seedCell (copierSeedZipper x)) (.groupReady z) ∧
        .markL :: z.focus :: z.right =
          MStarParserCopySpec.copiedWorkspace MStarConcreteAlphabet.zero
            MStarConcreteAlphabet.one MStarConcreteAlphabet.work x := by
  refine ⟨parser_reaches_reserved_copyReady x, ?_⟩
  rcases reserved_copyReady_enters_copier x with ⟨hstep, happly⟩
  refine ⟨hstep, happly, ?_⟩
  simpa [copierSeedZipper] using
    reaches_copier_copiedWorkspace x
      (MStarConcreteAlphabet.pairingPad x.length)

end PakFixedPolyomino.MStarCopierExecution
