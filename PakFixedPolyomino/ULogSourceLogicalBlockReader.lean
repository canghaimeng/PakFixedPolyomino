import PakFixedPolyomino.ULogSourceOneHotReader
import Mathlib.Tactic

/-!
# Finite reader for logical fixed-width source blocks

A logical block is either a binary one-hot word or a full physical blank word.
The latter denotes a designated logical blank.  Crucially, a blank is not a
binary zero: the finite control remembers which alphabet it entered, so a
mixed bit/blank word is rejected at its first change of alphabet.
-/

namespace PakFixedPolyomino.ULogSourceLogicalBlockReader

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics
open ULogSourceOneHotBlocks

abbrev Tape := Fin 3
abbrev zero : Tape := ULogSourceOneHotReader.zero
abbrev one : Tape := ULogSourceOneHotReader.one
abbrev blank : Tape := ULogSourceOneHotReader.blank
abbrev tapeOfBit : Bool → Tape := ULogSourceOneHotReader.tapeOfBit

variable {nt : ℕ}

/-- Which physical alphabet has appeared in the prefix already scanned. -/
inductive ScanMode (nt : ℕ) where
  | fresh
  | bits : Option (Fin nt) → ScanMode nt
  | blanks
  deriving DecidableEq, Fintype, Repr

/-- The finite control additionally stores the logical blank chosen for this
reader instance. -/
inductive State (nt : ℕ) where
  | scan : Fin nt → ScanMode nt → State nt
  | done : Fin nt → State nt
  | reject : State nt
  deriving DecidableEq, Fintype, Repr

/-- The next scan state, or the terminal result after the final cell. -/
def advance (logicalBlank : Fin nt) (i : Fin nt) (mode : ScanMode nt) : State nt :=
  if hlast : i.1 + 1 = nt then
    match mode with
    | .bits (some a) => .done a
    | .blanks => .done logicalBlank
    | _ => .reject
  else
    .scan ⟨i.1 + 1, by omega⟩ mode

/-- Literal deterministic source-cell action.  A bit after a blank, or a
blank after a bit, rejects immediately. -/
def readerAction (logicalBlank : Fin nt) : State nt → Tape → Action (State nt) Tape
  | .scan i .fresh, x =>
      if x = blank then ⟨x, advance logicalBlank i .blanks, .right⟩
      else if x = zero then ⟨x, advance logicalBlank i (.bits none), .right⟩
      else if x = one then ⟨x, advance logicalBlank i (.bits (some i)), .right⟩
      else ⟨x, .reject, .stay⟩
  | .scan i (.bits seen), x =>
      if x = zero then ⟨x, advance logicalBlank i (.bits seen), .right⟩
      else if x = one then
        match seen with
        | none => ⟨x, advance logicalBlank i (.bits (some i)), .right⟩
        | some _ => ⟨x, .reject, .stay⟩
      else ⟨x, .reject, .stay⟩
  | .scan i .blanks, x =>
      if x = blank then ⟨x, advance logicalBlank i .blanks, .right⟩
      else ⟨x, .reject, .stay⟩
  | .done a, x => ⟨x, .done a, .stay⟩
  | .reject, x => ⟨x, .reject, .stay⟩

def readerStep (logicalBlank : Fin nt) (q : State nt) (x : Tape) :
    Option (Action (State nt) Tape) := some (readerAction logicalBlank q x)

/-- A second physical one is rejected at the exact cell where it occurs. -/
@[simp] theorem readerAction_second_one (logicalBlank : Fin nt) (i seen : Fin nt) :
    (readerAction logicalBlank (.scan i (.bits (some seen))) one).target =
      .reject := by
  simp [readerAction]

/-- Reaching the final cell after only zeros rejects: a binary block is not
silently allowed to decode as the logical blank. -/
@[simp] theorem advance_last_without_one (logicalBlank : Fin nt) (i : Fin nt)
    (hlast : i.1 + 1 = nt) :
    advance logicalBlank i (.bits none) = .reject := by
  simp [advance, hlast]

/-- The transition at the first alphabet change is rejecting. -/
@[simp] theorem readerAction_blank_after_bit (logicalBlank : Fin nt) (i : Fin nt)
    (seen : Option (Fin nt)) :
    (readerAction logicalBlank (.scan i (.bits seen)) blank).target = .reject := by
  have hzero : blank ≠ zero := by decide
  have hone : blank ≠ one := by decide
  simp [readerAction, hzero, hone]

@[simp] theorem readerAction_bit_after_blank (logicalBlank : Fin nt) (i : Fin nt)
    (x : Tape) (hx : x = zero ∨ x = one) :
    (readerAction logicalBlank (.scan i .blanks) x).target = .reject := by
  rcases hx with rfl | rfl
  · have hzero : zero ≠ blank := by decide
    simp [readerAction, hzero]
  · have hone : one ≠ blank := by decide
    simp [readerAction, hone]

@[simp] theorem readerAction_first_blank (logicalBlank : Fin nt) (i : Fin nt) :
    (readerAction logicalBlank (.scan i .fresh) blank).target =
      advance logicalBlank i .blanks := by
  simp [readerAction]

@[simp] theorem readerAction_blank_continuation (logicalBlank : Fin nt) (i : Fin nt) :
    (readerAction logicalBlank (.scan i .blanks) blank).target =
      advance logicalBlank i .blanks := by
  simp [readerAction]

@[simp] theorem blank_final_target (logicalBlank : Fin nt) (i : Fin nt)
    (hlast : i.1 + 1 = nt) :
    (readerAction logicalBlank (.scan i .blanks) blank).target = .done logicalBlank := by
  simp [readerAction, advance, hlast]

def program (logicalBlank : Fin nt) : Program (State nt) Tape :=
  deterministic (readerStep logicalBlank)

def movable : Tape → Bool := fun _ => true

@[simp] theorem reader_slot_one_empty (logicalBlank : Fin nt) (q : State nt)
    (x : Tape) : (program logicalBlank).rule q x 1 = none := by rfl

@[simp] theorem reader_slot_zero (logicalBlank : Fin nt) (q : State nt)
    (x : Tape) : (program logicalBlank).rule q x 0 =
      some (readerAction logicalBlank q x) := by rfl

def literalArrow (logicalBlank : Fin nt) (q : State nt) (x : Tape) :
    Arrow (program logicalBlank) :=
  ⟨((q, x), 0), by simp [program, deterministic, readerStep]⟩

@[simp] theorem actionOf_literalArrow (logicalBlank : Fin nt) (q : State nt)
    (x : Tape) : actionOf (program logicalBlank) (literalArrow logicalBlank q x) =
      readerAction logicalBlank q x := by
  simp [literalArrow, actionOf, program, deterministic, readerStep]

theorem occupied_slot_unique (logicalBlank : Fin nt) (q : State nt) (x : Tape)
    (a : Arrow (program logicalBlank))
    (hsource : (transition (program logicalBlank) a).sourceState = q)
    (hread : (transition (program logicalBlank) a).read = x) :
    a = literalArrow logicalBlank q x := by
  rcases a with ⟨⟨⟨q', x'⟩, slot⟩, hoccupied⟩
  change q' = q at hsource
  change x' = x at hread
  subst q'
  subst x'
  fin_cases slot
  · rfl
  · simp [program, deterministic] at hoccupied

def nextConfig (logicalBlank : Fin nt) (c : Config (State nt) Tape) :
    Config (State nt) Tape :=
  let x := c.tape c.head
  let act := readerAction logicalBlank c.state x
  { state := act.target
    head := moveHead act.move c.head
    tape := writtenTape c act.write }

/-- Every nonrejecting reader action copies its currently read physical
letter.  This elementary update lemma is the tape component of the terminal
reader invariants. -/
theorem writtenTape_same_cell (c : Config (State nt) Tape) :
    writtenTape c (c.tape c.head) = c.tape := by
  funext z
  by_cases hz : z = c.head
  · subst z
    simp [writtenTape]
  · simp [writtenTape, Function.update_of_ne hz]

theorem writtenTape_of_current (q : State nt) (tape : Int → Tape)
    (head : Int) (x : Tape) (hread : tape head = x) :
    writtenTape ({ state := q, head := head, tape := tape } :
      Config (State nt) Tape) x = tape := by
  rw [← hread]
  exact writtenTape_same_cell _

theorem config_ext {a b : Config (State nt) Tape}
    (hstate : a.state = b.state) (hhead : a.head = b.head)
    (htape : a.tape = b.tape) : a = b := by
  cases a
  cases b
  simp_all

def initialConfig (logicalBlank : Fin nt) (hnt : 0 < nt) (tape : Int → Tape)
    (head : Int := 0) : Config (State nt) Tape :=
  { state := .scan ⟨0, hnt⟩ .fresh, head := head, tape := tape }

/-- Control expected after `n` cells of a physical blank block.  The first
cell is distinguished because it is where the reader commits from `fresh` to
the blank alphabet. -/
def blankStage (logicalBlank : Fin nt) (hnt : 0 < nt) (n : ℕ) : State nt :=
  if hzero : n = 0 then .scan ⟨0, by omega⟩ .fresh
  else if hscan : n < nt then .scan ⟨n, hscan⟩ .blanks
  else .done logicalBlank

@[simp] theorem blankStage_zero (logicalBlank : Fin nt) (hnt : 0 < nt) :
    blankStage logicalBlank hnt 0 = .scan ⟨0, hnt⟩ .fresh := by
  simp [blankStage]

theorem blankStage_pos (logicalBlank : Fin nt) (hnt : 0 < nt) (n : ℕ)
    (hzero : 0 < n) (hn : n < nt) :
    blankStage logicalBlank hnt n = .scan ⟨n, hn⟩ .blanks := by
  simp [blankStage, Nat.ne_of_gt hzero, hn]

@[simp] theorem blankStage_terminal (logicalBlank : Fin nt) (hnt : 0 < nt) :
    blankStage logicalBlank hnt nt = .done logicalBlank := by
  simp [blankStage, show nt ≠ 0 by omega]

def blankExpected (logicalBlank : Fin nt) (hnt : 0 < nt)
    (tape : Int → Tape) (head : Int) (n : ℕ) : Config (State nt) Tape :=
  { state := blankStage logicalBlank hnt n
    head := head + n
    tape := tape }

theorem blank_next_expected (logicalBlank : Fin nt) (hnt : 0 < nt)
    (tape : Int → Tape) (head : Int) (n : ℕ) (hn : n < nt)
    (hblank : tape (head + n) = blank) :
    nextConfig logicalBlank (blankExpected logicalBlank hnt tape head n) =
      blankExpected logicalBlank hnt tape head (n + 1) := by
  by_cases hzero : n = 0
  · subst n
    rw [show blankExpected logicalBlank hnt tape head 0 =
      { state := .scan ⟨0, hnt⟩ .fresh, head := head, tape := tape } by
        simp [blankExpected, blankStage_zero]]
    have hcell : tape head = blank := by simpa using hblank
    have hwrite : writtenTape
        ({ state := .scan ⟨0, hnt⟩ .fresh, head := head, tape := tape } : Config (State nt) Tape)
        blank = tape := by
      rw [← hcell]
      exact writtenTape_same_cell _
    unfold nextConfig
    dsimp
    rw [hcell]
    simp [readerAction, advance, hwrite, blankExpected, blankStage, moveHead]
    by_cases hlast : 1 = nt <;> simp [hlast, hnt]
    all_goals omega
  · have hpos : 0 < n := Nat.pos_of_ne_zero hzero
    change nextConfig logicalBlank
      { state := blankStage logicalBlank hnt n, head := head + n, tape := tape } = _
    rw [blankStage_pos logicalBlank hnt n hpos hn]
    have hwrite : writtenTape
        ({ state := .scan ⟨n, hn⟩ .blanks, head := head + n, tape := tape } : Config (State nt) Tape)
        blank = tape := by
      rw [← hblank]
      exact writtenTape_same_cell _
    unfold nextConfig
    dsimp
    rw [hblank]
    simp [readerAction, hwrite, blankExpected, moveHead]
    by_cases hlast : n + 1 = nt
    · simp [advance, blankStage, hzero, hn, hlast] <;> omega
    · have hnext : n + 1 < nt := by omega
      simp [advance, blankStage, hzero, hn, hlast, hnext] <;> omega

theorem iterate_blank_expected (logicalBlank : Fin nt) (hnt : 0 < nt)
    (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) = blank)
    (n : ℕ) (hn : n ≤ nt) :
    (nextConfig logicalBlank)^[n] (initialConfig logicalBlank hnt tape head) =
      blankExpected logicalBlank hnt tape head n := by
  induction n with
  | zero => simp [initialConfig, blankExpected, blankStage_zero]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact blank_next_expected logicalBlank hnt tape head n (by omega) (hblank n (by omega))

/-- Operational all-blank terminal theorem: the literal reader reaches the
designated logical blank after exactly one fixed-width block, advancing the
head by that width and preserving the tape. -/
theorem blank_operational_terminal (logicalBlank : Fin nt) (hnt : 0 < nt)
    (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) = blank) :
    (nextConfig logicalBlank)^[nt] (initialConfig logicalBlank hnt tape head) =
      { state := .done logicalBlank, head := head + nt, tape := tape } := by
  rw [iterate_blank_expected logicalBlank hnt tape head hblank nt le_rfl]
  simp [blankExpected, blankStage_terminal]

/-- Control expected after a one-hot prefix.  Before and including the
target offset no one has yet been consumed; after it the remembered one is
exactly `a`. -/
def oneHotStage (a : Fin nt) (hnt : 0 < nt) (n : ℕ) : State nt :=
  if hzero : n = 0 then .scan ⟨0, hnt⟩ .fresh
  else if hbefore : n ≤ a.1 then .scan ⟨n, by omega⟩ (.bits none)
  else if hscan : n < nt then .scan ⟨n, hscan⟩ (.bits (some a))
  else .done a

@[simp] theorem oneHotStage_zero (a : Fin nt) (hnt : 0 < nt) :
    oneHotStage a hnt 0 = .scan ⟨0, hnt⟩ .fresh := by
  simp [oneHotStage]

@[simp] theorem oneHotStage_terminal (a : Fin nt) (hnt : 0 < nt) :
    oneHotStage a hnt nt = .done a := by
  simp [oneHotStage, show nt ≠ 0 by omega, show ¬nt ≤ a.1 by omega]

def oneHotExpected (a : Fin nt) (hnt : 0 < nt)
    (tape : Int → Tape) (head : Int) (n : ℕ) : Config (State nt) Tape :=
  { state := oneHotStage a hnt n
    head := head + n
    tape := tape }

/-- Pointwise physical form of a fixed-width one-hot block.  This avoids
silently identifying the physical blank with binary zero in the operational
invariant. -/
def IsOneHotAt (a : Fin nt) (tape : Int → Tape) (head : Int) : Prop :=
  ∀ i : ℕ, i < nt → tape (head + i) = if i = a.1 then one else zero

theorem oneHotStage_before (a : Fin nt) (hnt : 0 < nt) (n : ℕ)
    (hpos : 0 < n) (hbefore : n ≤ a.1) :
    oneHotStage a hnt n = .scan ⟨n, by omega⟩ (.bits none) := by
  simp [oneHotStage, Nat.ne_of_gt hpos, hbefore]

theorem oneHotStage_after (a : Fin nt) (hnt : 0 < nt) (n : ℕ)
    (ha : a.1 < n) (hn : n < nt) :
    oneHotStage a hnt n = .scan ⟨n, hn⟩ (.bits (some a)) := by
  simp [oneHotStage, show n ≠ 0 by omega, show ¬n ≤ a.1 by omega, hn]

/-- One literal one-hot cell advances the corresponding operational prefix
state, preserving the physical tape. -/
theorem oneHot_next_expected (logicalBlank a : Fin nt) (hnt : 0 < nt)
    (tape : Int → Tape) (head : Int) (n : ℕ) (hn : n < nt)
    (hone : IsOneHotAt a tape head) :
    nextConfig logicalBlank (oneHotExpected a hnt tape head n) =
      oneHotExpected a hnt tape head (n + 1) := by
  have hcell := hone n hn
  have honeBlank : one ≠ blank := by decide
  have honeZero : one ≠ zero := by decide
  have hzeroBlank : zero ≠ blank := by decide
  by_cases hzero : n = 0
  · subst n
    rw [show oneHotExpected a hnt tape head 0 =
      { state := .scan ⟨0, hnt⟩ .fresh, head := head, tape := tape } by
        simp [oneHotExpected, oneHotStage_zero]]
    by_cases ha0 : 0 = a.1
    · have ha : a = ⟨0, hnt⟩ := Fin.ext ha0.symm
      subst a
      have hread : tape head = one := by
        rw [if_pos ha0] at hcell
        simpa using hcell
      have hwrite := writtenTape_of_current
        (.scan ⟨0, hnt⟩ .fresh) tape head one hread
      unfold nextConfig
      dsimp
      rw [hread]
      by_cases hlast : 1 = nt
      · have hlastInt : (1 : Int) = nt := by exact_mod_cast hlast
        have hnt0 : nt ≠ 0 := by omega
        apply config_ext <;>
          simp [readerAction, advance, hwrite, oneHotExpected, oneHotStage,
            hlast, moveHead, honeBlank, honeZero, hlastInt, hnt0] <;> omega
      · have hnext : 1 < nt := by omega
        apply config_ext <;>
          simp [readerAction, advance, hwrite, oneHotExpected, oneHotStage,
            hlast, hnext, moveHead, honeBlank, honeZero] <;> omega
    · have hread : tape head = zero := by
        rw [if_neg ha0] at hcell
        simpa using hcell
      have haPos : 0 < a.1 := Nat.pos_of_ne_zero (fun h => ha0 h.symm)
      have hnext : 1 < nt := by omega
      have hwrite := writtenTape_of_current
        (.scan ⟨0, hnt⟩ .fresh) tape head zero hread
      unfold nextConfig
      dsimp
      rw [hread]
      apply config_ext <;>
        simp [readerAction, advance, hwrite, oneHotExpected, oneHotStage,
          hnext, haPos, moveHead, hzeroBlank, show 1 ≤ a.1 by omega,
          show 1 ≠ nt by omega] <;> omega
  · have hpos : 0 < n := Nat.pos_of_ne_zero hzero
    by_cases hbefore : n ≤ a.1
    · rw [show oneHotExpected a hnt tape head n =
        { state := .scan ⟨n, hn⟩ (.bits none), head := head + n,
          tape := tape } by
            simp [oneHotExpected, oneHotStage_before a hnt n hpos hbefore]]
      by_cases heq : n = a.1
      · have hread : tape (head + n) = one := by
          rw [if_pos heq] at hcell
          exact hcell
        have hwrite := writtenTape_of_current
          (.scan ⟨n, hn⟩ (.bits none)) tape (head + n) one hread
        have hafin : (⟨n, hn⟩ : Fin nt) = a := Fin.ext heq
        rw [hafin] at hwrite
        unfold nextConfig
        dsimp
        rw [hread]
        by_cases hlast : n + 1 = nt
        · have hlastInt : (n : Int) + 1 = nt := by exact_mod_cast hlast
          have hnt0 : nt ≠ 0 := by omega
          have hlastA : a.1 + 1 = nt := by omega
          apply config_ext
          · simp [readerAction, advance, oneHotExpected, oneHotStage,
              hzero, heq, hlast, hafin, honeBlank, honeZero, hnt0,
              hlastA] <;> omega
          · simp [readerAction, honeZero, moveHead, oneHotExpected]
            omega
          · simpa [readerAction, honeZero, writtenTape, oneHotExpected,
              heq] using hwrite
        · have hnext : n + 1 < nt := by omega
          have hnextA : a.1 + 1 < nt := by omega
          have hnotlastA : a.1 + 1 ≠ nt := by omega
          apply config_ext
          · simp [readerAction, advance, oneHotExpected, oneHotStage,
              hzero, heq, hlast, hnext, hafin, honeBlank, honeZero,
              hnextA, hnotlastA]
          · simp [readerAction, honeZero, moveHead, oneHotExpected]
            omega
          · simpa [readerAction, honeZero, writtenTape, oneHotExpected,
              heq] using hwrite
      · have hlt : n < a.1 := by omega
        have hread : tape (head + n) = zero := by
          rw [if_neg heq] at hcell
          exact hcell
        have hnext : n + 1 ≤ a.1 := by omega
        have hwrite := writtenTape_of_current
          (.scan ⟨n, hn⟩ (.bits none)) tape (head + n) zero hread
        unfold nextConfig
        dsimp
        rw [hread]
        have hnotlast : n + 1 ≠ nt := by omega
        apply config_ext <;>
          simp [readerAction, advance, hwrite, oneHotExpected, oneHotStage,
            hzero, heq, hnext, hnotlast, moveHead, hzeroBlank] <;> omega
    · have ha : a.1 < n := by omega
      rw [show oneHotExpected a hnt tape head n =
        { state := .scan ⟨n, hn⟩ (.bits (some a)), head := head + n,
          tape := tape } by
            simp [oneHotExpected, oneHotStage_after a hnt n ha hn]]
      have hne : n ≠ a.1 := by omega
      have hread : tape (head + n) = zero := by
        rw [if_neg hne] at hcell
        exact hcell
      have hwrite := writtenTape_of_current
        (.scan ⟨n, hn⟩ (.bits (some a))) tape (head + n) zero hread
      unfold nextConfig
      dsimp
      rw [hread]
      by_cases hlast : n + 1 = nt
      · have hlastInt : (n : Int) + 1 = nt := by exact_mod_cast hlast
        have hnt0 : nt ≠ 0 := by omega
        apply config_ext <;>
          simp [readerAction, advance, hwrite, oneHotExpected, oneHotStage,
            hzero, hbefore, hlast, moveHead, hzeroBlank, hlastInt, hnt0,
            show ¬ nt ≤ a.1 by omega] <;> omega
      · have hnext : n + 1 < nt := by omega
        apply config_ext <;>
          simp [readerAction, advance, hwrite, oneHotExpected, oneHotStage,
            hzero, hbefore, hlast, hnext, moveHead, hzeroBlank,
            show a.1 ≤ n by omega] <;> omega

theorem iterate_oneHot_expected (logicalBlank a : Fin nt) (hnt : 0 < nt)
    (tape : Int → Tape) (head : Int) (hone : IsOneHotAt a tape head)
    (n : ℕ) (hn : n ≤ nt) :
    (nextConfig logicalBlank)^[n] (initialConfig logicalBlank hnt tape head) =
      oneHotExpected a hnt tape head n := by
  induction n with
  | zero => simp [initialConfig, oneHotExpected, oneHotStage_zero]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact oneHot_next_expected logicalBlank a hnt tape head n (by omega) hone

/-- Operational one-hot terminal theorem used by the integrated physical
source-step compiler. -/
theorem oneHot_operational_terminal (logicalBlank a : Fin nt) (hnt : 0 < nt)
    (tape : Int → Tape) (head : Int) (hone : IsOneHotAt a tape head) :
    (nextConfig logicalBlank)^[nt] (initialConfig logicalBlank hnt tape head) =
      { state := .done a, head := head + nt, tape := tape } := by
  rw [iterate_oneHot_expected logicalBlank a hnt tape head hone nt le_rfl]
  simp [oneHotExpected, oneHotStage_terminal]


def literalArrows (logicalBlank : Fin nt) : Config (State nt) Tape → ℕ →
    List (Arrow (program logicalBlank))
  | _, 0 => []
  | c, n + 1 => literalArrow logicalBlank c.state (c.tape c.head) ::
      literalArrows logicalBlank (nextConfig logicalBlank c) n

@[simp] theorem literalArrows_length (logicalBlank : Fin nt)
    (c : Config (State nt) Tape) (n : ℕ) :
    (literalArrows logicalBlank c n).length = n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp [literalArrows, ih]

theorem literalArrow_step (logicalBlank : Fin nt) (c : Config (State nt) Tape) :
    step (program logicalBlank) movable c
      (literalArrow logicalBlank c.state (c.tape c.head)) =
      some (nextConfig logicalBlank c) := by
  simp [FiniteOneTapeSemantics.step, literalArrow, actionOf, program,
    deterministic, readerStep, transition, nextConfig, movable, writtenTape,
    moveHead]

/-- Exact labelled execution for any number of ticks. -/
theorem literal_exact_run (logicalBlank : Fin nt) (c : Config (State nt) Tape)
    (n : ℕ) :
    run (program logicalBlank) movable (literalArrows logicalBlank c n) c =
      some ((nextConfig logicalBlank)^[n] c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      simp only [literalArrows, run_cons, literalArrow_step]
      simpa using ih (nextConfig logicalBlank c)

/-- Physical cells of one logical source block. -/
def blockCells (tape : Int → Tape) (head : Int) (nt : ℕ) : List Tape :=
  List.ofFn fun i : Fin nt => tape (head + i.1)

/-- Logical decoding: either the designated all-blank word or the ordinary
one-hot binary word. -/
def decodeLogicalBlock (logicalBlank : Fin nt) (cells : List Tape) : Option (Fin nt) :=
  if cells = List.replicate nt blank then some logicalBlank
  else ULogSourceOneHotReader.readResult nt cells

@[simp] theorem decodeLogicalBlock_blank (logicalBlank : Fin nt) :
    decodeLogicalBlock logicalBlank (List.replicate nt blank) = some logicalBlank := by
  simp [decodeLogicalBlock]

@[simp] theorem decodeLogicalBlock_oneHot (logicalBlank a : Fin nt) :
    decodeLogicalBlock logicalBlank (ULogSourceOneHotReader.oneHotCells a) = some a := by
  have hnotblank : ULogSourceOneHotReader.oneHotCells a ≠ List.replicate nt blank := by
    intro h
    have hmem :
        (ULogSourceOneHotReader.oneHotCells a).get ⟨a.val, by
          simpa [ULogSourceOneHotReader.oneHotCells] using a.isLt⟩ =
          (List.replicate nt blank).get ⟨a.val, by simpa using a.isLt⟩ := by
      simpa [h]
    simp [ULogSourceOneHotReader.oneHotCells, encodeOneHot] at hmem
    have hneq : tapeOfBit true ≠ blank := by decide
    exact hneq hmem
  simp [decodeLogicalBlock, hnotblank,
    ULogSourceOneHotReader.readResult_oneHotCells]

/-- Any non-all-blank word containing a physical blank is rejected.  This is
the formal mixed-alphabet barrier. -/
theorem decodeLogicalBlock_rejects_mixed (logicalBlank : Fin nt)
    (pre suf : List Tape)
    (hnotblank : pre ++ blank :: suf ≠ List.replicate nt blank) :
    decodeLogicalBlock logicalBlank (pre ++ blank :: suf) = none := by
  simp [decodeLogicalBlock, hnotblank,
    ULogSourceOneHotReader.readResult_rejects_blank]

/-- The unique literal successful-path statement: no other list of occupied
arrows of the prescribed length can run from a given configuration. -/
theorem successful_run_unique (logicalBlank : Fin nt) (c : Config (State nt) Tape)
    (n : ℕ) (as : List (Arrow (program logicalBlank)))
    (out : Config (State nt) Tape) (hlen : as.length = n)
    (hrun : run (program logicalBlank) movable as c = some out) :
    as = literalArrows logicalBlank c n ∧
      out = ((nextConfig logicalBlank)^[n] c) := by
  induction n generalizing c as out with
  | zero =>
      have has : as = [] := List.eq_nil_of_length_eq_zero hlen
      subst as
      simp at hrun
      subst out
      simp [literalArrows]
  | succ n ih =>
      cases as with
      | nil => simp at hlen
      | cons arrow tail =>
          simp only [List.length_cons] at hlen
          simp only [run_cons] at hrun
          cases hstep : step (program logicalBlank) movable c arrow with
          | none => simp [hstep] at hrun
          | some c' =>
              rw [hstep] at hrun
              have hsource := step_some_forces_source (program logicalBlank)
                movable c c' arrow hstep
              have harrow : arrow = literalArrow logicalBlank c.state (c.tape c.head) :=
                occupied_slot_unique logicalBlank c.state (c.tape c.head) arrow
                  hsource.1.symm hsource.2.symm
              subst arrow
              rw [literalArrow_step] at hstep
              have hc' : c' = nextConfig logicalBlank c := Option.some.inj hstep.symm
              subst c'
              have htailLength : tail.length = n := by omega
              obtain ⟨htail, hout⟩ := ih (nextConfig logicalBlank c) tail out
                htailLength hrun
              constructor
              · simp [literalArrows, htail]
              · rw [hout, Function.iterate_succ_apply]

/-- Exact one-hot read: `nt` literal steps, the data-level output, and the
unique labelled path are all fixed. -/
theorem oneHot_exact_run_output (logicalBlank a : Fin nt) (hnt : 0 < nt)
    (tape : Int → Tape) (head : Int)
    (hblock : blockCells tape head nt = ULogSourceOneHotReader.oneHotCells a) :
    run (program logicalBlank) movable
        (literalArrows logicalBlank (initialConfig logicalBlank hnt tape head) nt)
        (initialConfig logicalBlank hnt tape head) =
      some ((nextConfig logicalBlank)^[nt] (initialConfig logicalBlank hnt tape head)) ∧
      decodeLogicalBlock logicalBlank (blockCells tape head nt) = some a := by
  constructor
  · exact literal_exact_run logicalBlank (initialConfig logicalBlank hnt tape head) nt
  · rw [hblock]
    exact decodeLogicalBlock_oneHot logicalBlank a

/-- Exact all-blank read, with the same fixed `nt`-step literal path. -/
theorem blank_exact_run_output (logicalBlank : Fin nt) (hnt : 0 < nt)
    (tape : Int → Tape) (head : Int)
    (hblock : blockCells tape head nt = List.replicate nt blank) :
    run (program logicalBlank) movable
        (literalArrows logicalBlank (initialConfig logicalBlank hnt tape head) nt)
        (initialConfig logicalBlank hnt tape head) =
      some ((nextConfig logicalBlank)^[nt] (initialConfig logicalBlank hnt tape head)) ∧
      decodeLogicalBlock logicalBlank (blockCells tape head nt) = some logicalBlank := by
  constructor
  · exact literal_exact_run logicalBlank (initialConfig logicalBlank hnt tape head) nt
  · rw [hblock]
    exact decodeLogicalBlock_blank logicalBlank

end PakFixedPolyomino.ULogSourceLogicalBlockReader
