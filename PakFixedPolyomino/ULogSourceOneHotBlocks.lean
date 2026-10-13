import PakFixedPolyomino.ULogSourceTimedNormalizer
import Mathlib.Tactic

/-!
# Fixed-width one-hot source blocks

The variable-width unary codec in `ULogSourceTimedNormalizer` is useful for
the old self-delimiting source format.  The compiler layout instead uses the
fixed-width codec below: every `Fin nt` symbol occupies exactly `nt` binary
cells.  The logical zipper is deliberately data-only; it records the block
boundary arithmetic which a later finite tape program must implement.
-/

namespace PakFixedPolyomino.ULogSourceOneHotBlocks

open ULogSourceTimedNormalizer

/-- A symbol is represented by `false` cells, one `true` cell, and the
remaining `false` cells. -/
def encodeOneHot {nt : ℕ} (a : Fin nt) : List Bool :=
  List.replicate a.val false ++ true ::
    List.replicate (nt - a.val - 1) false

/-- The position of the unique `true` bit, if there is exactly one. -/
def decodeOneHotIndex : List Bool → Option ℕ
  | [] => none
  | false :: bits => (decodeOneHotIndex bits).map Nat.succ
  | true :: bits =>
      if bits.all (fun bit => bit == false) then some 0 else none

/-- Executable exact-width decoder.  In particular, it rejects a missing,
duplicate, or out-of-range `true` bit. -/
def decodeOneHot (nt : ℕ) (bits : List Bool) : Option (Fin nt) := do
  if hlength : bits.length = nt then
    let index ← decodeOneHotIndex bits
    if hindex : index < nt then
      pure ⟨index, hindex⟩
    else none
  else none

@[simp] theorem encodeOneHot_length {nt : ℕ} (a : Fin nt) :
    (encodeOneHot a).length = nt := by
  simp [encodeOneHot]
  omega

theorem encodeOneHot_getElem? {nt : ℕ} (a : Fin nt) (i : ℕ) (hi : i < nt) :
    (encodeOneHot a)[i]? = some (if i = a.val then true else false) := by
  unfold encodeOneHot
  rw [List.getElem?_append]
  simp only [List.length_replicate]
  by_cases hleft : i < a.val
  · simp [hleft, List.getElem?_replicate, show i ≠ a.val by omega]
  · rw [if_neg hleft]
    by_cases heq : i = a.val
    · subst i
      simp
    · have hpos : 0 < i - a.val := by omega
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
      rw [hj, List.getElem?_cons_succ]
      have hjlt : j < nt - a.val - 1 := by omega
      simp [List.getElem?_replicate, hjlt, heq]

theorem encodeOneHot_getElem {nt : ℕ} (a : Fin nt) (i : ℕ) (hi : i < nt) :
    (encodeOneHot a).get ⟨i, by rw [encodeOneHot_length]; exact hi⟩ =
      if i = a.val then true else false := by
  have h := encodeOneHot_getElem? a i hi
  rw [List.getElem?_eq_getElem (by simpa using hi)] at h
  exact Option.some.inj h

@[simp] theorem false_suffix_all (n : ℕ) :
    (List.replicate n false).all (fun bit => bit == false) = true := by
  simp [List.all_replicate]

theorem decodeOneHotIndex_false_prefix (n : ℕ) (bits : List Bool) :
    decodeOneHotIndex (List.replicate n false ++ bits) =
      (decodeOneHotIndex bits).map (fun i => n + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ]
      simp [decodeOneHotIndex, ih, Option.map_map, Function.comp_def,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

@[simp] theorem decodeOneHotIndex_encodeOneHot {nt : ℕ} (a : Fin nt) :
    decodeOneHotIndex (encodeOneHot a) = some a.val := by
  rw [encodeOneHot, decodeOneHotIndex_false_prefix]
  simp [decodeOneHotIndex, List.all_replicate]

@[simp] theorem decodeOneHot_encodeOneHot {nt : ℕ} (a : Fin nt) :
    decodeOneHot nt (encodeOneHot a) = some a := by
  simp [decodeOneHot, a.isLt]

theorem encodeOneHot_injective {nt : ℕ} : Function.Injective
    (encodeOneHot : Fin nt → List Bool) := by
  intro a b hab
  have hdecoded := congrArg (decodeOneHot nt) hab
  have : some a = some b := by simpa using hdecoded
  exact Option.some.inj this

/-- Concatenate fixed-width blocks. -/
def encodeOneHotList {nt : ℕ} (symbols : List (Fin nt)) : List Bool :=
  symbols.flatMap encodeOneHot

/-- Decode the specified number of fixed-width blocks, retaining a suffix for
the enclosing source frame. -/
def decodeOneHotBlocks (nt : ℕ) : ℕ → List Bool →
    Option (List (Fin nt) × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let a ← decodeOneHot nt (bits.take nt)
      let (as, suffix) ← decodeOneHotBlocks nt count (bits.drop nt)
      pure (a :: as, suffix)

/-- Decode a complete, externally length-framed block list. -/
def decodeOneHotListExact (nt count : ℕ) (bits : List Bool) :
    Option (List (Fin nt)) := do
  let (symbols, suffix) ← decodeOneHotBlocks nt count bits
  if suffix = [] then pure symbols else none

@[simp] theorem encodeOneHotList_nil {nt : ℕ} :
    encodeOneHotList ([] : List (Fin nt)) = [] := rfl

@[simp] theorem encodeOneHotList_cons {nt : ℕ} (a : Fin nt)
    (as : List (Fin nt)) :
    encodeOneHotList (a :: as) = encodeOneHot a ++ encodeOneHotList as := by
  simp [encodeOneHotList]

@[simp] theorem encodeOneHotList_append {nt : ℕ}
    (xs ys : List (Fin nt)) :
    encodeOneHotList (xs ++ ys) = encodeOneHotList xs ++ encodeOneHotList ys := by
  simp [encodeOneHotList, List.flatMap_append]

theorem take_encodeOneHot_append {nt : ℕ} (a : Fin nt) (tail : List Bool) :
    (encodeOneHot a ++ tail).take nt = encodeOneHot a := by
  rw [List.take_append]
  simp [encodeOneHot_length]

theorem drop_encodeOneHot_append {nt : ℕ} (a : Fin nt) (tail : List Bool) :
    (encodeOneHot a ++ tail).drop nt = tail := by
  rw [List.drop_append]
  simp [encodeOneHot_length]

theorem take_encodeOneHot_list_append {nt : ℕ} (a : Fin nt)
    (symbols : List (Fin nt)) (tail : List Bool) :
    (encodeOneHot a ++ encodeOneHotList symbols ++ tail).take nt =
      encodeOneHot a := by
  simpa [List.append_assoc] using
    (take_encodeOneHot_append a (encodeOneHotList symbols ++ tail))

theorem drop_encodeOneHot_list_append {nt : ℕ} (a : Fin nt)
    (symbols : List (Fin nt)) (tail : List Bool) :
    (encodeOneHot a ++ encodeOneHotList symbols ++ tail).drop nt =
      encodeOneHotList symbols ++ tail := by
  simpa [List.append_assoc] using
    (drop_encodeOneHot_append a (encodeOneHotList symbols ++ tail))

theorem decodeOneHotBlocks_encodeOneHotList_append {nt : ℕ}
    (symbols : List (Fin nt)) (suffix : List Bool) :
    decodeOneHotBlocks nt symbols.length (encodeOneHotList symbols ++ suffix) =
      some (symbols, suffix) := by
  induction symbols with
  | nil => simp [decodeOneHotBlocks]
  | cons a as ih =>
      simp only [List.length_cons, encodeOneHotList_cons, decodeOneHotBlocks]
      rw [take_encodeOneHot_list_append, decodeOneHot_encodeOneHot,
        drop_encodeOneHot_list_append]
      simp [ih]

@[simp] theorem decodeOneHotListExact_encodeOneHotList {nt : ℕ}
    (symbols : List (Fin nt)) :
    decodeOneHotListExact nt symbols.length (encodeOneHotList symbols) =
      some symbols := by
  unfold decodeOneHotListExact
  change (do
    let result ← decodeOneHotBlocks nt symbols.length (encodeOneHotList symbols)
    if result.2 = [] then pure result.1 else none) = some symbols
  rw [show decodeOneHotBlocks nt symbols.length (encodeOneHotList symbols) =
      some (symbols, []) by simpa using
        (decodeOneHotBlocks_encodeOneHotList_append symbols [])]
  simp

@[simp] theorem encodeOneHotList_length {nt : ℕ}
    (symbols : List (Fin nt)) :
    (encodeOneHotList symbols).length = nt * symbols.length := by
  induction symbols with
  | nil => simp [encodeOneHotList]
  | cons a as ih =>
      simp [encodeOneHotList_cons, encodeOneHot_length, ih, Nat.mul_succ,
        Nat.add_comm]

theorem encodeOneHotList_injective {nt : ℕ} : Function.Injective
    (encodeOneHotList : List (Fin nt) → List Bool) := by
  intro xs ys hxy
  have hlength : xs.length = ys.length := by
    by_cases hzero : nt = 0
    · subst nt
      have empty_fin_zero : ∀ zs : List (Fin 0), zs = [] := by
        intro zs
        cases zs with
        | nil => rfl
        | cons a _ => exact Fin.elim0 a
      rw [empty_fin_zero xs, empty_fin_zero ys]
    · have hencodedLength := congrArg List.length hxy
      apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hzero)
      simpa only [encodeOneHotList_length] using hencodedLength
  have hdecoded := congrArg (decodeOneHotBlocks nt xs.length) hxy
  rw [show decodeOneHotBlocks nt xs.length (encodeOneHotList xs) =
      some (xs, []) by simpa using
        (decodeOneHotBlocks_encodeOneHotList_append xs [])] at hdecoded
  rw [show decodeOneHotBlocks nt xs.length (encodeOneHotList ys) =
      some (ys, []) by simpa [hlength] using
        (decodeOneHotBlocks_encodeOneHotList_append ys [])] at hdecoded
  exact congrArg Prod.fst (Option.some.inj hdecoded)

/-- The encoded block belonging to an indexed source symbol starts at exactly
`nt * i`; this is the basic concatenation/index contract for the compiler. -/
theorem drop_encodeOneHotList_append {nt : ℕ} (xs : List (Fin nt))
    (tail : List Bool) :
    (encodeOneHotList xs ++ tail).drop (nt * xs.length) = tail := by
  rw [List.drop_append]
  simp [encodeOneHotList_length]

/-- The block in a concatenation begins at the exact physical offset of the
prefix, and its first `nt` cells are the encoding of that symbol. -/
theorem encodeOneHotList_block {nt : ℕ} (pre suf : List (Fin nt))
    (a : Fin nt) :
    ((encodeOneHotList (pre ++ a :: suf)).drop
      (nt * pre.length)).take nt = encodeOneHot a := by
  rw [encodeOneHotList_append, drop_encodeOneHotList_append]
  exact take_encodeOneHot_append a _

/-! ## Physical binary-tape embedding -/

abbrev PhysicalTape := ULogProgram.Tape

def physicalZero : PhysicalTape := ULogProgram.bitTape false
def physicalOne : PhysicalTape := ULogProgram.bitTape true

def encodeOneHotPhysical {nt : ℕ} (symbols : List (Fin nt)) :
    List PhysicalTape :=
  (encodeOneHotList symbols).map ULogProgram.bitTape

@[simp] theorem encodeOneHotPhysical_length {nt : ℕ}
    (symbols : List (Fin nt)) :
    (encodeOneHotPhysical symbols).length = nt * symbols.length := by
  simp [encodeOneHotPhysical]

theorem encodeOneHotPhysical_symbols {nt : ℕ} (symbols : List (Fin nt))
    (cell : PhysicalTape) (hcell : cell ∈ encodeOneHotPhysical symbols) :
    cell = physicalZero ∨ cell = physicalOne := by
  simp only [encodeOneHotPhysical, List.mem_map] at hcell
  obtain ⟨bit, -, rfl⟩ := hcell
  cases bit <;> simp [physicalZero, physicalOne]

/-! ## Logical zipper layout -/

/-- `leftRev` stores the closest symbol first.  Its reversal is therefore the
physical left-to-right order before the focus block. -/
structure LogicalZipper (nt : ℕ) where
  leftRev : List (Fin nt)
  focus : Fin nt
  right : List (Fin nt)

def LogicalZipper.encode {nt : ℕ} (z : LogicalZipper nt) : List Bool :=
  encodeOneHotList z.leftRev.reverse ++ encodeOneHot z.focus ++
    encodeOneHotList z.right

/-- The physical index of the first cell of the focus block. -/
def LogicalZipper.headIndex {nt : ℕ} (z : LogicalZipper nt) : ℕ :=
  nt * z.leftRev.length

@[simp] theorem LogicalZipper.encode_head_prefix {nt : ℕ}
    (z : LogicalZipper nt) :
    (LogicalZipper.encode z).take z.headIndex =
      encodeOneHotList z.leftRev.reverse := by
  unfold LogicalZipper.encode LogicalZipper.headIndex
  rw [List.take_append]
  simp [encodeOneHotList_length]

@[simp] theorem LogicalZipper.encode_focus_block {nt : ℕ}
    (z : LogicalZipper nt) :
    ((LogicalZipper.encode z).drop z.headIndex).take nt =
      encodeOneHot z.focus := by
  unfold LogicalZipper.encode LogicalZipper.headIndex
  rw [List.drop_append]
  simp [encodeOneHotList_length]

/-- Logical right movement, written in a shape convenient for later machine
refinement. -/
def LogicalZipper.moveRight {nt : ℕ} (left : List (Fin nt))
    (focus next : Fin nt) (right : List (Fin nt)) : LogicalZipper nt :=
  ⟨focus :: left, next, right⟩

/-- Logical left movement. -/
def LogicalZipper.moveLeft {nt : ℕ} (left : List (Fin nt))
    (previous focus : Fin nt) (right : List (Fin nt)) : LogicalZipper nt :=
  ⟨left, previous, focus :: right⟩

@[simp] theorem LogicalZipper.moveRight_headIndex {nt : ℕ}
    (left : List (Fin nt)) (focus next : Fin nt) (right : List (Fin nt)) :
    (LogicalZipper.moveRight left focus next right).headIndex =
      nt + nt * left.length := by
  simp [LogicalZipper.moveRight, LogicalZipper.headIndex]
  simp [Nat.mul_succ, Nat.add_comm]

@[simp] theorem LogicalZipper.moveLeft_headIndex {nt : ℕ}
    (left : List (Fin nt)) (previous focus : Fin nt) (right : List (Fin nt)) :
    (LogicalZipper.moveLeft left previous focus right).headIndex =
      nt * left.length := rfl

theorem LogicalZipper.moveRight_headIndex_add {nt : ℕ}
    (left : List (Fin nt)) (focus next : Fin nt) (right : List (Fin nt)) :
    (LogicalZipper.moveRight left focus next right).headIndex =
      (⟨left, focus, next :: right⟩ : LogicalZipper nt).headIndex + nt := by
  simp [LogicalZipper.moveRight, LogicalZipper.headIndex, Nat.mul_succ,
    Nat.add_comm]

theorem LogicalZipper.moveLeft_headIndex_add {nt : ℕ}
    (left : List (Fin nt)) (previous focus : Fin nt) (right : List (Fin nt)) :
    (LogicalZipper.moveLeft left previous focus right).headIndex + nt =
      (⟨previous :: left, focus, right⟩ : LogicalZipper nt).headIndex := by
  simp [LogicalZipper.moveLeft, LogicalZipper.headIndex, Nat.mul_succ,
    Nat.add_comm]

theorem LogicalZipper.encode_moveRight {nt : ℕ}
    (left : List (Fin nt)) (focus next : Fin nt) (right : List (Fin nt)) :
    (LogicalZipper.moveRight left focus next right).encode =
      (⟨left, focus, next :: right⟩ : LogicalZipper nt).encode := by
  simp [LogicalZipper.encode, LogicalZipper.moveRight, List.reverse_cons,
    encodeOneHotList_cons, List.append_assoc]

theorem LogicalZipper.encode_moveLeft {nt : ℕ}
    (left : List (Fin nt)) (previous focus : Fin nt) (right : List (Fin nt)) :
    (LogicalZipper.moveLeft left previous focus right).encode =
      (⟨previous :: left, focus, right⟩ : LogicalZipper nt).encode := by
  simp [LogicalZipper.encode, LogicalZipper.moveLeft, List.reverse_cons,
    encodeOneHotList_cons, List.append_assoc]

end PakFixedPolyomino.ULogSourceOneHotBlocks
