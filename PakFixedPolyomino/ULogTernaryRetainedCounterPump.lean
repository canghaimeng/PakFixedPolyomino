import PakFixedPolyomino.ULogFiniteTapeZipperRun

/-! A ternary repair of the retained pump interface. The delimiter is an
explicit blank2 between binary counter and binary source/output. Separate
scan and return states cross it once; every rule reads/writes below3.
Execution, ALL-raw counts and physical resource instantiation are separate
obligations. The table alone does not certify those claims. -/

namespace PakFixedPolyomino.ULogTernaryRetainedCounterPump

open ULogCompiler

def program : BoundedProgram 10 3 where
  rule := fun q read slot =>
    if slot then none else
      if q = 2 then
        if read = 0 then some ⟨0, 2, .right⟩
        else if read = 1 then some ⟨2, 4, .left⟩ else none
      else if q = 5 then some ⟨read, 6, .stay⟩
      else if q = 6 then
        if read = 2 then some ⟨2, 8, .right⟩ else some ⟨read, 6, .right⟩
      else if q = 8 then
        if read = 2 then some ⟨0, 9, .left⟩ else some ⟨read, 8, .right⟩
      else if q = 9 then
        if read = 2 then some ⟨2, 7, .left⟩ else some ⟨read, 9, .left⟩
      else if q = 7 then
        if read = 2 then some ⟨2, 3, .right⟩ else some ⟨read, 7, .left⟩
      else if q = 3 then
        if read = 0 then some ⟨1, 4, .left⟩
        else if read = 1 then some ⟨0, 3, .right⟩ else some ⟨2, 0, .stay⟩
      else if q = 4 then
        if read = 2 then some ⟨2, 5, .right⟩ else some ⟨read, 4, .left⟩
      else none

theorem rule_true (q : Fin 10) (read : Fin 3) : program.rule q read true = none := rfl

def cell : Bool → Fin 3
  | false => 0
  | true => 1

def cells (bs : List Bool) : List (Fin 3) := bs.map cell

def fromCells (q : Fin 10) (left : List (Fin 3)) : List (Fin 3) → BoundedConfig 10 3
  | [] => ⟨q, left, 2, []⟩
  | a :: rest => ⟨q, left, a, rest⟩

def data (bs source : List Bool) (m : Nat) : List (Fin 3) :=
  cells bs ++ 2 :: (cells source ++ List.replicate m 0)

def initial (k : Nat) (source : List Bool) : BoundedConfig 10 3 :=
  fromCells 2 [] (List.replicate k 0 ++ 1 :: cells source)

def sourceInput (k : Nat) (source : List Bool) : List Bool :=
  List.replicate k false ++ true :: source

def input (k : Nat) (source : List Bool) : List Bool := encodeInstance program (sourceInput k source)

theorem compiled_symbols_ternary :
    ∀ r ∈ compile program, r.read < 3 ∧ r.action.write < 3 := by
  intro r hr
  have hb := compile_rule_bounded program hr
  exact ⟨hb.2.1, hb.2.2.1⟩

end PakFixedPolyomino.ULogTernaryRetainedCounterPump
