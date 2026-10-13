import PakFixedPolyomino.StandardBitVariableAddRippleInterface
import PakFixedPolyomino.StandardBitNormalize

/-! Entire integer tapes for physical adder cleanup. Offsets count actual
tape cells; the only exterior marker is the left sentinel at -1. -/
namespace PakFixedPolyomino.StandardBitVariableAddTape
open StandardNondeterministicMachine StandardBitTime
open StandardBitVariableAdd (machine enc)

def blockTape (v : List Bool) (p : Nat) (z : Int) : Fin 32 :=
  if z = -1 then 3 else inputTape machine v (z-(p : Int))

theorem block_L (v : List Bool) (p : Nat) : blockTape v p (-1)=3 := by simp [blockTape]

theorem block_nat (v : List Bool) (p i : Nat) :
    blockTape v p (i : Int)=inputTape machine v ((i : Int)-(p : Int)) := by
  simp only [blockTape,if_neg (show (i : Int)≠-1 by omega)]

theorem block_at (v : List Bool) (p i : Nat) (hi : i<v.length) :
    blockTape v p (p+i : Nat)=enc v[i] := by
  rw [block_nat,show ((p+i : Nat) : Int)-(p : Int)=(i : Int) by omega]
  exact StandardBitVariableAdd.read_bit v i hi

theorem block_before (v : List Bool) (p : Nat) (z : Int) (hL : z≠-1)
    (hz : z<(p : Int)) : blockTape v p z=2 := by
  rw [blockTape,if_neg hL,inputTape_neg machine v _ (by omega)]
  rfl

theorem block_after (v : List Bool) (p : Nat) (z : Int)
    (hz : (p+v.length : Nat)≤z) : blockTape v p z=2 := by
  have hL : z≠-1 := by omega
  rw [blockTape,if_neg hL,inputTape_ge machine v _ (by omega)]
  rfl

theorem input_not_L (v : List Bool) (z : Int) : inputTape machine v z≠3 := by
  simp only [inputTape]
  split_ifs <;> try decide

theorem block_nat_not_L (v : List Bool) (p i : Nat) : blockTape v p (i : Int)≠3 := by
  rw [block_nat];exact input_not_L v _

theorem block_zero_nat (v : List Bool) (i : Nat) :
    blockTape v 0 (i : Int)=inputTape machine v (i : Int) := by rw [block_nat];simp

theorem block_zero_erase (v : List Bool) :
    Function.update (blockTape v 0) (-1) 2=inputTape machine v := by
  funext z
  by_cases hz : z=-1
  · subst z;rw [Function.update_self,inputTape_neg machine v _ (by omega)];rfl
  · rw [Function.update_of_ne hz,blockTape,if_neg hz]
    simp

theorem block_nil (p : Nat) : blockTape [] p=StandardBitVariableAdd.boundaryTape := by
  funext z
  rw [blockTape,StandardBitVariableAdd.inputTape_nil]
  rfl

end PakFixedPolyomino.StandardBitVariableAddTape
