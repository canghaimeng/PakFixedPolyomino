import PakFixedPolyomino.StandardBitVariableAdd

/-! Frozen interface between ripple addition and physical cleanup. The
initial parsed tape comes from the ordinary parser. The terminal tape
specifies every integer cell, including the untouched exterior. -/
namespace PakFixedPolyomino.StandardBitVariableAddRippleInterface
open StandardNondeterministicMachine StandardBitTime
open StandardBitVariableAdd (machine enc Epos addCarry endedTape)

def resultTape (x y v : List Bool) (z : Int) : Fin 32 :=
  if z = -1 then 3
  else if 0 ≤ z then
    let n := z.toNat
    if n < 2*x.length then (if n % 2 = 0 then 2 else 8)
    else if n = 2*x.length then 4
    else if n < Epos x y then 8
    else if n = Epos x y then 5
    else (inputTape machine v) (z - (Epos x y + 1 : Nat))
  else 2

def parsedStart (x y : List Bool) : Configuration 64 32 := ⟨8,0,endedTape x y⟩
def rippleFinal (x y : List Bool) : Configuration 64 32 :=
  ⟨26,(Epos x y : Int),resultTape x y (addCarry x y false)⟩

theorem resultTape_L (x y v : List Bool) : resultTape x y v (-1) = 3 := by
  simp [resultTape]

theorem resultTape_E (x y v : List Bool) : resultTape x y v (Epos x y : Int) = 5 := by
  have he : 2*x.length < Epos x y := by simp [Epos,StandardBitVariableAdd.D];omega
  simp [resultTape,show (Epos x y : Int) ≠ -1 by omega,
    show (0 : Int) ≤ (Epos x y : Int) by omega,
    show ¬ Epos x y < 2*x.length by omega,show Epos x y ≠ 2*x.length by omega]

theorem resultTape_right (x y v : List Bool) (i : Nat) :
    resultTape x y v (Epos x y + 1 + i : Nat) = inputTape machine v (i : Int) := by
  have he : 2*x.length < Epos x y := by simp [Epos,StandardBitVariableAdd.D];omega
  have hz : ((Epos x y + 1 + i : Nat) : Int) - ((Epos x y + 1 : Nat) : Int) = (i : Int) := by omega
  simp only [resultTape,if_neg (show ((Epos x y + 1 + i : Nat) : Int) ≠ -1 by omega),
    if_pos (show (0 : Int) ≤ ((Epos x y + 1 + i : Nat) : Int) by omega),Int.toNat_natCast,
    if_neg (show ¬ Epos x y + 1 + i < 2*x.length by omega),
    if_neg (show Epos x y + 1 + i ≠ 2*x.length by omega),
    if_neg (show ¬ Epos x y + 1 + i < Epos x y by omega),
    if_neg (show Epos x y + 1 + i ≠ Epos x y by omega),hz]

theorem parsed_run (x y : List Bool) :
    run machine (ticks (StandardBitVariableAdd.parseFuel x y))
      (initial machine (StandardBitMetric.pairBits x y)) = some (parsedStart x y) :=
  StandardBitVariableAdd.parse_run x y

end PakFixedPolyomino.StandardBitVariableAddRippleInterface
