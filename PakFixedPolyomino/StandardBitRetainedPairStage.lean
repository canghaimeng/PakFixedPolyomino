import PakFixedPolyomino.StandardBitProtectedCleanup
import PakFixedPolyomino.StandardBitMetric

/-! A finite physical stage for pairing a computed word with a retained answer.
The raw track contains pairBits x y and the work track contains the counter u.
A separate finite scratch track holds the output, so expansion never overwrites
the literal answer. Operational phases and their bounds are proved separately. -/
namespace PakFixedPolyomino.StandardBitRetainedPairStage
open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open StandardMachineProtectedTrack (pack unpack)
open StandardBitProtectedCleanup (rawTape rawBit)
open FiniteOneTapeSemantics (moveHead writtenTape)

variable {ns nt : Nat}
abbrev Alphabet (nt : Nat) := Fin (4*(2*(4*nt)))

def joint (r : Fin 4) (w : Fin nt) (p : Fin 2) (o : Fin 4) : Alphabet nt :=
  pack o (pack p (pack r w))
def raw (s : Alphabet nt) : Fin 4 := (unpack (unpack (unpack s).2).2).1
def work (s : Alphabet nt) : Fin nt := (unpack (unpack (unpack s).2).2).2
def seen (s : Alphabet nt) : Fin 2 := (unpack (unpack s).2).1
def output (s : Alphabet nt) : Fin 4 := (unpack s).1

theorem raw_joint (r : Fin 4) (w : Fin nt) (p : Fin 2) (o : Fin 4) :
    raw (joint r w p o)=r := by simp [raw,joint]
theorem work_joint (r : Fin 4) (w : Fin nt) (p : Fin 2) (o : Fin 4) :
    work (joint r w p o)=w := by simp [work,joint]
theorem seen_joint (r : Fin 4) (w : Fin nt) (p : Fin 2) (o : Fin 4) :
    seen (joint r w p o)=p := by simp [seen,joint]
theorem output_joint (r : Fin 4) (w : Fin nt) (p : Fin 2) (o : Fin 4) :
    output (joint r w p o)=o := by simp [output,joint]
theorem joint_parts (s : Alphabet nt) : joint (raw s) (work s) (seen s) (output s)=s := by
  simp [joint,raw,work,seen,output,StandardMachineProtectedTrack.pack_unpack]
theorem joint_work_injective {r : Fin 4} {a b : Fin nt} {p : Fin 2} {o : Fin 4}
    (h : joint r a p o=joint r b p o) : a=b := by
  simpa only [work_joint] using congrArg work h

def setRaw (s : Alphabet nt) (r : Fin 4) : Alphabet nt :=
  joint r (work s) (seen s) (output s)
def setSeen (s : Alphabet nt) (p : Fin 2) : Alphabet nt :=
  joint (raw s) (work s) p (output s)
def setOutput (s : Alphabet nt) (o : Fin 4) : Alphabet nt :=
  joint (raw s) (work s) (seen s) o
def blank (M : DeterministicMachine ns nt) : Alphabet nt := joint 2 M.blank 0 2
def cleanCell (M : DeterministicMachine ns nt) (s : Alphabet nt) : Alphabet nt :=
  joint 2 (if output s=0 then M.zero else if output s=1 then M.one else M.blank) 0 2

def machine (M : DeterministicMachine ns nt) : DeterministicMachine 30 (4*(2*(4*nt))) where
  rule := fun q s _ =>
    if q=2 then some ⟨s,3,.left⟩
    else if q=3 then some ⟨joint 2 M.blank 0 3,4,.right⟩
    else if q=4 then
      if seen s=1 then some ⟨s,4,.right⟩
      else if work s=M.blank then some ⟨s,13,.left⟩
      else if work s=M.zero then some ⟨setSeen s 1,5,.left⟩
      else if work s=M.one then some ⟨setSeen s 1,8,.left⟩
      else none
    else if q=5 then
      if output s=3 then some ⟨s,6,.right⟩ else some ⟨s,5,.left⟩
    else if q=8 then
      if output s=3 then some ⟨s,9,.right⟩ else some ⟨s,8,.left⟩
    else if q=6 then
      if output s=2 then some ⟨setOutput s 1,7,.right⟩ else some ⟨s,6,.right⟩
    else if q=9 then
      if output s=2 then some ⟨setOutput s 1,10,.right⟩ else some ⟨s,9,.right⟩
    else if q=7 then some ⟨setOutput s 0,12,.left⟩
    else if q=10 then some ⟨setOutput s 1,12,.left⟩
    else if q=12 then
      if output s=3 then some ⟨s,4,.right⟩ else some ⟨s,12,.left⟩
    else if q=13 then
      if output s=3 then some ⟨s,14,.right⟩ else some ⟨s,13,.left⟩
    else if q=14 then
      if output s=2 then some ⟨setOutput s 0,15,.left⟩ else some ⟨s,14,.right⟩
    else if q=15 then
      if output s=3 then some ⟨s,16,.right⟩ else some ⟨s,15,.left⟩
    else if q=16 then
      if raw s=1 then some ⟨s,17,.right⟩
      else if raw s=0 then some ⟨setRaw s 3,18,.right⟩
      else none
    else if q=17 then
      if raw s=0 ∨ raw s=1 then some ⟨s,16,.right⟩ else none
    else if q=18 then
      if raw s=3 then some ⟨s,18,.right⟩
      else if raw s=0 then some ⟨setRaw s 3,19,.left⟩
      else if raw s=1 then some ⟨setRaw s 3,22,.left⟩
      else if raw s=2 then some ⟨s,25,.left⟩
      else none
    else if q=19 then
      if output s=3 then some ⟨s,20,.right⟩ else some ⟨s,19,.left⟩
    else if q=22 then
      if output s=3 then some ⟨s,23,.right⟩ else some ⟨s,22,.left⟩
    else if q=20 then
      if output s=2 then some ⟨setOutput s 0,24,.left⟩ else some ⟨s,20,.right⟩
    else if q=23 then
      if output s=2 then some ⟨setOutput s 1,24,.left⟩ else some ⟨s,23,.right⟩
    else if q=24 then
      if output s=3 then some ⟨s,26,.right⟩ else some ⟨s,24,.left⟩
    else if q=26 then
      if raw s=3 then some ⟨s,18,.right⟩ else some ⟨s,26,.right⟩
    else if q=25 then
      if output s=3 then some ⟨s,27,.right⟩ else some ⟨s,25,.left⟩
    else if q=27 then
      if s=blank M then some ⟨s,28,.left⟩ else some ⟨cleanCell M s,27,.right⟩
    else if q=28 then
      if output s=3 then some ⟨blank M,0,.right⟩ else some ⟨s,28,.left⟩
    else none
  start := 2
  accept := 0
  reject := 1
  accept_ne_reject := by decide
  blank := blank M
  zero := joint 2 M.zero 0 2
  one := joint 2 M.one 0 2
  blank_ne_zero := fun h => M.blank_ne_zero (joint_work_injective h)
  blank_ne_one := fun h => M.blank_ne_one (joint_work_injective h)
  zero_ne_one := fun h => M.zero_ne_one (joint_work_injective h)
  accept_terminal := by intro s slot;simp
  reject_terminal := by intro s slot;simp

def startTape (M : DeterministicMachine ns nt) (r u : List Bool) (z : Int) : Alphabet nt :=
  joint (rawTape r z) (inputTape M u z) 0 2
def startConfig (M : DeterministicMachine ns nt) (r u : List Bool) :
    Configuration 30 (4*(2*(4*nt))) := ⟨2,0,startTape M r u⟩
def finalConfig (M : DeterministicMachine ns nt) (v : List Bool) :
    Configuration 30 (4*(2*(4*nt))) := ⟨0,0,inputTape (machine M) v⟩

theorem final_output (M : DeterministicMachine ns nt) (v : List Bool) :
    Output (machine M) v (finalConfig M v) := ⟨rfl,rfl,rfl⟩

def prefixOutput (u : List Bool) (k : Nat) : List Bool :=
  (u.take k).flatMap (fun b => [true,b])
theorem prefixOutput_length (u : List Bool) (k : Nat) (hk : k≤u.length) :
    (prefixOutput u k).length=2*k := by
  have hl : ∀ v : List Bool, (v.flatMap (fun b => [true,b])).length=2*v.length := by
    intro v
    induction v with
    | nil => rfl
    | cons b v ih => simp [List.flatMap_cons,ih];omega
  simpa only [prefixOutput,List.length_take,Nat.min_eq_left hk] using hl (u.take k)

def counterTape (M : DeterministicMachine ns nt) (r u : List Bool) (k : Nat) (z : Int) :
    Alphabet nt :=
  if z=-1 then joint 2 M.blank 0 3 else
    joint (rawTape r z) (inputTape M u z)
      (if 0≤z ∧ z.toNat<k then 1 else 0)
      (rawTape (prefixOutput u k) z)

def counterConfig (M : DeterministicMachine ns nt) (r u : List Bool) (k : Nat) :
    Configuration 30 (4*(2*(4*nt))) := ⟨4,0,counterTape M r u k⟩

theorem counter_negative (M : DeterministicMachine ns nt) (r u : List Bool) (k : Nat)
    (z : Int) (hz : z<0) (hL : z≠-1) : counterTape M r u k z=blank M := by
  simp [counterTape,hL,rawTape,inputTape_neg M u z hz,
    show ¬ 0≤z by omega,blank]

theorem counter_L (M : DeterministicMachine ns nt) (r u : List Bool) (k : Nat) :
    counterTape M r u k (-1)=joint 2 M.blank 0 3 := by simp [counterTape]

theorem counter_zero_setup (M : DeterministicMachine ns nt) (r u : List Bool) :
    run (machine M) (ticks 2) (startConfig M r u)=some (counterConfig M r u 0) := by
  have ht : Function.update (startTape M r u) 0 (startTape M r u 0)=startTape M r u :=
    Function.update_eq_self_iff.mpr rfl
  have hzero : Function.update (startTape M r u) (-1) (joint 2 M.blank 0 3)=
      counterTape M r u 0 := by
    funext z
    by_cases hL : z=(-1 : Int)
    · subst z;simp [counterTape]
    · rw [Function.update_of_ne hL]
      simp [counterTape,hL,startTape,prefixOutput,rawTape]
  simp [ticks,run,step,startConfig,counterConfig,machine,writtenTape,moveHead,ht,hzero]

end PakFixedPolyomino.StandardBitRetainedPairStage
