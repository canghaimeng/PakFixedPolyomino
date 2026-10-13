import PakFixedPolyomino.StandardBitTime
import PakFixedPolyomino.StandardMachineProtectedTrack

/-! Actual ordinary tape cleanup of a retained raw track. The start is an
explicit two-track stage configuration, not an arbitrary machine initializer. -/
namespace PakFixedPolyomino.StandardBitProtectedCleanup
open StandardNondeterministicMachine StandardBitTime StandardMachineProtectedTrack
open FiniteOneTapeSemantics (moveHead writtenTape)
variable {ns nt : Nat}

def rawBit (b : Bool) : Fin 4 := if b then 1 else 0
def rawTape (x : List Bool) (z : Int) : Fin 4 :=
  if hz : 0 ≤ z then
    if hi : z.toNat < x.length then rawBit x[z.toNat] else 2
  else 2

theorem rawBit_ne_blank (b : Bool) : rawBit b ≠ 2 := by cases b <;> decide

def machine (M : DeterministicMachine ns nt) : DeterministicMachine 6 (4*nt) where
  rule := fun q s _ =>
    if q = 2 then some ⟨s,3,.left⟩
    else if q = 3 then some ⟨pack (3 : Fin 4) M.blank,4,.right⟩
    else if q = 4 then
      if s = pack (2 : Fin 4) M.blank then some ⟨s,5,.left⟩
      else some ⟨pack (2 : Fin 4) (unpack s).2,4,.right⟩
    else if q = 5 then
      if s = pack (3 : Fin 4) M.blank then some ⟨pack (2 : Fin 4) M.blank,0,.right⟩
      else some ⟨s,5,.left⟩
    else none
  start := 2
  accept := 0
  reject := 1
  accept_ne_reject := by decide
  blank := pack (2 : Fin 4) M.blank
  zero := pack (2 : Fin 4) M.zero
  one := pack (2 : Fin 4) M.one
  blank_ne_zero := fun h => M.blank_ne_zero (pack_inj_right h)
  blank_ne_one := fun h => M.blank_ne_one (pack_inj_right h)
  zero_ne_one := fun h => M.zero_ne_one (pack_inj_right h)
  accept_terminal := by intro s slot;simp
  reject_terminal := by intro s slot;simp

def twoTape (M : DeterministicMachine ns nt) (x y : List Bool) (z : Int) : Fin (4*nt) :=
  pack (rawTape x z) (inputTape M y z)

def startConfig (M : DeterministicMachine ns nt) (x y : List Bool) : Configuration 6 (4*nt) :=
  ⟨2,0,twoTape M x y⟩

def phaseTape (M : DeterministicMachine ns nt) (x y : List Bool) (k : Nat) : Int → Fin (4*nt) :=
  Function.update
    (fun z => if 0 ≤ z ∧ z.toNat < k then pack (2 : Fin 4) (inputTape M y z) else twoTape M x y z)
    (-1) (pack (3 : Fin 4) M.blank)

def scanConfig (M : DeterministicMachine ns nt) (x y : List Bool) (k : Nat) : Configuration 6 (4*nt) :=
  ⟨4,(k : Int),phaseTape M x y k⟩

theorem inputTape_pack (M : DeterministicMachine ns nt) (y : List Bool) :
    inputTape (machine M) y = fun z => pack (2 : Fin 4) (inputTape M y z) := by
  funext z
  simp only [inputTape,machine]
  split_ifs <;> rfl

theorem phase_read (M : DeterministicMachine ns nt) (x y : List Bool) (k : Nat) :
    phaseTape M x y k (k : Int) = twoTape M x y (k : Int) := by
  simp [phaseTape,Function.update_apply]

theorem phase_write (M : DeterministicMachine ns nt) (x y : List Bool) (k : Nat) :
    Function.update (phaseTape M x y k) (k : Int)
      (pack (2 : Fin 4) (inputTape M y (k : Int))) = phaseTape M x y (k+1) := by
  funext z
  by_cases hl : z = -1
  · subst z
    simp [phaseTape,Function.update_apply]
  · by_cases hk : z = (k : Int)
    · subst z
      simp [phaseTape,Function.update_apply]
    · have hc : (0 ≤ z ∧ z.toNat < k+1) ↔ (0 ≤ z ∧ z.toNat < k) := by
        by_cases hz : 0 ≤ z
        · have hne : z.toNat ≠ k := by
            intro he
            apply hk
            have hh := Int.toNat_of_nonneg hz
            omega
          omega
        · simp [hz]
      simp only [Function.update_apply,if_neg hk,phaseTape,if_neg hl,hc]

theorem twoTape_nonblank (M : DeterministicMachine ns nt) (x y : List Bool) (k : Nat)
    (hk : k < max x.length y.length) : twoTape M x y (k : Int) ≠ pack (2 : Fin 4) M.blank := by
  intro h
  rcases lt_max_iff.mp hk with hx | hy
  · have hr := congrArg (fun s : Fin (4*nt) => (unpack s).1) h
    have hbit : rawBit x[k] = 2 := by simpa [twoTape,rawTape,hx] using hr
    exact rawBit_ne_blank x[k] hbit
  · have hw := congrArg (fun s : Fin (4*nt) => (unpack s).2) h
    have hb : (if y[k] then M.one else M.zero) = M.blank := by
      simpa [twoTape,inputTape,hy] using hw
    cases hbit : y[k] <;> simp [hbit] at hb
    · exact M.blank_ne_zero hb.symm
    · exact M.blank_ne_one hb.symm

theorem setup_run (M : DeterministicMachine ns nt) (x y : List Bool) :
    run (machine M) (ticks 2) (startConfig M x y) = some (scanConfig M x y 0) := by
  have ht : Function.update (twoTape M x y) 0 (twoTape M x y 0) = twoTape M x y :=
    Function.update_eq_self_iff.mpr rfl
  simp [ticks,run,step,machine,startConfig,scanConfig,moveHead,writtenTape,phaseTape,ht]

theorem scan_step (M : DeterministicMachine ns nt) (x y : List Bool) (k : Nat)
    (hk : k < max x.length y.length) :
    step (machine M) 0 (scanConfig M x y k) = some (scanConfig M x y (k+1)) := by
  have hn := twoTape_nonblank M x y k hk
  have hu : (unpack (twoTape M x y (k : Int))).2 = inputTape M y (k : Int) := by simp [twoTape]
  simp only [step,scanConfig,phase_read,machine,show (4 : Fin 6) ≠ 2 by decide,
    show (4 : Fin 6) ≠ 3 by decide,if_false,ite_true,hn,Option.map_some,hu]
  apply congrArg some
  apply config_ext
  · rfl
  · simp [moveHead]
  · exact phase_write M x y k

theorem scan_run (M : DeterministicMachine ns nt) (x y : List Bool) (j k : Nat)
    (hk : j+k ≤ max x.length y.length) :
    run (machine M) (ticks k) (scanConfig M x y j) = some (scanConfig M x y (j+k)) := by
  induction k generalizing j with
  | zero => simp [ticks]
  | succ k ih =>
    rw [show k+1 = 1+k by omega,ticks_add,run_append,run_ticks_one,scan_step M x y j (by omega),Option.bind_some]
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (j+1) (by omega)

def endTape (M : DeterministicMachine ns nt) (y : List Bool) : Int → Fin (4*nt) :=
  Function.update (inputTape (machine M) y) (-1) (pack (3 : Fin 4) M.blank)

theorem phase_complete (M : DeterministicMachine ns nt) (x y : List Bool) :
    phaseTape M x y (max x.length y.length) = endTape M y := by
  funext z
  by_cases hl : z = -1
  · simp [phaseTape,endTape,hl]
  · rw [phaseTape,endTape,Function.update_of_ne hl,Function.update_of_ne hl,inputTape_pack]
    by_cases hz : 0 ≤ z
    · by_cases hk : z.toNat < max x.length y.length
      · simp [hz,hk]
      · have hx : ¬z.toNat < x.length := by omega
        simp [hz,hk,twoTape,rawTape,hx]
    · simp [hz,twoTape,rawTape]

def returnConfig (M : DeterministicMachine ns nt) (y : List Bool) (h : Int) : Configuration 6 (4*nt) :=
  ⟨5,h,endTape M y⟩

theorem endTape_nat (M : DeterministicMachine ns nt) (y : List Bool) (k : Nat) :
    endTape M y (k : Int) = pack (2 : Fin 4) (inputTape M y (k : Int)) := by
  rw [endTape,Function.update_of_ne (by omega),inputTape_pack]

theorem endTape_not_sentinel (M : DeterministicMachine ns nt) (y : List Bool) (k : Nat) :
    endTape M y (k : Int) ≠ pack (3 : Fin 4) M.blank := by
  rw [endTape_nat]
  intro h
  have hr := congrArg (fun s : Fin (4*nt) => (unpack s).1) h
  simp at hr

theorem turn_step (M : DeterministicMachine ns nt) (x y : List Bool) :
    step (machine M) 0 (scanConfig M x y (max x.length y.length)) =
      some (returnConfig M y ((max x.length y.length : Nat)-1 : Int)) := by
  have hx : (x.length : Int) ≤ (max x.length y.length : Nat) := by exact_mod_cast Nat.le_max_left _ _
  have hy : (y.length : Int) ≤ (max x.length y.length : Nat) := by exact_mod_cast Nat.le_max_right _ _
  have hr : twoTape M x y (max x.length y.length : Nat) = pack (2 : Fin 4) M.blank := by
    rw [twoTape,inputTape_ge M y _ hy]
    simp [rawTape]
  have hread := (phase_read M x y (max x.length y.length)).trans hr
  have ht : Function.update (phaseTape M x y (max x.length y.length))
      (max x.length y.length : Nat) (pack (2 : Fin 4) M.blank) = endTape M y :=
    (Function.update_eq_self_iff.mpr hread.symm).trans (phase_complete M x y)
  simp only [step,scanConfig,hread,machine,show (4 : Fin 6) ≠ 2 by decide,
    show (4 : Fin 6) ≠ 3 by decide,if_false,ite_true,Option.map_some]
  apply congrArg some
  apply config_ext
  · rfl
  · rfl
  · exact ht

theorem return_step (M : DeterministicMachine ns nt) (y : List Bool) (k : Nat) :
    step (machine M) 0 (returnConfig M y (k : Int)) = some (returnConfig M y ((k : Int)-1)) := by
  have hn := endTape_not_sentinel M y k
  simp [step,returnConfig,machine,hn,moveHead,writtenTape,Function.update_eq_self_iff]

theorem return_run (M : DeterministicMachine ns nt) (y : List Bool) (k : Nat) :
    run (machine M) (ticks (k+1)) (returnConfig M y (k : Int)) = some (returnConfig M y (-1)) := by
  induction k with
  | zero => simpa using return_step M y 0
  | succ k ih =>
    rw [show k+1+1 = 1+(k+1) by omega,ticks_add,run_append,run_ticks_one,return_step,Option.bind_some]
    simpa using ih

def finalConfig (M : DeterministicMachine ns nt) (y : List Bool) : Configuration 6 (4*nt) :=
  ⟨0,0,inputTape (machine M) y⟩

theorem erase_step (M : DeterministicMachine ns nt) (y : List Bool) :
    step (machine M) 0 (returnConfig M y (-1)) = some (finalConfig M y) := by
  have ht : Function.update (endTape M y) (-1) (pack (2 : Fin 4) M.blank) = inputTape (machine M) y := by
    rw [endTape,Function.update_idem]
    apply Function.update_eq_self_iff.mpr
    rw [inputTape_neg (machine M) y (-1) (by decide)]
    rfl
  have hr : endTape M y (-1) = pack (3 : Fin 4) M.blank := by simp [endTape]
  simp only [step,returnConfig,hr,machine,show (5 : Fin 6) ≠ 2 by decide,
    show (5 : Fin 6) ≠ 3 by decide,show (5 : Fin 6) ≠ 4 by decide,
    if_false,ite_true,Option.map_some]
  apply congrArg some
  apply config_ext
  · rfl
  · rfl
  · exact ht

theorem cleanup_run (M : DeterministicMachine ns nt) (x y : List Bool) :
    run (machine M) (ticks (2*max x.length y.length+4)) (startConfig M x y) =
      some (finalConfig M y) := by
  let L := max x.length y.length
  have hs : 2*L+4 = 2+L+1+(L+1) := by omega
  rw [show 2*max x.length y.length+4 = 2+L+1+(L+1) by exact hs,
    ticks_add,run_append,ticks_add,run_append,ticks_add,run_append,setup_run,Option.bind_some,
    scan_run M x y 0 L (by simp [L]),Option.bind_some,
    show 0+L = max x.length y.length by simp [L],run_ticks_one,turn_step,Option.bind_some]
  by_cases hz : L = 0
  · have hm : max x.length y.length = 0 := hz
    rw [hm]
    simpa only [hz,Nat.zero_add,Nat.cast_zero,run_ticks_one,zero_sub] using erase_step M y
  · have hp : 0 < L := Nat.pos_of_ne_zero hz
    rw [show L+1 = ((L-1)+1)+1 by omega,ticks_add,run_append]
    have hh : ((max x.length y.length : Nat)-1 : Int) = ((L-1 : Nat) : Int) := by
      dsimp [L]
      omega
    rw [hh,return_run,Option.bind_some,run_ticks_one,erase_step]

theorem cleanup_output (M : DeterministicMachine ns nt) (y : List Bool) :
    Output (machine M) y (finalConfig M y) := by
  exact ⟨rfl,rfl,rfl⟩

theorem cleanup_prefix_bound (M : DeterministicMachine ns nt) (x y : List Bool)
    (slots : List (Fin 1)) (out : Configuration 6 (4*nt))
    (hr : run (machine M) slots (startConfig M x y) = some out) :
    slots.length ≤ 2*max x.length y.length+4 := by
  let L := 2*max x.length y.length+4
  by_contra hbad
  have hlt : L < slots.length := by omega
  have he : slots.length = L+(slots.length-L) := by omega
  have hn : ticks (slots.length-L) ≠ [] := by
    intro hz
    have hh := congrArg List.length hz
    simp only [ticks_length,List.length_nil] at hh
    omega
  have hterm := run_accept_nonempty_none (machine M) (finalConfig M y) rfl
    (ticks (slots.length-L)) hn
  rw [deterministic_word slots,he,ticks_add,run_append,cleanup_run,Option.bind_some,hterm] at hr
  contradiction

theorem cleanup_exact (M : DeterministicMachine ns nt) (x y : List Bool) :
    run (machine M) (ticks (2*max x.length y.length+4)) (startConfig M x y) =
        some (finalConfig M y) ∧
    Output (machine M) y (finalConfig M y) ∧
    ∀ slots out,run (machine M) slots (startConfig M x y) = some out →
      slots.length ≤ 2*max x.length y.length+4 :=
  ⟨cleanup_run M x y,cleanup_output M y,cleanup_prefix_bound M x y⟩

end PakFixedPolyomino.StandardBitProtectedCleanup
