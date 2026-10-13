import PakFixedPolyomino.StandardBitProtectedLoader

/-! Physical restoration of a retained raw input after a clean boolean result.
The raw track is preserved and the work track is rebuilt in exactly 2n+4 ticks. -/
namespace PakFixedPolyomino.StandardBitProtectedRestore
open StandardNondeterministicMachine StandardBitTime StandardMachineProtectedTrack
open StandardBitProtectedLoader (rawTape bitRaw bitWork)
open FiniteOneTapeProgram (Action)
open FiniteOneTapeSemantics (moveHead writtenTape Config)

variable {ns nt : Nat}

def rule (M : DeterministicMachine ns nt) (q : Fin 6) (s : Fin (4*nt))
    (_ : Fin 1) : Option (Action (Fin 6) (Fin (4*nt))) :=
  if q=2 then some ⟨s,3,.left⟩
  else if q=3 then some ⟨pack (3 : Fin 4) M.blank,4,.right⟩
  else if q=4 then
    if (unpack s).1=(2 : Fin 4) then some ⟨pack (2 : Fin 4) M.blank,5,.left⟩
    else some ⟨pack (unpack s).1 (if (unpack s).1=(1 : Fin 4) then M.one else M.zero),4,.right⟩
  else if q=5 then
    if (unpack s).1=(3 : Fin 4) then some ⟨pack (2 : Fin 4) M.blank,0,.right⟩
    else some ⟨s,5,.left⟩
  else none

def machine (M : DeterministicMachine ns nt) : DeterministicMachine 6 (4*nt) where
  rule := rule M
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
  accept_terminal := by intro s slot; simp [rule]
  reject_terminal := by intro s slot; simp [rule]

def startConfig (M : DeterministicMachine ns nt) (x : List Bool) (b : Bool) :
    Configuration 6 (4*nt) :=
  ⟨2,0,fun z => pack (rawTape x z) (inputTape M [b] z)⟩

def scanTape (M : DeterministicMachine ns nt) (x : List Bool) (b : Bool)
    (k : Nat) (z : Int) : Fin (4*nt) :=
  if z = -1 then pack (3 : Fin 4) M.blank
  else pack (rawTape x z)
    (if 0 ≤ z ∧ z.toNat < k then inputTape M x z else inputTape M [b] z)

def doneTape (M : DeterministicMachine ns nt) (x : List Bool) (z : Int) : Fin (4*nt) :=
  if z = -1 then pack (3 : Fin 4) M.blank
  else pack (rawTape x z) (inputTape M x z)

def finalConfig (M : DeterministicMachine ns nt) (x : List Bool) : Configuration 6 (4*nt) :=
  ⟨0,0,fun z => pack (rawTape x z) (inputTape M x z)⟩

theorem init_step (M : DeterministicMachine ns nt) (x : List Bool) (b : Bool) :
    step (machine M) 0 (startConfig M x b) =
      some (Config.mk 3 (-1) (startConfig M x b).tape) := by
  simp [step,machine,rule,startConfig,writtenTape,moveHead,Function.update_eq_self]

theorem mark_tape (M : DeterministicMachine ns nt) (x : List Bool) (b : Bool) :
    Function.update (startConfig M x b).tape (-1) (pack (3 : Fin 4) M.blank) =
      scanTape M x b 0 := by
  funext z
  by_cases hz : z = -1
  · simp [hz,scanTape]
  · simp [Function.update_of_ne hz,scanTape,hz,startConfig]

theorem mark_step (M : DeterministicMachine ns nt) (x : List Bool) (b : Bool) :
    step (machine M) 0 (Config.mk 3 (-1) (startConfig M x b).tape) =
      some (Config.mk 4 0 (scanTape M x b 0)) := by
  simp [step,machine,rule,writtenTape,moveHead,mark_tape]

theorem scan_read (M : DeterministicMachine ns nt) (x : List Bool) (b : Bool)
    (k : Nat) (hk : k < x.length) :
    (unpack (scanTape M x b k k)).1 = bitRaw x[k] := by
  have hne : (k : Int) ≠ -1 := by omega
  simp [scanTape,hne,rawTape,hk,bitRaw]

theorem scan_write (M : DeterministicMachine ns nt) (x : List Bool) (b : Bool)
    (k : Nat) (hk : k < x.length) :
    Function.update (scanTape M x b k) (k : Int) (pack (bitRaw x[k]) (bitWork M x[k])) =
      scanTape M x b (k+1) := by
  funext z
  by_cases hz : z=(k : Int)
  · subst z
    have hne : (k : Int) ≠ -1 := by omega
    simp [scanTape,hne,rawTape,hk,bitRaw,bitWork,inputTape]
  · rw [Function.update_of_ne hz]
    unfold scanTape
    by_cases hm : z = -1
    · simp [hm]
    · rw [if_neg hm,if_neg hm]
      have he : (0 ≤ z ∧ z.toNat < k) ↔ (0 ≤ z ∧ z.toNat < k+1) := by
        constructor
        · intro h; exact ⟨h.1,by omega⟩
        · intro h
          have hn : z.toNat ≠ k := by
            intro heq; apply hz
            have ht := Int.toNat_of_nonneg h.1
            omega
          exact ⟨h.1,by omega⟩
      simp only [he]

theorem scan_step (M : DeterministicMachine ns nt) (x : List Bool) (b : Bool)
    (k : Nat) (hk : k < x.length) :
    step (machine M) 0 (Config.mk 4 k (scanTape M x b k)) =
      some (Config.mk 4 ((k : Int)+1) (scanTape M x b (k+1))) := by
  have hread := scan_read M x b k hk
  have hn : bitRaw x[k] ≠ (2 : Fin 4) := by cases (x[k] : Bool) <;> simp [bitRaw]
  have hw : (if bitRaw x[k]=(1 : Fin 4) then M.one else M.zero) = bitWork M x[k] := by
    cases (x[k] : Bool) <;> simp [bitRaw,bitWork]
  simp [step,machine,rule,hread,hn,hw,writtenTape,moveHead,scan_write M x b k hk]

theorem scan_bits (M : DeterministicMachine ns nt) (x : List Bool) (b : Bool)
    (k : Nat) (hk : k ≤ x.length) :
    run (machine M) (ticks k) (Config.mk 4 0 (scanTape M x b 0)) =
      some (Config.mk 4 k (scanTape M x b k)) := by
  induction k with
  | zero => simp [ticks]
  | succ k ih =>
    rw [ticks_add,run_append,ih (by omega),Option.bind_some,run_ticks_one,
      scan_step M x b k (by omega)]
    simp [Nat.cast_add]

theorem end_tape (M : DeterministicMachine ns nt) (x : List Bool) (b : Bool) :
    Function.update (scanTape M x b x.length) (x.length : Int) (pack (2 : Fin 4) M.blank) =
      doneTape M x := by
  funext z
  by_cases hz : z=(x.length : Int)
  · subst z
    have hne : (x.length : Int) ≠ -1 := by omega
    simp [doneTape,hne,rawTape,inputTape]
  · rw [Function.update_of_ne hz]
    unfold scanTape doneTape
    by_cases hm : z = -1
    · simp [hm]
    · rw [if_neg hm,if_neg hm]
      by_cases hi : 0 ≤ z ∧ z.toNat < x.length
      · simp [hi]
      · rw [if_neg hi]
        congr 1
        by_cases hp : 0 ≤ z
        · have hn : x.length ≤ z.toNat := by omega
          have hn0 : 1 ≤ z.toNat := by
            have ht := Int.toNat_of_nonneg hp
            by_contra h; have : z.toNat=0 := by omega
            have : x.length=0 := by omega
            apply hz; omega
          have ht := Int.toNat_of_nonneg hp
          rw [inputTape_ge M [b] z (by simp only [List.length_singleton];omega),
            inputTape_ge M x z (by omega)]
        · simp [inputTape,hp]

theorem scan_blank (M : DeterministicMachine ns nt) (x : List Bool) (b : Bool) :
    step (machine M) 0 (Config.mk 4 x.length (scanTape M x b x.length)) =
      some (Config.mk 5 ((x.length : Int)-1) (doneTape M x)) := by
  have hne : (x.length : Int) ≠ -1 := by omega
  have hread : (unpack (scanTape M x b x.length x.length)).1=(2 : Fin 4) := by
    simp [scanTape,hne,rawTape]
  simp [step,machine,rule,hread,writtenTape,moveHead,end_tape]

theorem done_nat_ne_mark (M : DeterministicMachine ns nt) (x : List Bool)
    (z : Int) (hz : 0 ≤ z) : (unpack (doneTape M x z)).1 ≠ (3 : Fin 4) := by
  have hne : z ≠ -1 := by omega
  simp [doneTape,hne,rawTape,hz]
  split_ifs <;> decide

theorem return_left (M : DeterministicMachine ns nt) (x : List Bool)
    (k : Nat) (hk : k ≤ x.length) :
    run (machine M) (ticks k) (Config.mk 5 ((x.length : Int)-1) (doneTape M x)) =
      some (Config.mk 5 ((x.length : Int)-1-k) (doneTape M x)) := by
  induction k with
  | zero => simp [ticks]
  | succ k ih =>
    rw [ticks_add,run_append,ih (by omega),Option.bind_some,run_ticks_one]
    have hp : 0 ≤ (x.length : Int)-1-k := by omega
    have hn := done_nat_ne_mark M x _ hp
    simp [step,machine,rule,hn,writtenTape,moveHead,Function.update_eq_self]
    omega

theorem erase_mark (M : DeterministicMachine ns nt) (x : List Bool) :
    Function.update (doneTape M x) (-1) (pack (2 : Fin 4) M.blank) =
      fun z => pack (rawTape x z) (inputTape M x z) := by
  funext z
  by_cases hz : z = -1
  · subst z; simp [rawTape,inputTape]
  · simp [Function.update_of_ne hz,doneTape,hz]

theorem final_step (M : DeterministicMachine ns nt) (x : List Bool) :
    step (machine M) 0 (Config.mk 5 (-1) (doneTape M x)) = some (finalConfig M x) := by
  simp [step,machine,rule,doneTape,writtenTape,moveHead,finalConfig,erase_mark]

theorem restore_run (M : DeterministicMachine ns nt) (x : List Bool) (b : Bool) :
    run (machine M) (ticks (2*x.length+4)) (startConfig M x b) = some (finalConfig M x) := by
  rw [StandardBitProtectedLoader.fuel_split,run_append,run_ticks_one,init_step,
    Option.bind_some,run_append,run_ticks_one,mark_step,Option.bind_some,
    run_append,scan_bits M x b x.length le_rfl,Option.bind_some,run_append,
    run_ticks_one,scan_blank,Option.bind_some,run_append,
    return_left M x x.length le_rfl,Option.bind_some]
  have hh : (x.length : Int)-1-x.length = -1 := by omega
  rw [hh,run_ticks_one,final_step]

theorem restore_spec (M : DeterministicMachine ns nt) (x : List Bool) (b : Bool) :
    run (machine M) (ticks (2*x.length+4)) (startConfig M x b) = some (finalConfig M x) ∧
    (finalConfig M x).state=(machine M).accept ∧ (finalConfig M x).head=0 ∧
    (∀ z, (unpack ((finalConfig M x).tape z)).1=rawTape x z) ∧
    (∀ z, (unpack ((finalConfig M x).tape z)).2=inputTape M x z) := by
  exact ⟨restore_run M x b,rfl,rfl,by intro z;simp [finalConfig],by intro z;simp [finalConfig]⟩

end PakFixedPolyomino.StandardBitProtectedRestore
