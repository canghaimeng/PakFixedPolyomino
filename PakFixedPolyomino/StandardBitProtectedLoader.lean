import PakFixedPolyomino.StandardBitTime
import PakFixedPolyomino.StandardMachineProtectedTrack

/-! Physically copy the ordinary input into the protected raw track. -/
namespace PakFixedPolyomino.StandardBitProtectedLoader

open StandardNondeterministicMachine StandardBitTime StandardMachineProtectedTrack
open FiniteOneTapeProgram (Action)
open FiniteOneTapeSemantics (moveHead writtenTape Config)

variable {ns nt : ℕ}

def rawTape (x : List Bool) (z : Int) : Fin 4 :=
  if hz : 0 ≤ z then
    if hi : z.toNat < x.length then
      if x[z.toNat] then 1 else 0
    else 2
  else 2

def stInit : Fin (ns + 4) := ⟨ns, by omega⟩
def stMark : Fin (ns + 4) := ⟨ns + 1, by omega⟩
def stScan : Fin (ns + 4) := ⟨ns + 2, by omega⟩
def stRet : Fin (ns + 4) := ⟨ns + 3, by omega⟩

def lift (c : Configuration ns (4 * nt)) : Configuration (ns + 4) (4 * nt) :=
  { state := Fin.castAdd 4 c.state, head := c.head, tape := c.tape }

def coreState (q : Fin (ns + 4)) : Option (Fin ns) :=
  if h : q.val < ns then some ⟨q.val, h⟩ else none

@[simp] theorem coreState_castAdd (q : Fin ns) :
    coreState (Fin.castAdd 4 q) = some q := by
  simp [coreState, Fin.val_castAdd]

@[simp] theorem coreState_stInit : coreState (ns := ns) stInit = none := by
  simp [coreState, stInit]
@[simp] theorem coreState_stMark : coreState (ns := ns) stMark = none := by
  simp [coreState, stMark]
@[simp] theorem coreState_stScan : coreState (ns := ns) stScan = none := by
  simp [coreState, stScan]
@[simp] theorem coreState_stRet : coreState (ns := ns) stRet = none := by
  simp [coreState, stRet]

def bitRaw (b : Bool) : Fin 4 := if b then 1 else 0
def bitWork (M : DeterministicMachine ns nt) (b : Bool) : Fin nt :=
  if b then M.one else M.zero

def loaderRule (M : DeterministicMachine ns nt) (q : Fin (ns + 4))
    (s : Fin (4 * nt)) (_slot : Fin 1) :
    Option (Action (Fin (ns + 4)) (Fin (4 * nt))) :=
  match coreState q with
  | some q0 =>
      ((protect (nr := 4) M (2 : Fin 4)).rule q0 s 0).map fun a =>
        ⟨a.write, Fin.castAdd 4 a.target, a.move⟩
  | none =>
      if q.val = ns then some ⟨s, stMark, .left⟩
      else if q.val = ns + 1 then some ⟨pack (3 : Fin 4) M.blank, stScan, .right⟩
      else if q.val = ns + 2 then
        if (unpack s).2 = M.blank then some ⟨s, stRet, .left⟩
        else some ⟨pack (if (unpack s).2 = M.one then (1 : Fin 4) else 0)
            (unpack s).2, stScan, .right⟩
      else if (unpack s).1 = (3 : Fin 4) then
        some ⟨pack (2 : Fin 4) M.blank, Fin.castAdd 4 M.start, .right⟩
      else some ⟨s, stRet, .left⟩

def loader (M : DeterministicMachine ns nt) :
    DeterministicMachine (ns + 4) (4 * nt) where
  rule := loaderRule M
  start := stInit
  accept := Fin.castAdd 4 M.accept
  reject := Fin.castAdd 4 M.reject
  accept_ne_reject := by
    intro h
    apply M.accept_ne_reject
    apply Fin.ext
    simpa [Fin.val_castAdd] using congrArg Fin.val h
  blank := pack (2 : Fin 4) M.blank
  zero := pack (2 : Fin 4) M.zero
  one := pack (2 : Fin 4) M.one
  blank_ne_zero := fun h => M.blank_ne_zero (pack_inj_right h)
  blank_ne_one := fun h => M.blank_ne_one (pack_inj_right h)
  zero_ne_one := fun h => M.zero_ne_one (pack_inj_right h)
  accept_terminal := by
    intro s slot
    simp [loaderRule, protectRule, M.accept_terminal]
  reject_terminal := by
    intro s slot
    simp [loaderRule, protectRule, M.reject_terminal]

@[simp] theorem loader_rule_eq (M : DeterministicMachine ns nt) :
    (loader M).rule = loaderRule M := rfl
@[simp] theorem loader_start_eq (M : DeterministicMachine ns nt) :
    (loader M).start = stInit := rfl
@[simp] theorem stInit_val : (stInit : Fin (ns + 4)).val = ns := rfl
@[simp] theorem stMark_val : (stMark : Fin (ns + 4)).val = ns + 1 := rfl
@[simp] theorem stScan_val : (stScan : Fin (ns + 4)).val = ns + 2 := rfl
@[simp] theorem stRet_val : (stRet : Fin (ns + 4)).val = ns + 3 := rfl

theorem loader_input (M : DeterministicMachine ns nt) (x : List Bool) (z : Int) :
    inputTape (loader M) x z = pack (2 : Fin 4) (inputTape M x z) := by
  simp [inputTape, loader]
  split_ifs <;> rfl

def scanTape (M : DeterministicMachine ns nt) (x : List Bool) (k : ℕ) (z : Int) :
    Fin (4 * nt) :=
  if z = -1 then pack (3 : Fin 4) M.blank
  else if hz : 0 ≤ z then
    if hi : z.toNat < k ∧ z.toNat < x.length then
      pack (bitRaw (x[z.toNat])) (bitWork M (x[z.toNat]))
    else pack (2 : Fin 4) (inputTape M x z)
  else pack (2 : Fin 4) (inputTape M x z)

theorem scanTape_ge0_ne3 (M : DeterministicMachine ns nt) (x : List Bool)
    (k : ℕ) (z : Int) (hz : 0 ≤ z) : (unpack (scanTape M x k z)).1 ≠ 3 := by
  unfold scanTape
  have : ¬z = -1 := by omega
  simp [this, hz, bitRaw]
  split_ifs <;> simp

theorem endpoint_tape (M : DeterministicMachine ns nt) (x : List Bool) :
    Function.update (scanTape M x x.length) (-1) (pack (2 : Fin 4) M.blank) =
      fun z => pack (rawTape x z) (inputTape M x z) := by
  funext z
  by_cases hneg : z = -1
  · subst z
    have : ¬0 ≤ (-1 : Int) := by omega
    simp [Function.update_self, rawTape, inputTape, this]
  · rw [Function.update_of_ne hneg, scanTape, rawTape]
    simp [hneg]
    split_ifs <;> simp [bitRaw, bitWork, inputTape, *]

theorem fuel_split (n : ℕ) :
    ticks (2 * n + 4) =
      ticks 1 ++ (ticks 1 ++ (ticks n ++ (ticks 1 ++ (ticks n ++ ticks 1)))) := by
  have h : 2 * n + 4 = 1 + (1 + (n + (1 + (n + 1)))) := by omega
  simp [h, ticks_add]

theorem init_step (M : DeterministicMachine ns nt) (x : List Bool) :
    step (loader M) 0 (initial (loader M) x) =
      some { state := stMark, head := -1, tape := inputTape (loader M) x } := by
  simp [step, initial, loader_rule_eq, loader_start_eq, loaderRule, writtenTape,
    moveHead, Function.update_eq_self]

theorem mark_tape (M : DeterministicMachine ns nt) (x : List Bool) :
    Function.update (inputTape (loader M) x) (-1) (pack (3 : Fin 4) M.blank) =
      scanTape M x 0 := by
  funext z
  by_cases hz : z = -1
  · subst z; simp [Function.update_self, scanTape]
  · rw [Function.update_of_ne hz]
    simp [scanTape, hz, loader_input]

theorem mark_step (M : DeterministicMachine ns nt) (x : List Bool) :
    step (loader M) 0
        { state := stMark, head := -1, tape := inputTape (loader M) x } =
      some { state := stScan, head := 0, tape := scanTape M x 0 } := by
  simp [step, loader_rule_eq, loaderRule, writtenTape, moveHead, mark_tape]

theorem scan_at (M : DeterministicMachine ns nt) (x : List Bool) (k : ℕ)
    (hk : k < x.length) :
    scanTape M x k (k : Int) = pack (2 : Fin 4) (bitWork M (x[k])) := by
  have hnn : (k : Int) ≠ -1 := by omega
  have hge : 0 ≤ (k : Int) := by omega
  have hto : (k : Int).toNat = k := Int.toNat_natCast k
  simp [scanTape, hnn, hge, hto, inputTape, hk, bitWork]

theorem scan_write (M : DeterministicMachine ns nt) (b : Bool) :
    pack (if bitWork M b = M.one then (1 : Fin 4) else 0) (bitWork M b) =
      pack (bitRaw b) (bitWork M b) := by
  cases b <;> simp [bitWork, bitRaw, M.zero_ne_one]

theorem scanTape_succ (M : DeterministicMachine ns nt) (x : List Bool) (k : ℕ)
    (hk : k < x.length) :
    Function.update (scanTape M x k) k (pack (bitRaw (x[k])) (bitWork M (x[k]))) =
      scanTape M x (k + 1) := by
  funext z
  by_cases hz : z = (k : Int)
  · subst z
    have hnn : (k : Int) ≠ -1 := by omega
    have hge : 0 ≤ (k : Int) := by omega
    have hto : (k : Int).toNat = k := Int.toNat_natCast k
    simp [Function.update_self, scanTape, hnn, hge, hto, hk]
  · rw [Function.update_of_ne hz]
    unfold scanTape
    split_ifs <;> first | rfl | (exfalso; omega)

theorem scan_step (M : DeterministicMachine ns nt) (x : List Bool) (k : ℕ)
    (hk : k < x.length) :
    step (loader M) 0 { state := stScan, head := k, tape := scanTape M x k } =
      some { state := stScan, head := (k : Int) + 1, tape := scanTape M x (k + 1) } := by
  have hread := scan_at M x k hk
  have hnb : bitWork M (x[k]) ≠ M.blank := by
    cases (x[k] : Bool) <;> simp [bitWork, M.blank_ne_one.symm, M.blank_ne_zero.symm]
  simp [step, loader_rule_eq, loaderRule, hread, unpack_pack, hnb, writtenTape,
    moveHead, scan_write, scanTape_succ M x k hk]

theorem scan_bits (M : DeterministicMachine ns nt) (x : List Bool) (k : ℕ)
    (hk : k ≤ x.length) :
    run (loader M) (ticks k)
        { state := stScan, head := 0, tape := scanTape M x 0 } =
      some { state := stScan, head := k, tape := scanTape M x k } := by
  induction k with
  | zero => simp [ticks]
  | succ k ih =>
      have hk' : k < x.length := by omega
      have hdecomp : ticks (k + 1) = ticks k ++ ticks 1 := by simp [ticks_add]
      rw [hdecomp, run_append, ih (by omega)]
      simp [run_ticks_one, scan_step M x k hk', Nat.cast_succ]

theorem scan_blank (M : DeterministicMachine ns nt) (x : List Bool) :
    step (loader M) 0
        { state := stScan, head := x.length, tape := scanTape M x x.length } =
      some (Config.mk stRet ((x.length : Int) - 1) (scanTape M x x.length)) := by
  have hnn : (x.length : Int) ≠ -1 := by omega
  have hge : 0 ≤ (x.length : Int) := by omega
  have hto : (x.length : Int).toNat = x.length := Int.toNat_natCast x.length
  have hread : scanTape M x x.length (x.length : Int) = pack (2 : Fin 4) M.blank := by
    simp [scanTape, hnn, hge, hto, inputTape]
  simp [step, loader_rule_eq, loaderRule, hread, unpack_pack, writtenTape,
    moveHead, Function.update_eq_self]

theorem return_left (M : DeterministicMachine ns nt) (x : List Bool) (k : ℕ)
    (hk : k ≤ x.length) :
    run (loader M) (ticks k)
        (Config.mk stRet ((x.length : Int) - 1) (scanTape M x x.length)) =
      some (Config.mk stRet ((x.length : Int) - 1 - k) (scanTape M x x.length)) := by
  induction k with
  | zero => simp [ticks]
  | succ k ih =>
      have hdecomp : ticks (k + 1) = ticks k ++ ticks 1 := by simp [ticks_add]
      rw [hdecomp, run_append, ih (by omega)]
      simp only [Option.bind_some, run_ticks_one]
      have hge : 0 ≤ (x.length : Int) - 1 - k := by omega
      have hne3 := scanTape_ge0_ne3 M x x.length ((x.length : Int) - 1 - k) hge
      simp [step, loader_rule_eq, loaderRule, coreState_stRet, stRet_val]
      rw [if_neg hne3]
      simp [writtenTape, moveHead]
      omega

theorem restore_step (M : DeterministicMachine ns nt) (x : List Bool) :
    step (loader M) 0
        { state := stRet, head := -1, tape := scanTape M x x.length } =
      some (lift (embed (rawTape x) (initial M x))) := by
  have hread : scanTape M x x.length (-1) = pack (3 : Fin 4) M.blank := by
    simp [scanTape]
  simp [step, loader_rule_eq, loaderRule, hread, unpack_pack, writtenTape,
    moveHead, lift, embed, initial, endpoint_tape]

theorem loader_run (M : DeterministicMachine ns nt) (x : List Bool) :
    run (loader M) (ticks (2 * x.length + 4)) (initial (loader M) x) =
      some (lift (embed (rawTape x) (initial M x))) := by
  rw [fuel_split, run_append, run_ticks_one, init_step, Option.bind_some,
    run_append, run_ticks_one, mark_step, Option.bind_some,
    run_append, scan_bits M x x.length (le_rfl), Option.bind_some,
    run_append, run_ticks_one, scan_blank, Option.bind_some,
    run_append, return_left M x x.length (le_rfl), Option.bind_some]
  have hhead : (x.length : Int) - 1 - x.length = (-1 : Int) := by omega
  simp [run_ticks_one, hhead, restore_step]

theorem lift_step (M : DeterministicMachine ns nt) (c : Configuration ns (4 * nt)) :
    step (loader M) 0 (lift c) =
      (step (protect (nr := 4) M (2 : Fin 4)) 0 c).map lift := by
  simp only [step, lift, loader_rule_eq, loaderRule, coreState_castAdd]
  cases (protect (nr := 4) M (2 : Fin 4)).rule c.state (c.tape c.head) 0 with
  | none => simp
  | some a =>
      simp only [Option.map_some]
      apply congrArg some
      apply config_ext <;> rfl

theorem lift_run (M : DeterministicMachine ns nt) (slots : List (Fin 1))
    (c : Configuration ns (4 * nt)) :
    run (loader M) slots (lift c) =
      (run (protect (nr := 4) M (2 : Fin 4)) slots c).map lift := by
  induction slots generalizing c with
  | nil => simp
  | cons slot slots ih =>
      have hslot : slot = 0 := Subsingleton.elim _ _
      subst hslot
      simp only [run_cons, lift_step]
      cases step (protect (nr := 4) M (2 : Fin 4)) 0 c with
      | none => simp
      | some d => simp [ih]

theorem loader_source_exact (M : DeterministicMachine ns nt) (x : List Bool)
    (slots : List (Fin 1)) :
    run (loader M) (ticks (2 * x.length + 4) ++ slots) (initial (loader M) x) =
      (run M slots (initial M x)).map (fun out => lift (embed (rawTape x) out)) := by
  rw [run_append, loader_run]
  simp only [Option.bind_some, lift_run, run_exact, Option.map_map]
  rfl

theorem loader_source_some_iff (M : DeterministicMachine ns nt) (x : List Bool)
    (slots : List (Fin 1)) (out : Configuration (ns + 4) (4 * nt)) :
    run (loader M) (ticks (2 * x.length + 4) ++ slots) (initial (loader M) x) =
        some out ↔
      ∃ d, run M slots (initial M x) = some d ∧
        out = lift (embed (rawTape x) d) := by
  constructor
  · intro h
    cases hd : run M slots (initial M x) with
    | none =>
        rw [loader_source_exact, hd] at h
        simp at h
    | some d =>
        refine ⟨d, rfl, ?_⟩
        rw [loader_source_exact, hd] at h
        exact (Option.some.inj h).symm
  · rintro ⟨d, hd, rfl⟩
    rw [loader_source_exact, hd]
    rfl

theorem loader_passive (M : DeterministicMachine ns nt) (x : List Bool)
    (slots : List (Fin 1)) (out : Configuration (ns + 4) (4 * nt))
    (h : run (loader M) (ticks (2 * x.length + 4) ++ slots)
      (initial (loader M) x) = some out) :
    ∀ z : Int, (unpack (out.tape z)).1 = rawTape x z := by
  obtain ⟨d, -, rfl⟩ := (loader_source_some_iff M x slots out).mp h
  intro z
  simp [lift, embed]

theorem protected_loader_spec (M : DeterministicMachine ns nt) (x : List Bool)
    (slots : List (Fin 1)) :
    run (loader M) (ticks (2 * x.length + 4)) (initial (loader M) x) =
      some (lift (embed (rawTape x) (initial M x))) ∧
    run (loader M) (ticks (2 * x.length + 4) ++ slots) (initial (loader M) x) =
      (run M slots (initial M x)).map (fun out => lift (embed (rawTape x) out)) ∧
    ∀ out, run (loader M) (ticks (2 * x.length + 4) ++ slots)
        (initial (loader M) x) = some out →
      ∀ z, (unpack (out.tape z)).1 = rawTape x z :=
  ⟨loader_run M x, loader_source_exact M x slots, loader_passive M x slots⟩

end PakFixedPolyomino.StandardBitProtectedLoader
