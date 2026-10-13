import PakFixedPolyomino.ULogFiniteTapeZipperRun

/-! ALL raw deterministic runs for arbitrary finite tape alphabets.
The actual blank code2 is explicit for semantic inversion/count transfer.
The accepted-run premise is generic and must be internally realized before
any fixed-pump specialization. No loader or headline claim. -/

namespace PakFixedPolyomino.ULogFiniteAlphabetDeterministicRuns

open ULogCompiler
open ULogFiniteTapeZipperRun
open FiniteOneTapeSemantics (moveHead)

variable {ns nt : Nat}
variable (blank : Fin nt) (hblank : blank.val = ULogSemantics.blankCode)

def FalseOnly (p : BoundedProgram ns nt) : Prop :=
  ∀ (q : Fin ns) (read : Fin nt), p.rule q read true = none

theorem zipperSlotRun_true_eq_none (p : BoundedProgram ns nt)
    (falseOnly : FalseOnly p) (rest : List Bool) (head : Int)
    (z : BoundedConfig ns nt) :
    run p blank (true :: rest) head z = none := by
  dsimp [run]
  cases boundedHalted z with
  | true => rfl
  | false =>
      change (match p.rule z.state z.focus true with
        | none => none
        | some a =>
            run p blank rest (moveHead a.move head)
              (applyBounded blank z a)) = none
      rw [falseOnly]

theorem zipperSlotRun_halted_cons (p : BoundedProgram ns nt)
    {z : BoundedConfig ns nt} (hh : boundedHalted z = true)
    (slot : Bool) (rest : List Bool) (head : Int) :
    run p blank (slot :: rest) head z = none := by
  simp [run, hh]

theorem halted_of_state0 {z : BoundedConfig ns nt} (h : z.state.val = 0) :
    boundedHalted z = true := by
  simp [boundedHalted, h]

theorem zipperSlotRun_cons_false {p : BoundedProgram ns nt}
    {rest : List Bool} {head : Int} {z : BoundedConfig ns nt}
    {hz : Int × BoundedConfig ns nt}
    (h : run p blank (false :: rest) head z = some hz) :
    boundedHalted z = false ∧
      ∃ a, p.rule z.state z.focus false = some a ∧
        run p blank rest (moveHead a.move head)
          (applyBounded blank z a) = some hz := by
  cases hh : boundedHalted z with
  | true =>
      rw [zipperSlotRun_halted_cons blank p hh] at h
      cases h
  | false =>
      dsimp [run] at h
      simp [hh] at h
      cases hr : p.rule z.state z.focus false with
      | none =>
          simp [hr] at h
      | some a =>
          refine ⟨rfl, ⟨a, rfl, ?_⟩⟩
          simpa [hr] using h

theorem successful_zipper_is_false (p : BoundedProgram ns nt)
    (falseOnly : FalseOnly p) {w : List Bool} {head : Int}
    {z : BoundedConfig ns nt} {hz : Int × BoundedConfig ns nt}
    (hw : run p blank w head z = some hz) :
    w = List.replicate w.length false := by
  induction w generalizing head z hz with
  | nil => rfl
  | cons slot rest ih =>
      cases slot with
      | true =>
          rw [zipperSlotRun_true_eq_none blank p falseOnly] at hw
          cases hw
      | false =>
          obtain ⟨_, _, _, hrest⟩ := zipperSlotRun_cons_false blank hw
          have hfalse := ih hrest
          simp only [List.length_cons, List.replicate_succ]
          exact congrArg (List.cons false) hfalse

theorem successful_zipper_length_le (p : BoundedProgram ns nt)
    (falseOnly : FalseOnly p) (L : Nat) (head : Int)
    (z zf : BoundedConfig ns nt) (hf : Int)
    (accepted : run p blank (List.replicate L false) head z =
      some (hf, zf))
    (accepts : zf.state.val = 0) {w : List Bool}
    {hz : Int × BoundedConfig ns nt}
    (hw : run p blank w head z = some hz) :
    w.length ≤ L := by
  have hwfalse := successful_zipper_is_false blank p falseOnly hw
  by_contra hlen
  have hle : L ≤ w.length := by omega
  have hsplit :
      w = List.replicate L false ++
        List.replicate (w.length - L) false := by
    calc
      w = List.replicate w.length false := hwfalse
      _ = List.replicate (L + (w.length - L)) false := by
          rw [Nat.add_sub_of_le hle]
      _ = List.replicate L false ++ List.replicate (w.length - L) false :=
          List.replicate_add L (w.length - L) false
  have hrestlen : 0 < w.length - L := by omega
  rw [hsplit, run_append, accepted] at hw
  have hw' :
      run p blank (List.replicate (w.length - L) false) hf zf = some hz :=
    hw
  cases hpos : w.length - L with
  | zero => omega
  | succ k =>
      rw [hpos, List.replicate_succ, zipperSlotRun_halted_cons blank p
        (halted_of_state0 accepts)] at hw'
      cases hw'

theorem accepting_zipper_word_eq (p : BoundedProgram ns nt)
    (falseOnly : FalseOnly p) (L : Nat) (head : Int)
    (z zf : BoundedConfig ns nt) (hf : Int)
    (accepted : run p blank (List.replicate L false) head z =
      some (hf, zf))
    (accepts : zf.state.val = 0) {w : List Bool} {h' : Int}
    {z' : BoundedConfig ns nt}
    (hw : run p blank w head z = some (h', z'))
    (ha : z'.state.val = 0) :
    w = List.replicate L false ∧ h' = hf ∧ z' = zf := by
  have hwfalse := successful_zipper_is_false blank p falseOnly hw
  have hlen :=
    successful_zipper_length_le blank p falseOnly L head z zf hf accepted accepts hw
  have hk : w.length = L := by
    refine le_antisymm hlen ?_
    by_contra hlt
    have hrestlen : 0 < L - w.length := by omega
    set n := w.length with hn
    have hwrep : w = List.replicate n false := by
      rw [hn]; exact hwfalse
    have hsplit :
        List.replicate L false =
          w ++ List.replicate (L - n) false := by
      have hLn : n ≤ L := by rw [hn]; exact hlen
      rw [hwrep]
      conv_lhs =>
        rw [show L = n + (L - n) from (Nat.add_sub_of_le hLn).symm]
      exact List.replicate_add n (L - n) false
    rw [hsplit, run_append, hw] at accepted
    have accepted' :
        run p blank (List.replicate (L - n) false) h' z' =
          some (hf, zf) :=
      accepted
    have hpos0 : L - n ≠ 0 := by rw [hn]; omega
    cases hpos : L - n with
    | zero => exact (hpos0 hpos).elim
    | succ k =>
        rw [hpos, List.replicate_succ, zipperSlotRun_halted_cons blank p
          (halted_of_state0 ha)] at accepted'
        cases accepted'
  have hwL : w = List.replicate L false := by
    rw [hwfalse, hk]
  refine ⟨hwL, ?_⟩
  have hrun : run p blank (List.replicate L false) head z =
      some (h', z') := by
    rwa [← hwL]
  have heq := hrun.symm.trans accepted
  exact Prod.mk.inj (Option.some.inj heq)

include hblank in
theorem successful_semantic_of_zipper (p : BoundedProgram ns nt)
    {w : List Bool} {head : Int} {z : BoundedConfig ns nt}
    {out : ULogSemantics.Config}
    (hsem : semanticRun (liftConfig p z) w = some out) :
    ∃ hz, run p blank w head z = some hz ∧
      liftConfig p hz.2 = out := by
  have hlift := run_lift p blank hblank w head z
  have hmap : (run p blank w head z).map (fun hz => liftConfig p hz.2) =
      some out := by
    rw [hlift, hsem]
  exact Option.map_eq_some_iff.mp hmap

include hblank in
theorem successful_semantic_length_le (p : BoundedProgram ns nt)
    (falseOnly : FalseOnly p) (L : Nat) (head : Int)
    (z zf : BoundedConfig ns nt) (hf : Int)
    (accepted : run p blank (List.replicate L false) head z =
      some (hf, zf))
    (accepts : zf.state.val = 0) {w : List Bool}
    {out : ULogSemantics.Config}
    (hsem : semanticRun (liftConfig p z) w = some out) :
    w.length ≤ L := by
  obtain ⟨hz, hzip, _⟩ := successful_semantic_of_zipper blank hblank p hsem (head := head)
  exact successful_zipper_length_le blank p falseOnly L head z zf hf accepted
    accepts hzip

include hblank in
theorem accepting_semantic_word_eq (p : BoundedProgram ns nt)
    (falseOnly : FalseOnly p) (L : Nat) (head : Int)
    (z zf : BoundedConfig ns nt) (hf : Int)
    (accepted : run p blank (List.replicate L false) head z =
      some (hf, zf))
    (accepts : zf.state.val = 0) {w : List Bool}
    {out : ULogSemantics.Config}
    (hsem : semanticRun (liftConfig p z) w = some out)
    (ha : out.state = 0) :
    w = List.replicate L false := by
  obtain ⟨hz, hzip, hlift⟩ :=
    successful_semantic_of_zipper blank hblank p hsem (head := head)
  have hstate : hz.2.state.val = 0 := by
    have : (liftConfig p hz.2).state = 0 := by
      rw [hlift, ha]
    simpa [liftConfig] using this
  exact (accepting_zipper_word_eq blank p falseOnly L head z zf hf accepted
    accepts hzip hstate).1

theorem boundedStepSlot_true_none (p : BoundedProgram ns nt)
    (falseOnly : FalseOnly p) (z : BoundedConfig ns nt) :
    boundedStepSlot p blank true z = none := by
  unfold boundedStepSlot
  cases boundedHalted z with
  | true => rfl
  | false =>
      change (p.rule z.state z.focus true).map
          (applyBounded blank z) = none
      rw [falseOnly]
      rfl

theorem boundedStepSlot_false_of_rule {p : BoundedProgram ns nt}
    {z : BoundedConfig ns nt} {a : BoundedAction ns nt}
    (hnh : boundedHalted z = false)
    (hrule : p.rule z.state z.focus false = some a) :
    boundedStepSlot p blank false z =
      some (applyBounded blank z a) := by
  simp [boundedStepSlot, hnh, hrule]

include hblank in
theorem next_false_only (p : BoundedProgram ns nt)
    (falseOnly : FalseOnly p) {z : BoundedConfig ns nt}
    {a : BoundedAction ns nt}
    (hnh : boundedHalted z = false)
    (hrule : p.rule z.state z.focus false = some a) :
    ULogSemantics.next (liftConfig p z) =
      [liftConfig p (applyBounded blank z a)] := by
  rw [next_liftConfig p blank hblank]
  simp [boundedNext, boundedStepSlot_false_of_rule blank hnh hrule,
    boundedStepSlot_true_none blank p falseOnly]

theorem zipperSlotRun_replicate_succ {p : BoundedProgram ns nt}
    {n : Nat} {head : Int} {z : BoundedConfig ns nt}
    {hz : Int × BoundedConfig ns nt}
    (h : run p blank (List.replicate (n + 1) false) head z = some hz) :
    boundedHalted z = false ∧
      ∃ a, p.rule z.state z.focus false = some a ∧
        run p blank (List.replicate n false) (moveHead a.move head)
          (applyBounded blank z a) = some hz := by
  simpa [List.replicate_succ] using zipperSlotRun_cons_false blank h

include hblank in
/-- Actual `acceptingPaths` threshold: one accepting word of length `L`,
counted at every clock `T ≥ L` and nowhere earlier. -/
theorem acceptingPaths_threshold (p : BoundedProgram ns nt)
    (falseOnly : FalseOnly p) (L : Nat) (head : Int)
    (z zf : BoundedConfig ns nt) (hf : Int)
    (accepted : run p blank (List.replicate L false) head z =
      some (hf, zf))
    (accepts : zf.state.val = 0) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T (liftConfig p z) =
      if L ≤ T then 1 else 0 := by
  induction L generalizing head z hf zf T with
  | zero =>
      have hz : head = hf ∧ z = zf := by
        simpa [run] using accepted
      rcases hz with ⟨_, rfl⟩
      have ha : ULogSemantics.accepting (liftConfig p z) = true := by
        simp [ULogSemantics.accepting, ULogSemantics.acceptCode, liftConfig,
          accepts]
      have hh : ULogSemantics.halted (liftConfig p z) = true :=
        ULogSemantics.accepting_halted ha
      simpa using
        BinaryNondeterministicMachine.acceptingPaths_halt_accept
          ULogSemantics.machine hh ha T
  | succ L ih =>
      obtain ⟨hnh, a, hrule, hrest⟩ := zipperSlotRun_replicate_succ blank accepted
      cases T with
      | zero =>
          have hh : ULogSemantics.halted (liftConfig p z) = false := hnh
          simp [BinaryNondeterministicMachine.acceptingPaths,
            ULogSemantics.machine, hh]
      | succ T =>
          have hh : ULogSemantics.halted (liftConfig p z) = false := hnh
          have hpaths :=
            BinaryNondeterministicMachine.acceptingPaths_succ_nonhalt
              ULogSemantics.machine hh T
          rw [hpaths]
          change (List.map (ULogSemantics.machine.acceptingPaths T)
              (ULogSemantics.next (liftConfig p z))).sum = _
          rw [next_false_only blank hblank p falseOnly hnh hrule]
          simp
          exact ih (moveHead a.move head) (applyBounded blank z a) zf hf
            hrest accepts T

end PakFixedPolyomino.ULogFiniteAlphabetDeterministicRuns
