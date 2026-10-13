import PakFixedPolyomino.ULogFiniteTapeGuardedStageCompositionRuns
import PakFixedPolyomino.ULogFiniteProgramZipperRunBridge

/-! ALL labelled leaf and cutoff-count transfer across the real two-tick
highest-state guard. First-stage `FalseOnly` and one genuine accepted child
run are explicit intermediate hypotheses. Child `q` stays fully
nondeterministic. Concrete Entry/Loop/FreshScanner instantiation and the
original headline remain open. -/

namespace PakFixedPolyomino.ULogFiniteTapeGuardedStageLeafCounts

open ULogCompiler
open ULogFiniteTapeZipperRun (run run_lift run_append)
open ULogFiniteTapeGuardedStageComposition
open ULogFiniteTapeGuardedStageCompositionRuns
open ULogFiniteAlphabetDeterministicRuns
open ULogFiniteProgramZipperRunBridge
open FiniteOneTapeSemantics (moveHead)

variable {ns ms : Nat}

theorem zipperSlotRun_eq_run (p : BoundedProgram ns 3)
    (w : List Bool) (head : Int) (z : BoundedConfig ns 3) :
    zipperSlotRun p w head z = run p (2 : Fin 3) w head z := by
  induction w generalizing head z with
  | nil => rfl
  | cons slot rest ih =>
      dsimp [zipperSlotRun, run]
      cases boundedHalted z with
      | true => rfl
      | false =>
          cases p.rule z.state z.focus slot with
          | none => rfl
          | some a => exact ih _ _

theorem whole_word (D : Nat) (v : List Bool) :
    List.replicate D false ++ false :: false :: v =
      List.replicate (D + 2) false ++ v := by
  have h : List.replicate (D + 2) false =
      List.replicate D false ++ [false, false] := by
    rw [show D + 2 = D + 1 + 1 by omega, List.replicate_succ, List.replicate_add,
      List.replicate_succ, List.replicate_zero]; simp
  rw [h, List.append_assoc]; simp

theorem drop_prefix (D : Nat) (v : List Bool) :
    (List.replicate (D + 2) false ++ v).drop (D + 2) = v := by
  simp [List.length_replicate]

theorem step_false_apply {p : BoundedProgram ns 3} {head hf : Int}
    {z zf : BoundedConfig ns 3}
    (h : run p (2 : Fin 3) [false] head z = some (hf, zf)) :
    boundedHalted z = false ∧
      boundedStepSlot p (2 : Fin 3) false z = some zf := by
  obtain ⟨hlive, a, hrule, hrest⟩ := zipperSlotRun_cons_false (2 : Fin 3) h
  have heq := Prod.mk.inj (Option.some.inj (by simpa [run] using hrest))
  exact ⟨hlive, by simp [boundedStepSlot, hlive, hrule, heq.2]⟩

theorem semantic_of_run (p : BoundedProgram ns 3) (w : List Bool)
    (head hf : Int) (z zf : BoundedConfig ns 3)
    (hzip : run p (2 : Fin 3) w head z = some (hf, zf)) :
    semanticRun (liftConfig p z) w = some (liftConfig p zf) := by
  have h := zipperSlotRun_lift p w head z
  rw [zipperSlotRun_eq_run, hzip] at h; simpa using h.symm

theorem run_of_semantic (p : BoundedProgram ns 3) (w : List Bool)
    (head : Int) (z : BoundedConfig ns 3) (out : ULogSemantics.Config)
    (hsem : semanticRun (liftConfig p z) w = some out) :
    ∃ hf zf, run p (2 : Fin 3) w head z = some (hf, zf) ∧
      liftConfig p zf = out := by
  have hmap :
      (zipperSlotRun p w head z).map (fun hz => liftConfig p hz.2) = some out := by
    rw [zipperSlotRun_lift, hsem]
  obtain ⟨hz, hzip, hlift⟩ := Option.map_eq_some_iff.mp hmap
  rw [zipperSlotRun_eq_run] at hzip; exact ⟨hz.1, hz.2, hzip, hlift⟩

theorem lift_state0 (p : BoundedProgram ns 3) (z : BoundedConfig ns 3) :
    (liftConfig p z).state = 0 ↔ z.state.val = 0 := by simp [liftConfig]

section Bridge
variable (p : BoundedProgram ns 3) (q : BoundedProgram ms 3)
variable (hns : 3 ≤ ns) (hms : 3 ≤ ms) (handoff : OneTapeTableau.Move)

theorem accepting_whole_split (z zp : BoundedConfig ns 3)
    (H mid : Int) (D : Nat) (hpFalse : FalseOnly p)
    (hp : run p (2 : Fin 3) (List.replicate D false) H z = some (mid, zp))
    (ha : zp.state.val = 0) (w : List Bool) (hf : Int)
    (zf : BoundedConfig (stateCount ns ms) 3)
    (hw : run (program p q hns hms handoff) (2 : Fin 3) w H (leftConfig z) =
      some (hf, zf)) (hacc : zf.state.val = 0) :
    ∃ v zq, w = List.replicate D false ++ false :: false :: v ∧
      run q (2 : Fin 3) v (moveHead handoff mid)
        (secondStart hms (2 : Fin 3) handoff zp) = some (hf, zq) ∧
      zq.state.val = 0 ∧ zf = rightConfig zq := by
  obtain ⟨u, v, mid', zp', zq, he, hp', hap, hq, hqa, hz⟩ :=
    every_accepting_run_splits p q hns hms handoff (2 : Fin 3) w H hf z zf hw hacc
  obtain ⟨rfl, rfl, rfl⟩ :=
    accepting_zipper_word_eq (2 : Fin 3) p hpFalse D H z zp mid hp ha hp' hap
  exact ⟨v, zq, he, hq, hqa, hz⟩

theorem accepting_whole_inverse (z zp : BoundedConfig ns 3)
    (H mid : Int) (D : Nat)
    (hp : run p (2 : Fin 3) (List.replicate D false) H z = some (mid, zp))
    (ha : zp.state.val = 0) (v : List Bool) (hf : Int) (zq : BoundedConfig ms 3)
    (hv : run q (2 : Fin 3) v (moveHead handoff mid)
      (secondStart hms (2 : Fin 3) handoff zp) = some (hf, zq)) :
    run (program p q hns hms handoff) (2 : Fin 3)
      (List.replicate D false ++ false :: false :: v) H (leftConfig z) =
      some (hf, rightConfig zq) :=
  sequential_run p q hns hms handoff (2 : Fin 3) (List.replicate D false) v
    H mid hf z zp zq hp ha hv

theorem all_raw_length_le (z zp : BoundedConfig ns 3)
    (H mid : Int) (D : Nat) (hpFalse : FalseOnly p)
    (hp : run p (2 : Fin 3) (List.replicate D false) H z = some (mid, zp))
    (ha : zp.state.val = 0) (Q : Nat)
    (hQ : ∀ v hf zq, run q (2 : Fin 3) v (moveHead handoff mid)
      (secondStart hms (2 : Fin 3) handoff zp) = some (hf, zq) → v.length ≤ Q)
    (w : List Bool) (hf : Int) (zf : BoundedConfig (stateCount ns ms) 3)
    (hw : run (program p q hns hms handoff) (2 : Fin 3) w H (leftConfig z) =
      some (hf, zf)) : w.length ≤ D + 2 + Q := by
  rcases deterministic_first_stage_split p q hns hms handoff (2 : Fin 3)
      hpFalse D H mid z zp hp ha w hf zf hw with hfirst | hguard | hsecond
  · obtain ⟨hlen, _, _, _⟩ := hfirst; omega
  · obtain ⟨rfl, _, _⟩ := hguard
    simp [List.length_replicate]; omega
  · obtain ⟨v, zq, rfl, hq, _⟩ := hsecond
    have hv := hQ v hf zq hq
    simp [List.length_append, List.length_cons, List.length_replicate]; omega

theorem boundedStepSlot_right (slot : Bool) (zq : BoundedConfig ms 3) :
    boundedStepSlot (program p q hns hms handoff) (2 : Fin 3) slot (rightConfig zq) =
      (boundedStepSlot q (2 : Fin 3) slot zq).map rightConfig := by
  unfold boundedStepSlot; rw [right_halted]
  cases hh : boundedHalted zq with
  | true => simp
  | false =>
      rw [show (rightConfig (ns := ns) zq).state = rightState zq.state by rfl,
        show (rightConfig (ns := ns) zq).focus = zq.focus by rfl,
        rule_right p q hns hms handoff zq slot hh]
      cases q.rule zq.state zq.focus slot with
      | none => simp
      | some a => simp [apply_right]

theorem boundedNext_right (zq : BoundedConfig ms 3) :
    boundedNext (program p q hns hms handoff) (2 : Fin 3) (rightConfig zq) =
      (boundedNext q (2 : Fin 3) zq).map rightConfig := by
  unfold boundedNext
  rw [boundedStepSlot_right p q hns hms handoff false zq,
    boundedStepSlot_right p q hns hms handoff true zq]
  cases boundedStepSlot q (2 : Fin 3) false zq <;>
    cases boundedStepSlot q (2 : Fin 3) true zq <;> rfl

theorem right_halted_sem (zq : BoundedConfig ms 3) :
    ULogSemantics.halted
      (liftConfig (program p q hns hms handoff) (rightConfig zq)) =
      ULogSemantics.halted (liftConfig q zq) := by
  change boundedHalted (rightConfig (ns := ns) zq) = boundedHalted zq
  exact right_halted zq

theorem right_accept_sem (zq : BoundedConfig ms 3) :
    ULogSemantics.accepting
      (liftConfig (program p q hns hms handoff) (rightConfig zq)) =
      ULogSemantics.accepting (liftConfig q zq) := by
  simp [ULogSemantics.accepting, ULogSemantics.acceptCode, liftConfig]
  by_cases h : zq.state.val = 0
  · simp [h, (right_accepts_iff (ns := ns) zq).mpr h]
  · simp [h, mt (right_accepts_iff (ns := ns) zq).mp h]

theorem right_acceptingPaths (zq : BoundedConfig ms 3) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T
      (liftConfig (program p q hns hms handoff) (rightConfig zq)) =
      ULogSemantics.machine.acceptingPaths T (liftConfig q zq) := by
  induction T generalizing zq with
  | zero =>
      simp [BinaryNondeterministicMachine.acceptingPaths, ULogSemantics.machine,
        right_halted_sem p q hns hms handoff zq,
        right_accept_sem p q hns hms handoff zq]
      rfl
  | succ T ih =>
      have hhalt := right_halted_sem p q hns hms handoff zq
      cases hh : ULogSemantics.halted (liftConfig q zq) with
      | true =>
          have hP : ULogSemantics.halted
              (liftConfig (program p q hns hms handoff) (rightConfig zq)) = true :=
            hhalt.trans hh
          simp [BinaryNondeterministicMachine.acceptingPaths, ULogSemantics.machine,
            hP, hh, right_accept_sem p q hns hms handoff zq]
          rfl
      | false =>
          have hP : ULogSemantics.halted
              (liftConfig (program p q hns hms handoff) (rightConfig zq)) = false :=
            hhalt.trans hh
          rw [BinaryNondeterministicMachine.acceptingPaths_succ_nonhalt
              ULogSemantics.machine hP,
            BinaryNondeterministicMachine.acceptingPaths_succ_nonhalt
              ULogSemantics.machine hh]
          change ((ULogSemantics.next
                (liftConfig (program p q hns hms handoff) (rightConfig zq))).map
              (fun c : ULogSemantics.Config =>
                ULogSemantics.machine.acceptingPaths T c)).sum =
            ((ULogSemantics.next (liftConfig q zq)).map
              (fun c : ULogSemantics.Config =>
                ULogSemantics.machine.acceptingPaths T c)).sum
          rw [next_liftConfig (program p q hns hms handoff) (2 : Fin 3) rfl,
            next_liftConfig q (2 : Fin 3) rfl,
            boundedNext_right p q hns hms handoff]
          suffices ∀ l : List (BoundedConfig ms 3),
              (((l.map rightConfig).map
                  (liftConfig (program p q hns hms handoff))).map
                (fun c : ULogSemantics.Config =>
                  ULogSemantics.machine.acceptingPaths T c)).sum =
              ((l.map (liftConfig q)).map
                (fun c : ULogSemantics.Config =>
                  ULogSemantics.machine.acceptingPaths T c)).sum by
            exact this (boundedNext q (2 : Fin 3) zq)
          intro l
          induction l with
          | nil => rfl
          | cons z' rest ihL =>
              simp only [List.map_cons]
              rw [List.sum_cons, List.sum_cons, ih z', ihL]

theorem boundedStepSlot_left_live (z : BoundedConfig ns 3)
    (hl : boundedHalted z = false) (slot : Bool) :
    boundedStepSlot (program p q hns hms handoff) (2 : Fin 3) slot (leftConfig z) =
      (boundedStepSlot p (2 : Fin 3) slot z).map leftConfig := by
  unfold boundedStepSlot
  have hL := left_live (ms := ms) z hl
  simp [hl, hL]
  rw [show (leftConfig (ms := ms) z).state = leftState z.state by rfl,
    show (leftConfig (ms := ms) z).focus = z.focus by rfl,
    rule_left p q hns hms handoff z slot hl]
  cases p.rule z.state z.focus slot with
  | none => simp
  | some a => simp [apply_left]

theorem next_left_falseOnly (hpFalse : FalseOnly p) (z : BoundedConfig ns 3)
    (hl : boundedHalted z = false) {a : BoundedAction ns 3}
    (hrule : p.rule z.state z.focus false = some a) :
    ULogSemantics.next (liftConfig (program p q hns hms handoff) (leftConfig z)) =
      [liftConfig (program p q hns hms handoff)
        (leftConfig (applyBounded (2 : Fin 3) z a))] := by
  rw [next_liftConfig (program p q hns hms handoff) (2 : Fin 3) rfl]
  have hf : boundedStepSlot (program p q hns hms handoff) (2 : Fin 3) false
      (leftConfig z) = some (leftConfig (applyBounded (2 : Fin 3) z a)) := by
    rw [boundedStepSlot_left_live p q hns hms handoff z hl]
    simp [boundedStepSlot, hl, hrule]
  have ht : boundedStepSlot (program p q hns hms handoff) (2 : Fin 3) true
      (leftConfig z) = none := by
    rw [boundedStepSlot_left_live p q hns hms handoff z hl]
    simp [boundedStepSlot, hl, hpFalse z.state z.focus]
  simp [boundedNext, hf, ht]

theorem next_first_handoff (z : BoundedConfig ns 3) (hz : z.state.val = 0) :
    ULogSemantics.next (liftConfig (program p q hns hms handoff) (leftConfig z)) =
      [liftConfig (program p q hns hms handoff)
        (guardConfig (2 : Fin 3) handoff z)] := by
  rw [next_liftConfig (program p q hns hms handoff) (2 : Fin 3) rfl]
  have hf := (step_false_apply
    (first_handoff_run p q hns hms handoff (2 : Fin 3) 0 z hz)).2
  have ht : boundedStepSlot (program p q hns hms handoff) (2 : Fin 3) true
      (leftConfig z) = none := by
    have hl := left_accept_live (ms := ms) hns z hz
    simp [boundedStepSlot, program, leftConfig, leftState, hz]
  simp [boundedNext, hf, ht]

theorem next_second_handoff (z : BoundedConfig ns 3) :
    ULogSemantics.next (liftConfig (program p q hns hms handoff)
        (guardConfig (2 : Fin 3) handoff z)) =
      [liftConfig (program p q hns hms handoff)
        (rightConfig (secondStart hms (2 : Fin 3) handoff z))] := by
  rw [next_liftConfig (program p q hns hms handoff) (2 : Fin 3) rfl]
  have hf := (step_false_apply
    (second_handoff_run p q hns hms handoff (2 : Fin 3) 0 z)).2
  have ht : boundedStepSlot (program p q hns hms handoff) (2 : Fin 3) true
      (guardConfig (2 : Fin 3) handoff z) = none := by
    have hs := guard_state (ms := ms) (2 : Fin 3) handoff z
    have hl : boundedHalted (guardConfig (ms := ms) (2 : Fin 3) handoff z) =
        false := by simp [boundedHalted, hs]; omega
    simp [boundedStepSlot, hl, program, hs]
  simp [boundedNext, hf, ht]

theorem guard_live (z : BoundedConfig ns 3) :
    ULogSemantics.halted (liftConfig (program p q hns hms handoff)
      (guardConfig (2 : Fin 3) handoff z)) = false := by
  change boundedHalted (guardConfig (ms := ms) (2 : Fin 3) handoff z) = false
  simp [boundedHalted, guard_state (ms := ms) (2 : Fin 3) handoff z]; omega

theorem cutoff_acceptingPaths (z zp : BoundedConfig ns 3)
    (H mid : Int) (D : Nat) (hpFalse : FalseOnly p)
    (hp : run p (2 : Fin 3) (List.replicate D false) H z = some (mid, zp))
    (ha : zp.state.val = 0) (T : Nat) :
    ULogSemantics.machine.acceptingPaths T
      (liftConfig (program p q hns hms handoff) (leftConfig z)) =
      if D + 2 ≤ T then
        ULogSemantics.machine.acceptingPaths (T - (D + 2))
          (liftConfig q (secondStart hms (2 : Fin 3) handoff zp))
      else 0 := by
  induction D generalizing H z mid zp T with
  | zero =>
      have hz : H = mid ∧ z = zp := by simpa [run] using hp
      rcases hz with ⟨rfl, rfl⟩
      have hlive : ULogSemantics.halted
          (liftConfig (program p q hns hms handoff) (leftConfig z)) = false :=
        left_accept_live (ms := ms) hns z ha
      cases T with
      | zero =>
          simp [BinaryNondeterministicMachine.acceptingPaths,
            ULogSemantics.machine, hlive]
      | succ T =>
          rw [BinaryNondeterministicMachine.acceptingPaths_succ_nonhalt
            ULogSemantics.machine hlive T]
          change ((ULogSemantics.next
                (liftConfig (program p q hns hms handoff) (leftConfig z))).map
              (ULogSemantics.machine.acceptingPaths T)).sum = _
          rw [next_first_handoff p q hns hms handoff z ha]
          dsimp only [ULogSemantics.machine]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            Nat.add_zero]
          change ULogSemantics.machine.acceptingPaths T
              (liftConfig (program p q hns hms handoff)
                (guardConfig (2 : Fin 3) handoff z)) = _
          cases T with
          | zero =>
              simp [BinaryNondeterministicMachine.acceptingPaths,
                ULogSemantics.machine, guard_live p q hns hms handoff z]
          | succ T =>
              rw [BinaryNondeterministicMachine.acceptingPaths_succ_nonhalt
                ULogSemantics.machine (guard_live p q hns hms handoff z) T]
              change ((ULogSemantics.next
                    (liftConfig (program p q hns hms handoff)
                      (guardConfig (2 : Fin 3) handoff z))).map
                  (ULogSemantics.machine.acceptingPaths T)).sum = _
              rw [next_second_handoff p q hns hms handoff z]
              dsimp only [ULogSemantics.machine]
              simp only [List.map_cons, List.map_nil, List.sum_cons,
                List.sum_nil, Nat.add_zero]
              have hle : 2 ≤ T + 1 + 1 := by omega
              simp [hle]
              simpa only [ULogSemantics.machine] using
                right_acceptingPaths p q hns hms handoff
                  (secondStart hms (2 : Fin 3) handoff z) T
  | succ D ih =>
      obtain ⟨hnh, a, hrule, hrest⟩ := zipperSlotRun_replicate_succ (2 : Fin 3) hp
      have hlive : ULogSemantics.halted
          (liftConfig (program p q hns hms handoff) (leftConfig z)) = false :=
        left_live (ms := ms) z hnh
      cases T with
      | zero =>
          simp [BinaryNondeterministicMachine.acceptingPaths,
            ULogSemantics.machine, hlive]
      | succ T =>
          rw [BinaryNondeterministicMachine.acceptingPaths_succ_nonhalt
            ULogSemantics.machine hlive T]
          change ((ULogSemantics.next
                (liftConfig (program p q hns hms handoff) (leftConfig z))).map
              (ULogSemantics.machine.acceptingPaths T)).sum = _
          rw [next_left_falseOnly p q hns hms handoff hpFalse z hnh hrule]
          dsimp only [ULogSemantics.machine]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            Nat.add_zero]
          change ULogSemantics.machine.acceptingPaths T
              (liftConfig (program p q hns hms handoff)
                (leftConfig (applyBounded (2 : Fin 3) z a))) =
            if D + 1 + 2 ≤ T + 1 then
              ULogSemantics.machine.acceptingPaths (T + 1 - (D + 1 + 2))
                (liftConfig q (secondStart hms (2 : Fin 3) handoff zp))
            else 0
          have hif :
              (if D + 1 + 2 ≤ T + 1 then
                ULogSemantics.machine.acceptingPaths (T + 1 - (D + 1 + 2))
                  (liftConfig q (secondStart hms (2 : Fin 3) handoff zp))
              else 0) =
              (if D + 2 ≤ T then
                ULogSemantics.machine.acceptingPaths (T - (D + 2))
                  (liftConfig q (secondStart hms (2 : Fin 3) handoff zp))
              else 0) := by
            have hiff : D + 1 + 2 ≤ T + 1 ↔ D + 2 ≤ T := by omega
            have hsub : T + 1 - (D + 1 + 2) = T - (D + 2) := by omega
            simp [hiff, hsub]
          rw [hif]
          exact ih (applyBounded (2 : Fin 3) z a) zp (moveHead a.move H) mid
            hrest ha T

noncomputable def dropLeaf (z zp : BoundedConfig ns 3)
    (H mid : Int) (D : Nat) (hpFalse : FalseOnly p)
    (hp : run p (2 : Fin 3) (List.replicate D false) H z = some (mid, zp))
    (ha : zp.state.val = 0)
    (leaf : SemanticLeaves (program p q hns hms handoff) (leftConfig z)) :
    SemanticLeaves q (secondStart hms (2 : Fin 3) handoff zp) :=
  ⟨leaf.1.drop (D + 2), by
    obtain ⟨out, hsem, hacc⟩ := leaf.2
    obtain ⟨hf, zf, hzip, hlift⟩ :=
      run_of_semantic (program p q hns hms handoff) leaf.1 H (leftConfig z) out hsem
    have hst : zf.state.val = 0 :=
      (lift_state0 (program p q hns hms handoff) zf).mp (by simpa [hlift] using hacc)
    obtain ⟨v, zq, he, hq, hqa, _⟩ :=
      accepting_whole_split p q hns hms handoff z zp H mid D hpFalse hp ha
        leaf.1 hf zf hzip hst
    have hv : leaf.1.drop (D + 2) = v := by rw [he, whole_word, drop_prefix]
    refine ⟨liftConfig q zq, ?_, (lift_state0 q zq).mpr hqa⟩
    rw [hv]
    exact semantic_of_run q v (moveHead handoff mid) hf
      (secondStart hms (2 : Fin 3) handoff zp) zq hq⟩

noncomputable def prefixLeaf (z zp : BoundedConfig ns 3)
    (H mid : Int) (D : Nat)
    (hp : run p (2 : Fin 3) (List.replicate D false) H z = some (mid, zp))
    (ha : zp.state.val = 0)
    (leaf : SemanticLeaves q (secondStart hms (2 : Fin 3) handoff zp)) :
    SemanticLeaves (program p q hns hms handoff) (leftConfig z) :=
  ⟨List.replicate (D + 2) false ++ leaf.1, by
    obtain ⟨out, hsem, hacc⟩ := leaf.2
    obtain ⟨hf, zq, hzip, hlift⟩ :=
      run_of_semantic q leaf.1 (moveHead handoff mid)
        (secondStart hms (2 : Fin 3) handoff zp) out hsem
    have hqa : zq.state.val = 0 :=
      (lift_state0 q zq).mp (by simpa [hlift] using hacc)
    have hP := accepting_whole_inverse p q hns hms handoff z zp H mid D hp ha
      leaf.1 hf zq hzip
    refine ⟨liftConfig (program p q hns hms handoff) (rightConfig zq), ?_, ?_⟩
    · rw [← whole_word]
      exact semantic_of_run (program p q hns hms handoff)
        (List.replicate D false ++ false :: false :: leaf.1) H hf
        (leftConfig z) (rightConfig zq) hP
    · exact (lift_state0 (program p q hns hms handoff) (rightConfig zq)).mpr
        ((right_accepts_iff (ns := ns) zq).mpr hqa)⟩

noncomputable def leafEquiv (z zp : BoundedConfig ns 3)
    (H mid : Int) (D : Nat) (hpFalse : FalseOnly p)
    (hp : run p (2 : Fin 3) (List.replicate D false) H z = some (mid, zp))
    (ha : zp.state.val = 0) :
    SemanticLeaves (program p q hns hms handoff) (leftConfig z) ≃
      SemanticLeaves q (secondStart hms (2 : Fin 3) handoff zp) where
  toFun := dropLeaf p q hns hms handoff z zp H mid D hpFalse hp ha
  invFun := prefixLeaf p q hns hms handoff z zp H mid D hp ha
  left_inv := fun leaf => by
    apply Subtype.ext; dsimp [dropLeaf, prefixLeaf]
    obtain ⟨out, hsem, hacc⟩ := leaf.2
    obtain ⟨hf, zf, hzip, hlift⟩ :=
      run_of_semantic (program p q hns hms handoff) leaf.1 H (leftConfig z) out hsem
    have hst : zf.state.val = 0 :=
      (lift_state0 (program p q hns hms handoff) zf).mp (by simpa [hlift] using hacc)
    obtain ⟨v, zq, he, hq, hqa, _⟩ :=
      accepting_whole_split p q hns hms handoff z zp H mid D hpFalse hp ha
        leaf.1 hf zf hzip hst
    have hv : leaf.1.drop (D + 2) = v := by rw [he, whole_word, drop_prefix]
    rw [hv, ← whole_word, he]
  right_inv := fun leaf => by
    apply Subtype.ext; dsimp [dropLeaf, prefixLeaf]; exact drop_prefix D leaf.1

theorem leafEquiv_laws (z zp : BoundedConfig ns 3)
    (H mid : Int) (D : Nat) (hpFalse : FalseOnly p)
    (hp : run p (2 : Fin 3) (List.replicate D false) H z = some (mid, zp))
    (ha : zp.state.val = 0) :
    let e := leafEquiv p q hns hms handoff z zp H mid D hpFalse hp ha
    (∀ leaf, (e leaf).1 = leaf.1.drop (D + 2)) ∧
    (∀ leaf, leaf.1 = List.replicate (D + 2) false ++ (e leaf).1) ∧
    (∀ leaf, (e leaf).1.length + (D + 2) = leaf.1.length) ∧
    (∀ leaf, (e.symm leaf).1 = List.replicate (D + 2) false ++ leaf.1) ∧
    Nat.card (SemanticLeaves (program p q hns hms handoff) (leftConfig z)) =
      Nat.card (SemanticLeaves q (secondStart hms (2 : Fin 3) handoff zp)) := by
  refine ⟨fun _ => rfl, ?_, ?_, fun _ => rfl,
    Nat.card_congr (leafEquiv p q hns hms handoff z zp H mid D hpFalse hp ha)⟩
  · intro leaf
    exact (congrArg Subtype.val
      ((leafEquiv p q hns hms handoff z zp H mid D hpFalse hp ha).left_inv leaf)).symm
  · intro leaf
    rw [show leaf.1 = List.replicate (D + 2) false ++
          (leafEquiv p q hns hms handoff z zp H mid D hpFalse hp ha leaf).1 from
      (congrArg Subtype.val
        ((leafEquiv p q hns hms handoff z zp H mid D hpFalse hp ha).left_inv
          leaf)).symm]
    simp [List.length_append, List.length_replicate]
    omega

def guarded_stage_leaf_count_spec (z zp : BoundedConfig ns 3)
    (H mid : Int) (D : Nat) (_hpFalse : FalseOnly p)
    (_hp : run p (2 : Fin 3) (List.replicate D false) H z = some (mid, zp))
    (_ha : zp.state.val = 0) : Prop :=
  let P := program p q hns hms handoff
  let s := secondStart hms (2 : Fin 3) handoff zp
  (run P (2 : Fin 3) [false] mid (leftConfig zp) =
      some (moveHead handoff mid, guardConfig (2 : Fin 3) handoff zp)) ∧
  (run P (2 : Fin 3) [false] (moveHead handoff mid)
      (guardConfig (2 : Fin 3) handoff zp) =
      some (moveHead handoff mid, rightConfig s)) ∧
  ((guardConfig (ms := ms) (2 : Fin 3) handoff zp).state.val = ns + ms) ∧
  (∀ w hf zf, run P (2 : Fin 3) w H (leftConfig z) = some (hf, zf) →
    zf.state.val = 0 → ∃ v zq, w = List.replicate D false ++ false :: false :: v ∧
      run q (2 : Fin 3) v (moveHead handoff mid) s = some (hf, zq) ∧
      zq.state.val = 0 ∧ zf = rightConfig zq) ∧
  (∀ v hf zq, run q (2 : Fin 3) v (moveHead handoff mid) s = some (hf, zq) →
    zq.state.val = 0 →
      run P (2 : Fin 3) (List.replicate D false ++ false :: false :: v) H
        (leftConfig z) = some (hf, rightConfig zq)) ∧
  (∃ e : SemanticLeaves P (leftConfig z) ≃ SemanticLeaves q s,
    (∀ leaf, (e leaf).1 = leaf.1.drop (D + 2)) ∧
    (∀ leaf, leaf.1 = List.replicate (D + 2) false ++ (e leaf).1) ∧
    (∀ leaf, (e leaf).1.length + (D + 2) = leaf.1.length) ∧
    (∀ leaf, (e.symm leaf).1 = List.replicate (D + 2) false ++ leaf.1) ∧
    Nat.card (SemanticLeaves P (leftConfig z)) = Nat.card (SemanticLeaves q s)) ∧
  (∀ T, ULogSemantics.machine.acceptingPaths T (liftConfig P (leftConfig z)) =
      if D + 2 ≤ T then
        ULogSemantics.machine.acceptingPaths (T - (D + 2)) (liftConfig q s)
      else 0) ∧
  (∀ Q, (∀ v hf zq, run q (2 : Fin 3) v (moveHead handoff mid) s = some (hf, zq) →
      v.length ≤ Q) →
    ∀ w hf zf, run P (2 : Fin 3) w H (leftConfig z) = some (hf, zf) →
      w.length ≤ D + 2 + Q)

theorem guarded_stage_leaf_count_spec_holds (z zp : BoundedConfig ns 3)
    (H mid : Int) (D : Nat) (hpFalse : FalseOnly p)
    (hp : run p (2 : Fin 3) (List.replicate D false) H z = some (mid, zp))
    (ha : zp.state.val = 0) :
    guarded_stage_leaf_count_spec p q hns hms handoff z zp H mid D hpFalse hp ha := by
  refine ⟨first_handoff_run p q hns hms handoff (2 : Fin 3) mid zp ha,
    second_handoff_run p q hns hms handoff (2 : Fin 3) (moveHead handoff mid) zp,
    guard_state (ms := ms) (2 : Fin 3) handoff zp,
    accepting_whole_split p q hns hms handoff z zp H mid D hpFalse hp ha, ?_,
    ⟨leafEquiv p q hns hms handoff z zp H mid D hpFalse hp ha,
      (leafEquiv_laws p q hns hms handoff z zp H mid D hpFalse hp ha).1,
      (leafEquiv_laws p q hns hms handoff z zp H mid D hpFalse hp ha).2.1,
      (leafEquiv_laws p q hns hms handoff z zp H mid D hpFalse hp ha).2.2.1,
      (leafEquiv_laws p q hns hms handoff z zp H mid D hpFalse hp ha).2.2.2.1,
      (leafEquiv_laws p q hns hms handoff z zp H mid D hpFalse hp ha).2.2.2.2⟩,
    cutoff_acceptingPaths p q hns hms handoff z zp H mid D hpFalse hp ha,
    all_raw_length_le p q hns hms handoff z zp H mid D hpFalse hp ha⟩
  intro v hf zq hv _; exact accepting_whole_inverse p q hns hms handoff z zp H mid D
    hp ha v hf zq hv

end Bridge

end PakFixedPolyomino.ULogFiniteTapeGuardedStageLeafCounts
