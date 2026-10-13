import PakFixedPolyomino.StandardMachineNondeterministicFeedback

/-! Causal ALL-successful-prefix bound on the feedback machine.
Each later-phase cost and each return uses the actual origin I-entry together
with the complete executed component histories, never an arbitrary H-accept. -/
set_option maxHeartbeats 0
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace PakFixedPolyomino.StandardMachineNondeterministicFeedbackReachable
noncomputable section
open StandardNondeterministicMachine StandardBitTime
open StandardMachineNondeterministicFeedback

variable {nsP nsM nsH nt nb : Nat}

structure CausalPremises (P : DeterministicMachine nsP nt)
    (M : Machine nsM nt nb) (H : DeterministicMachine nsH nt)
    (I : Configuration nsP nt → Prop) (r : Configuration nsP nt → Nat)
    (A B C : Nat) : Prop where
  hP : ∀ cP, I cP → ∀ a p, run P (ticks a) cP = some p → a ≤ A
  hH1 : ∀ cP a p, I cP →
    run P (ticks a) cP = some p → p.state = P.accept → p.tape p.head = P.one →
    ∀ b h1, run H (ticks b) (restartH H p) = some h1 → b ≤ C
  hM : ∀ cP a p b h1, I cP →
    run P (ticks a) cP = some p → p.state = P.accept → p.tape p.head = P.one →
    run H (ticks b) (restartH H p) = some h1 → h1.state = H.accept →
    ∀ u m, run M u (restartM M h1) = some m → u.length ≤ B
  hH2 : ∀ cP a p b h1 u m, I cP →
    run P (ticks a) cP = some p → p.state = P.accept → p.tape p.head = P.one →
    run H (ticks b) (restartH H p) = some h1 → h1.state = H.accept →
    run M u (restartM M h1) = some m → m.state = M.accept →
    m.tape m.head = M.one →
    ∀ d h2, run H (ticks d) (restartH H m) = some h2 → d ≤ C
  hret : ∀ cP a p b h1 u m d h2, I cP →
    run P (ticks a) cP = some p → p.state = P.accept → p.tape p.head = P.one →
    run H (ticks b) (restartH H p) = some h1 → h1.state = H.accept →
    run M u (restartM M h1) = some m → m.state = M.accept →
    m.tape m.head = M.one →
    run H (ticks d) (restartH H m) = some h2 → h2.state = H.accept →
    I (restartP P h2) ∧ r (restartP P h2) < r cP

theorem ticks_succ (n : Nat) : ticks (n + 1) = ticks n ++ [0] := by
  rw [ticks_add n 1]; rfl

theorem run_ticks_zero {ns : Nat} (S : DeterministicMachine ns nt)
    (c : Configuration ns nt) : run S (ticks 0) c = some c := by
  simp [ticks]

theorem run_ticks_succ {ns : Nat} (S : DeterministicMachine ns nt)
    (origin c c' : Configuration ns nt) (t : Nat)
    (hpre : run S (ticks t) origin = some c) (hstep : step S 0 c = some c') :
    run S (ticks (t + 1)) origin = some c' := by
  rw [ticks_succ, run_append, hpre, Option.bind_some, run_cons, hstep,
    Option.bind_some, run_nil]

theorem run_snoc (S : Machine nsM nt nb) (start c c' : Configuration nsM nt)
    (u0 : List (Fin nb)) (slot : Fin nb)
    (hpre : run S u0 start = some c) (hstep : step S slot c = some c') :
    run S (u0 ++ [slot]) start = some c' := by
  rw [run_append, hpre, Option.bind_some, run_cons, hstep, Option.bind_some, run_nil]

theorem rest_nil_of_accept (P : DeterministicMachine nsP nt)
    (M : Machine nsM nt nb) (H : DeterministicMachine nsH nt)
    (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (c : Configuration (nsP + nsM + 2 * nsH + 2) nt) (hacc : c.state = acceptC)
    (rest : List (Fin nb)) (out : Configuration (nsP + nsM + 2 * nsH + 2) nt)
    (h : run (machine P M H hnb hcodes) rest c = some out) : rest = [] := by
  cases rest with
  | nil => rfl
  | cons s rest =>
      have hst : c.state = (machine P M H hnb hcodes).accept := by
        simpa [machine_accept] using hacc
      have hnone := run_accept_nonempty_none (machine P M H hnb hcodes)
        c hst (s :: rest) (by simp)
      simp [hnone] at h

theorem rest_nil_of_reject (P : DeterministicMachine nsP nt)
    (M : Machine nsM nt nb) (H : DeterministicMachine nsH nt)
    (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (c : Configuration (nsP + nsM + 2 * nsH + 2) nt) (hrej : c.state = rejectC)
    (rest : List (Fin nb)) (out : Configuration (nsP + nsM + 2 * nsH + 2) nt)
    (h : run (machine P M H hnb hcodes) rest c = some out) : rest = [] := by
  cases rest with
  | nil => rfl
  | cons s rest =>
      have hst : c.state = (machine P M H hnb hcodes).reject := by
        simpa [machine_reject] using hrej
      have hnone := run_reject_nonempty_none (machine P M H hnb hcodes)
        c hst (s :: rest) (by simp)
      simp [hnone] at h

theorem prefix_len (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (I : Configuration nsP nt → Prop) (r : Configuration nsP nt → Nat)
    (A B C : Nat) (hyp : CausalPremises P M H I r A B C)
    (slots : List (Fin nb)) (out : Configuration (nsP + nsM + 2 * nsH + 2) nt) :
    (∀ (c origin : Configuration nsP nt) (t fuel k : Nat),
      I origin → r origin ≤ k → run P (ticks t) origin = some c →
      (∀ s d, run P (ticks s) c = some d → s ≤ fuel) →
      run (machine P M H hnb hcodes) slots (liftP c) = some out →
      slots.length ≤ fuel + 1 + B + 2 * C + 3 + k * cycleBound A B C) ∧
    (∀ (c : Configuration nsH nt) (origin p : Configuration nsP nt)
        (a b fuel k : Nat),
      I origin → r origin ≤ k →
      run P (ticks a) origin = some p → p.state = P.accept →
      p.tape p.head = P.one → run H (ticks b) (restartH H p) = some c →
      (∀ s d, run H (ticks s) c = some d → s ≤ fuel) →
      run (machine P M H hnb hcodes) slots (liftHM c) = some out →
      slots.length ≤ fuel + 1 + B + C + 2 + k * cycleBound A B C) ∧
    (∀ (c : Configuration nsM nt) (origin p : Configuration nsP nt)
        (h1 : Configuration nsH nt) (u0 : List (Fin nb)) (a b fuel k : Nat),
      I origin → r origin ≤ k →
      run P (ticks a) origin = some p → p.state = P.accept →
      p.tape p.head = P.one →
      run H (ticks b) (restartH H p) = some h1 → h1.state = H.accept →
      run M u0 (restartM M h1) = some c →
      (∀ v d, run M v c = some d → v.length ≤ fuel) →
      run (machine P M H hnb hcodes) slots (liftM c) = some out →
      slots.length ≤ fuel + 1 + C + 1 + k * cycleBound A B C) ∧
    (∀ (c : Configuration nsH nt) (origin p : Configuration nsP nt)
        (h1 : Configuration nsH nt) (m : Configuration nsM nt)
        (u0 : List (Fin nb)) (a b d fuel k : Nat),
      I origin → r origin ≤ k →
      run P (ticks a) origin = some p → p.state = P.accept →
      p.tape p.head = P.one →
      run H (ticks b) (restartH H p) = some h1 → h1.state = H.accept →
      run M u0 (restartM M h1) = some m → m.state = M.accept →
      m.tape m.head = M.one → run H (ticks d) (restartH H m) = some c →
      (∀ s e, run H (ticks s) c = some e → s ≤ fuel) →
      run (machine P M H hnb hcodes) slots (liftHP c) = some out →
      slots.length ≤ fuel + 1 + k * cycleBound A B C) := by
  induction slots with
  | nil =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro c origin t fuel k hI hr hpre hfuel h; simp at h ⊢
      · intro c origin p a b fuel k hI hr hp hpa hone hh hfuel h; simp at h ⊢
      · intro c origin p h1 u0 a b fuel k hI hr hp hpa hone hh hha hm hfuel h
        simp at h ⊢
      · intro c origin p h1 m u0 a b d fuel k hI hr hp hpa hone hh hha hm hma
          hmone hh2 hfuel h; simp at h ⊢
  | cons slot rest ih =>
      rcases ih with ⟨ihP, ihHM, ihM, ihHP⟩
      refine ⟨?fromP, ?fromHM, ?fromM, ?fromHP⟩
      · intro c origin t fuel k hI hr hpre hfuel h
        rw [run_cons] at h
        cases hstep : step (machine P M H hnb hcodes) slot (liftP c) with
        | none => simp [hstep] at h
        | some mid =>
            simp [hstep] at h
            have hinv := step_P_inv P M H hnb hcodes c slot mid hstep
            rcases hinv with hC | hS | hR | hO
            · rcases hC with ⟨hs, hs0, hone, hmid⟩
              subst slot; rw [hmid] at h
              have hHf : ∀ s d, run H (ticks s) (restartH H c) = some d → s ≤ C :=
                fun s d hk => hyp.hH1 origin t c hI hpre hs hone s d hk
              have hH0 := run_ticks_zero H (restartH H c)
              have := ihHM (restartH H c) origin c t 0 C k hI hr hpre hs hone
                hH0 hHf h
              simp [cycleBound] at this ⊢; omega
            · rcases hS with ⟨_, hs0, _, hmid⟩
              subst slot; rw [hmid] at h
              have hnil := rest_nil_of_accept P M H hnb hcodes
                { state := acceptC, head := c.head, tape := c.tape } rfl rest out h
              subst rest; simp; omega
            · rcases hR with ⟨_, hs0, hmid⟩
              subst slot; rw [hmid] at h
              have hnil := rest_nil_of_reject P M H hnb hcodes
                { state := rejectC, head := c.head, tape := c.tape } rfl rest out h
              subst rest; simp; omega
            · rcases hO with ⟨_, _, hs0, c', hPstep, hmid⟩
              subst slot; subst mid
              have hpre' := run_ticks_succ P origin c c' t hpre hPstep
              have hf := det_fuel_pred P c c' fuel hPstep hfuel
              have := ihP c' origin (t + 1) (fuel - 1) k hI hr hpre' hf.2 h
              simp at this ⊢; omega
      · intro c origin p a b fuel k hI hr hp hpa hone hh hfuel h
        rw [run_cons] at h
        cases hstep : step (machine P M H hnb hcodes) slot (liftHM c) with
        | none => simp [hstep] at h
        | some mid =>
            simp [hstep] at h
            have hinv := step_HM_inv P M H hnb hcodes c slot mid hstep
            rcases hinv with hA | hR | hO
            · rcases hA with ⟨hs, hs0, hmid⟩
              subst slot; rw [hmid] at h
              have hMf : ∀ v d, run M v (restartM M c) = some d → v.length ≤ B :=
                fun v d hk => hyp.hM origin a p b c hI hp hpa hone hh hs v d hk
              have hM0 : run M [] (restartM M c) = some (restartM M c) := by simp
              have := ihM (restartM M c) origin p c [] a b B k hI hr hp hpa hone
                hh hs hM0 hMf h
              simp [cycleBound] at this ⊢; omega
            · rcases hR with ⟨_, hs0, hmid⟩
              subst slot; rw [hmid] at h
              have hnil := rest_nil_of_reject P M H hnb hcodes
                { state := rejectC, head := c.head, tape := c.tape } rfl rest out h
              subst rest; simp; omega
            · rcases hO with ⟨_, _, hs0, c', hH, hmid⟩
              subst slot; subst mid
              have hpre' := run_ticks_succ H (restartH H p) c c' b hh hH
              have hf := det_fuel_pred H c c' fuel hH hfuel
              have := ihHM c' origin p a (b + 1) (fuel - 1) k hI hr hp hpa hone
                hpre' hf.2 h
              simp at this ⊢; omega
      · intro c origin p h1 u0 a b fuel k hI hr hp hpa hone hh hha hm hfuel h
        rw [run_cons] at h
        cases hstep : step (machine P M H hnb hcodes) slot (liftM c) with
        | none => simp [hstep] at h
        | some mid =>
            simp [hstep] at h
            have hinv := step_M_inv P M H hnb hcodes c slot mid hstep
            rcases hinv with hC | hBad | hR | hO
            · rcases hC with ⟨hs, hs0, honeM, hmid⟩
              subst slot; rw [hmid] at h
              have hHf :
                  ∀ s e, run H (ticks s) (restartH H c) = some e → s ≤ C :=
                fun s e hk =>
                  hyp.hH2 origin a p b h1 u0 c hI hp hpa hone hh hha hm hs honeM
                    s e hk
              have hH0 := run_ticks_zero H (restartH H c)
              have := ihHP (restartH H c) origin p h1 c u0 a b 0 C k hI hr hp
                hpa hone hh hha hm hs honeM hH0 hHf h
              simp [cycleBound] at this ⊢; omega
            · rcases hBad with ⟨_, hs0, _, hmid⟩
              subst slot; rw [hmid] at h
              have hnil := rest_nil_of_reject P M H hnb hcodes
                { state := rejectC, head := c.head, tape := c.tape } rfl rest out h
              subst rest; simp; omega
            · rcases hR with ⟨_, hs0, hmid⟩
              subst slot; rw [hmid] at h
              have hnil := rest_nil_of_reject P M H hnb hcodes
                { state := rejectC, head := c.head, tape := c.tape } rfl rest out h
              subst rest; simp; omega
            · rcases hO with ⟨_, _, c', hMstep, hmid⟩
              subst mid
              have hpre' := run_snoc M (restartM M h1) c c' u0 slot hm hMstep
              have hf := nd_fuel_pred M c c' slot fuel hMstep hfuel
              have := ihM c' origin p h1 (u0 ++ [slot]) a b (fuel - 1) k hI hr
                hp hpa hone hh hha hpre' hf.2 h
              simp [List.length_append] at this ⊢; omega
      · intro c origin p h1 m u0 a b d fuel k hI hr hp hpa hone hh hha hm hma
          hmone hh2 hfuel h
        rw [run_cons] at h
        cases hstep : step (machine P M H hnb hcodes) slot (liftHP c) with
        | none => simp [hstep] at h
        | some mid =>
            simp [hstep] at h
            have hinv := step_HP_inv P M H hnb hcodes c slot mid hstep
            rcases hinv with hA | hR | hO
            · rcases hA with ⟨hs, hs0, hmid⟩
              subst slot; rw [hmid] at h
              have hrt := hyp.hret origin a p b h1 u0 m d c hI hp hpa hone hh
                hha hm hma hmone hh2 hs
              have hlt : r (restartP P c) < k ∨ k = 0 := by omega
              cases hlt with
              | inl hlt =>
                  have hkpos : 0 < k := Nat.zero_lt_of_lt hlt
                  have hr' : r (restartP P c) ≤ k - 1 := Nat.le_pred_of_lt hlt
                  have hPf : ∀ s e, run P (ticks s) (restartP P c) = some e →
                      s ≤ A := hyp.hP (restartP P c) hrt.1
                  have hpre0 := run_ticks_zero P (restartP P c)
                  have hrest :=
                    ihP (restartP P c) (restartP P c) 0 A (k - 1) hrt.1 hr'
                      hpre0 hPf h
                  have hkeq : (k - 1) + 1 = k := Nat.succ_pred_eq_of_pos hkpos
                  have hmul : k * cycleBound A B C =
                      (k - 1) * cycleBound A B C + cycleBound A B C := by
                    conv => lhs; rw [← hkeq]
                    rw [Nat.succ_mul]
                  have hpad : A + 1 + B + 2 * C + 3 = cycleBound A B C := by
                    simp [cycleBound]; omega
                  rw [hpad] at hrest
                  have hrest' : rest.length ≤ k * cycleBound A B C := by
                    rw [hmul, Nat.add_comm]; exact hrest
                  simp; omega
              | inr hk =>
                  subst k
                  have : r (restartP P c) < 0 :=
                    Nat.lt_of_lt_of_le hrt.2 (by omega)
                  exact (Nat.not_lt_zero _ this).elim
            · rcases hR with ⟨_, hs0, hmid⟩
              subst slot; rw [hmid] at h
              have hnil := rest_nil_of_reject P M H hnb hcodes
                { state := rejectC, head := c.head, tape := c.tape } rfl rest out h
              subst rest; simp; omega
            · rcases hO with ⟨_, _, hs0, c', hH, hmid⟩
              subst slot; subst mid
              have hpre' := run_ticks_succ H (restartH H m) c c' d hh2 hH
              have hf := det_fuel_pred H c c' fuel hH hfuel
              have := ihHP c' origin p h1 m u0 a b (d + 1) (fuel - 1) k hI hr
                hp hpa hone hh hha hm hma hmone hpre' hf.2 h
              simp at this ⊢; omega

theorem prefix_from_P (P : DeterministicMachine nsP nt) (M : Machine nsM nt nb)
    (H : DeterministicMachine nsH nt) (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (I : Configuration nsP nt → Prop) (r : Configuration nsP nt → Nat)
    (A B C K : Nat) (hyp : CausalPremises P M H I r A B C)
    (cP : Configuration nsP nt) (slots : List (Fin nb))
    (out : Configuration (nsP + nsM + 2 * nsH + 2) nt)
    (hI : I cP) (hr : r cP ≤ K)
    (h : run (machine P M H hnb hcodes) slots (liftP cP) = some out) :
    slots.length ≤ (K + 1) * cycleBound A B C := by
  have hpre := run_ticks_zero P cP
  have hfuel : ∀ s d, run P (ticks s) cP = some d → s ≤ A := hyp.hP cP hI
  have := (prefix_len P M H hnb hcodes I r A B C hyp slots out).1
    cP cP 0 A K hI hr hpre hfuel h
  have hpad : A + 1 + B + 2 * C + 3 = cycleBound A B C := by
    simp [cycleBound]; omega
  rw [hpad] at this
  have hmul : cycleBound A B C + K * cycleBound A B C =
      (K + 1) * cycleBound A B C := by rw [Nat.add_comm, Nat.succ_mul]
  omega

theorem reachable_spec (P : DeterministicMachine nsP nt)
    (M : Machine nsM nt nb) (H : DeterministicMachine nsH nt)
    (hnb : 0 < nb) (hcodes : SameCodes P M H)
    (I : Configuration nsP nt → Prop) (r : Configuration nsP nt → Nat)
    (A B C K : Nat) (hyp : CausalPremises P M H I r A B C) :
    (∀ raw slots, Accepted (machine P M H hnb hcodes) raw slots ↔
      AcceptTrace P M H hnb (initial P raw) slots) ∧
    (∀ (cP : Configuration nsP nt) (slots : List (Fin nb))
        (out : Configuration (nsP + nsM + 2 * nsH + 2) nt),
      I cP → r cP ≤ K →
        run (machine P M H hnb hcodes) slots (liftP cP) = some out →
        slots.length ≤ (K + 1) * cycleBound A B C) := by
  refine ⟨accepted_iff_init P M H hnb hcodes, ?_⟩
  intro cP slots out hI hr hrun
  exact prefix_from_P P M H hnb hcodes I r A B C K hyp cP slots out hI hr hrun

end
end PakFixedPolyomino.StandardMachineNondeterministicFeedbackReachable
