import PakFixedPolyomino.ULogSourceOneHotPhysicalMacro
import PakFixedPolyomino.ULogSourceOneHotPhaseEndpoints
import Mathlib.Tactic

/-!
# One-step inverse facts for the physical source macro

These local inverses separate the sole labelled source-choice step from all
deterministic slot-zero microsteps.  They are deliberately one-step facts so
later full-run uniqueness can concatenate them without hiding labels.
-/

namespace PakFixedPolyomino.ULogSourceOneHotMacroInverse

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceOneHotPhysicalStep ULogSourceOneHotPhysicalMacro
open ULogSourceOneHotPhaseEndpoints

variable {ns nt : ℕ}

/-- A successful step from a live branch state identifies one concrete source
slot and occupied bounded action; its literal arrow and successor are forced. -/
theorem branch_success_inverse (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (read : Fin nt)
    (hlive : haltedSource q = false) (tape : Int → Tape) (head : Int)
    (arrow : Arrow (program p hnt logicalBlank)) (out : Config (State ns nt) Tape)
    (hstep : step (program p hnt logicalBlank) (fun _ => true)
      ({ state := .branch q read, head := head, tape := tape } :
        Config (State ns nt) Tape) arrow = some out) :
    ∃ (slot : Fin 2) (a : BoundedAction ns nt)
      (hocc : p.rule q read (slot = 1) = some a),
      arrow = branchArrow p hnt logicalBlank q read slot (tape head) hlive a hocc ∧
      out = branchResult q read slot a tape head := by
  have hsource := step_some_forces_source (program p hnt logicalBlank)
    (fun _ => true) _ out arrow hstep
  rcases hsource with ⟨hstate, hread⟩
  rcases arrow with ⟨⟨⟨source, x⟩, slot⟩, hoccupied⟩
  change .branch q read = source at hstate
  change tape head = x at hread
  subst source
  subst x
  cases hrule : p.rule q read (slot = 1) with
  | none =>
      rw [branch_rule_exact p hnt logicalBlank q read slot (tape head) hlive,
        hrule] at hoccupied
      simp at hoccupied
  | some a =>
      have harrow :
          (⟨((State.branch q read, tape head), slot), hoccupied⟩ :
            Arrow (program p hnt logicalBlank)) =
          branchArrow p hnt logicalBlank q read slot (tape head) hlive a hrule := by
        rfl
      refine ⟨slot, a, hrule, harrow, ?_⟩
      have hbranch := branchArrow_step p hnt logicalBlank q read slot a hlive hrule
        tape head
      rw [harrow, hbranch] at hstep
      exact Option.some.inj hstep.symm

/-- Any successful one-step execution outside source branching uses the
unique slot-zero micro arrow and has the deterministic micro successor. -/
theorem nonbranch_success_inverse (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (s : State ns nt) (tape : Int → Tape) (head : Int)
    (hs : ∀ q read, s ≠ State.branch q read)
    (arrow : Arrow (program p hnt logicalBlank)) (out : Config (State ns nt) Tape)
    (hstep : step (program p hnt logicalBlank) (fun _ => true)
      ({ state := s, head := head, tape := tape } : Config (State ns nt) Tape)
      arrow = some out) :
    arrow.1.2 = 0 ∧
      arrow = microArrow p hnt logicalBlank s (tape head) hs ∧
      out = nextMicroConfig hnt logicalBlank
        ({ state := s, head := head, tape := tape } : Config (State ns nt) Tape) := by
  have hsource := step_some_forces_source (program p hnt logicalBlank)
    (fun _ => true) _ out arrow hstep
  rcases hsource with ⟨hstate, hread⟩
  rcases arrow with ⟨⟨⟨source, x⟩, slot⟩, hoccupied⟩
  change s = source at hstate
  change tape head = x at hread
  subst source
  subst x
  have hslot : slot = 0 := by
    fin_cases slot
    · rfl
    · have hempty := nonbranch_slot_one_empty p hnt logicalBlank s (tape head) hs
      exact False.elim (hoccupied hempty)
  subst slot
  have harrow :
      (⟨((s, tape head), 0), hoccupied⟩ : Arrow (program p hnt logicalBlank)) =
        microArrow p hnt logicalBlank s (tape head) hs := by
      rfl
  refine ⟨rfl, harrow, ?_⟩
  have hmicro := microArrow_step p hnt logicalBlank
    ({ state := s, head := head, tape := tape } : Config (State ns nt) Tape) hs
  rw [harrow, hmicro] at hstep
  exact Option.some.inj hstep.symm

/-- A successful run that avoids source branching has one and only one
literal occupied micro-arrow ledger. -/
theorem nonbranch_successful_run_unique_of_avoids
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (c : Config (State ns nt) Tape) (n : ℕ)
    (havoid : ∀ k : ℕ, k < n → ∀ q read,
      ((nextMicroConfig hnt logicalBlank)^[k] c).state ≠ State.branch q read)
    (as : List (Arrow (program p hnt logicalBlank))) (out : Config (State ns nt) Tape)
    (hlen : as.length = n)
    (hrun : run (program p hnt logicalBlank) (fun _ => true) as c = some out) :
    ∃ bs, nonbranchArrows p hnt logicalBlank c n = some bs ∧
      as = bs ∧ out = (nextMicroConfig hnt logicalBlank)^[n] c := by
  induction n generalizing c as out with
  | zero =>
      have has : as = [] := List.eq_nil_of_length_eq_zero hlen
      subst as
      simp at hrun
      subst out
      exact ⟨[], rfl, rfl, rfl⟩
  | succ n ih =>
      cases as with
      | nil => simp at hlen
      | cons arrow tail =>
          simp only [List.length_cons] at hlen
          simp only [run_cons] at hrun
          cases hstep : step (program p hnt logicalBlank) (fun _ => true) c arrow with
          | none => simp [hstep] at hrun
          | some c' =>
              rw [hstep] at hrun
              simp only [Option.bind_some] at hrun
              rcases c with ⟨s, head, tape⟩
              have hs : ∀ q read, s ≠ State.branch q read := by
                intro q read
                have h := havoid 0 (by omega) q read
                change s ≠ State.branch q read at h
                exact h
              rcases nonbranch_success_inverse p hnt logicalBlank s tape head hs arrow c' hstep
                with ⟨_, harrow, hnext⟩
              subst arrow
              subst c'
              have htailAvoid : ∀ k : ℕ, k < n → ∀ q read,
                  ((nextMicroConfig hnt logicalBlank)^[k]
                    (nextMicroConfig hnt logicalBlank
                      ({ state := s, head := head, tape := tape } :
                        Config (State ns nt) Tape))).state ≠ State.branch q read := by
                intro k hk q read
                have h := havoid (k + 1) (by omega) q read
                simpa only [Function.iterate_succ_apply] using h
              obtain ⟨bs, hbs, htail, hout⟩ := ih
                (nextMicroConfig hnt logicalBlank
                  ({ state := s, head := head, tape := tape } : Config (State ns nt) Tape))
                htailAvoid tail out (by omega) hrun
              refine ⟨microArrow p hnt logicalBlank s (tape head) hs :: bs, ?_, ?_, ?_⟩
              · cases s with
                | branch q read => exact False.elim (hs q read rfl)
                | reading q r => simp [nonbranchArrows, hbs, readArrow]
                | rewind q read slot a i => simp [nonbranchArrows, hbs, rewindArrow]
                | writing a i => simp [nonbranchArrows, hbs, writeArrow]
                | relocate a i => simp [nonbranchArrows, hbs, relocateArrow]
                | accept => simp [nonbranchArrows, hbs]
                | reject => simp [nonbranchArrows, hbs]
              · simp [htail]
              · rw [hout, Function.iterate_succ_apply]

theorem rewind_successful_run_unique (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (read : Fin nt) (slot : Bool)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int)
    (as : List (Arrow (program p hnt logicalBlank))) (out : Config (State ns nt) Tape)
    (hlen : as.length = nt)
    (hrun : run (program p hnt logicalBlank) (fun _ => true) as
      (rewindInitial hnt q read slot a tape head) = some out) :
    ∃ bs, nonbranchArrows p hnt logicalBlank
      (rewindInitial hnt q read slot a tape head) nt = some bs ∧ as = bs ∧
      out = writerInitial hnt a tape (head - nt) := by
  obtain ⟨bs, hbs, has, hout⟩ := nonbranch_successful_run_unique_of_avoids
    p hnt logicalBlank (rewindInitial hnt q read slot a tape head) nt
    (by
      intro k hk q' read'
      rw [iterate_rewind_expected hnt logicalBlank q read slot a tape head k (by omega)]
      simp [rewindExpected, rewindStage, hk]) as out hlen hrun
  refine ⟨bs, hbs, has, ?_⟩
  rw [hout, rewind_operational_terminal]
  apply config_ext <;> simp [writerInitial]

theorem writer_successful_run_unique (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int)
    (as : List (Arrow (program p hnt logicalBlank))) (out : Config (State ns nt) Tape)
    (hlen : as.length = nt)
    (hrun : run (program p hnt logicalBlank) (fun _ => true) as
      (writerInitial hnt a tape head) = some out) :
    ∃ bs, nonbranchArrows p hnt logicalBlank
      (writerInitial hnt a tape head) nt = some bs ∧ as = bs ∧
      out = relocateInitial a
        (ULogSourceOneHotWriter.writePrefix a.write head tape nt) (head + nt) := by
  obtain ⟨bs, hbs, has, hout⟩ := nonbranch_successful_run_unique_of_avoids
    p hnt logicalBlank (writerInitial hnt a tape head) nt
    (by
      intro k hk q read
      rw [iterate_writer_expected hnt logicalBlank a tape head k (by omega)]
      simp [writerExpected, writerStage, hk]) as out hlen hrun
  refine ⟨bs, hbs, has, ?_⟩
  rw [hout, writer_operational_terminal]
  apply config_ext
  · simp only [relocateInitial, relocateExpected]
    congr
  · simp [relocateInitial, relocateExpected]
  · simp [relocateInitial, relocateExpected]

theorem relocate_successful_run_unique (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int)
    (as : List (Arrow (program p hnt logicalBlank))) (out : Config (State ns nt) Tape)
    (hlen : as.length = relocationDistance a.move nt + 1)
    (hrun : run (program p hnt logicalBlank) (fun _ => true) as
      (relocateInitial a tape head) = some out) :
    ∃ bs, nonbranchArrows p hnt logicalBlank
      (relocateInitial a tape head) (relocationDistance a.move nt + 1) = some bs ∧
      as = bs ∧ out =
        { state := .reading a.target (initialReaderState hnt),
          head := head - relocationDistance a.move nt,
          tape := tape } := by
  obtain ⟨bs, hbs, has, hout⟩ := nonbranch_successful_run_unique_of_avoids
    p hnt logicalBlank (relocateInitial a tape head)
    (relocationDistance a.move nt + 1)
    (by
      intro k hk q read
      have hk' : k ≤ relocationDistance a.move nt := by omega
      rw [iterate_relocate_expected hnt logicalBlank a tape head k hk']
      simp [relocateExpected]) as out hlen hrun
  refine ⟨bs, hbs, has, ?_⟩
  rw [hout, relocate_operational_terminal]

theorem iterate_liftReaderConfig (hnt : 0 < nt) (logicalBlank : Fin nt)
    (q : Fin ns) (hlive : haltedSource q = false)
    (c : Config (ULogSourceLogicalBlockReader.State nt) Tape) (n : ℕ) :
    (nextMicroConfig hnt logicalBlank)^[n] (liftReaderConfig q c) =
      liftReaderConfig q ((ULogSourceLogicalBlockReader.nextConfig logicalBlank)^[n] c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simpa [Function.iterate_succ_apply'] using
        nextMicroConfig_liftReaderConfig hnt logicalBlank q hlive
          ((ULogSourceLogicalBlockReader.nextConfig logicalBlank)^[n] c)

/-- Any successful `nt`-tick physical reader segment over a valid one-hot
block is the literal reader ledger and ends at its exact source branch. -/
theorem reader_successful_run_unique (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head)
    (as : List (Arrow (program p hnt logicalBlank))) (out : Config (State ns nt) Tape)
    (hlen : as.length = nt)
    (hrun : run (program p hnt logicalBlank) (fun _ => true) as
      (liftReaderConfig q
        (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head)) = some out) :
    ∃ bs, nonbranchArrows p hnt logicalBlank
      (liftReaderConfig q
        (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head)) nt = some bs ∧
      as = bs ∧ out =
        ({ state := .branch q read, head := head + nt, tape := tape } : Config (State ns nt) Tape) := by
  let logicalInitial := ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head
  obtain ⟨bs, hbs, has, hout⟩ := nonbranch_successful_run_unique_of_avoids
    p hnt logicalBlank (liftReaderConfig q logicalInitial) nt
      (by
      intro k hk q' read'
      rw [iterate_liftReaderConfig hnt logicalBlank q hlive]
      obtain ⟨i, mode, hscan⟩ := oneHot_initial_scanning logicalBlank read hnt tape head hone k hk
      dsimp [logicalInitial]
      change liftReaderControl q
        (((ULogSourceLogicalBlockReader.nextConfig logicalBlank)^[k]
          (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head)).state) ≠
        State.branch q' read'
      rw [hscan]
      simp [liftReaderConfig, liftReaderControl]) as out hlen hrun
  refine ⟨bs, ?_, has, ?_⟩
  · simpa [logicalInitial] using hbs
  rw [hout, iterate_liftReaderConfig hnt logicalBlank q hlive,
    ULogSourceLogicalBlockReader.oneHot_operational_terminal logicalBlank read hnt tape head hone]
  rfl

theorem blank_reader_successful_run_unique (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (logicalBlank : Fin nt) (q : Fin ns)
    (hlive : haltedSource q = false) (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) =
      ULogSourceLogicalBlockReader.blank)
    (as : List (Arrow (program p hnt logicalBlank)))
    (out : Config (State ns nt) Tape) (hlen : as.length = nt)
    (hrun : run (program p hnt logicalBlank) (fun _ => true) as
      (liftReaderConfig q
        (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head)) = some out) :
    ∃ bs, nonbranchArrows p hnt logicalBlank
      (liftReaderConfig q
        (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head)) nt = some bs ∧
      as = bs ∧ out =
        ({ state := .branch q logicalBlank, head := head + nt, tape := tape } :
          Config (State ns nt) Tape) := by
  let logicalInitial := ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head
  obtain ⟨bs, hbs, has, hout⟩ := nonbranch_successful_run_unique_of_avoids
    p hnt logicalBlank (liftReaderConfig q logicalInitial) nt
      (by
        intro k hk q' read'
        rw [iterate_liftReaderConfig hnt logicalBlank q hlive]
        obtain ⟨i, mode, hscan⟩ := blank_initial_scanning logicalBlank hnt
          tape head hblank k hk
        dsimp [logicalInitial]
        change liftReaderControl q
          (((ULogSourceLogicalBlockReader.nextConfig logicalBlank)^[k]
            (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head)).state) ≠
          State.branch q' read'
        rw [hscan]
        simp [liftReaderControl]) as out hlen hrun
  refine ⟨bs, ?_, has, ?_⟩
  · simpa [logicalInitial] using hbs
  rw [hout, iterate_liftReaderConfig hnt logicalBlank q hlive,
    ULogSourceLogicalBlockReader.blank_operational_terminal logicalBlank hnt
      tape head hblank]
  rfl

/-- Successful concatenated runs expose a successful intermediate boundary. -/
theorem run_append_eq (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt)
    (xs ys : List (Arrow (program p hnt logicalBlank)))
    (c : Config (State ns nt) Tape) :
    run (program p hnt logicalBlank) (fun _ => true) (xs ++ ys) c =
      (run (program p hnt logicalBlank) (fun _ => true) xs c).bind
        (run (program p hnt logicalBlank) (fun _ => true) ys) := by
  induction xs generalizing c with
  | nil => rfl
  | cons arrow xs ih =>
      simp only [List.cons_append, run_cons]
      cases hstep : step (program p hnt logicalBlank) (fun _ => true) c arrow with
      | none => simp [hstep]
      | some c' => simp [hstep, ih]

theorem run_append_success_split (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (xs ys : List (Arrow (program p hnt logicalBlank)))
    (c out : Config (State ns nt) Tape)
    (hrun : run (program p hnt logicalBlank) (fun _ => true) (xs ++ ys) c = some out) :
    ∃ mid, run (program p hnt logicalBlank) (fun _ => true) xs c = some mid ∧
      run (program p hnt logicalBlank) (fun _ => true) ys mid = some out := by
  induction xs generalizing c with
  | nil => exact ⟨c, rfl, hrun⟩
  | cons arrow xs ih =>
      rw [List.cons_append, run_cons] at hrun
      cases hstep : step (program p hnt logicalBlank) (fun _ => true) c arrow with
      | none => simp [hstep] at hrun
      | some c' =>
          rw [hstep] at hrun
          simp only [Option.bind_some] at hrun
          obtain ⟨mid, hxs, hys⟩ := ih c' hrun
          exact ⟨mid, by simp [run_cons, hstep, hxs], hys⟩

theorem run_take_drop_success_split (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (as : List (Arrow (program p hnt logicalBlank)))
    (k : ℕ) (c out : Config (State ns nt) Tape)
    (hrun : run (program p hnt logicalBlank) (fun _ => true) as c = some out) :
    ∃ mid, run (program p hnt logicalBlank) (fun _ => true) (as.take k) c = some mid ∧
      run (program p hnt logicalBlank) (fun _ => true) (as.drop k) mid = some out := by
  have hsplit := run_append_success_split p hnt logicalBlank (as.take k) (as.drop k) c out
    (by simpa [List.take_append_drop] using hrun)
  exact hsplit

/-- Inductive successor transport for a raw successful prefix: after its
endpoint has been identified with the canonical iterate, a nonbranch next
step is forced to the literal micro arrow and next iterate. -/
theorem canonical_prefix_successor (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (c : Config (State ns nt) Tape) (k : ℕ)
    (pre : List (Arrow (program p hnt logicalBlank)))
    (hprefix : pre.length = k ∧
      run (program p hnt logicalBlank) (fun _ => true) pre c =
        some ((nextMicroConfig hnt logicalBlank)^[k] c))
    (hs : ∀ q read,
      ((nextMicroConfig hnt logicalBlank)^[k] c).state ≠ State.branch q read)
    (arrow : Arrow (program p hnt logicalBlank)) (out : Config (State ns nt) Tape)
    (hstep : step (program p hnt logicalBlank) (fun _ => true)
      ((nextMicroConfig hnt logicalBlank)^[k] c) arrow = some out) :
    arrow = microArrow p hnt logicalBlank
      ((nextMicroConfig hnt logicalBlank)^[k] c).state
      (((nextMicroConfig hnt logicalBlank)^[k] c).tape
        ((nextMicroConfig hnt logicalBlank)^[k] c).head) hs ∧
      out = (nextMicroConfig hnt logicalBlank)^[k + 1] c := by
  rcases nonbranch_success_inverse p hnt logicalBlank
    ((nextMicroConfig hnt logicalBlank)^[k] c).state
    ((nextMicroConfig hnt logicalBlank)^[k] c).tape
    ((nextMicroConfig hnt logicalBlank)^[k] c).head hs arrow out hstep with
    ⟨_, harrow, hout⟩
  refine ⟨harrow, ?_⟩
  rw [hout, Function.iterate_succ_apply']

/-- Every successful prefix of a choice-free nonbranch suffix is the
canonical deterministic iterate.  The hypothesis speaks only about actual
successful `take` prefixes; the conclusion reconstructs the canonical state
without assuming it in the input. -/
theorem successful_prefixes_are_canonical
    (p : BoundedProgram ns nt) (hnt : 0 < nt) (logicalBlank : Fin nt)
    (as : List (Arrow (program p hnt logicalBlank)))
    (c out : Config (State ns nt) Tape)
    (hrun : run (program p hnt logicalBlank) (fun _ => true) as c = some out)
    (hno : ∀ k : ℕ, k ≤ as.length → ∀ mid,
      run (program p hnt logicalBlank) (fun _ => true) (as.take k) c =
          some mid →
        ∀ q read, mid.state ≠ State.branch q read) :
    ∀ k : ℕ, k ≤ as.length →
      run (program p hnt logicalBlank) (fun _ => true) (as.take k) c =
          some ((nextMicroConfig hnt logicalBlank)^[k] c) ∧
        (k < as.length → ∀ q read,
          ((nextMicroConfig hnt logicalBlank)^[k] c).state ≠
            State.branch q read) := by
  intro k hk
  induction k with
  | zero =>
      constructor
      · rfl
      · intro hlt
        exact hno 0 (Nat.zero_le _) c rfl
  | succ k ih =>
      have hklt : k < as.length := by omega
      obtain ⟨hpre, havoid⟩ := ih (by omega)
      have htakesucc : as.take (k + 1) = as.take k ++ [as[k]] := by
        rw [List.take_succ, List.getElem?_eq_getElem hklt]
        rfl
      obtain ⟨succOut, hsuccRun, -⟩ :=
        run_take_drop_success_split p hnt logicalBlank as (k + 1) c out hrun
      have honeStep : step (program p hnt logicalBlank) (fun _ => true)
          ((nextMicroConfig hnt logicalBlank)^[k] c) as[k] = some succOut := by
        have hlocal := hsuccRun
        rw [htakesucc, run_append_eq, hpre] at hlocal
        simp only [Option.bind_some] at hlocal
        cases hs : step (program p hnt logicalBlank) (fun _ => true)
            ((nextMicroConfig hnt logicalBlank)^[k] c) as[k] with
        | none => simp [hs] at hlocal
        | some mid =>
            have hmid : mid = succOut := by simpa [hs] using hlocal
            simpa [hs, hmid]
      have htakeLength : (as.take k).length = k := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hklt)]
      obtain ⟨-, hout⟩ := canonical_prefix_successor p hnt logicalBlank c k
        (as.take k) ⟨htakeLength, hpre⟩ (havoid hklt) as[k] succOut honeStep
      have hsuccCanonical :
          run (program p hnt logicalBlank) (fun _ => true) (as.take (k + 1)) c =
            some ((nextMicroConfig hnt logicalBlank)^[k + 1] c) := by
        simpa [hout] using hsuccRun
      constructor
      · exact hsuccCanonical
      · intro hlt
        exact hno (k + 1) (by omega)
          ((nextMicroConfig hnt logicalBlank)^[k + 1] c)
          hsuccCanonical

end PakFixedPolyomino.ULogSourceOneHotMacroInverse
