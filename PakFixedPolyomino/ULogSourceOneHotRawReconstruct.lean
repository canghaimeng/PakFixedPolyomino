import PakFixedPolyomino.ULogSourceOneHotMacroEquiv
import Mathlib.Tactic

/-!
# Deterministic post-branch reconstruction

This layer isolates the move-dependent timing calculation used by raw macro
history reconstruction. -/

namespace PakFixedPolyomino.ULogSourceOneHotRawReconstruct

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics ULogCompiler
open ULogSourceOneHotPhysicalStep ULogSourceOneHotPhysicalMacro
open ULogSourceOneHotPhaseEndpoints ULogSourceOneHotMacroEquiv ULogSourceOneHotFullMacro
open ULogSourceOneHotMacroInverse

variable {ns nt : ℕ}

/-- The exact deterministic post-branch duration is two fixed-width phases
plus relocation's move-dependent left distance and stay handoff. -/
theorem correct_post_endpoint (hnt : 0 < nt) (logicalBlank : Fin nt)
    (q : Fin ns) (read : Fin nt) (slot : Bool) (a : BoundedAction ns nt)
    (tape : Int → Tape) (head : Int) :
    (nextMicroConfig hnt logicalBlank)^[2 * nt + relocationDistance a.move nt + 1]
      (rewindInitial hnt q read slot a tape (head + nt)) =
      fullEndpoint hnt a tape head := by
  let targetTape := ULogSourceOneHotWriter.writePrefix a.write head tape nt
  let zeroIndex : Fin (2 * nt + 1) := ⟨0, Nat.zero_lt_succ _⟩
  rw [show 2 * nt + relocationDistance a.move nt + 1 =
      (relocationDistance a.move nt + 1) + nt + nt by omega,
    Function.iterate_add_apply, Function.iterate_add_apply,
    rewind_operational_terminal]
  have hwriterStart :
      ({ state := .writing a ⟨0, hnt⟩, head := head + nt - nt, tape := tape } :
        Config (State ns nt) Tape) = writerInitial hnt a tape head := by
    apply config_ext <;> simp [writerInitial] <;> omega
  rw [hwriterStart, writer_operational_terminal]
  have hrelocateStart :
      ({ state := State.relocate a 0, head := head + nt, tape := targetTape } :
        Config (State ns nt) Tape) =
      relocateInitial a targetTape (head + nt) := by
    apply config_ext
    · simp only [relocateInitial, relocateExpected]
      congr
    · simp [relocateInitial, relocateExpected]
    · simp [relocateInitial, relocateExpected]
  convert (relocate_operational_terminal hnt logicalBlank a targetTape (head + nt)) using 1 <;>
    simp [targetTape, fullEndpoint, hrelocateStart]

theorem post_iterate_relocate_prefix (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (read : Fin nt) (slot : Bool)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int)
    (r : ℕ) (hr : r ≤ relocationDistance a.move nt) :
    (nextMicroConfig hnt logicalBlank)^[2 * nt + r]
        (rewindInitial hnt q read slot a tape (head + nt)) =
      relocateExpected a
        (ULogSourceOneHotWriter.writePrefix a.write head tape nt)
        (head + nt) r hr := by
  let targetTape := ULogSourceOneHotWriter.writePrefix a.write head tape nt
  rw [show 2 * nt + r = r + nt + nt by omega,
    Function.iterate_add_apply, Function.iterate_add_apply,
    rewind_operational_terminal]
  have hwriterStart :
      ({ state := .writing a ⟨0, hnt⟩, head := head + nt - nt, tape := tape } :
        Config (State ns nt) Tape) = writerInitial hnt a tape head := by
    apply config_ext <;> simp [writerInitial] <;> omega
  rw [hwriterStart, writer_operational_terminal]
  have hstart :
      ({ state := State.relocate a 0, head := head + nt, tape := targetTape } :
        Config (State ns nt) Tape) = relocateInitial a targetTape (head + nt) := by
    apply config_ext
    · simp [relocateInitial, relocateExpected, relocateIndex]
    · simp [relocateInitial, relocateExpected]
    · simp [relocateInitial, relocateExpected]
  calc
    (nextMicroConfig hnt logicalBlank)^[r]
        ({ state := State.relocate a 0, head := head + nt, tape := targetTape } :
          Config (State ns nt) Tape) =
      (nextMicroConfig hnt logicalBlank)^[r]
        (relocateInitial a targetTape (head + nt)) := congrArg _ hstart
    _ = relocateExpected a targetTape (head + nt) r hr :=
      iterate_relocate_expected hnt logicalBlank a targetTape (head + nt) r hr

/-- No canonical post-branch prefix before the final handoff is a source
branch state. -/
theorem post_iterate_avoids_branch (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (read : Fin nt) (slot : Bool)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int) :
    ∀ k : ℕ, k < 2 * nt + relocationDistance a.move nt + 1 →
      ∀ q' read',
        ((nextMicroConfig hnt logicalBlank)^[k]
          (rewindInitial hnt q read slot a tape (head + nt))).state ≠
            State.branch q' read' := by
  intro k hk q' read'
  by_cases hrewind : k < nt
  · exact rewind_avoids_branch hnt logicalBlank q read slot a tape
      (head + nt) k hrewind q' read'
  by_cases hwriter : k < 2 * nt
  · let r := k - nt
    have hr : r < nt := by dsimp [r]; omega
    have hkSplit : k = r + nt := by dsimp [r]; omega
    have hrewindToWriter :
        (nextMicroConfig hnt logicalBlank)^[nt]
          (rewindInitial hnt q read slot a tape (head + nt)) =
            writerInitial hnt a tape head := by
      rw [rewind_operational_terminal]
      apply config_ext <;> simp [writerInitial] <;> omega
    rw [hkSplit, Function.iterate_add_apply, hrewindToWriter]
    exact writer_avoids_branch hnt logicalBlank a tape head r hr q' read'
  · let r := k - 2 * nt
    have hr : r ≤ relocationDistance a.move nt := by dsimp [r]; omega
    have hkSplit : k = 2 * nt + r := by dsimp [r]; omega
    rw [hkSplit, post_iterate_relocate_prefix hnt logicalBlank q read slot
      a tape head r hr]
    simp [relocateExpected]

theorem post_iterate_not_reader_before (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (read : Fin nt) (slot : Bool)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int) :
    ∀ k : ℕ, k < 2 * nt + relocationDistance a.move nt + 1 →
      ∀ target,
        ((nextMicroConfig hnt logicalBlank)^[k]
          (rewindInitial hnt q read slot a tape (head + nt))).state ≠
            State.reading target (initialReaderState hnt) := by
  intro k hk target
  by_cases hrewind : k < nt
  · rw [iterate_rewind_expected hnt logicalBlank q read slot a tape
      (head + nt) k (by omega)]
    simp [rewindExpected, rewindStage, hrewind]
  by_cases hwriter : k < 2 * nt
  · let r := k - nt
    have hr : r < nt := by dsimp [r]; omega
    have hkSplit : k = r + nt := by dsimp [r]; omega
    have hrewindToWriter :
        (nextMicroConfig hnt logicalBlank)^[nt]
          (rewindInitial hnt q read slot a tape (head + nt)) =
            writerInitial hnt a tape head := by
      rw [rewind_operational_terminal]
      apply config_ext <;> simp [writerInitial] <;> omega
    rw [hkSplit, Function.iterate_add_apply, hrewindToWriter,
      iterate_writer_expected hnt logicalBlank a tape head r (by omega)]
    simp [writerExpected, writerStage, hr]
  · let r := k - 2 * nt
    have hr : r ≤ relocationDistance a.move nt := by dsimp [r]; omega
    have hkSplit : k = 2 * nt + r := by dsimp [r]; omega
    rw [hkSplit, post_iterate_relocate_prefix hnt logicalBlank q read slot
      a tape head r hr]
    simp [relocateExpected]

/-- Raw post execution is forced to the canonical micro-iterate, using only
its successful-prefix no-branch legality condition. -/
theorem raw_post_endpoint_canonical (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (h : RawPhysicalMacroHistory p hnt logicalBlank read q hlive tape head) :
    h.endpoint = (nextMicroConfig hnt logicalBlank)^[h.post.length] h.branch_out := by
  obtain ⟨hcanonical, _⟩ := successful_prefixes_are_canonical
    p hnt logicalBlank h.post h.branch_out h.endpoint h.post_run h.post_no_branch
    h.post.length le_rfl
  have hcanonical' : run (program p hnt logicalBlank) (fun _ => true) h.post h.branch_out =
      some ((nextMicroConfig hnt logicalBlank)^[h.post.length] h.branch_out) := by
    simpa using hcanonical
  exact Option.some.inj (h.post_run.symm.trans hcanonical')

/-- The choice-free first-return conditions force the only post length
compatible with the action extracted from the literal branch arrow. -/
theorem raw_post_length_exact (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (h : RawPhysicalMacroHistory p hnt logicalBlank read q hlive tape head)
    (choice : SourceChoice p q read)
    (hbranchOut : h.branch_out =
      branchResult q read choice.slot choice.action tape (head + nt)) :
    h.post.length =
      2 * nt + relocationDistance choice.action.move nt + 1 := by
  have hbranchInitial : h.branch_out =
      rewindInitial hnt q read (choice.slot = 1) choice.action tape (head + nt) := by
    rw [hbranchOut]
    apply config_ext
    · simp only [ULogSourceOneHotPhysicalMacro.branchResult, rewindInitial]
    · simp [ULogSourceOneHotPhysicalMacro.branchResult, rewindInitial]
    · simp [ULogSourceOneHotPhysicalMacro.branchResult, rewindInitial]
  have hcanonical := raw_post_endpoint_canonical p hnt logicalBlank read q
    hlive tape head h
  have hprefixes := successful_prefixes_are_canonical p hnt logicalBlank
    h.post h.branch_out h.endpoint h.post_run h.post_no_branch
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hshort | hlong
  · have hbase : 2 * nt ≤ h.post.length := by
      rcases h.post_length with hlen | hlen | hlen <;> omega
    let r := h.post.length - 2 * nt
    have hsplit : h.post.length = 2 * nt + r := by
      dsimp [r]
      omega
    have hr : r ≤ relocationDistance choice.action.move nt := by
      dsimp [r]
      omega
    have hiter :
        (nextMicroConfig hnt logicalBlank)^[h.post.length] h.branch_out =
          relocateExpected choice.action
            (ULogSourceOneHotWriter.writePrefix choice.action.write head tape nt)
            (head + nt) r hr := by
      rw [hbranchInitial, hsplit]
      exact post_iterate_relocate_prefix hnt logicalBlank q read
        (choice.slot = 1) choice.action tape head r hr
    obtain ⟨target, htarget⟩ := h.endpoint_reader
    have hstate := congrArg (fun c : Config (State ns nt) Tape => c.state)
      (hcanonical.trans hiter)
    rw [htarget] at hstate
    simp [relocateExpected] at hstate
  · let correct :=
        2 * nt + relocationDistance choice.action.move nt + 1
    have hcorrectLt : correct < h.post.length := by
      dsimp [correct]
      exact hlong
    obtain ⟨hcorrectRun, -⟩ := hprefixes correct (Nat.le_of_lt hcorrectLt)
    have hcorrectEndpoint :
        (nextMicroConfig hnt logicalBlank)^[correct] h.branch_out =
          fullEndpoint hnt choice.action tape head := by
      rw [hbranchInitial]
      exact correct_post_endpoint hnt logicalBlank q read
        (choice.slot = 1) choice.action tape head
    have hforbid := h.first_return correct hcorrectLt
      ((nextMicroConfig hnt logicalBlank)^[correct] h.branch_out)
      hcorrectRun choice.action.target
    apply hforbid
    rw [hcorrectEndpoint]
    rfl

/-- A raw legal history reconstructs the literal reader prefix, its unique
occupied source choice, and the unique deterministic post-branch ledger. -/
theorem raw_reconstruct (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head)
    (h : RawPhysicalMacroHistory p hnt logicalBlank read q hlive tape head) :
    ∃ (choice : SourceChoice p q read)
      (preCanon postCanon : List (Arrow (program p hnt logicalBlank))),
      nonbranchArrows p hnt logicalBlank
        (liftReaderConfig q
          (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head)) nt = some preCanon ∧
      h.pre = preCanon ∧
      h.branch = branchArrow p hnt logicalBlank q read choice.slot (tape (head + nt)) hlive
        choice.action choice.occupied ∧
      nonbranchArrows p hnt logicalBlank
        (rewindInitial hnt q read (choice.slot = 1) choice.action tape (head + nt))
        (2 * nt + relocationDistance choice.action.move nt + 1) = some postCanon ∧
      h.post = postCanon ∧
      h.endpoint = fullEndpoint hnt choice.action tape head ∧
      h.arrows = preCanon ++
        branchArrow p hnt logicalBlank q read choice.slot (tape (head + nt)) hlive
          choice.action choice.occupied :: postCanon := by
  obtain ⟨choice, hbranch, hbranchOut⟩ := raw_extract_choice p hnt logicalBlank read q
    hlive tape head h
  have hinitial : initialPhysical hnt logicalBlank q tape head =
      liftReaderConfig q (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head) := by
    rfl
  obtain ⟨preCanon, hpreCanon, hpreEq, hpreOut⟩ := reader_successful_run_unique
    p hnt logicalBlank read q hlive tape head hone h.pre
    ({ state := .branch q read, head := head + nt, tape := tape } : Config (State ns nt) Tape)
    h.pre_length (by rw [← hinitial]; exact h.pre_run)
  have hlength := raw_post_length_exact p hnt logicalBlank read q hlive tape head h choice hbranchOut
  have hprefixes := successful_prefixes_are_canonical p hnt logicalBlank
    h.post h.branch_out h.endpoint h.post_run h.post_no_branch
  have havoid : ∀ k : ℕ, k < 2 * nt + relocationDistance choice.action.move nt + 1 →
      ∀ q' read',
        ((nextMicroConfig hnt logicalBlank)^[k]
          (rewindInitial hnt q read (choice.slot = 1) choice.action tape (head + nt))).state ≠
          State.branch q' read' := by
    intro k hk q' read'
    have hcan := (hprefixes k (by rw [hlength]; omega)).2 (by rw [hlength]; omega) q' read'
    rw [hbranchOut] at hcan
    simpa [ULogSourceOneHotPhysicalMacro.branchResult, rewindInitial] using hcan
  have hbranchInitial : branchResult q read choice.slot choice.action tape (head + nt) =
      rewindInitial hnt q read (choice.slot = 1) choice.action tape (head + nt) := by
    apply config_ext <;> simp [ULogSourceOneHotPhysicalMacro.branchResult, rewindInitial]
  have hpostRun := h.post_run
  rw [hbranchOut, hbranchInitial] at hpostRun
  obtain ⟨postCanon, hpostCanon, hpostEq, hpostOut⟩ :=
    nonbranch_successful_run_unique_of_avoids p hnt logicalBlank
      (rewindInitial hnt q read (choice.slot = 1) choice.action tape (head + nt))
      (2 * nt + relocationDistance choice.action.move nt + 1) havoid h.post h.endpoint
      (by rw [hlength]) hpostRun
  refine ⟨choice, preCanon, postCanon, hpreCanon, hpreEq, hbranch, hpostCanon, hpostEq, ?_, ?_⟩
  · rw [hpostOut, correct_post_endpoint hnt logicalBlank q read
      (choice.slot = 1) choice.action tape head]
  · rw [h.decomposes, hpreEq, hbranch, hpostEq]

theorem blank_raw_reconstruct (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) =
      ULogSourceLogicalBlockReader.blank)
    (h : RawPhysicalMacroHistory p hnt logicalBlank logicalBlank q hlive tape head) :
    ∃ (choice : SourceChoice p q logicalBlank)
      (preCanon postCanon : List (Arrow (program p hnt logicalBlank))),
      nonbranchArrows p hnt logicalBlank
        (liftReaderConfig q
          (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head)) nt = some preCanon ∧
      h.pre = preCanon ∧
      h.branch = branchArrow p hnt logicalBlank q logicalBlank choice.slot
        (tape (head + nt)) hlive choice.action choice.occupied ∧
      nonbranchArrows p hnt logicalBlank
        (rewindInitial hnt q logicalBlank (choice.slot = 1) choice.action tape
          (head + nt))
        (2 * nt + relocationDistance choice.action.move nt + 1) = some postCanon ∧
      h.post = postCanon ∧
      h.endpoint = fullEndpoint hnt choice.action tape head ∧
      h.arrows = preCanon ++
        branchArrow p hnt logicalBlank q logicalBlank choice.slot
          (tape (head + nt)) hlive choice.action choice.occupied :: postCanon := by
  obtain ⟨choice, hbranch, hbranchOut⟩ := raw_extract_choice p hnt
    logicalBlank logicalBlank q hlive tape head h
  have hinitial : initialPhysical hnt logicalBlank q tape head =
      liftReaderConfig q
        (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head) := rfl
  obtain ⟨preCanon, hpreCanon, hpreEq, -⟩ :=
    blank_reader_successful_run_unique p hnt logicalBlank q hlive tape head
      hblank h.pre
      ({ state := .branch q logicalBlank, head := head + nt, tape := tape } :
        Config (State ns nt) Tape)
      h.pre_length (by rw [← hinitial]; exact h.pre_run)
  have hlength := raw_post_length_exact p hnt logicalBlank logicalBlank q
    hlive tape head h choice hbranchOut
  have hprefixes := successful_prefixes_are_canonical p hnt logicalBlank
    h.post h.branch_out h.endpoint h.post_run h.post_no_branch
  have havoid : ∀ k : ℕ,
      k < 2 * nt + relocationDistance choice.action.move nt + 1 →
      ∀ q' read',
        ((nextMicroConfig hnt logicalBlank)^[k]
          (rewindInitial hnt q logicalBlank (choice.slot = 1) choice.action
            tape (head + nt))).state ≠ State.branch q' read' := by
    intro k hk q' read'
    have hcan := (hprefixes k (by rw [hlength]; omega)).2
      (by rw [hlength]; omega) q' read'
    rw [hbranchOut] at hcan
    simpa [ULogSourceOneHotPhysicalMacro.branchResult, rewindInitial] using hcan
  have hbranchInitial : branchResult q logicalBlank choice.slot choice.action
      tape (head + nt) =
      rewindInitial hnt q logicalBlank (choice.slot = 1) choice.action tape
        (head + nt) := by
    apply config_ext <;>
      simp [ULogSourceOneHotPhysicalMacro.branchResult, rewindInitial]
  have hpostRun := h.post_run
  rw [hbranchOut, hbranchInitial] at hpostRun
  obtain ⟨postCanon, hpostCanon, hpostEq, hpostOut⟩ :=
    nonbranch_successful_run_unique_of_avoids p hnt logicalBlank
      (rewindInitial hnt q logicalBlank (choice.slot = 1) choice.action tape
        (head + nt))
      (2 * nt + relocationDistance choice.action.move nt + 1) havoid
      h.post h.endpoint (by rw [hlength]) hpostRun
  refine ⟨choice, preCanon, postCanon, hpreCanon, hpreEq, hbranch,
    hpostCanon, hpostEq, ?_, ?_⟩
  · rw [hpostOut, correct_post_endpoint hnt logicalBlank q logicalBlank
      (choice.slot = 1) choice.action tape head]
  · rw [h.decomposes, hpreEq, hbranch, hpostEq]

/-- The canonical deterministic post-branch arrow ledger, retaining all
literal slot-zero arrows from rewind, writer, and relocation. -/
noncomputable def canonicalPost (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (choice : SourceChoice p q read) (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    List (Arrow (program p hnt logicalBlank)) :=
  let data := canonicalData p hnt logicalBlank read q hlive choice tape head hone
  data.rewind ++ data.writer ++ data.relocate

theorem canonicalPost_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (choice : SourceChoice p q read) (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    (canonicalPost p hnt logicalBlank read q hlive choice tape head hone).length =
      2 * nt + relocationDistance choice.action.move nt + 1 := by
  unfold canonicalPost
  let data := canonicalData p hnt logicalBlank read q hlive choice tape head hone
  have hr := nonbranchArrows_length p hnt logicalBlank
    (rewindInitial hnt q read (choice.slot = 1) choice.action tape (head + nt))
    nt data.rewind data.rewind_ok
  have hw := nonbranchArrows_length p hnt logicalBlank
    (writerInitial hnt choice.action tape head) nt data.writer data.writer_ok
  have hl := nonbranchArrows_length p hnt logicalBlank
    (relocateInitial choice.action
      (ULogSourceOneHotWriter.writePrefix choice.action.write head tape nt) (head + nt))
    (relocationDistance choice.action.move nt + 1) data.relocate data.relocate_ok
  change (data.rewind ++ data.writer ++ data.relocate).length = _
  simp [hr, hw, hl]
  omega

theorem canonicalPost_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (choice : SourceChoice p q read) (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    run (program p hnt logicalBlank) (fun _ => true)
      (canonicalPost p hnt logicalBlank read q hlive choice tape head hone)
      (rewindInitial hnt q read (choice.slot = 1) choice.action tape (head + nt)) =
      some (fullEndpoint hnt choice.action tape head) := by
  let data := canonicalData p hnt logicalBlank read q hlive choice tape head hone
  have hrewRun := nonbranchArrows_run p hnt logicalBlank
    (rewindInitial hnt q read (choice.slot = 1) choice.action tape (head + nt))
    nt data.rewind data.rewind_ok
  have hrewEnd :
      ((nextMicroConfig hnt logicalBlank)^[nt]
        (rewindInitial hnt q read (choice.slot = 1) choice.action tape (head + nt))) =
      writerInitial hnt choice.action tape head := by
    rw [rewind_operational_terminal]
    apply config_ext <;> simp [writerInitial] <;> omega
  have hwriterRun := nonbranchArrows_run p hnt logicalBlank
    (writerInitial hnt choice.action tape head) nt data.writer data.writer_ok
  have hwriterEnd :
      ((nextMicroConfig hnt logicalBlank)^[nt]
        (writerInitial hnt choice.action tape head)) =
      relocateInitial choice.action
        (ULogSourceOneHotWriter.writePrefix choice.action.write head tape nt) (head + nt) := by
    rw [writer_operational_terminal]
    apply config_ext
    · simp only [relocateInitial, relocateExpected]
      congr
    · simp [relocateInitial, relocateExpected]
    · simp [relocateInitial, relocateExpected]
  have hrelocateRun := nonbranchArrows_run p hnt logicalBlank
    (relocateInitial choice.action
      (ULogSourceOneHotWriter.writePrefix choice.action.write head tape nt) (head + nt))
    (relocationDistance choice.action.move nt + 1) data.relocate data.relocate_ok
  have hrelocateEnd := relocate_operational_terminal hnt logicalBlank choice.action
    (ULogSourceOneHotWriter.writePrefix choice.action.write head tape nt) (head + nt)
  unfold canonicalPost
  change run (program p hnt logicalBlank) (fun _ => true)
      (data.rewind ++ data.writer ++ data.relocate)
      (rewindInitial hnt q read (choice.slot = 1) choice.action tape (head + nt)) = _
  rw [List.append_assoc]
  apply ULogSourceOneHotFullMacro.run_append_some p hnt logicalBlank data.rewind
    (data.writer ++ data.relocate) _ _ _
  · rw [hrewRun, hrewEnd]
  · apply ULogSourceOneHotFullMacro.run_append_some p hnt logicalBlank data.writer data.relocate _ _ _
    · rw [hwriterRun, hwriterEnd]
    · rw [hrelocateRun, hrelocateEnd]
      rfl

theorem canonicalPost_no_branch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (choice : SourceChoice p q read) (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    ∀ n : ℕ,
      n ≤ (canonicalPost p hnt logicalBlank read q hlive choice tape head hone).length →
      ∀ c,
        run (program p hnt logicalBlank) (fun _ => true)
            ((canonicalPost p hnt logicalBlank read q hlive choice tape head hone).take n)
            (rewindInitial hnt q read (choice.slot = 1) choice.action tape (head + nt)) =
              some c →
          ∀ q' read', c.state ≠ State.branch q' read' := by
  intro n hn c hrun q' read'
  have hlength := canonicalPost_length p hnt logicalBlank read q hlive
    choice tape head hone
  by_cases hproper : n <
      (canonicalPost p hnt logicalBlank read q hlive choice tape head hone).length
  · have htakeLength :
        ((canonicalPost p hnt logicalBlank read q hlive choice tape head hone).take n).length = n := by
      rw [List.length_take, Nat.min_eq_left hn]
    have havoid : ∀ k : ℕ, k < n → ∀ q'' read'',
        ((nextMicroConfig hnt logicalBlank)^[k]
          (rewindInitial hnt q read (choice.slot = 1) choice.action tape
            (head + nt))).state ≠ State.branch q'' read'' := by
      intro k hk
      apply post_iterate_avoids_branch hnt logicalBlank q read
        (choice.slot = 1) choice.action tape head k
      rw [← hlength]
      omega
    obtain ⟨-, -, -, hout⟩ := nonbranch_successful_run_unique_of_avoids
      p hnt logicalBlank
      (rewindInitial hnt q read (choice.slot = 1) choice.action tape (head + nt))
      n havoid
      ((canonicalPost p hnt logicalBlank read q hlive choice tape head hone).take n)
      c htakeLength hrun
    rw [hout]
    apply post_iterate_avoids_branch hnt logicalBlank q read
      (choice.slot = 1) choice.action tape head n
    rw [← hlength]
    exact hproper
  · have hnEq : n =
        (canonicalPost p hnt logicalBlank read q hlive choice tape head hone).length := by
      omega
    subst n
    rw [List.take_length] at hrun
    have hfull := canonicalPost_run p hnt logicalBlank read q hlive
      choice tape head hone
    have hc : c = fullEndpoint hnt choice.action tape head :=
      Option.some.inj (hrun.symm.trans hfull)
    rw [hc]
    simp [fullEndpoint]

theorem canonicalPost_first_return (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (choice : SourceChoice p q read) (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    ∀ n : ℕ,
      n < (canonicalPost p hnt logicalBlank read q hlive choice tape head hone).length →
      ∀ c,
        run (program p hnt logicalBlank) (fun _ => true)
            ((canonicalPost p hnt logicalBlank read q hlive choice tape head hone).take n)
            (rewindInitial hnt q read (choice.slot = 1) choice.action tape (head + nt)) =
              some c →
          ∀ target, c.state ≠ State.reading target (initialReaderState hnt) := by
  intro n hn c hrun target
  have hlength := canonicalPost_length p hnt logicalBlank read q hlive
    choice tape head hone
  have htakeLength :
      ((canonicalPost p hnt logicalBlank read q hlive choice tape head hone).take n).length = n := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)]
  have havoid : ∀ k : ℕ, k < n → ∀ q' read',
      ((nextMicroConfig hnt logicalBlank)^[k]
        (rewindInitial hnt q read (choice.slot = 1) choice.action tape
          (head + nt))).state ≠ State.branch q' read' := by
    intro k hk
    apply post_iterate_avoids_branch hnt logicalBlank q read
      (choice.slot = 1) choice.action tape head k
    rw [← hlength]
    omega
  obtain ⟨-, -, -, hout⟩ := nonbranch_successful_run_unique_of_avoids
    p hnt logicalBlank
    (rewindInitial hnt q read (choice.slot = 1) choice.action tape (head + nt))
    n havoid
    ((canonicalPost p hnt logicalBlank read q hlive choice tape head hone).take n)
    c htakeLength hrun
  rw [hout]
  apply post_iterate_not_reader_before hnt logicalBlank q read
    (choice.slot = 1) choice.action tape head n
  rw [← hlength]
  exact hn

/-- Every occupied source choice produces a choice-free raw history satisfying
the operational first-return grammar. -/
noncomputable def rawForward (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head)
    (choice : SourceChoice p q read) :
    RawPhysicalMacroHistory p hnt logicalBlank read q hlive tape head := by
  let data := canonicalData p hnt logicalBlank read q hlive choice tape head hone
  let pre := readerHistory p hnt logicalBlank q tape head
  let post := canonicalPost p hnt logicalBlank read q hlive choice tape head hone
  let branch := branchArrow p hnt logicalBlank q read choice.slot
    (tape (head + nt)) hlive choice.action choice.occupied
  let branchOut := branchResult q read choice.slot choice.action tape (head + nt)
  let endpoint := fullEndpoint hnt choice.action tape head
  refine
    { arrows := fullArrows p hnt logicalBlank pre data.rewind data.writer
        data.relocate branch
      endpoint := endpoint
      branch := branch
      branch_out := branchOut
      pre := pre
      post := post
      decomposes := ?_
      pre_length := ?_
      post_length := ?_
      pre_run := ?_
      run_ok := ?_
      branch_step := ?_
      post_run := ?_
      post_no_branch := ?_
      endpoint_reader := ?_
      first_return := ?_ }
  · simp [fullArrows, pre, post, canonicalPost, data, branch]
  · exact readerHistory_length p hnt logicalBlank q tape head
  · have hlen := canonicalPost_length p hnt logicalBlank read q hlive
      choice tape head hone
    dsimp [post]
    cases hm : choice.action.move with
    | left => right; right; simp [relocationDistance, hm] at hlen; omega
    | stay => right; left; simp [relocationDistance, hm] at hlen; omega
    | right => left; simpa [relocationDistance, hm] using hlen
  · have hrun := readerPrefix_oneHot_run p hnt logicalBlank read q hlive
      tape head hone pre rfl
    simpa [initialPhysical, liftReaderConfig, liftReaderControl, pre] using hrun
  · exact data.run_ok
  · exact branchArrow_step p hnt logicalBlank q read choice.slot
      choice.action hlive choice.occupied tape (head + nt)
  · exact canonicalPost_run p hnt logicalBlank read q hlive choice tape head hone
  · exact canonicalPost_no_branch p hnt logicalBlank read q hlive
      choice tape head hone
  · exact ⟨choice.action.target, rfl⟩
  · exact canonicalPost_first_return p hnt logicalBlank read q hlive
      choice tape head hone

theorem readerHistory_nonbranchArrows (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    nonbranchArrows p hnt logicalBlank
      (liftReaderConfig q
        (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head)) nt =
      some (readerHistory p hnt logicalBlank q tape head) := by
  have hrun := readerPrefix_oneHot_run p hnt logicalBlank read q hlive tape head hone
    (readerHistory p hnt logicalBlank q tape head) rfl
  obtain ⟨bs, hbs, hsame, -⟩ := reader_successful_run_unique
    p hnt logicalBlank read q hlive tape head hone
    (readerHistory p hnt logicalBlank q tape head)
    ({ state := .branch q read, head := head + nt, tape := tape } : Config (State ns nt) Tape)
    (readerHistory_length p hnt logicalBlank q tape head) hrun
  simpa [hsame] using hbs

theorem canonicalPost_nonbranchArrows (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (choice : SourceChoice p q read) (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    nonbranchArrows p hnt logicalBlank
      (rewindInitial hnt q read (choice.slot = 1) choice.action tape (head + nt))
      (2 * nt + relocationDistance choice.action.move nt + 1) =
      some (canonicalPost p hnt logicalBlank read q hlive choice tape head hone) := by
  have hrun := canonicalPost_run p hnt logicalBlank read q hlive choice tape head hone
  have hlen := canonicalPost_length p hnt logicalBlank read q hlive choice tape head hone
  obtain ⟨bs, hbs, hsame, -⟩ := nonbranch_successful_run_unique_of_avoids
    p hnt logicalBlank
    (rewindInitial hnt q read (choice.slot = 1) choice.action tape (head + nt))
    (2 * nt + relocationDistance choice.action.move nt + 1)
    (by
      intro k hk q' read'
      apply post_iterate_avoids_branch hnt logicalBlank q read
        (choice.slot = 1) choice.action tape head k
      omega)
    (canonicalPost p hnt logicalBlank read q hlive choice tape head hone)
    (fullEndpoint hnt choice.action tape head) hlen hrun
  simpa [hsame] using hbs

noncomputable def rawBackwardCore (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (h : RawPhysicalMacroHistory p hnt logicalBlank read q hlive tape head) :
    SourceChoice p q read :=
  Classical.choose (raw_extract_choice p hnt logicalBlank read q hlive
    tape head h)

noncomputable def rawBackward (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head)
    (h : RawPhysicalMacroHistory p hnt logicalBlank read q hlive tape head) :
    SourceChoice p q read :=
  rawBackwardCore p hnt logicalBlank read q hlive tape head h

theorem rawBackward_spec (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head)
    (h : RawPhysicalMacroHistory p hnt logicalBlank read q hlive tape head) :
    h.branch = branchArrow p hnt logicalBlank q read
        (rawBackward p hnt logicalBlank read q hlive tape head hone h).slot
        (tape (head + nt)) hlive
        (rawBackward p hnt logicalBlank read q hlive tape head hone h).action
        (rawBackward p hnt logicalBlank read q hlive tape head hone h).occupied ∧
      h.branch_out = branchResult q read
        (rawBackward p hnt logicalBlank read q hlive tape head hone h).slot
        (rawBackward p hnt logicalBlank read q hlive tape head hone h).action
        tape (head + nt) := by
  exact Classical.choose_spec (raw_extract_choice p hnt logicalBlank read q
    hlive tape head h)

theorem extracted_choice_unique (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (choice₁ choice₂ : SourceChoice p q read)
    (h : branchArrow p hnt logicalBlank q read choice₁.slot
        (tape (head + nt)) hlive choice₁.action choice₁.occupied =
      branchArrow p hnt logicalBlank q read choice₂.slot
        (tape (head + nt)) hlive choice₂.action choice₂.occupied) :
    choice₁ = choice₂ := by
  apply SourceChoice.ext
  simpa [branchArrow] using
    congrArg (fun arrow : Arrow (program p hnt logicalBlank) => arrow.1.2) h

theorem rawBackward_rawForward (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head)
    (choice : SourceChoice p q read) :
    rawBackward p hnt logicalBlank read q hlive tape head hone
      (rawForward p hnt logicalBlank read q hlive tape head hone choice) = choice := by
  have hspec := (rawBackward_spec p hnt logicalBlank read q hlive tape head
    hone (rawForward p hnt logicalBlank read q hlive tape head hone choice)).1
  apply extracted_choice_unique p hnt logicalBlank read q hlive tape head
  simpa [rawForward] using hspec.symm

theorem raw_data_identification (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head)
    (h : RawPhysicalMacroHistory p hnt logicalBlank read q hlive tape head) :
    let choice := rawBackward p hnt logicalBlank read q hlive tape head hone h
    h.pre = readerHistory p hnt logicalBlank q tape head ∧
      h.branch = branchArrow p hnt logicalBlank q read choice.slot
        (tape (head + nt)) hlive choice.action choice.occupied ∧
      h.branch_out = branchResult q read choice.slot choice.action tape (head + nt) ∧
      h.post = canonicalPost p hnt logicalBlank read q hlive choice tape head hone ∧
      h.endpoint = fullEndpoint hnt choice.action tape head ∧
      h.arrows = canonicalArrows p hnt logicalBlank read q hlive choice tape head hone := by
  dsimp
  obtain ⟨choice', preCanon, postCanon, hpreN, hpreEq, hbranch,
    hpostN, hpostEq, hend, harrows⟩ :=
    raw_reconstruct p hnt logicalBlank read q hlive tape head hone h
  have hspec := rawBackward_spec p hnt logicalBlank read q hlive tape head hone h
  have hchoice : choice' =
      rawBackward p hnt logicalBlank read q hlive tape head hone h := by
    apply extracted_choice_unique p hnt logicalBlank read q hlive tape head
    exact hbranch.symm.trans hspec.1
  subst choice'
  have hreaderN := readerHistory_nonbranchArrows p hnt logicalBlank read q
    hlive tape head hone
  have hpreCanon : preCanon = readerHistory p hnt logicalBlank q tape head :=
    Option.some.inj (hpreN.symm.trans hreaderN)
  have hpostCanonical := canonicalPost_nonbranchArrows p hnt logicalBlank read q
    hlive (rawBackward p hnt logicalBlank read q hlive tape head hone h)
    tape head hone
  have hpostCanon : postCanon = canonicalPost p hnt logicalBlank read q hlive
      (rawBackward p hnt logicalBlank read q hlive tape head hone h)
      tape head hone := Option.some.inj (hpostN.symm.trans hpostCanonical)
  refine ⟨hpreEq.trans hpreCanon, hspec.1, hspec.2,
    hpostEq.trans hpostCanon, hend, ?_⟩
  rw [harrows, hpreCanon, hpostCanon]
  unfold canonicalArrows canonicalPost
  simp [fullArrows, List.append_assoc]

theorem RawPhysicalMacroHistory.ext
    {p : BoundedProgram ns nt} {hnt : 0 < nt} {logicalBlank read : Fin nt}
    {q : Fin ns} {hlive : haltedSource q = false} {tape : Int → Tape}
    {head : Int}
    {h₁ h₂ : RawPhysicalMacroHistory p hnt logicalBlank read q hlive tape head}
    (harrows : h₁.arrows = h₂.arrows)
    (hendpoint : h₁.endpoint = h₂.endpoint)
    (hbranch : h₁.branch = h₂.branch)
    (hbranchOut : h₁.branch_out = h₂.branch_out)
    (hpre : h₁.pre = h₂.pre) (hpost : h₁.post = h₂.post) : h₁ = h₂ := by
  cases h₁
  cases h₂
  simp_all

noncomputable def rawSourceChoiceEquiv (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (logicalBlank read : Fin nt) (q : Fin ns)
    (hlive : haltedSource q = false) (tape : Int → Tape) (head : Int)
    (hone : ULogSourceLogicalBlockReader.IsOneHotAt read tape head) :
    SourceChoice p q read ≃
      RawPhysicalMacroHistory p hnt logicalBlank read q hlive tape head where
  toFun := rawForward p hnt logicalBlank read q hlive tape head hone
  invFun := rawBackward p hnt logicalBlank read q hlive tape head hone
  left_inv := rawBackward_rawForward p hnt logicalBlank read q hlive tape head hone
  right_inv := by
    intro h
    obtain ⟨hpre, hbranch, hbranchOut, hpost, hendpoint, harrows⟩ :=
      raw_data_identification p hnt logicalBlank read q hlive tape head hone h
    apply RawPhysicalMacroHistory.ext
    · simpa [rawForward, canonicalArrows, canonicalPost, fullArrows,
        List.append_assoc] using harrows.symm
    · simpa [rawForward] using hendpoint.symm
    · simpa [rawForward] using hbranch.symm
    · simpa [rawForward] using hbranchOut.symm
    · simpa [rawForward] using hpre.symm
    · simpa [rawForward] using hpost.symm

structure BlankCanonicalData (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (choice : SourceChoice p q logicalBlank) (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) =
      ULogSourceLogicalBlockReader.blank) where
  rewind : List (Arrow (program p hnt logicalBlank))
  writer : List (Arrow (program p hnt logicalBlank))
  relocate : List (Arrow (program p hnt logicalBlank))
  rewind_ok : nonbranchArrows p hnt logicalBlank
    (rewindInitial hnt q logicalBlank (choice.slot = 1) choice.action tape
      (head + nt)) nt = some rewind
  writer_ok : nonbranchArrows p hnt logicalBlank
    (writerInitial hnt choice.action tape head) nt = some writer
  relocate_ok : nonbranchArrows p hnt logicalBlank
    (relocateInitial choice.action
      (ULogSourceOneHotWriter.writePrefix choice.action.write head tape nt)
      (head + nt))
    (relocationDistance choice.action.move nt + 1) = some relocate
  run_ok : run (program p hnt logicalBlank) (fun _ => true)
    (fullArrows p hnt logicalBlank
      (readerHistory p hnt logicalBlank q tape head) rewind writer relocate
      (branchArrow p hnt logicalBlank q logicalBlank choice.slot
        (tape (head + nt)) hlive choice.action choice.occupied))
    (initialPhysical hnt logicalBlank q tape head) =
      some (fullEndpoint hnt choice.action tape head)

theorem blankCanonicalData_exists (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (choice : SourceChoice p q logicalBlank) (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) =
      ULogSourceLogicalBlockReader.blank) :
    Nonempty (BlankCanonicalData p hnt logicalBlank q hlive choice tape head hblank) := by
  obtain ⟨rewind, writer, relocate, hrewind, hwriter, hrelocate, hrun⟩ :=
    blank_occupied_action_forward p hnt logicalBlank q hlive choice.slot
      choice.action choice.occupied tape head hblank
      (readerHistory p hnt logicalBlank q tape head) rfl
  exact ⟨⟨rewind, writer, relocate, hrewind, hwriter, hrelocate, hrun⟩⟩

noncomputable def blankCanonicalData (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (logicalBlank : Fin nt) (q : Fin ns)
    (hlive : haltedSource q = false) (choice : SourceChoice p q logicalBlank)
    (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) =
      ULogSourceLogicalBlockReader.blank) :
    BlankCanonicalData p hnt logicalBlank q hlive choice tape head hblank :=
  Classical.choice (blankCanonicalData_exists p hnt logicalBlank q hlive
    choice tape head hblank)

noncomputable def blankCanonicalPost (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (logicalBlank : Fin nt) (q : Fin ns)
    (hlive : haltedSource q = false) (choice : SourceChoice p q logicalBlank)
    (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) =
      ULogSourceLogicalBlockReader.blank) :
    List (Arrow (program p hnt logicalBlank)) :=
  let data := blankCanonicalData p hnt logicalBlank q hlive choice tape head hblank
  data.rewind ++ data.writer ++ data.relocate

theorem blankCanonicalPost_length (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (choice : SourceChoice p q logicalBlank) (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) =
      ULogSourceLogicalBlockReader.blank) :
    (blankCanonicalPost p hnt logicalBlank q hlive choice tape head hblank).length =
      2 * nt + relocationDistance choice.action.move nt + 1 := by
  unfold blankCanonicalPost
  let data := blankCanonicalData p hnt logicalBlank q hlive choice tape head hblank
  have hr := nonbranchArrows_length p hnt logicalBlank
    (rewindInitial hnt q logicalBlank (choice.slot = 1) choice.action tape
      (head + nt)) nt data.rewind data.rewind_ok
  have hw := nonbranchArrows_length p hnt logicalBlank
    (writerInitial hnt choice.action tape head) nt data.writer data.writer_ok
  have hl := nonbranchArrows_length p hnt logicalBlank
    (relocateInitial choice.action
      (ULogSourceOneHotWriter.writePrefix choice.action.write head tape nt)
      (head + nt)) (relocationDistance choice.action.move nt + 1)
    data.relocate data.relocate_ok
  change (data.rewind ++ data.writer ++ data.relocate).length = _
  simp [hr, hw, hl]
  omega

theorem blankCanonicalPost_run (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (choice : SourceChoice p q logicalBlank) (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) =
      ULogSourceLogicalBlockReader.blank) :
    run (program p hnt logicalBlank) (fun _ => true)
      (blankCanonicalPost p hnt logicalBlank q hlive choice tape head hblank)
      (rewindInitial hnt q logicalBlank (choice.slot = 1) choice.action tape
        (head + nt)) = some (fullEndpoint hnt choice.action tape head) := by
  let data := blankCanonicalData p hnt logicalBlank q hlive choice tape head hblank
  have hrewRun := nonbranchArrows_run p hnt logicalBlank
    (rewindInitial hnt q logicalBlank (choice.slot = 1) choice.action tape
      (head + nt)) nt data.rewind data.rewind_ok
  have hrewEnd :
      ((nextMicroConfig hnt logicalBlank)^[nt]
        (rewindInitial hnt q logicalBlank (choice.slot = 1) choice.action tape
          (head + nt))) = writerInitial hnt choice.action tape head := by
    rw [rewind_operational_terminal]
    apply config_ext <;> simp [writerInitial] <;> omega
  have hwriterRun := nonbranchArrows_run p hnt logicalBlank
    (writerInitial hnt choice.action tape head) nt data.writer data.writer_ok
  have hwriterEnd :
      ((nextMicroConfig hnt logicalBlank)^[nt]
        (writerInitial hnt choice.action tape head)) =
      relocateInitial choice.action
        (ULogSourceOneHotWriter.writePrefix choice.action.write head tape nt)
        (head + nt) := by
    rw [writer_operational_terminal]
    apply config_ext
    · simp only [relocateInitial, relocateExpected]
      congr
    · simp [relocateInitial, relocateExpected]
    · simp [relocateInitial, relocateExpected]
  have hrelocateRun := nonbranchArrows_run p hnt logicalBlank
    (relocateInitial choice.action
      (ULogSourceOneHotWriter.writePrefix choice.action.write head tape nt)
      (head + nt)) (relocationDistance choice.action.move nt + 1)
    data.relocate data.relocate_ok
  have hrelocateEnd := relocate_operational_terminal hnt logicalBlank
    choice.action
    (ULogSourceOneHotWriter.writePrefix choice.action.write head tape nt)
    (head + nt)
  unfold blankCanonicalPost
  change run (program p hnt logicalBlank) (fun _ => true)
      (data.rewind ++ data.writer ++ data.relocate)
      (rewindInitial hnt q logicalBlank (choice.slot = 1) choice.action tape
        (head + nt)) = _
  rw [List.append_assoc]
  apply ULogSourceOneHotFullMacro.run_append_some p hnt logicalBlank
    data.rewind (data.writer ++ data.relocate) _ _ _
  · rw [hrewRun, hrewEnd]
  · apply ULogSourceOneHotFullMacro.run_append_some p hnt logicalBlank
      data.writer data.relocate _ _ _
    · rw [hwriterRun, hwriterEnd]
    · rw [hrelocateRun, hrelocateEnd]
      rfl

theorem postLedger_no_branch (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (slot : Bool)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int)
    (post : List (Arrow (program p hnt logicalBlank)))
    (hlength : post.length = 2 * nt + relocationDistance a.move nt + 1)
    (hfull : run (program p hnt logicalBlank) (fun _ => true) post
      (rewindInitial hnt q read slot a tape (head + nt)) =
        some (fullEndpoint hnt a tape head)) :
    ∀ n : ℕ, n ≤ post.length → ∀ c,
      run (program p hnt logicalBlank) (fun _ => true) (post.take n)
        (rewindInitial hnt q read slot a tape (head + nt)) = some c →
      ∀ q' read', c.state ≠ State.branch q' read' := by
  intro n hn c hrun q' read'
  by_cases hproper : n < post.length
  · have htakeLength : (post.take n).length = n := by
      rw [List.length_take, Nat.min_eq_left hn]
    have havoid : ∀ k : ℕ, k < n → ∀ q'' read'',
        ((nextMicroConfig hnt logicalBlank)^[k]
          (rewindInitial hnt q read slot a tape (head + nt))).state ≠
          State.branch q'' read'' := by
      intro k hk
      apply post_iterate_avoids_branch hnt logicalBlank q read slot a tape head k
      rw [← hlength]
      omega
    obtain ⟨-, -, -, hout⟩ := nonbranch_successful_run_unique_of_avoids
      p hnt logicalBlank (rewindInitial hnt q read slot a tape (head + nt))
      n havoid (post.take n) c htakeLength hrun
    rw [hout]
    apply post_iterate_avoids_branch hnt logicalBlank q read slot a tape head n
    rw [← hlength]
    exact hproper
  · have hnEq : n = post.length := by omega
    subst n
    rw [List.take_length] at hrun
    have hc : c = fullEndpoint hnt a tape head :=
      Option.some.inj (hrun.symm.trans hfull)
    rw [hc]
    simp [fullEndpoint]

theorem postLedger_first_return (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (slot : Bool)
    (a : BoundedAction ns nt) (tape : Int → Tape) (head : Int)
    (post : List (Arrow (program p hnt logicalBlank)))
    (hlength : post.length = 2 * nt + relocationDistance a.move nt + 1) :
    ∀ n : ℕ, n < post.length → ∀ c,
      run (program p hnt logicalBlank) (fun _ => true) (post.take n)
        (rewindInitial hnt q read slot a tape (head + nt)) = some c →
      ∀ target, c.state ≠ State.reading target (initialReaderState hnt) := by
  intro n hn c hrun target
  have htakeLength : (post.take n).length = n := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)]
  have havoid : ∀ k : ℕ, k < n → ∀ q' read',
      ((nextMicroConfig hnt logicalBlank)^[k]
        (rewindInitial hnt q read slot a tape (head + nt))).state ≠
      State.branch q' read' := by
    intro k hk
    apply post_iterate_avoids_branch hnt logicalBlank q read slot a tape head k
    rw [← hlength]
    omega
  obtain ⟨-, -, -, hout⟩ := nonbranch_successful_run_unique_of_avoids
    p hnt logicalBlank (rewindInitial hnt q read slot a tape (head + nt))
    n havoid (post.take n) c htakeLength hrun
  rw [hout]
  apply post_iterate_not_reader_before hnt logicalBlank q read slot a tape head n
  rw [← hlength]
  exact hn

def blankCanonicalPost_no_branch (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (logicalBlank : Fin nt) (q : Fin ns)
    (hlive : haltedSource q = false) (choice : SourceChoice p q logicalBlank)
    (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) =
      ULogSourceLogicalBlockReader.blank) :=
  postLedger_no_branch p hnt logicalBlank logicalBlank q (choice.slot = 1)
    choice.action tape head
    (blankCanonicalPost p hnt logicalBlank q hlive choice tape head hblank)
    (blankCanonicalPost_length p hnt logicalBlank q hlive choice tape head hblank)
    (blankCanonicalPost_run p hnt logicalBlank q hlive choice tape head hblank)

def blankCanonicalPost_first_return (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (logicalBlank : Fin nt) (q : Fin ns)
    (hlive : haltedSource q = false) (choice : SourceChoice p q logicalBlank)
    (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) =
      ULogSourceLogicalBlockReader.blank) :=
  postLedger_first_return p hnt logicalBlank logicalBlank q (choice.slot = 1)
    choice.action tape head
    (blankCanonicalPost p hnt logicalBlank q hlive choice tape head hblank)
    (blankCanonicalPost_length p hnt logicalBlank q hlive choice tape head hblank)

noncomputable def blankRawForward (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) =
      ULogSourceLogicalBlockReader.blank)
    (choice : SourceChoice p q logicalBlank) :
    RawPhysicalMacroHistory p hnt logicalBlank logicalBlank q hlive tape head := by
  let data := blankCanonicalData p hnt logicalBlank q hlive choice tape head hblank
  let pre := readerHistory p hnt logicalBlank q tape head
  let post := blankCanonicalPost p hnt logicalBlank q hlive choice tape head hblank
  let branch := branchArrow p hnt logicalBlank q logicalBlank choice.slot
    (tape (head + nt)) hlive choice.action choice.occupied
  let branchOut := branchResult q logicalBlank choice.slot choice.action tape
    (head + nt)
  let endpoint := fullEndpoint hnt choice.action tape head
  refine
    { arrows := fullArrows p hnt logicalBlank pre data.rewind data.writer
        data.relocate branch
      endpoint := endpoint
      branch := branch
      branch_out := branchOut
      pre := pre
      post := post
      decomposes := ?_
      pre_length := ?_
      post_length := ?_
      pre_run := ?_
      run_ok := ?_
      branch_step := ?_
      post_run := ?_
      post_no_branch := ?_
      endpoint_reader := ?_
      first_return := ?_ }
  · simp [fullArrows, pre, post, blankCanonicalPost, data, branch]
  · exact readerHistory_length p hnt logicalBlank q tape head
  · have hlen := blankCanonicalPost_length p hnt logicalBlank q hlive
      choice tape head hblank
    dsimp [post]
    cases hm : choice.action.move with
    | left => right; right; simp [relocationDistance, hm] at hlen; omega
    | stay => right; left; simp [relocationDistance, hm] at hlen; omega
    | right => left; simpa [relocationDistance, hm] using hlen
  · have hrun := readerPrefix_blank_run p hnt logicalBlank q hlive tape head
      hblank pre rfl
    simpa [initialPhysical, liftReaderConfig, liftReaderControl, pre] using hrun
  · exact data.run_ok
  · exact branchArrow_step p hnt logicalBlank q logicalBlank choice.slot
      choice.action hlive choice.occupied tape (head + nt)
  · exact blankCanonicalPost_run p hnt logicalBlank q hlive choice tape head
      hblank
  · exact blankCanonicalPost_no_branch p hnt logicalBlank q hlive choice
      tape head hblank
  · exact ⟨choice.action.target, rfl⟩
  · exact blankCanonicalPost_first_return p hnt logicalBlank q hlive choice
      tape head hblank

theorem blankReaderHistory_nonbranchArrows (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) = ULogSourceLogicalBlockReader.blank) :
    nonbranchArrows p hnt logicalBlank
      (liftReaderConfig q
        (ULogSourceLogicalBlockReader.initialConfig logicalBlank hnt tape head)) nt =
      some (readerHistory p hnt logicalBlank q tape head) := by
  have hrun := readerPrefix_blank_run p hnt logicalBlank q hlive tape head hblank
    (readerHistory p hnt logicalBlank q tape head) rfl
  obtain ⟨bs, hbs, hsame, -⟩ := blank_reader_successful_run_unique
    p hnt logicalBlank q hlive tape head hblank
    (readerHistory p hnt logicalBlank q tape head)
    ({ state := .branch q logicalBlank, head := head + nt, tape := tape } : Config (State ns nt) Tape)
    (readerHistory_length p hnt logicalBlank q tape head) hrun
  simpa [hsame] using hbs

theorem blankCanonicalPost_nonbranchArrows (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (logicalBlank : Fin nt) (q : Fin ns)
    (hlive : haltedSource q = false) (choice : SourceChoice p q logicalBlank)
    (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) = ULogSourceLogicalBlockReader.blank) :
    nonbranchArrows p hnt logicalBlank
      (rewindInitial hnt q logicalBlank (choice.slot = 1) choice.action tape (head + nt))
      (2 * nt + relocationDistance choice.action.move nt + 1) =
      some (blankCanonicalPost p hnt logicalBlank q hlive choice tape head hblank) := by
  have hrun := blankCanonicalPost_run p hnt logicalBlank q hlive choice tape head hblank
  have hlen := blankCanonicalPost_length p hnt logicalBlank q hlive choice tape head hblank
  obtain ⟨bs, hbs, hsame, -⟩ := nonbranch_successful_run_unique_of_avoids
    p hnt logicalBlank
    (rewindInitial hnt q logicalBlank (choice.slot = 1) choice.action tape (head + nt))
    (2 * nt + relocationDistance choice.action.move nt + 1)
    (by
      intro k hk q' read'
      apply post_iterate_avoids_branch hnt logicalBlank q logicalBlank
        (choice.slot = 1) choice.action tape head k
      omega)
    (blankCanonicalPost p hnt logicalBlank q hlive choice tape head hblank)
    (fullEndpoint hnt choice.action tape head) hlen hrun
  simpa [hsame] using hbs

theorem rawBackwardCore_spec (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (logicalBlank read : Fin nt) (q : Fin ns) (hlive : haltedSource q = false)
    (tape : Int → Tape) (head : Int)
    (h : RawPhysicalMacroHistory p hnt logicalBlank read q hlive tape head) :
    h.branch = branchArrow p hnt logicalBlank q read
        (rawBackwardCore p hnt logicalBlank read q hlive tape head h).slot
        (tape (head + nt)) hlive
        (rawBackwardCore p hnt logicalBlank read q hlive tape head h).action
        (rawBackwardCore p hnt logicalBlank read q hlive tape head h).occupied ∧
      h.branch_out = branchResult q read
        (rawBackwardCore p hnt logicalBlank read q hlive tape head h).slot
        (rawBackwardCore p hnt logicalBlank read q hlive tape head h).action
        tape (head + nt) := by
  exact Classical.choose_spec (raw_extract_choice p hnt logicalBlank read q
    hlive tape head h)

theorem blank_rawBackward_rawForward (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (logicalBlank : Fin nt) (q : Fin ns)
    (hlive : haltedSource q = false) (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) =
      ULogSourceLogicalBlockReader.blank)
    (choice : SourceChoice p q logicalBlank) :
    rawBackwardCore p hnt logicalBlank logicalBlank q hlive tape head
      (blankRawForward p hnt logicalBlank q hlive tape head hblank choice) =
      choice := by
  have hspec := (rawBackwardCore_spec p hnt logicalBlank logicalBlank q hlive
    tape head (blankRawForward p hnt logicalBlank q hlive tape head hblank choice)).1
  apply extracted_choice_unique p hnt logicalBlank logicalBlank q hlive tape head
  simpa [blankRawForward] using hspec.symm

theorem blank_raw_data_identification (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (logicalBlank : Fin nt) (q : Fin ns)
    (hlive : haltedSource q = false) (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) =
      ULogSourceLogicalBlockReader.blank)
    (h : RawPhysicalMacroHistory p hnt logicalBlank logicalBlank q hlive tape head) :
    let choice := rawBackwardCore p hnt logicalBlank logicalBlank q hlive tape head h
    h.pre = readerHistory p hnt logicalBlank q tape head ∧
      h.branch = branchArrow p hnt logicalBlank q logicalBlank choice.slot
        (tape (head + nt)) hlive choice.action choice.occupied ∧
      h.branch_out = branchResult q logicalBlank choice.slot choice.action tape
        (head + nt) ∧
      h.post = blankCanonicalPost p hnt logicalBlank q hlive choice tape head hblank ∧
      h.endpoint = fullEndpoint hnt choice.action tape head ∧
      h.arrows = fullArrows p hnt logicalBlank
        (readerHistory p hnt logicalBlank q tape head)
        (blankCanonicalData p hnt logicalBlank q hlive choice tape head hblank).rewind
        (blankCanonicalData p hnt logicalBlank q hlive choice tape head hblank).writer
        (blankCanonicalData p hnt logicalBlank q hlive choice tape head hblank).relocate
        (branchArrow p hnt logicalBlank q logicalBlank choice.slot
          (tape (head + nt)) hlive choice.action choice.occupied) := by
  dsimp
  obtain ⟨choice', preCanon, postCanon, hpreN, hpreEq, hbranch,
    hpostN, hpostEq, hend, harrows⟩ :=
    blank_raw_reconstruct p hnt logicalBlank q hlive tape head hblank h
  have hspec := rawBackwardCore_spec p hnt logicalBlank logicalBlank q hlive
    tape head h
  have hchoice : choice' =
      rawBackwardCore p hnt logicalBlank logicalBlank q hlive tape head h := by
    apply extracted_choice_unique p hnt logicalBlank logicalBlank q hlive tape head
    exact hbranch.symm.trans hspec.1
  subst choice'
  have hreaderN := blankReaderHistory_nonbranchArrows p hnt logicalBlank q
    hlive tape head hblank
  have hpreCanon : preCanon = readerHistory p hnt logicalBlank q tape head :=
    Option.some.inj (hpreN.symm.trans hreaderN)
  have hpostCanonical := blankCanonicalPost_nonbranchArrows p hnt logicalBlank
    q hlive (rawBackwardCore p hnt logicalBlank logicalBlank q hlive tape head h)
    tape head hblank
  have hpostCanon : postCanon = blankCanonicalPost p hnt logicalBlank q hlive
      (rawBackwardCore p hnt logicalBlank logicalBlank q hlive tape head h)
      tape head hblank := Option.some.inj (hpostN.symm.trans hpostCanonical)
  refine ⟨hpreEq.trans hpreCanon, hspec.1, hspec.2,
    hpostEq.trans hpostCanon, hend, ?_⟩
  rw [harrows, hpreCanon, hpostCanon]
  unfold blankCanonicalPost
  simp [fullArrows, List.append_assoc]

noncomputable def blankRawSourceChoiceEquiv (p : BoundedProgram ns nt)
    (hnt : 0 < nt) (logicalBlank : Fin nt) (q : Fin ns)
    (hlive : haltedSource q = false) (tape : Int → Tape) (head : Int)
    (hblank : ∀ i : ℕ, i < nt → tape (head + i) =
      ULogSourceLogicalBlockReader.blank) :
    SourceChoice p q logicalBlank ≃
      RawPhysicalMacroHistory p hnt logicalBlank logicalBlank q hlive tape head where
  toFun := blankRawForward p hnt logicalBlank q hlive tape head hblank
  invFun := rawBackwardCore p hnt logicalBlank logicalBlank q hlive tape head
  left_inv := blank_rawBackward_rawForward p hnt logicalBlank q hlive tape head hblank
  right_inv := by
    intro h
    obtain ⟨hpre, hbranch, hbranchOut, hpost, hendpoint, harrows⟩ :=
      blank_raw_data_identification p hnt logicalBlank q hlive tape head hblank h
    apply RawPhysicalMacroHistory.ext
    · simpa [blankRawForward] using harrows.symm
    · simpa [blankRawForward] using hendpoint.symm
    · simpa [blankRawForward] using hbranch.symm
    · simpa [blankRawForward] using hbranchOut.symm
    · simpa [blankRawForward] using hpre.symm
    · simpa [blankRawForward] using hpost.symm

end PakFixedPolyomino.ULogSourceOneHotRawReconstruct
