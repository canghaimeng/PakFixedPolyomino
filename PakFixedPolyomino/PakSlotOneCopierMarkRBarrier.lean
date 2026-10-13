import PakFixedPolyomino.PakSlotOneCopierRightEndReflection

/-! # The copier's `markR` barrier before the terminal scan

`rightEnd` and the parser's `lenDone` are the same tape letter. Consequently
there is no global ``a copier run never creates rightEnd'' invariant. This
file records the narrower control-flow fact that is actually true: a successful
run starting in `seedCell` enters the terminal right-buffer phase through the
literal `markR` transition, and only after that phase can it consume `rightEnd`.

The spatial assertion here is occurrence-sensitive. `markR` is overwritten by
work on entry to `rightBufferScan`, so it is not generally a member of the
current left zipper at the later `rightEnd` read. The theorem therefore retains
the earlier barrier occurrence as a run index rather than asserting the false
statement `markR ∈ leftRev` at the terminal read.

The remaining *parser-to-copier origin* interface is intentionally not
postulated here.  The exact missing lemma has the following content.  For a
`SlotOneFullFrame F`, an accepting parser history which reaches a physical
`copyStart` seed must factor the original ordered raw scanner word as
`core ++ optional [rightEnd] ++ hashes`, and must preserve that suffix as the
region to the right of the later copier-created `markR`.  In particular,
parser-written `lenDone = rightEnd` occurrences must be certified on the
left side of that marker.  Existing `CanAcceptResult` only supplies an
existential `copyReady` endpoint, and existing raw-shape facts only supply the
ordered input word; neither one presently retains this common occurrence map.
-/

namespace PakFixedPolyomino.PakSlotOneCopierMarkRBarrier

open MStarCopierMicrocode
open MStarOuterProgram
open MStarCopierExecution

/-- The two controls that can occur after the terminal right-buffer phase has
started. This is intentionally a control predicate, not a tape invariant. -/
def PostRightBuffer (q : CopierState) : Prop :=
  q = .rightBufferScan ∨ q = .finalReturn

/-- A literal run occurrence at which the copier crosses the physical `markR`
boundary into the right-buffer region. -/
def CrossesMarkR (fuel : ℕ) (r : Result) : Prop :=
  ∃ k z z',
    k < fuel ∧
    run k r = .running .finalSeekBoundary z ∧
    z.focus = .markR ∧
    oneStep (.running .finalSeekBoundary z) = .running .rightBufferScan z'

def CopierReadsRightEnd : Result → Prop
  | .running .rightBufferScan z => z.focus = rightEnd
  | _ => False

def ReadsRightEnd : ℕ → Result → Prop
  | 0, _ => False
  | fuel + 1, r => CopierReadsRightEnd r ∨ ReadsRightEnd fuel (oneStep r)

theorem readsRightEnd_iff_exists (fuel : ℕ) (r : Result) :
    ReadsRightEnd fuel r ↔
      ∃ j, j < fuel ∧ CopierReadsRightEnd (run j r) := by
  induction fuel generalizing r with
  | zero => simp [ReadsRightEnd]
  | succ fuel ih =>
      constructor
      · intro h
        simp only [ReadsRightEnd] at h
        rcases h with hnow | hlater
        · exact ⟨0, Nat.zero_lt_succ _, by simpa [run]⟩
        · rcases ih (oneStep r) |>.mp hlater with ⟨j, hj, hread⟩
          refine ⟨j + 1, Nat.succ_lt_succ hj, ?_⟩
          simpa [run] using hread
      · rintro ⟨j, hj, hread⟩
        cases j with
        | zero =>
            simp [ReadsRightEnd, run] at hread ⊢
            exact Or.inl hread
        | succ j =>
            have hj' : j < fuel := by omega
            apply Or.inr
            apply ih (oneStep r) |>.mpr
            refine ⟨j, hj', ?_⟩
            simpa [run] using hread

/-- Closed-table classification of an edge entering `finalReturn`. The
`finalReturn` self loop is retained because a successful run may already be in
that phase when this local lemma is invoked. -/
theorem oneStep_running_to_finalReturn
    (q : CopierState) (z z' : MStarParserExecution.Zipper ConcreteTape)
    (hstep : oneStep (.running q z) = .running .finalReturn z') :
    q = .finalReturn ∨ (q = .rightBufferScan ∧ z.focus = rightEnd) := by
  simp only [oneStep] at hstep
  cases htable : copierStep (UState := Unit) () q z.focus with
  | none => simp [htable] at hstep
  | some a =>
      rw [htable] at hstep
      cases happly : MStarParserExecution.applyAction z a with
      | none => simp [happly] at hstep
      | some w =>
          dsimp only at hstep
          rw [happly] at hstep
          cases htarget : a.target with
          | parser p =>
              cases p with
              | inl p => simp [htarget] at hstep
              | inr q' =>
                  have hq' : q' = .finalReturn := by
                    have hw : Result.running q' w =
                        .running .finalReturn z' := by
                      simpa [htarget] using hstep
                    exact (Result.running.inj hw).1
                  subst q'
                  cases q <;>
                    simp [copierStep, copyGo, copyReject, copySim] at htable <;>
                    all_goals
                      repeat' first | split at htable
                      all_goals cases htable
                      all_goals simp_all
          | sim u | start | accept | reject => simp [htarget] at hstep

/-- Reaching the universal start can only be the final-return action from the
left marker. -/
theorem oneStep_running_to_groupReady
    (q : CopierState) (z z' : MStarParserExecution.Zipper ConcreteTape)
    (hstep : oneStep (.running q z) = .groupReady z') :
    q = .finalReturn ∧ z.focus = .markL := by
  simp only [oneStep] at hstep
  cases htable : copierStep (UState := Unit) () q z.focus with
  | none => simp [htable] at hstep
  | some a =>
      rw [htable] at hstep
      cases happly : MStarParserExecution.applyAction z a with
      | none => simp [happly] at hstep
      | some w =>
          dsimp only at hstep
          rw [happly] at hstep
          cases htarget : a.target with
          | sim u =>
              cases q <;>
                simp [copierStep, copyGo, copyReject, copySim] at htable <;>
                all_goals
                  repeat' first | split at htable
                  all_goals cases htable
                  all_goals simp_all
          | parser p =>
              cases p <;> simp [htarget] at hstep
          | start | accept | reject => simp [htarget] at hstep

/-- Apart from the `rightBufferScan` self loop, the only transition into that
control reads the actual `markR` cell. -/
theorem oneStep_running_to_rightBufferScan
    (q : CopierState) (z z' : MStarParserExecution.Zipper ConcreteTape)
    (hstep : oneStep (.running q z) = .running .rightBufferScan z') :
    q = .rightBufferScan ∨ (q = .finalSeekBoundary ∧ z.focus = .markR) := by
  simp only [oneStep] at hstep
  cases htable : copierStep (UState := Unit) () q z.focus with
  | none => simp [htable] at hstep
  | some a =>
      rw [htable] at hstep
      cases happly : MStarParserExecution.applyAction z a with
      | none => simp [happly] at hstep
      | some w =>
          dsimp only at hstep
          rw [happly] at hstep
          cases htarget : a.target with
          | parser p =>
              cases p with
              | inl p => simp [htarget] at hstep
              | inr q' =>
                  have hq' : q' = .rightBufferScan := by
                    have hw : Result.running q' w =
                        .running .rightBufferScan z' := by
                      simpa [htarget] using hstep
                    exact (Result.running.inj hw).1
                  subst q'
                  cases q <;>
                    simp [copierStep, copyGo, copyReject, copySim] at htable <;>
                    all_goals
                      repeat' first | split at htable
                      all_goals cases htable
                      all_goals simp_all
          | sim u | start | accept | reject => simp [htarget] at hstep

/-- A one-step entrance to the terminal scan from outside its post-phase is
exactly a `finalSeekBoundary` read of `markR`. -/
theorem oneStep_nonpost_to_rightBuffer_crossesMarkR
    (q : CopierState) (z z' : MStarParserExecution.Zipper ConcreteTape)
    (hq : ¬ PostRightBuffer q)
    (hstep : oneStep (.running q z) = .running .rightBufferScan z') :
    q = .finalSeekBoundary ∧ z.focus = .markR := by
  rcases oneStep_running_to_rightBufferScan q z z' hstep with hself | hbarrier
  · exact (hq (Or.inl hself)).elim
  · exact hbarrier

/-- If a successful finite run starts before the terminal phase, it contains a
literal `markR` crossing. The disjunction is needed for the genuinely more
general statement: a run which starts in `rightBufferScan` or `finalReturn`
has already crossed the barrier before its supplied initial state. -/
theorem run_to_groupReady_post_or_crossesMarkR :
    ∀ (fuel : ℕ) (q : CopierState)
      (z out : MStarParserExecution.Zipper ConcreteTape),
      run fuel (.running q z) = .groupReady out →
        PostRightBuffer q ∨ CrossesMarkR fuel (.running q z) := by
  intro fuel
  induction fuel with
  | zero =>
      intro q z out hrun
      cases hrun
  | succ fuel ih =>
      intro q z out hrun
      rw [run_succ] at hrun
      cases hnext : oneStep (.running q z) with
      | rejected =>
          rw [hnext, rejected_absorbing] at hrun
          cases hrun
      | stuck =>
          rw [hnext, stuck_absorbing] at hrun
          cases hrun
      | groupReady w =>
          have hfinal := oneStep_running_to_groupReady q z w hnext
          exact Or.inl (Or.inr hfinal.1)
      | running q' z' =>
          have htail : run fuel (.running q' z') = .groupReady out := by
            simpa [hnext] using hrun
          rcases ih q' z' out htail with hpost | hcross
          · rcases hpost with hscan | hfinal
            · subst q'
              by_cases hq : PostRightBuffer q
              · exact Or.inl hq
              · right
                rcases oneStep_nonpost_to_rightBuffer_crossesMarkR q z z' hq hnext with
                  ⟨hstate, hfocus⟩
                refine ⟨0, z, z', Nat.zero_lt_succ _, ?_, hfocus, ?_⟩
                · simpa [hstate]
                · simpa [hstate] using hnext
            · subst q'
              rcases oneStep_running_to_finalReturn q z z' hnext with hself | hread
              · exact Or.inl (Or.inr hself)
              · exact Or.inl (Or.inl hread.1)
          · right
            rcases hcross with ⟨k, w, w', hk, hrunCross, hfocus, hstepCross⟩
            refine ⟨k + 1, w, w', by omega, ?_, hfocus, hstepCross⟩
            rw [run_succ, hnext]
            exact hrunCross

/-- The slot-one copier never begins in the terminal phase. Therefore every
successful run from the physical seed has a concrete earlier `markR` crossing. -/
theorem seed_run_to_groupReady_crossesMarkR
    (fuel : ℕ) (z out : MStarParserExecution.Zipper ConcreteTape)
    (hrun : run fuel (.running .seedCell z) = .groupReady out) :
    CrossesMarkR fuel (.running .seedCell z) := by
  rcases run_to_groupReady_post_or_crossesMarkR fuel .seedCell z out hrun with
    hpost | hcross
  · rcases hpost with h | h <;> cases h
  · exact hcross

/-- Any successful run either begins in the final-return phase or visits a
literal `rightBufferScan/rightEnd` state. This is the state-specific version
of right-end reflection; it makes no false global claim about writes of the
shared `scratch 2` tape letter. -/
theorem run_to_groupReady_reads_or_starts_finalReturn :
    ∀ (fuel : ℕ) (q : CopierState)
      (z out : MStarParserExecution.Zipper ConcreteTape),
      run fuel (.running q z) = .groupReady out →
        q = .finalReturn ∨ ReadsRightEnd fuel (.running q z) := by
  intro fuel
  induction fuel with
  | zero =>
      intro q z out hrun
      cases hrun
  | succ fuel ih =>
      intro q z out hrun
      rw [run_succ] at hrun
      cases hnext : oneStep (.running q z) with
      | rejected =>
          rw [hnext, rejected_absorbing] at hrun
          cases hrun
      | stuck =>
          rw [hnext, stuck_absorbing] at hrun
          cases hrun
      | groupReady w =>
          exact Or.inl (oneStep_running_to_groupReady q z w hnext).1
      | running q' z' =>
          have htail : run fuel (.running q' z') = .groupReady out := by
            simpa [hnext] using hrun
          rcases ih q' z' out htail with hfinal | hreads
          · subst q'
            rcases oneStep_running_to_finalReturn q z z' hnext with hself | hread
            · exact Or.inl hself
            · right
              simp [ReadsRightEnd, CopierReadsRightEnd, hread.1, hread.2]
          · right
            simp [ReadsRightEnd, hnext, hreads]

theorem seed_run_to_groupReady_readsRightEnd
    (fuel : ℕ) (z out : MStarParserExecution.Zipper ConcreteTape)
    (hrun : run fuel (.running .seedCell z) = .groupReady out) :
    ReadsRightEnd fuel (.running .seedCell z) := by
  rcases run_to_groupReady_reads_or_starts_finalReturn fuel .seedCell z out hrun with
    hbad | hread
  · cases hbad
  · exact hread

/-- In a successful run begun before the terminal phase, the barrier and
terminal read have an actual temporal order.  The index `k` is a
`finalSeekBoundary/markR` occurrence; the later index `j` is a
`rightBufferScan/rightEnd` occurrence. -/
theorem seed_run_to_groupReady_markR_before_rightEnd
    (fuel : ℕ) (z out : MStarParserExecution.Zipper ConcreteTape)
    (hrun : run fuel (.running .seedCell z) = .groupReady out) :
    ∃ k j barrier next,
      k < j ∧ j < fuel ∧
      run k (.running .seedCell z) = .running .finalSeekBoundary barrier ∧
      barrier.focus = .markR ∧
      oneStep (.running .finalSeekBoundary barrier) =
        .running .rightBufferScan next ∧
      CopierReadsRightEnd (run j (.running .seedCell z)) := by
  rcases seed_run_to_groupReady_crossesMarkR fuel z out hrun with
    ⟨k, barrier, next, hk, hbarrier, hfocus, henter⟩
  have hsum : fuel = k + (fuel - k) := (Nat.add_sub_of_le hk.le).symm
  have hafterBarrier : run (fuel - k) (.running .finalSeekBoundary barrier) =
      .groupReady out := by
    rw [← hbarrier, ← run_add, ← hsum]
    exact hrun
  have hpositive : 0 < fuel - k := Nat.sub_pos_of_lt hk
  cases hrem : fuel - k with
  | zero => omega
  | succ remaining =>
      have hafterEnter : run remaining (.running .rightBufferScan next) =
          .groupReady out := by
        rw [hrem, run_succ, henter] at hafterBarrier
        exact hafterBarrier
      have hreads : ReadsRightEnd remaining (.running .rightBufferScan next) := by
        rcases run_to_groupReady_reads_or_starts_finalReturn remaining
          .rightBufferScan next out hafterEnter with hbad | hread
        · cases hbad
        · exact hread
      rcases readsRightEnd_iff_exists remaining (.running .rightBufferScan next) |>.mp
        hreads with ⟨offset, hoffset, hread⟩
      refine ⟨k, k + 1 + offset, barrier, next, ?_, ?_, hbarrier, hfocus,
        henter, ?_⟩
      · omega
      · rw [hsum, hrem]
        omega
      · rw [show k + 1 + offset = k + (1 + offset) by omega, run_add, hbarrier,
          show 1 + offset = offset + 1 by omega, run_succ, henter]
        exact hread

/-- The final successful terminal read is not merely an arbitrary `scratch 2`:
it is preceded, in the same execution, by a real entry through `markR`. This
combines the new barrier occurrence with the already-proved state-specific
right-end read certificate. -/
theorem seed_run_to_groupReady_barrier_and_readsRightEnd
    (fuel : ℕ) (z out : MStarParserExecution.Zipper ConcreteTape)
    (hrun : run fuel (.running .seedCell z) = .groupReady out) :
    CrossesMarkR fuel (.running .seedCell z) ∧
      ReadsRightEnd fuel (.running .seedCell z) := by
  exact ⟨seed_run_to_groupReady_crossesMarkR fuel z out hrun,
    seed_run_to_groupReady_readsRightEnd fuel z out hrun⟩

/-- The local occurrence-preserving interface needed by the missing
slot-one/copy-start bridge.  Once a physical copier seed has been factored as
two work cells followed by `tail`, the first four copier steps install `markR`
strictly before that exact untouched tail.  Thus any later proof identifying a
raw scanner suffix with this `tail` may transport occurrence provenance across
the marker without a global tape-alphabet invariant. -/
theorem seed_markR_install_preserves_tail
    (source tail : List ConcreteTape) :
    run 4
      (.running .seedCell
        ⟨.markL :: source, .core MStarConcreteAlphabet.work,
          .core MStarConcreteAlphabet.work :: tail⟩) =
      .running (.findOld 0)
        ⟨.markL :: source, cellA, .markR :: tail⟩ := by
  exact seed_reaches_round_zero_source tail source

/-- A running copier state which reaches `groupReady` cannot take an immediate
rejecting transition. -/
theorem running_run_to_groupReady_not_oneStep_rejected
    (q : CopierState) (z : MStarParserExecution.Zipper ConcreteTape)
    (fuel : ℕ) (out : MStarParserExecution.Zipper ConcreteTape)
    (hstep : oneStep (.running q z) = .rejected)
    (hrun : run fuel (.running q z) = .groupReady out) : False := by
  cases fuel with
  | zero => cases hrun
  | succ fuel =>
      rw [run_succ, hstep, rejected_absorbing] at hrun
      cases hrun

/-- A running copier state which reaches `groupReady` cannot take an immediate
stuck transition. -/
theorem running_run_to_groupReady_not_oneStep_stuck
    (q : CopierState) (z : MStarParserExecution.Zipper ConcreteTape)
    (fuel : ℕ) (out : MStarParserExecution.Zipper ConcreteTape)
    (hstep : oneStep (.running q z) = .stuck)
    (hrun : run fuel (.running q z) = .groupReady out) : False := by
  cases fuel with
  | zero => cases hrun
  | succ fuel =>
      rw [run_succ, hstep, stuck_absorbing] at hrun
      cases hrun

/-- Pure zipper atom for the copy-start junction.  It needs neither a parser
soundness theorem nor any statement about all occurrences of `scratch 2`:
when the physical copy-entry action is followed by a successful copier run,
the returned seed has exactly the two-work-cell form needed by
`seed_markR_install_preserves_tail`. -/
theorem copyEntry_successful_seed_has_two_work_prefix
    (z seed out : MStarParserExecution.Zipper ConcreteTape) (fuel : ℕ)
    (happly : MStarParserExecution.applyAction z
      (copyGo (UState := Unit) .markL .seedCell .right) = some seed)
    (hrun : run fuel (.running .seedCell seed) = .groupReady out) :
    ∃ source tail,
      seed = ⟨.markL :: source, .core MStarConcreteAlphabet.work,
        .core MStarConcreteAlphabet.work :: tail⟩ := by
  rcases z with ⟨source, focus, right⟩
  cases right with
  | nil => simp [MStarParserExecution.applyAction, copyGo] at happly
  | cons y right =>
      simp [MStarParserExecution.applyAction, copyGo] at happly
      cases happly
      have hy : y = .core MStarConcreteAlphabet.work := by
        by_contra hy
        apply running_run_to_groupReady_not_oneStep_rejected .seedCell
          ⟨.markL :: source, y, right⟩ fuel out
        · simp [oneStep, copierStep, hy, copyReject,
            MStarParserExecution.applyAction]
        · exact hrun
      subst y
      cases right with
      | nil =>
          exact (running_run_to_groupReady_not_oneStep_stuck .seedCell
            ⟨.markL :: source, .core MStarConcreteAlphabet.work, []⟩ fuel out
            (by simp [oneStep, copierStep, copyGo,
              MStarParserExecution.applyAction]) hrun).elim
      | cons y tail =>
          have hy : y = .core MStarConcreteAlphabet.work := by
            by_contra hy
            have hone : oneStep (.running .seedCell
                ⟨.markL :: source, .core MStarConcreteAlphabet.work,
                  y :: tail⟩) =
                .running .seedBoundary
                  ⟨cellA :: .markL :: source, y, tail⟩ := by
              simp [oneStep, copierStep, copyGo,
                MStarParserExecution.applyAction]
            have htail : run (fuel - 1)
                (.running .seedBoundary ⟨cellA :: .markL :: source, y, tail⟩) =
                .groupReady out := by
              cases fuel with
              | zero => cases hrun
              | succ fuel =>
                  rw [run_succ, hone] at hrun
                  exact hrun
            apply running_run_to_groupReady_not_oneStep_rejected .seedBoundary
              ⟨cellA :: .markL :: source, y, tail⟩ (fuel - 1) out ?_ htail
            simp [oneStep, copierStep, hy, copyReject,
              MStarParserExecution.applyAction]
          subst y
          exact ⟨source, tail, rfl⟩

/-- Composition of the two local physical interfaces: a successful copy-entry
first has two work cells, then installs `markR` while preserving precisely the
same named tail. -/
theorem copyEntry_successful_seed_markR_preserves_tail
    (z seed out : MStarParserExecution.Zipper ConcreteTape) (fuel : ℕ)
    (happly : MStarParserExecution.applyAction z
      (copyGo (UState := Unit) .markL .seedCell .right) = some seed)
    (hrun : run fuel (.running .seedCell seed) = .groupReady out) :
    ∃ source tail,
      seed = ⟨.markL :: source, .core MStarConcreteAlphabet.work,
        .core MStarConcreteAlphabet.work :: tail⟩ ∧
      run 4 (.running .seedCell seed) =
        .running (.findOld 0) ⟨.markL :: source, cellA, .markR :: tail⟩ := by
  rcases copyEntry_successful_seed_has_two_work_prefix z seed out fuel happly hrun
    with ⟨source, tail, hseed⟩
  refine ⟨source, tail, hseed, ?_⟩
  rw [hseed]
  exact seed_markR_install_preserves_tail source tail

/-- Actual slot-one integration of the pure copy-entry atom.  No reverse use
of `CanAcceptResult` occurs: the input is the literal outer-history projection
already proved for the full frame, including its physical copy-start action
and its successful finite copier continuation. -/
theorem slotOneFrame_seed_has_two_work_prefix
    {n : ℕ} (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    ∃ (seedConfig : PakParserOuterBridge.OuterConfig) (seedHead : Fin n) (fuel : ℕ)
      (out : MStarParserExecution.Zipper ConcreteTape)
      (source tail : List ConcreteTape),
      seedConfig.state = (.parser (.inr CopierState.seedCell) : PakParserOuterBridge.OuterState) ∧
      PakOuterParserReflection.windowZipper n seedConfig seedHead =
        ⟨.markL :: source, .core MStarConcreteAlphabet.work,
          .core MStarConcreteAlphabet.work :: tail⟩ ∧
      run fuel
        (.running .seedCell
          ⟨.markL :: source, .core MStarConcreteAlphabet.work,
            .core MStarConcreteAlphabet.work :: tail⟩) =
        .groupReady out := by
  rcases PakSlotOneCopierRightEndReflection.slotOneFrame_copyStart_seedRun F with
    ⟨copyConfig, seedConfig, copyHead, seedHead, fuel, out,
      _hparser, happly, hstate, hrun⟩
  rcases copyEntry_successful_seed_has_two_work_prefix
      (PakOuterParserReflection.windowZipper n copyConfig copyHead)
      (PakOuterParserReflection.windowZipper n seedConfig seedHead)
      out fuel happly hrun with ⟨source, tail, hshape⟩
  refine ⟨seedConfig, seedHead, fuel, out, source, tail, hstate, hshape, ?_⟩
  rw [hshape] at hrun
  exact hrun

/-- Actual full-frame version of the preceding tail-preservation certificate.
It records the exact outer-window seed and its four-step `markR` installation,
so the subsequent parser-origin theorem has only one remaining duty: identify
this named `tail` with the ordered scanner terminal suffix. -/
theorem slotOneFrame_seed_markR_preserves_tail
    {n : ℕ} (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    ∃ (seedConfig : PakParserOuterBridge.OuterConfig) (seedHead : Fin n) (fuel : ℕ)
      (out : MStarParserExecution.Zipper ConcreteTape)
      (source tail : List ConcreteTape),
      seedConfig.state = (.parser (.inr CopierState.seedCell) : PakParserOuterBridge.OuterState) ∧
      PakOuterParserReflection.windowZipper n seedConfig seedHead =
        ⟨.markL :: source, .core MStarConcreteAlphabet.work,
          .core MStarConcreteAlphabet.work :: tail⟩ ∧
      run 4 (.running .seedCell
        (PakOuterParserReflection.windowZipper n seedConfig seedHead)) =
        .running (.findOld 0) ⟨.markL :: source, cellA, .markR :: tail⟩ ∧
      run fuel (.running .seedCell
        (PakOuterParserReflection.windowZipper n seedConfig seedHead)) =
        .groupReady out := by
  rcases PakSlotOneCopierRightEndReflection.slotOneFrame_copyStart_seedRun F with
    ⟨copyConfig, seedConfig, copyHead, seedHead, fuel, out,
      _hparser, happly, hstate, hrun⟩
  rcases copyEntry_successful_seed_markR_preserves_tail
      (PakOuterParserReflection.windowZipper n copyConfig copyHead)
      (PakOuterParserReflection.windowZipper n seedConfig seedHead)
      out fuel happly hrun with ⟨source, tail, hshape, hmark⟩
  exact ⟨seedConfig, seedHead, fuel, out, source, tail,
    hstate, hshape, hmark, hrun⟩

end PakFixedPolyomino.PakSlotOneCopierMarkRBarrier
