import PakFixedPolyomino.ULogFiniteProgramPrefixFootprint
import PakFixedPolyomino.ULogFiniteTapeHeadTranslation
import PakFixedPolyomino.ULogSourceObliviousExteriorZipper
import PakFixedPolyomino.ULogSourceObliviousRunTime

/-! Every successful labelled scanner word, including truncated pre-branch
prefixes, partial return/update sweeps, rejected and empty words, has its
chronological head inside the two delimiters and therefore extends no
allocated cell. Acceptance is not assumed. Physical microtime is separate. -/
namespace PakFixedPolyomino.ULogSourceObliviousAllPrefixGrowth
open StandardNondeterministicMachine hiding run
open StandardMachineWindowBridge
open ULogCompiler ULogSourceObliviousBytecode ULogSourceObliviousBytecodeRunBridge
open ULogSourceObliviousExteriorZipper ULogSourceObliviousInitialWindowExecution
open ULogSourceObliviousUpdateExecution ULogSourceObliviousScanProgram
open ULogSourceObliviousScanExecution ULogSourceObliviousInitialWindowInverse
open ULogSourceObliviousRunPrefix ULogSourceObliviousWindowFootprint
open ULogSourceObliviousCycleExecution ULogSourceObliviousOverflowExecution
open ULogSourceObliviousSafeSuffix ULogSourceObliviousRunTime
open ULogSourceObliviousHaltingProgram ULogSourceObliviousHaltingCounts
open ULogSourceObliviousWindow ULogSourceObliviousLRWindowExecution
open ULogSourceObliviousRLWindowExecution ULogSourceObliviousScanInverse
open ULogFiniteProgramZipperRunBridge ULogFiniteProgramPrefixFootprint
open ULogFiniteTapeGrowthLedger ULogFiniteTapePrefixGrowth
open ULogFiniteTapeHeadTranslation FiniteOneTapeProgram FiniteOneTapeSemantics
open FiniteOneTapeHaltingRestriction
open StandardMachineZipperBridge (physical toBounded)
variable {ns nt : Nat}

theorem forcedPrefix_take (P : Program (State ns nt) Phys) (movable : Phys → Bool)
    (pre : List (Arrow P)) (c : Config (State ns nt) Phys) (k : Nat)
    (h : ForcedPrefix P movable pre c) : ForcedPrefix P movable (pre.take k) c := by
  induction pre generalizing c k with
  | nil => simp [ForcedPrefix]
  | cons a as ih =>
      cases k with
      | zero => simp [ForcedPrefix]
      | succ k => rcases h with ⟨d, hs, hu, ht⟩; exact ⟨d, hs, hu, ih d k ht⟩

theorem eq_take_of_forced_le (P : Program (State ns nt) Phys) (movable : Phys → Bool)
    (pre raw : List (Arrow P)) (c out : Config (State ns nt) Phys)
    (hforced : ForcedPrefix P movable pre c)
    (hrun : run P movable raw c = some out) (hlen : raw.length ≤ pre.length) :
    raw = pre.take raw.length :=
  (forcedPrefix_unique_successful_run P movable (pre.take raw.length) raw c out
    (forcedPrefix_take P movable pre c raw.length hforced) hrun
    (List.length_take.trans (Nat.min_eq_left hlen))).1

theorem prefixInInterval_take (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (lo hi : Int) (arrows : List (ScanArrow p hnt blank))
    (c : ScanCfg ns nt) (h : PrefixInInterval p hnt blank lo hi arrows c) (n : Nat) :
    PrefixInInterval p hnt blank lo hi (arrows.take n) c := by
  intro k hk
  have hk' : k ≤ arrows.length := by simp [List.length_take] at hk; omega
  obtain ⟨middle, hm, hlo, hhi⟩ := h k hk'
  have hmin : k ≤ n := by simp [List.length_take] at hk; omega
  exact ⟨middle, by simpa [List.take_take, Nat.min_eq_left hmin] using hm, hlo, hhi⟩

theorem prefixInInterval_of_short_forced (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (lo hi : Int) (pre raw : List (ScanArrow p hnt blank))
    (c out : ScanCfg ns nt)
    (hforced : ForcedPrefix (program p hnt blank) (fun _ => true) pre c)
    (hpre : PrefixInInterval p hnt blank lo hi pre c)
    (hrun : run (program p hnt blank) (fun _ => true) raw c = some out)
    (hlen : raw.length ≤ pre.length) :
    PrefixInInterval p hnt blank lo hi raw c :=
  eq_take_of_forced_le _ _ pre raw c out hforced hrun hlen ▸
    prefixInInterval_take p hnt blank lo hi pre c hpre raw.length

theorem interval_of_right_or_stay (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (lo hi : Int) (arrows : List (ScanArrow p hnt blank))
    (c out : ScanCfg ns nt)
    (hmoves : ∀ a ∈ arrows, (transition (program p hnt blank) a).move = .right ∨
      (transition (program p hnt blank) a).move = .stay)
    (hrun : run (program p hnt blank) (fun _ => true) arrows c = some out)
    (hlo : lo ≤ c.head) (hhi : out.head ≤ hi) :
    PrefixInInterval p hnt blank lo hi arrows c := by
  intro k hk
  obtain ⟨middle, hm⟩ := run_take_exists (program p hnt blank) (fun _ => true)
    arrows c out hrun k hk
  have hdrop : run (program p hnt blank) (fun _ => true) (arrows.drop k) middle =
      some out := by
    have hfull := hrun
    rw [← List.take_append_drop k arrows, run_append p hnt blank, hm,
      Option.bind_some] at hfull
    exact hfull
  have h1 := run_head_nondecreasing (program p hnt blank) (fun _ => true) _ c middle
    (fun a ha => hmoves a (List.mem_of_mem_take ha)) hm
  have h2 := run_head_nondecreasing (program p hnt blank) (fun _ => true) _ middle out
    (fun a ha => hmoves a (List.mem_of_mem_drop ha)) hdrop
  exact ⟨middle, hm, by omega, by omega⟩

theorem preBranch_nonleft (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys) :
    ∀ a ∈ preBranchArrows p hnt blank q w exterior,
      (transition (program p hnt blank) a).move = .right ∨
        (transition (program p hnt blank) a).move = .stay := by
  intro a ha
  simp only [preBranchArrows, List.mem_cons, List.mem_append] at ha
  rcases ha with rfl | hpre | hmarked
  · exact Or.inl (by simp [startScanArrow, transition])
  · exact unmarkedRange_nonleft p hnt blank q none w exterior 0 w.head.val a hpre
  · exact markedCellPre_nonleft p hnt blank q _ _ a hmarked

theorem preBranch_footprint (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys) :
    PrefixInInterval p hnt blank 0 (windowWidth w + 1 : Int)
      (preBranchArrows p hnt blank q w exterior)
      (initialWindowConfig q w exterior) := by
  refine interval_of_right_or_stay p hnt blank 0 _ _ _ _
    (preBranch_nonleft p hnt blank q w exterior)
    (preBranch_run p hnt blank q w exterior) (by change 0 ≤ (0 : Int); omega) ?_
  have hle : w.head.val + 1 ≤ w.cells.length := Nat.succ_le_of_lt w.head.isLt
  have hmul := Nat.mul_le_mul_right (nt + 1) hle
  change cellHead nt (w.head.val + 1) ≤ (windowWidth w + 1 : Int)
  unfold cellHead
  have hnat : 1 + (w.head.val + 1) * (nt + 1) ≤ windowWidth w + 1 := by
    rw [windowWidth_eq, Nat.add_comm (w.cells.length * (nt + 1)) 1]
    exact Nat.add_le_add_left hmul 1
  exact_mod_cast hnat

theorem lr_cell_right (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed : Bool) (x write : Phys) (armed' : Bool)
    (hne : x ≠ ULogSourceOneHotReader.blank)
    (hupd : updateLR a armed x = some (write, armed')) (bits : List Phys)
    (hbits : bits.length = nt) (hvalid : ∀ y ∈ bits, validBit y = true) :
    ∀ b ∈ ULogSourceObliviousLRCellExecution.cellArrows p hnt blank a armed x write
      armed' hne hupd bits hbits hvalid,
      (transition (program p hnt blank) b).move = .right := by
  intro b hb
  simp only [ULogSourceObliviousLRCellExecution.cellArrows, skipLRArrows,
    List.mem_cons] at hb
  rcases hb with rfl | hb
  · simp [updateLRFlagInteriorArrow, transition]
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact skipLRArrow_move p hnt blank a armed' _ i _ _

theorem overflowLRReject_nonleft (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length) :
    ∀ b ∈ overflowLRReject p hnt blank a w hmove hover,
      (transition (program p hnt blank) b).move = .right ∨
        (transition (program p hnt blank) b).move = .stay := by
  intro b hb
  simp only [overflowLRReject, overflowLRInterior, overflowLRTake, List.mem_append,
    List.mem_singleton] at hb
  rcases hb with hb | rfl
  · obtain ⟨cell, hc, hb⟩ := List.mem_flatten.mp hb
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
    exact Or.inl (lr_cell_right p hnt blank a _ _ _ _ _ _ _ _ _ b hb)
  · exact Or.inr (by simp [updateLRFlagOverflowArrow, transition])

theorem overflowLR_interval (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length)
    (exterior : Int → Phys) :
    PrefixInInterval p hnt blank 0 (windowWidth w + 1 : Int)
      (overflowLRReject p hnt blank a w hmove hover) (lrStart a w exterior) := by
  obtain ⟨tape, hrun⟩ := overflowLRReject_run p hnt blank a w hmove hover exterior
  exact interval_of_right_or_stay p hnt blank 0 _ _ _ _
    (overflowLRReject_nonleft p hnt blank a w hmove hover) hrun
    (by change 0 ≤ (1 : Int); omega)
    (by change ((windowWidth w + 1 : Int) ≤ (windowWidth w + 1 : Int)); omega)

theorem run_head_nonincreasing (P : Program (State ns nt) Phys)
    (movable : Phys → Bool) (arrows : List (Arrow P))
    (c out : Config (State ns nt) Phys)
    (hmoves : ∀ a ∈ arrows, (transition P a).move = .left ∨ (transition P a).move = .stay)
    (hrun : run P movable arrows c = some out) : out.head ≤ c.head := by
  induction arrows generalizing c with
  | nil => have := Option.some.inj hrun; subst out; exact le_rfl
  | cons a arrows ih =>
      cases hs : FiniteOneTapeSemantics.step P movable c a with
      | none => simp [FiniteOneTapeSemantics.run, hs] at hrun
      | some d =>
          have hd := step_some_head P movable c d a hs
          have hout := ih d (fun b hb => hmoves b (by simp [hb]))
            (by simpa [FiniteOneTapeSemantics.run, hs] using hrun)
          rcases hmoves a (by simp) with hleft | hstay
          · rw [hleft, moveHead] at hd; omega
          · rw [hstay, moveHead] at hd; omega

theorem interval_of_left_or_stay (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (lo hi : Int) (arrows : List (ScanArrow p hnt blank))
    (c out : ScanCfg ns nt)
    (hmoves : ∀ a ∈ arrows, (transition (program p hnt blank) a).move = .left ∨
      (transition (program p hnt blank) a).move = .stay)
    (hrun : run (program p hnt blank) (fun _ => true) arrows c = some out)
    (hhi : c.head ≤ hi) (hlo : lo ≤ out.head) :
    PrefixInInterval p hnt blank lo hi arrows c := by
  intro k hk
  obtain ⟨middle, hm⟩ := run_take_exists (program p hnt blank) (fun _ => true)
    arrows c out hrun k hk
  have hdrop : run (program p hnt blank) (fun _ => true) (arrows.drop k) middle =
      some out := by
    have hfull := hrun
    rw [← List.take_append_drop k arrows, run_append p hnt blank, hm,
      Option.bind_some] at hfull
    exact hfull
  have h1 := run_head_nonincreasing (program p hnt blank) (fun _ => true) _ c middle
    (fun a ha => hmoves a (List.mem_of_mem_take ha)) hm
  have h2 := run_head_nonincreasing (program p hnt blank) (fun _ => true) _ middle out
    (fun a ha => hmoves a (List.mem_of_mem_drop ha)) hdrop
  exact ⟨middle, hm, by omega, by omega⟩

theorem rl_cell_left (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (a : BoundedAction ns nt) (armed : Bool) (x write : Phys) (armed' : Bool)
    (hupd : updateRL a armed x = some (write, armed')) (bits : List Phys)
    (hbits : bits.length = nt) (hvalid : ∀ y ∈ bits, validBit y = true)
    (hneBits : ∀ y ∈ bits, y ≠ ULogSourceOneHotReader.blank) :
    ∀ b ∈ ULogSourceObliviousRLCellExecution.cellArrows p hnt blank a armed x write
      armed' hupd bits hbits hvalid hneBits,
      (transition (program p hnt blank) b).move = .left := by
  intro b hb
  simp only [ULogSourceObliviousRLCellExecution.cellArrows, skipRLBitArrows,
    List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hb
    exact skipRLArrow_move p hnt blank a armed _ _ _ _
  · simp [updateRLFlagArrow, transition]

theorem overflowRLReject_left_or_stay (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hmove : a.move = .left) (hhead : u.head.val = 0) :
    ∀ b ∈ overflowRLReject p hnt blank a u hmove hhead,
      (transition (program p hnt blank) b).move = .left ∨
        (transition (program p hnt blank) b).move = .stay := by
  intro b hb
  simp only [overflowRLReject, overflowRLInterior, overflowRLTake, List.mem_append,
    List.mem_singleton] at hb
  rcases hb with hb | rfl
  · obtain ⟨cell, hc, hb⟩ := List.mem_flatten.mp hb
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
    exact Or.inl (rl_cell_left p hnt blank a _ _ _ _ _ _ _ _ _ b hb)
  · exact Or.inr (by simp [skipRLOverflowArrow, transition])

theorem overflowRL_interval (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (a : BoundedAction ns nt) (u : LogicalWindow nt)
    (hmove : a.move = .left) (hhead : u.head.val = 0) (exterior : Int → Phys) :
    PrefixInInterval p hnt blank 0 (windowWidth u + 1 : Int)
      (overflowRLReject p hnt blank a u hmove hhead) (rlStart hnt a u exterior) := by
  obtain ⟨tape, hrun⟩ := overflowRLReject_run p hnt blank a u hmove hhead exterior
  exact interval_of_left_or_stay p hnt blank 0 _ _ _ _
    (overflowRLReject_left_or_stay p hnt blank a u hmove hhead) hrun
    (by change (windowWidth u : Int) ≤ (windowWidth u + 1 : Int); omega)
    (by change 0 ≤ (0 : Int); omega)

theorem unsafeRight_interval (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length)
    (exterior : Int → Phys) :
    PrefixInInterval p hnt blank 0 (windowWidth w + 1 : Int)
      (unsafeRightPrefix p hnt blank q a w hmove hover)
      (startConfig q a w exterior) :=
  prefixInInterval_append p hnt blank _ _ _ _ _ (lrStart a w exterior)
    (return_window_prefix_interval p hnt blank q a w exterior)
    (returnLeft_run p hnt blank q a w exterior)
    (overflowLR_interval p hnt blank a w hmove hover exterior)

theorem unsafeLeft_interval (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : a.move = .left) (hhd : w.head.val = 0) (exterior : Int → Phys) :
    PrefixInInterval p hnt blank 0 (windowWidth w + 1 : Int)
      (unsafeLeftPrefix p hnt blank q a w hmove hhd)
      (startConfig q a w exterior) := by
  have hright := vacuous_right_of_left w a hmove
  have hret := returnLeft_run p hnt blank q a w exterior
  have hmid :
      run (program p hnt blank) (fun _ => true)
        (lrWindowArrows p hnt blank a w hright)
        { state := .updateLRFlag a false, head := 1, tape := windowTape w exterior } =
        some (rlStart hnt a (lrWindow w a hright) exterior) := by
    simpa [lrStart, rlStart, lrWindow_windowWidth] using
      lr_window_run p hnt blank a w hright exterior
  apply prefixInInterval_append p hnt blank _ _ _ _ _
    (rlStart hnt a (lrWindow w a hright) exterior)
  · exact prefixInInterval_append p hnt blank _ _ _ _ _ (lrStart a w exterior)
      (return_window_prefix_interval p hnt blank q a w exterior) hret
      (lr_window_prefix_interval p hnt blank a w hright exterior)
  · rw [run_append p hnt blank, hret, Option.bind_some]; exact hmid
  · simpa only [lrWindow_windowWidth] using overflowRL_interval p hnt blank a
      (lrWindow w a hright) hmove
      (by simpa using lrWindow_head_of_left w a hmove ▸ hhd) exterior

theorem unsafe_right_raw_length_le (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (hmove : a.move = .right) (hover : w.head.val + 1 = w.cells.length)
    (exterior : Int → Phys) (raw : List (ScanArrow p hnt blank))
    (out : ScanCfg ns nt)
    (hrun : FiniteOneTapeSemantics.run (program p hnt blank) (fun _ => true) raw
      (startConfig q a w exterior) = some out) :
    raw.length ≤ (unsafeRightPrefix p hnt blank q a w hmove hover).length := by
  by_cases hle : raw.length ≤
      (unsafeRightPrefix p hnt blank q a w hmove hover).length
  · exact hle
  · have hge : (unsafeRightPrefix p hnt blank q a w hmove hover).length ≤
        raw.length := Nat.le_of_not_ge hle
    obtain ⟨tail, boundary, heq, hpre, htail⟩ :=
      nonbranchPrefix_split_successful_run p hnt blank
        (unsafeRightPrefix p hnt blank q a w hmove hover) raw
        (startConfig q a w exterior) out
        (unsafeRightPrefix_nonbranch p hnt blank q a w hmove hover exterior)
        hrun hge
    obtain ⟨tape, hfwd⟩ :=
      unsafeRightPrefix_run p hnt blank q a w hmove hover exterior
    have hb : boundary = {
        state := .reject
        head := (windowWidth w + 1 : Int)
        tape := tape } := Option.some.inj (hpre.symm.trans hfwd)
    subst boundary
    have htl : tail ≠ [] := by
      intro hnil
      subst tail
      have he := congrArg List.length heq
      simp only [List.length_append, List.length_nil, Nat.add_zero] at he
      omega
    have hnone := reject_run_nonempty p hnt blank
      { state := .reject, head := (windowWidth w + 1 : Int), tape := tape }
      tail rfl htl
    simp [hnone] at htail

theorem suffix_interval (p : BoundedProgram ns nt) (hnt : 0 < nt) (blank : Fin nt)
    (q : Fin ns) (a : BoundedAction ns nt) (w : LogicalWindow nt)
    (exterior : Int → Phys) (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw
      (startConfig q a w exterior) = some out)
    (hlen : raw.length ≤ 3 * windowWidth w + 4) :
    PrefixInInterval p hnt blank 0 (windowWidth w + 1 : Int) raw
      (startConfig q a w exterior) := by
  cases hact : w.applyAction? a with
  | some next =>
      exact prefixInInterval_of_short_forced p hnt blank 0 _ _ raw _ out
        (nonbranchPrefix_forced _ _ _ _ _
          (safe_suffix_nonbranch p hnt blank q a w next hact exterior))
        (safe_suffix_prefix_interval p hnt blank q a w next hact exterior) hrun
        (by simpa [safeSuffixArrows_length] using hlen)
  | none =>
      rcases (applyAction?_eq_none_iff w a).mp hact with ⟨hmove, hover⟩ | ⟨hmove, hhd⟩
      · exact prefixInInterval_of_short_forced p hnt blank 0 _ _ raw _ out
          (nonbranchPrefix_forced _ _ _ _ _
            (unsafeRightPrefix_nonbranch p hnt blank q a w hmove hover exterior))
          (unsafeRight_interval p hnt blank q a w hmove hover exterior) hrun
          (unsafe_right_raw_length_le p hnt blank q a w hmove hover exterior raw
            out hrun)
      · exact prefixInInterval_of_short_forced p hnt blank 0 _ _ raw _ out
          (nonbranchPrefix_forced _ _ _ _ _
            (unsafeLeftPrefix_nonbranch p hnt blank q a w hmove hhd exterior))
          (unsafeLeft_interval p hnt blank q a w hmove hhd exterior) hrun
          (by simpa [unsafeLeftPrefix_length] using hlen)

theorem remainder_interval (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw
      (initialWindowConfig q w exterior) = some out)
    (hlen : raw.length ≤ 4 * windowWidth w + 6) :
    PrefixInInterval p hnt blank 0 (windowWidth w + 1 : Int) raw
      (initialWindowConfig q w exterior) := by
  by_cases hscan : windowWidth w + 2 ≤ raw.length
  · obtain ⟨choice, tail, hraw, htail⟩ :=
      raw_scan_prefix p hnt blank q w exterior raw out hrun hscan
    have hsuf : tail.length ≤ 3 * windowWidth w + 4 := by
      have he := congrArg List.length hraw
      simp only [List.length_append, sourceScanArrows_length] at he; omega
    rw [hraw]
    exact prefixInInterval_append p hnt blank _ _ _ _ _
      (startConfig q choice.action w exterior)
      (source_scan_footprint p hnt blank q w choice exterior)
      (sourceScan_run p hnt blank q w choice exterior)
      (suffix_interval p hnt blank q choice.action w exterior tail out htail hsuf)
  · let pre := preBranchArrows p hnt blank q w exterior
    by_cases hbefore : raw.length ≤ pre.length
    · exact prefixInInterval_of_short_forced p hnt blank 0 _ pre raw _ out
        (nonbranchPrefix_forced _ _ _ pre _
          (preBranch_nonbranch p hnt blank q w exterior))
        (preBranch_footprint p hnt blank q w exterior) hrun hbefore
    · obtain ⟨tail, boundary, hraw, hboundary, htail⟩ :=
        nonbranchPrefix_split_successful_run p hnt blank pre raw
          (initialWindowConfig q w exterior) out
          (preBranch_nonbranch p hnt blank q w exterior) hrun (Nat.le_of_not_ge hbefore)
      have hb : boundary = preBranchConfig q w exterior :=
        Option.some.inj (hboundary.symm.trans (preBranch_run p hnt blank q w exterior))
      subst boundary
      cases tail with
      | nil => simp [hraw] at hbefore
      | cons b rest =>
          cases hs : FiniteOneTapeSemantics.step (program p hnt blank) (fun _ => true)
            (preBranchConfig q w exterior) b with
          | none => simp [FiniteOneTapeSemantics.run, hs] at htail
          | some d =>
              have hr : FiniteOneTapeSemantics.run (program p hnt blank) (fun _ => true)
                  rest d = some out := by
                simpa [FiniteOneTapeSemantics.run, hs] using htail
              obtain ⟨choice, hbeq, hd⟩ := branch_success_inverse p hnt blank q
                (w.cells.get w.head) (windowTape w exterior)
                (cellHead nt (w.head.val + 1)) b d hs
              have hd' : d = postBranchConfig q choice.action w exterior := by
                simpa [postBranchConfig, rangeConfig, preBranchConfig] using hd
              subst d
              let post := postBranchArrows p hnt blank q choice.action w exterior
              have hshort : rest.length ≤ post.length := by
                have he : raw.length = pre.length + rest.length + 1 := by
                  rw [hraw, List.length_append, List.length_cons, Nat.add_assoc]
                have hpreL : pre.length = (w.head.val + 1) * (nt + 1) + 1 :=
                  preBranchArrows_length p hnt blank q w exterior
                have hpostL : post.length =
                    (w.cells.length - w.head.val - 1) * (nt + 1) :=
                  postBranchArrows_length p hnt blank q choice.action w exterior
                have hpart : pre.length + 1 + post.length = windowWidth w + 2 := by
                  rw [hpreL, hpostL]; exact scan_length_partition w
                omega
              have hrest : rest = post.take rest.length :=
                eq_take_of_forced_le _ _ post rest _ out
                  (nonbranchPrefix_forced _ _ _ post _
                    (postBranch_nonbranch p hnt blank q choice.action w exterior))
                  hr hshort
              have hword : raw =
                  (sourceScanArrows p hnt blank q w choice exterior).take raw.length := by
                have hlenr : raw.length = pre.length + rest.length + 1 := by
                  rw [hraw, List.length_append, List.length_cons, Nat.add_assoc]
                have hprele : pre.length ≤ raw.length := by omega
                have hsub : raw.length - pre.length = rest.length + 1 := by omega
                rw [sourceScanArrows, List.take_append, List.take_of_length_le hprele,
                  hsub, Nat.add_one, List.take_succ_cons, ← hrest, ← hbeq, ← hraw]
              rw [hword]
              exact prefixInInterval_take p hnt blank 0 _
                (sourceScanArrows p hnt blank q w choice exterior) _
                (source_scan_footprint p hnt blank q w choice exterior) raw.length

theorem original_prefix_interval (p : BoundedProgram ns nt) (hnt : 0 < nt)
    (blank : Fin nt) (q : Fin ns) (w : LogicalWindow nt) (exterior : Int → Phys)
    (raw : List (ScanArrow p hnt blank)) (out : ScanCfg ns nt)
    (hrun : run (program p hnt blank) (fun _ => true) raw
      (initialWindowConfig q w exterior) = some out) :
    PrefixInInterval p hnt blank 0 (windowWidth w + 1 : Int) raw
      (initialWindowConfig q w exterior) := by
  induction hlen : raw.length using Nat.strong_induction_on generalizing q w raw out with
  | h n ih =>
      subst hlen
      by_cases hlong : 4 * windowWidth w + 6 < raw.length
      · obtain ⟨choice, next, hsafe, tail, hraw, htail⟩ :=
          extended_cycle_prefix p hnt blank q w exterior raw out hrun hlong
        have htl : tail.length < raw.length := by
          have he := congrArg List.length hraw
          simp only [List.length_append, cycleArrows_length] at he
          have := windowWidth_pos w; omega
        have hw : windowWidth next = windowWidth w := by
          simpa [windowWidth] using congrArg (fun m => m * (nt + 1))
            (LogicalWindow.applyAction_preserves_width w next choice.action hsafe)
        rw [hraw]
        apply prefixInInterval_append p hnt blank _ _ _ _ _
          (initialWindowConfig choice.action.target next exterior)
          (cycle_footprint p hnt blank q w choice next hsafe exterior)
          (cycle_run p hnt blank q w choice next hsafe exterior)
        simpa only [hw] using
          ih tail.length htl choice.action.target next tail out htail rfl
      · exact remainder_interval p hnt blank q w exterior raw out hrun
          (Nat.le_of_not_gt hlong)

theorem numerical_all_prefix_heads (M : Machine ns nt 2) (x : List Bool)
    (bound : Nat) (left suffix : List (Fin 3))
    (word : List (Arrow (numericalProgram M)))
    (out : Config (Fin (2 + Fintype.card (Active M))) (Fin 3))
    (hw : run (numericalProgram M) (fun _ => true) word
      (physical (2 : Fin 3) 0 (zipper M (inputWindow M x bound) left suffix)) =
        some out) :
    ∀ k ≤ word.length, ∃ middle,
      run (numericalProgram M) (fun _ => true) (word.take k)
        (physical (2 : Fin 3) 0 (zipper M (inputWindow M x bound) left suffix)) =
          some middle ∧ 0 ≤ middle.head ∧
      middle.head ≤ (((x.length + 2 * bound + 3) * (nt + 1) + 1 : Nat) : Int) := by
  let ext := exterior M (inputWindow M x bound) left suffix
  let haltWord := word.map (arrowEquiv M).symm
  have hrestore : word = haltWord.map (arrowEquiv M) :=
    (map_arrowEquiv_right M word).symm
  have hphys := zipper_physical M (inputWindow M x bound) left suffix
  have hnum : run (numericalProgram M) (fun _ => true) (haltWord.map (arrowEquiv M))
      (encodeConfig M (initialWindowConfig M.start (inputWindow M x bound) ext)) =
        some out := by simpa [hrestore, hphys] using hw
  have hhalt' := (run_arrowEquiv M (fun _ => true) haltWord
    (initialWindowConfig M.start (inputWindow M x bound) ext)).symm.trans hnum
  obtain ⟨haltOut, hhalt, _⟩ := Option.map_eq_some_iff.mp hhalt'
  have hinc := (run_includeArrows (original M) (halted M) (fun _ => true) haltWord
    (initialWindowConfig M.start (inputWindow M x bound) ext)).trans hhalt
  have horig := original_prefix_interval (toBounded M)
    (Nat.zero_lt_of_lt M.blank.isLt) M.blank M.start (inputWindow M x bound) ext
    (haltWord.map (includeArrow (original M) (halted M))) haltOut hinc
  intro k hk
  have hlenk : (haltWord.map (includeArrow (original M) (halted M))).length =
      word.length :=
    (List.length_map (as := haltWord) (includeArrow (original M) (halted M))).trans
      (List.length_map (as := word) (arrowEquiv M).symm)
  obtain ⟨middle, hm, hlo, hhi⟩ := horig k (by simpa [hlenk] using hk)
  have width : windowWidth (inputWindow M x bound) =
      (x.length + 2 * bound + 3) * (nt + 1) := by
    rw [windowWidth_eq, inputWindow_length]
  refine ⟨encodeConfig M middle, ?_, hlo, by simpa [width] using hhi⟩
  have hprefix : word.take k = (haltWord.take k).map (arrowEquiv M) := by
    rw [hrestore]
    exact (List.map_take (f := (arrowEquiv M : Arrow (haltProgram M) →
      Arrow (numericalProgram M))) (l := haltWord) (i := k)).symm
  have heq := run_includeArrows (original M) (halted M) (fun _ => true)
    (haltWord.take k) (initialWindowConfig M.start (inputWindow M x bound) ext)
  have hm' : run (haltProgram M) (fun _ => true) (haltWord.take k)
      (initialWindowConfig M.start (inputWindow M x bound) ext) = some middle := by
    have hmap := (List.map_take
      (f := includeArrow (original M) (halted M)) (l := haltWord) (i := k)).symm
    rw [hmap] at hm
    exact heq.symm.trans hm
  rw [hprefix, hphys, run_arrowEquiv, hm']; rfl

theorem all_raw_prefix_heads_zero (M : Machine ns nt 2) (x : List Bool)
    (bound : Nat) (_ht : RunsAtMost M x bound) (left suffix : List (Fin 3))
    (slots : List Bool) (hf : Int)
    (out : BoundedConfig (2 + Fintype.card (Active M)) 3)
    (hw : ULogFiniteTapeZipperRun.run (boundedProgram M) 2 slots 0
      (zipper M (inputWindow M x bound) left suffix) = some (hf, out)) :
    PrefixHeads (boundedProgram M) 2 slots 0
      (zipper M (inputWindow M x bound) left suffix) 0
      (((x.length + 2 * bound + 3) * (nt + 1) + 1 : Nat) : Int) := by
  have hz : zipperSlotRun (boundedProgram M) slots 0
      (zipper M (inputWindow M x bound) left suffix) = some (hf, out) := by
    rw [ULogFiniteTapeGuardedStageLeafCounts.zipperSlotRun_eq_run]; exact hw
  obtain ⟨word, hslots, _, hword⟩ := successful_zipper_to_arrows
    (boundedProgram M) slots 0 _ hf out hz
  apply transfer_prefix_heads (boundedProgram M) (scanner_terminal_table M) word slots
    0 0 _ _ hslots
  exact numerical_all_prefix_heads M x bound left suffix word
    (physical (2 : Fin 3) hf out) hword

theorem prefix_heads_add (p : BoundedProgram ns 3) (w : List Bool)
    (H lo hi : Int) (z : BoundedConfig ns 3) (h : PrefixHeads p 2 w 0 z lo hi) :
    PrefixHeads p 2 w H z (H + lo) (H + hi) := by
  intro k hk hf out hw
  have he := run_add p 2 (w.take k) 0 H z
  simp only [zero_add] at he
  rw [hw] at he
  obtain ⟨⟨h0, z0⟩, hr, hv⟩ := Option.map_eq_some_iff.mp he.symm
  have heads := (Prod.mk.inj hv).1
  obtain ⟨hlo, hhi⟩ := h k hk h0 z0 hr
  change h0 + H = hf at heads
  constructor <;> omega

theorem delimiter_subset_edges (M : Machine ns nt 2) (x : List Bool)
    (bound : Nat) (left suffix : List (Fin 3)) (H : Int) :
    leftEdge H (zipper M (inputWindow M x bound) left suffix) ≤ H ∧
      H + (((x.length + 2 * bound + 3) * (nt + 1) + 1 : Nat) : Int) ≤
        rightEdge H (zipper M (inputWindow M x bound) left suffix) := by
  have width : (inputWindow M x bound).encode.length =
      (x.length + 2 * bound + 3) * (nt + 1) := by
    change windowWidth (inputWindow M x bound) = _
    rw [windowWidth_eq, inputWindow_length]
  simp only [leftEdge, rightEdge, zipper, List.length_append, List.length_cons,
    Nat.cast_add, Nat.cast_one]
  rw [width]; constructor <;> omega

theorem all_raw_prefix_heads (M : Machine ns nt 2) (x : List Bool)
    (bound : Nat) (ht : RunsAtMost M x bound) (left suffix : List (Fin 3))
    (slots : List Bool) (H hf : Int)
    (out : BoundedConfig (2 + Fintype.card (Active M)) 3)
    (hw : ULogFiniteTapeZipperRun.run (boundedProgram M) 2 slots H
      (zipper M (inputWindow M x bound) left suffix) = some (hf, out)) :
    PrefixHeads (boundedProgram M) 2 slots H
      (zipper M (inputWindow M x bound) left suffix) H
      (H + (((x.length + 2 * bound + 3) * (nt + 1) + 1 : Nat) : Int)) := by
  obtain ⟨hf0, h0, _⟩ := run_from_zero (boundedProgram M) 2 slots H hf
    (zipper M (inputWindow M x bound) left suffix) out hw
  simpa [zero_add] using prefix_heads_add (boundedProgram M) slots H 0 _
    (zipper M (inputWindow M x bound) left suffix)
    (all_raw_prefix_heads_zero M x bound ht left suffix slots hf0 out h0)

theorem all_raw_zero_growth (M : Machine ns nt 2) (x : List Bool)
    (bound : Nat) (ht : RunsAtMost M x bound) (left suffix : List (Fin 3))
    (slots : List Bool) (H hf : Int)
    (out : BoundedConfig (2 + Fintype.card (Active M)) 3)
    (hw : ULogFiniteTapeZipperRun.run (boundedProgram M) 2 slots H
      (zipper M (inputWindow M x bound) left suffix) = some (hf, out)) :
    GrowthRun (boundedProgram M) 2 slots H
      (zipper M (inputWindow M x bound) left suffix) hf out 0 0 := by
  have heads := all_raw_prefix_heads M x bound ht left suffix slots H hf out hw
  have hedge := delimiter_subset_edges M x bound left suffix H
  apply no_growth_of_prefix_heads (boundedProgram M) 2 slots H hf _ out _ hw
  intro k hk hmid middle hrun
  obtain ⟨hl, hr⟩ := heads k hk hmid middle hrun
  constructor <;> omega

def scanner_all_prefix_growth_spec (M : Machine ns nt 2) (x : List Bool)
    (bound : Nat) (_ht : RunsAtMost M x bound) (left suffix : List (Fin 3)) : Prop :=
  ∀ (slots : List Bool) (H hf : Int)
    (out : BoundedConfig (2 + Fintype.card (Active M)) 3),
    ULogFiniteTapeZipperRun.run (boundedProgram M) 2 slots H
      (zipper M (inputWindow M x bound) left suffix) = some (hf, out) →
    PrefixHeads (boundedProgram M) 2 slots H
      (zipper M (inputWindow M x bound) left suffix) H
      (H + (((x.length + 2 * bound + 3) * (nt + 1) + 1 : Nat) : Int)) ∧
    GrowthRun (boundedProgram M) 2 slots H
      (zipper M (inputWindow M x bound) left suffix) hf out 0 0

theorem scanner_all_prefix_growth_spec_holds (M : Machine ns nt 2)
    (x : List Bool) (bound : Nat) (ht : RunsAtMost M x bound)
    (left suffix : List (Fin 3)) :
    scanner_all_prefix_growth_spec M x bound ht left suffix := fun slots H hf out hw =>
  ⟨all_raw_prefix_heads M x bound ht left suffix slots H hf out hw,
    all_raw_zero_growth M x bound ht left suffix slots H hf out hw⟩

end PakFixedPolyomino.ULogSourceObliviousAllPrefixGrowth
