import PakFixedPolyomino.ULogPassivePaths

/-! Automatic rule-list scan certificates from passive encoded paths. -/

namespace PakFixedPolyomino.ULogBootstrapExecution

open ULogAlphabet ULogControl ULogProgram
open MStarParserExecution

theorem sourceCell_readHeadNat (n : ℕ) (hn : n < 3) :
    (readHeadNat n ≠ ulogCore stateZero ∧
      readHeadNat n ≠ ulogCore stateOne ∧
      readHeadNat n ≠ MStarConcreteAlphabet.work ∧
      readHeadNat n ≠ ulogCore sourceMark ∧
      readHeadNat n ≠ ulogCore pcMark ∧
      readHeadNat n ≠ ulogCore stateMark ∧
      readHeadNat n ≠ ulogCore sourceBoundary ∧
      readHeadNat n ≠ ulogCore sourceBoundaryZero ∧
      readHeadNat n ≠ ulogCore sourceBoundaryOne) := by
  interval_cases n <;> decide

theorem readHeadNat_ne_readBoundary (n : ℕ) (hn : n < 3) :
    readHeadNat n ≠ ulogCore readBoundary := by
  interval_cases n <;> decide

theorem cursorMatchedMovePath_passive (rs : List ULogBytecode.RuleCode)
    (programToHead : List Tape) (hp : PassivePath programToHead) :
    PassivePath (cursorMatchedMovePath rs programToHead) := by
  apply passivePath_append
  · exact passivePath_map_codeTape (ULogBytecode.encodeRules rs)
  · exact hp

theorem encodedActionPath_passive (write target : ℕ)
    (move : OneTapeTableau.Move) (movePath : List Tape)
    (hp : PassivePath movePath) :
    PassivePath (encodedActionPath write target move movePath) := by
  unfold encodedActionPath moveBits
  apply passivePath_append
  · apply passivePath_append
    · exact passivePath_map_codeTape
        (ULogBytecode.encodeNatField write ++
          ULogBytecode.encodeNatField target)
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact passiveCell_codeTape (moveFirst move)
      · exact passiveCell_codeTape (moveSecond move)
  · exact hp

theorem cursorReadScanPath_passive (r : ULogBytecode.RuleCode)
    (rs : List ULogBytecode.RuleCode) (programToHead : List Tape)
    (hp : PassivePath programToHead) :
    PassivePath (cursorReadScanPath r rs programToHead) := by
  unfold cursorReadScanPath
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact passiveCell_codeTape r.slot
  · exact encodedActionPath_passive _ _ _ _
      (cursorMatchedMovePath_passive rs programToHead hp) x hx

theorem readMismatchRestorePath_safe_passive
    (source read : ℕ) (scanPath : List Tape)
    (hscan : PassivePath scanPath) :
    MismatchRestorePathSafe
      (readMismatchRestorePath source read scanPath) := by
  intro x hx
  unfold readMismatchRestorePath at hx
  simp only [List.mem_append, List.mem_reverse, List.mem_cons,
    List.mem_replicate] at hx
  rcases hx with hpre | ho | hs
  · rcases hpre with hp | hb | hz
    · exact (hscan x hp).mismatch
    · rw [hb]; decide
    · rw [hz.2]; exact (passiveCell_codeTape false).mismatch
  · rw [ho]; exact (passiveCell_codeTape true).mismatch
  · rw [hs.2]; exact (passiveCell_codeTape false).mismatch

theorem slotMismatchRestorePath_safe (source read : ℕ) :
    MismatchRestorePathSafe (slotMismatchRestorePath source read) := by
  intro x hx
  unfold slotMismatchRestorePath at hx
  simp only [List.mem_append, List.mem_cons, List.mem_replicate] at hx
  rcases hx with hpre | ho | hs
  · rcases hpre with ho | hz
    · rw [ho]; exact (passiveCell_codeTape true).mismatch
    · rw [hz.2]; exact (passiveCell_codeTape false).mismatch
  · rw [ho]; exact (passiveCell_codeTape true).mismatch
  · rw [hs.2]; exact (passiveCell_codeTape false).mismatch

theorem ruleScanCertificate_of_passive
    (slot : Bool) (current actual : ℕ) (hactual : actual < 3)
    (programToHead runtime : List Tape)
    (hp : PassivePath programToHead) (hruntime : PassivePath runtime)
    (r : ULogBytecode.RuleCode) (rs : List ULogBytecode.RuleCode)
    (hread : r.read < 3) :
    RuleScanCertificate slot current actual programToHead runtime r rs := by
  have hcode : PassivePath
      ((ULogBytecode.encodeNatField r.read ++ [r.slot] ++
        ULogBytecode.encodeAction r.action ++
          ULogBytecode.encodeRules rs).map codeTape) :=
    passivePath_map_codeTape _
  have hmove := cursorMatchedMovePath_passive rs programToHead hp
  have haction := encodedActionPath_passive r.action.write
    r.action.target r.action.move _ hmove
  have hreadScan := cursorReadScanPath_passive r rs programToHead hp
  refine
    { actual_valid := hactual
      read_valid := hread
      source_corridor := ?_
      read_boundary_free := ?_
      read_scan := passivePath_read hreadScan
      read_restore := readMismatchRestorePath_safe_passive r.source
        r.read (cursorReadScanPath r rs programToHead) hreadScan
      slot_scan := ?_
      slot_restore := slotMismatchRestorePath_safe r.source r.read
      program_restore := passivePath_restoreMismatch hp }
  · intro x hx
    unfold cursorRuleCorridor ruleContinuationCorridor at hx
    rcases List.mem_append.mp hx with hc | hpayload
    · exact (hcode x hc).source
    · rcases List.mem_append.mp hpayload with hp' | hheadRuntime
      · exact (hp x hp').source
      · rcases List.mem_cons.mp hheadRuntime with rfl | hr
        · exact sourceCell_readHeadNat actual hactual
        · exact (hruntime x hr).source
  · intro x hx
    unfold cursorRuleCorridor ruleContinuationCorridor at hx
    rcases List.mem_append.mp hx with hc | hpayload
    · exact (hcode x hc).read.2.2.2.2.1
    · rcases List.mem_append.mp hpayload with hp' | hheadRuntime
      · exact (hp x hp').read.2.2.2.2.1
      · rcases List.mem_cons.mp hheadRuntime with rfl | hr
        · exact readHeadNat_ne_readBoundary actual hactual
        · exact (hruntime x hr).read.2.2.2.2.1
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (passiveCell_codeTape (!slot)).read
    · exact (haction x hx).read

theorem certifiedProgramScan_of_passive
    (slot : Bool) (current actual : ℕ) (hactual : actual < 3)
    (programToHead runtime : List Tape)
    (hp : PassivePath programToHead) (hruntime : PassivePath runtime)
    (rules : List ULogBytecode.RuleCode)
    (hreads : ∀ r ∈ rules, r.read < 3) :
    CertifiedProgramScan slot current actual programToHead runtime rules := by
  induction rules with
  | nil => exact .nil
  | cons r rs ih =>
      exact .cons r rs
        (ruleScanCertificate_of_passive slot current actual hactual
          programToHead runtime hp hruntime r rs (hreads r (by simp)))
        (ih (fun s hs => hreads s (by simp [hs])))

end PakFixedPolyomino.ULogBootstrapExecution
