import PakFixedPolyomino.ULogTernaryGeneratedMarginEntrySpace

/-! Directional growth of the executed compact sealed entry. The one new
reserve seal is charged to the right. This supplies actual resource ledgers
above a sufficient capacity, not exclusion of low-capacity physical runs. -/
namespace PakFixedPolyomino.ULogTernaryGeneratedMarginEntryResources
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteAlphabetDeterministicRuns
open ULogFiniteTapeGrowthLedger ULogTernaryGeneratedMarginEntry
open ULogTernaryGeneratedHeadedSourceReturn (sourceBits retained)
variable {nt : Nat}

theorem source_left_head (nt k d c : Nat) (x : List Bool) :
    ULogTernaryGeneratedHeadedSourceReturn.finalHead nt k d c x =
      (k : Int) + (ULogTernaryNestedHeaderParser.header d c x).length + x.length + 1 := by
  simp only [ULogTernaryGeneratedHeadedSourceReturn.finalHead,
    ULogTernaryGeneratedHeadedSourceExpansion.finalHead,
    ULogTernaryPreparedHeadedSourceExpansion.finalHead,
    ULogTernaryGuardedPumpDelimiter.finalHead,
    ULogTernaryGuardedPumpDelimiter.prefixHead, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  ring

theorem retained_length (k d c : Nat) (hc : 0 < c) (x : List Bool) :
    (retained k d c x).length =
      k + (ULogTernaryNestedHeaderParser.header d c x).length + x.length + 2 := by
  have hu := congrArg List.length
    (ULogTernaryParserLeftSentinel.real_left_cell d c x
      (ULogTernaryGuardedPumpSentinel.parserLeft k) hc)
  simp only [List.length_append, List.length_reverse,
    ULogTernaryNestedHeaderParser.cells_length, List.length_cons] at hu
  have hl : (ULogTernaryGuardedPumpSentinel.parserLeft k).length = k + 2 := by
    simp [ULogTernaryGuardedPumpSentinel.parserLeft]
  rw [hl] at hu
  simp only [retained, List.length_append, ULogTernaryCountedSourceDelimiter.ones,
    List.length_replicate, List.length_cons, ULogTernaryGuardedPumpDelimiter.under]
  omega

theorem corrected_length (codes : Fin 3 → Fin nt) (blank : Fin nt) (x : List Bool) :
    (correctedBits codes blank x).length =
      if x.length = 0 then nt + 1 else (x.length + 1) * (nt + 1) := by
  cases x with
  | nil => simp [correctedBits, ULogTernaryGeneratedHeadedSourceReturn.source_length,
      ULogTernaryPreparedHeadedSourceExpansion.tail]
  | cons b rest =>
      simp [correctedBits, ULogTernaryGeneratedHeadedSourceReturn.source_length,
        ULogTernaryPreparedHeadedSourceExpansion.tail, ULogTernaryBalancedBlankPair.block,
        ULogSourceOneHotBlocks.encodeOneHot_length]
      ring

theorem final_edges (codes : Fin 3 → Fin nt) (blank : Fin nt) (k d c : Nat)
    (hc : 0 < c) (x : List Bool)
    (hpool : nt + 1 ≤ zeroCount nt k x) :
    leftEdge (ULogTernaryGeneratedHeadedSourceReturn.finalHead nt k d c x)
        (final codes blank k d c x) = -1 ∧
    rightEdge (ULogTernaryGeneratedHeadedSourceReturn.finalHead nt k d c x)
        (final codes blank k d c x) =
      (k + (ULogTernaryGuardedPumpSentinel.source d c x).length + 2 ^ k + 1 : Nat) := by
  have ht := final_tape codes blank k d c x hpool
  have hu := retained_length k d c hc x
  have hh := source_left_head nt k d c x
  have hs : (ULogTernaryGuardedPumpSentinel.source d c x).length =
      (ULogTernaryNestedHeaderParser.header d c x).length + 2 * x.length + 1 := by
    simp [ULogTernaryGuardedPumpSentinel.source,
      ULogTernaryNestedHeaderParser.nested_length,
      ULogTernaryNestedHeaderParser.counted_length, Nat.add_assoc]
  constructor
  · simp only [leftEdge, ht.1, hu, hh, Nat.cast_add]
    omega
  · simp only [rightEdge, ht.2.2, List.length_append, List.length_cons,
      ULogTernaryRetainedCounterPump.cells, List.length_map, List.length_replicate,
      List.length_nil, corrected_length, hh, hs]
    have hr : 0 < 2 ^ k := by positivity
    have hbefore : zeroCount nt k x =
        if x.length = 0 then 2 ^ k - 2 - nt else 2 ^ k - 1 - nt * x.length := rfl
    have hafter : ULogTernaryMarginReserveBudget.after nt (2 ^ k) x.length =
        zeroCount nt k x - (if x.length = 0 then 0 else nt + 1) := rfl
    by_cases hn : x.length = 0
    · simp only [hn, ↓reduceIte, Nat.mul_zero, Nat.add_zero] at hbefore hafter ⊢
      rw [hbefore] at hpool
      rw [hafter]
      omega
    · simp only [hn, ↓reduceIte] at hbefore hafter ⊢
      rw [hbefore] at hpool
      have hcost : nt * x.length + 1 ≤ 2 ^ k := by omega
      have he : ULogTernaryMarginReserveBudget.after nt (2 ^ k) x.length +
          (nt + 1) + 1 + nt * x.length = 2 ^ k := by omega
      have hm : (x.length + 1) * (nt + 1) = nt * x.length + x.length + nt + 1 := by ring
      rw [hm]
      have heI := congrArg (fun t : Nat => (t : Int)) he
      push_cast at heI
      push_cast
      omega

theorem actual_growth (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (blank : Fin nt)
    (k d c : Nat) (hc : 0 < c) (x : List Bool)
    (hfit : ULogTernaryGeneratedHeadedSourceExpansion.reserveCost nt x ≤ 2 ^ k - 1)
    (hpool : nt + 1 ≤ zeroCount nt k x) :
    GrowthRun (program hnt codes blank d c) 2 (List.replicate (deadline nt k d c x) false)
      0 (initial nt k d c x) (ULogTernaryGeneratedHeadedSourceReturn.finalHead nt k d c x)
      (final codes blank k d c x) 1 (2 ^ k + 1) := by
  obtain ⟨lg, rg, hg⟩ := every_actual_run (program hnt codes blank d c) 2
    (List.replicate (deadline nt k d c x) false) 0 _ _ _
    (actual_run hnt codes blank k d c hc x hfit hpool)
  have hi := ULogTernaryGuardedPumpDelimiterSpace.initial_edges k d c x
  change leftEdge 0 (initial nt k d c x) = 0 ∧ rightEdge 0 (initial nt k d c x) =
    (k + (ULogTernaryGuardedPumpSentinel.source d c x).length : Nat) at hi
  have hf := final_edges codes blank k d c hc x hpool
  have hl := hg.exact_ledger.1
  have hr := hg.exact_ledger.2.1
  rw [hi.1, hf.1] at hl
  rw [hi.2, hf.2] at hr
  have hlg : lg = 1 := by omega
  have hrg : rg = 2 ^ k + 1 := by omega
  simpa [hlg, hrg] using hg

theorem every_raw_growth (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (blank : Fin nt)
    (k d c : Nat) (hc : 0 < c) (x : List Bool)
    (hfit : ULogTernaryGeneratedHeadedSourceExpansion.reserveCost nt x ≤ 2 ^ k - 1)
    (hpool : nt + 1 ≤ zeroCount nt k x)
    {w : List Bool} {hf : Int} {out : BoundedConfig (states nt d c) 3}
    (hw : run (program hnt codes blank d c) 2 w 0 (initial nt k d c x) = some (hf, out)) :
    ∃ lg rg, GrowthRun (program hnt codes blank d c) 2 w 0 (initial nt k d c x) hf out lg rg ∧
      lg ≤ 1 ∧ rg ≤ 2 ^ k + 1 := by
  have hfalse := successful_zipper_is_false (2 : Fin 3) _
    (program_falseOnly hnt codes blank d c) hw
  have hlen := successful_zipper_length_le (2 : Fin 3) _
    (program_falseOnly hnt codes blank d c) (deadline nt k d c x) 0
    (initial nt k d c x) (final codes blank k d c x)
    (ULogTernaryGeneratedHeadedSourceReturn.finalHead nt k d c x)
    (actual_run hnt codes blank k d c hc x hfit hpool)
    (final_accepts codes blank k d c x) hw
  obtain ⟨lg, rg, hg⟩ := every_actual_run (program hnt codes blank d c) 2 w 0 hf _ out hw
  have split : List.replicate (deadline nt k d c x) false =
      w ++ List.replicate (deadline nt k d c x - w.length) false := by
    rw [hfalse]
    simpa only [List.length_replicate] using
      ULogTernaryOneHotBlockWriter.replicate_split _ _ hlen
  have full := actual_growth hnt codes blank k d c hc x hfit hpool
  have le := ULogTernaryOneHotBlockWriter.growth_append_le (by simpa [split] using full) hg
  exact ⟨lg, rg, hg, le⟩

theorem every_raw_extents (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (blank : Fin nt)
    (k d c : Nat) (hc : 0 < c) (x : List Bool)
    (hfit : ULogTernaryGeneratedHeadedSourceExpansion.reserveCost nt x ≤ 2 ^ k - 1)
    (hpool : nt + 1 ≤ zeroCount nt k x)
    {w : List Bool} {hf : Int} {out : BoundedConfig (states nt d c) 3}
    (hw : run (program hnt codes blank d c) 2 w 0 (initial nt k d c x) = some (hf, out)) :
    -1 ≤ leftEdge hf out ∧ rightEdge hf out ≤
      (k + (ULogTernaryGuardedPumpSentinel.source d c x).length + 2 ^ k + 1 : Nat) := by
  obtain ⟨lg, rg, hg, hl, hr⟩ := every_raw_growth hnt codes blank k d c hc x hfit hpool hw
  have hi := ULogTernaryGuardedPumpDelimiterSpace.initial_edges k d c x
  change leftEdge 0 (initial nt k d c x) = 0 ∧ rightEdge 0 (initial nt k d c x) =
    (k + (ULogTernaryGuardedPumpSentinel.source d c x).length : Nat) at hi
  have he := hg.exact_ledger
  rw [hi.1, hi.2] at he
  exact ⟨by omega, by omega⟩

theorem every_raw_ready (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (blank : Fin nt)
    (k d c : Nat) (hc : 0 < c) (x : List Bool)
    (hfit : ULogTernaryGeneratedHeadedSourceExpansion.reserveCost nt x ≤ 2 ^ k - 1)
    (hpool : nt + 1 ≤ zeroCount nt k x)
    {w : List Bool} {hf : Int} {out : BoundedConfig (states nt d c) 3}
    (hw : run (program hnt codes blank d c) 2 w 0 (initial nt k d c x) = some (hf, out)) :
    ∃ lg rg, GrowthRun (program hnt codes blank d c) 2 w 0 (initial nt k d c x) hf out lg rg ∧
      lg ≤ 1 ∧ rg ≤ 2 ^ k + 1 ∧
      ∀ C tail, 2 ^ k + 1 + (states nt d c - 1) ≤ C →
        ULogFiniteTapeDeterministicFrameReadiness.ActiveReadyRun (program hnt codes blank d c)
          w 0 (initial nt k d c x) C (MStarConcreteAlphabet.work :: tail) ∧
        ULogFiniteTapePhysicalResourceLedger.resourceRun (program hnt codes blank d c) 2
          w 0 (initial nt k d c x) C (MStarConcreteAlphabet.work :: tail) =
            some (hf, out, C - rg, (MStarConcreteAlphabet.work :: tail).drop lg) := by
  obtain ⟨lg, rg, growth, hl, hr⟩ := every_raw_growth hnt codes blank k d c hc x hfit hpool hw
  refine ⟨lg, rg, growth, hl, hr, ?_⟩
  intro C tail capacity
  refine ⟨?_, ULogFiniteTapePhysicalResourceLedger.actual_resource_run growth C
    (MStarConcreteAlphabet.work :: tail)⟩
  cases lg with
  | zero =>
      simpa using ULogFiniteTapeDeterministicFrameReadiness.actual_active_ready growth
        (program_falseOnly hnt codes blank d c) C (MStarConcreteAlphabet.work :: tail) (by omega)
  | succ lg =>
      have hz : lg = 0 := by omega
      subst lg
      simpa using ULogFiniteTapeDeterministicFrameReadiness.actual_active_ready growth
        (program_falseOnly hnt codes blank d c) C tail (by omega)

theorem compact_entry_resource_spec (hnt : 0 < nt) (codes : Fin 3 → Fin nt) (blank : Fin nt)
    (p : Polynomial Nat) (x : List Bool) :
    let k := ULogTernaryGeneratedHeadedSourceExpansion.width nt p x
    ∀ w hf out, run (compactProgram hnt codes blank p) 2 w 0 (compactInitial nt p x) = some (hf, out) →
      ∃ lg rg, GrowthRun (compactProgram hnt codes blank p) 2 w 0 (compactInitial nt p x) hf out lg rg ∧
        lg ≤ 1 ∧ rg ≤ 2 ^ k + 1 ∧
        ∀ C tail, 2 ^ k + 1 +
            (states nt
              (ULogTernaryGuardedPumpDelimiterInput.depth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p))
              (ULogTernaryGuardedPumpDelimiterInput.seedWidth (ULogTernaryGeneratedHeadedSourceExpansion.polynomial nt p)) - 1) ≤ C →
          ULogFiniteTapeDeterministicFrameReadiness.ActiveReadyRun (compactProgram hnt codes blank p)
            w 0 (compactInitial nt p x) C (MStarConcreteAlphabet.work :: tail) ∧
          ULogFiniteTapePhysicalResourceLedger.resourceRun (compactProgram hnt codes blank p) 2
            w 0 (compactInitial nt p x) C (MStarConcreteAlphabet.work :: tail) =
              some (hf, out, C - rg, (MStarConcreteAlphabet.work :: tail).drop lg) := by
  dsimp only
  intro w hf out hw
  exact every_raw_ready hnt codes blank _ _ _ (ULogTernaryGuardedPumpDelimiterInput.seed_positive _) x
    (ULogTernaryGeneratedHeadedSourceExpansion.compact_reserve_fits nt p x) (compact_pool_fits nt p x) hw

end PakFixedPolyomino.ULogTernaryGeneratedMarginEntryResources
