import PakFixedPolyomino.MStarParserTailSoundness

/-! # Ordered raw scanner words -/

namespace PakFixedPolyomino.PakScannerRawShape

open MStarParserTailSoundness

def scannerTapeLetter (b : ConcretePakScanner.Buffer) : MStarULogAssembly.Tape :=
  OneTapeTableau.cellLetter
    (PakCouplingGenerated.bufferCell MStarULogAssembly.boundaryData b)

def scannerCoreLetter : ConcretePakScanner.Buffer → MStarULogAssembly.CoreTape
  | .zero | .headZero => MStarConcreteAlphabet.zero
  | .one | .headOne => MStarConcreteAlphabet.one
  | .work => MStarConcreteAlphabet.work
  | .rightEnd | .hash => MStarConcreteAlphabet.zero

theorem windowCells_drop_eq_ofFn (n start : ℕ)
    (c : PakMStarCouplingCorrectness.MStarConfig) (hstart : start ≤ n) :
    (PakOuterParserReflection.windowCells n c).drop start =
      List.ofFn (fun i : Fin (n - start) => c.tape (i.1 + start)) := by
  apply List.ext_get
  · simp [PakOuterParserReflection.windowCells]
  · intro i hi h'i
    simp [PakOuterParserReflection.windowCells, Int.add_comm]

inductive ScannerWordStage where
  | core | rightEnd | hash
  deriving DecidableEq, Repr

def bufferStage : ConcretePakScanner.Buffer → ScannerWordStage
  | .zero | .one | .work | .headZero | .headOne => .core
  | .rightEnd => .rightEnd
  | .hash => .hash

theorem scannerTapeLetter_eq_core_of_stage_core
    (b : ConcretePakScanner.Buffer) (hb : bufferStage b = .core) :
    scannerTapeLetter b = .core (scannerCoreLetter b) := by
  cases b <;> simp [bufferStage] at hb ⊢ <;>
    rfl

def stageStep : ScannerWordStage → ConcretePakScanner.Buffer →
    Option ScannerWordStage
  | .core, b => some (bufferStage b)
  | .rightEnd, .hash => some .hash
  | .hash, .hash => some .hash
  | _, _ => none

inductive OrderedScannerBuffers : List ConcretePakScanner.Buffer →
    ScannerWordStage → Prop
  | nil : OrderedScannerBuffers [] .core
  | snoc {xs : List ConcretePakScanner.Buffer} {stage next : ScannerWordStage}
      (H : OrderedScannerBuffers xs stage) (b : ConcretePakScanner.Buffer)
      (hstep : stageStep stage b = some next) :
      OrderedScannerBuffers (xs ++ [b]) next

private theorem bottom_edge_stage_core :
    ∀ (t : ConcretePakScanner.State) (b : Bool),
      ConcretePakScanner.LegalScan PakCouplingGenerated.scannerBottom t b →
        bufferStage t.centre = .core := by
  native_decide

private theorem legal_edge_stage_step :
    ∀ (s t : ConcretePakScanner.State) (b : Bool),
      ScannerRawStateOK s → s.phase ≠ .bot →
      ConcretePakScanner.LegalScan s t b →
        stageStep (bufferStage s.centre) t.centre = some (bufferStage t.centre) := by
  native_decide

def scannerBufferPrefix {n : ℕ}
    (P : PakScannerBaselineAutomaton.ScannerPath n) :
    ∀ k : ℕ, k ≤ n → List ConcretePakScanner.Buffer
  | 0, _ => []
  | k + 1, hk => scannerBufferPrefix P k (by omega) ++
      [(P.states ⟨k + 1, by omega⟩).centre]

theorem scannerBufferPrefix_eq_ofFn {n : ℕ}
    (P : PakScannerBaselineAutomaton.ScannerPath n) :
    ∀ (k : ℕ) (hk : k ≤ n),
      scannerBufferPrefix P k hk =
        List.ofFn (fun i : Fin k =>
          (P.states ⟨i.1 + 1, by omega⟩).centre) := by
  intro k
  induction k with
  | zero => intro hk; rfl
  | succ k ih =>
      intro hk
      rw [scannerBufferPrefix, ih]
      rw [List.ofFn_succ_last]
      congr 1

theorem scannerBufferPrefix_ordered {n : ℕ}
    (P : PakScannerBaselineAutomaton.ScannerPath n) :
    ∀ (k : ℕ) (hk : k + 1 ≤ n),
      OrderedScannerBuffers (scannerBufferPrefix P (k + 1) hk)
        (bufferStage (P.states ⟨k + 1, by omega⟩).centre) := by
  intro k
  induction k with
  | zero =>
      intro hk
      have hlegal : ConcretePakScanner.LegalScan PakCouplingGenerated.scannerBottom
          (P.states ⟨1, by omega⟩) (n.testBit 0) := by
        rw [← P.bottom]
        simpa using P.legal ⟨0, by omega⟩
      exact .snoc .nil _ rfl
  | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hok := scannerPath_state_succ_rawState P k (by omega)
      let jpos : Fin (n + 1) := ⟨k + 1, by have := hk; omega⟩
      have hphase := scannerPath_phase_ne_bot_of_pos P jpos (by simp [jpos])
      have hedge := legal_edge_stage_step
        (P.states ⟨k + 1, by omega⟩) (P.states ⟨k + 2, by omega⟩)
        (n.testBit (k + 1)) hok hphase (by
          simpa using P.legal ⟨k + 1, by omega⟩)
      exact .snoc hprev _ hedge

def shapeStage (hasRightEnd : Bool) (hashes : ℕ) : ScannerWordStage :=
  if hashes = 0 then if hasRightEnd then .rightEnd else .core else .hash

theorem OrderedScannerBuffers.decompose {xs : List ConcretePakScanner.Buffer}
    {stage : ScannerWordStage} (H : OrderedScannerBuffers xs stage) :
    ∃ core : List ConcretePakScanner.Buffer, ∃ hasRightEnd : Bool, ∃ hashes : ℕ,
      xs = core ++ (if hasRightEnd then [.rightEnd] else []) ++
          List.replicate hashes .hash ∧
      (∀ b ∈ core, bufferStage b = .core) ∧
      stage = shapeStage hasRightEnd hashes := by
  induction H with
  | nil =>
      exact ⟨[], false, 0, by simp, by simp, by rfl⟩
  | @snoc xs stage next H b hstep ih =>
      rcases ih with ⟨core, hasRightEnd, hashes, hxs, hcore, hstage⟩
      subst stage
      cases hashes with
      | zero =>
          cases hasRightEnd with
          | false =>
              by_cases hb : bufferStage b = .core
              · have hnext : next = .core := by
                  have hbn : bufferStage b = next := Option.some.inj (by
                    simpa [shapeStage, stageStep] using hstep)
                  exact hbn.symm.trans hb
                refine ⟨core ++ [b], false, 0, ?_, ?_, ?_⟩
                · simp [hxs, List.append_assoc]
                · intro x hx
                  rcases List.mem_append.mp hx with hx | hx
                  · exact hcore x hx
                  · have hxb : x = b := by simpa using hx
                    subst x
                    exact hb
                · simpa [shapeStage] using hnext
              · cases b with
                | hash =>
                    refine ⟨core, false, 1, ?_, hcore, ?_⟩
                    · simp [hxs, List.append_assoc]
                    · simpa [shapeStage, stageStep, bufferStage] using hstep.symm
                | rightEnd =>
                    refine ⟨core, true, 0, ?_, hcore, ?_⟩
                    · simp [hxs, List.append_assoc]
                    · simpa [shapeStage, stageStep, bufferStage] using hstep.symm
                | zero | one | work | headZero | headOne =>
                    exact (hb rfl).elim
          | true =>
              cases b <;> simp [shapeStage, stageStep, bufferStage] at hstep
              refine ⟨core, true, 1, ?_, hcore, ?_⟩
              · simp [hxs, List.append_assoc]
              · exact hstep.symm
      | succ hashes =>
          cases b <;> simp [shapeStage, stageStep, bufferStage] at hstep
          refine ⟨core, hasRightEnd, hashes + 2, ?_, hcore, ?_⟩
          · rw [hxs]
            cases hasRightEnd <;>
              simp [List.replicate_succ, List.append_assoc]
          · simpa [shapeStage] using hstep.symm

theorem slotOne_timeZero_tape_eq_scannerBuffer {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) (j : Fin n) :
    ((PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).config
      ⟨0, Nat.zero_lt_succ n⟩).tape j.1 =
    OneTapeTableau.cellLetter (PakCouplingGenerated.bufferCell
      MStarULogAssembly.boundaryData
      ((PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1).states
        ⟨j.1, Nat.lt_succ_of_lt j.2⟩).centre) := by
  let R := PakFullFrameTableauReadback.FullFrame.tableau_column_readback F.1
    (PakMStarCouplingCorrectness.eastIndex F.1.width_pos)
  have hconfig :
      (PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).config
        ⟨0, Nat.zero_lt_succ n⟩ = R.before := by
    change PakFullFrameTableauReadback.FullFrame.reverse_tableau_config F.1
      ⟨0, Nat.zero_lt_succ n⟩ = R.before
    simp [PakFullFrameTableauReadback.FullFrame.reverse_tableau_config,
      F.1.width_pos, PakFullFrameTableauReadback.reverseColumn,
      PakMStarCouplingCorrectness.eastIndex, R]
  rw [hconfig]
  change R.oldTape j.1 = _
  rw [R.oldTape_at j]
  rcases F.1.east_emits_tableau_window j with ⟨s, t, hscan, hold⟩
  have hstrip : R.oldStrip j =
      PakCouplingGenerated.emittedWindow MStarULogAssembly.boundaryData s t := by
    simpa [R] using hold
  have hpair : PakScannerBaselineAutomaton.FullFrame.eastPair F.1 j = (s, t) :=
    Option.some.inj
      ((PakScannerBaselineAutomaton.FullFrame.eastPair_spec F.1 j).symm.trans hscan)
  have hstates := PakScannerBaselineAutomaton.FullFrame.eastPair_eq_states F.1 j
  have hs : s =
      (PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1).states
        ⟨j.1, Nat.lt_succ_of_lt j.2⟩ :=
    congrArg Prod.fst (hpair.symm.trans hstates)
  rw [hstrip, hs]
  rfl

theorem slotOne_timeOne_tape_eq_scannerBuffer {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) (j : Fin n) :
    ((PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).config
      ⟨1, Nat.succ_lt_succ F.1.width_pos⟩).tape j.1 =
    OneTapeTableau.cellLetter (PakCouplingGenerated.bufferCell
      MStarULogAssembly.boundaryData
      ((PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1).states
        ⟨j.1, Nat.lt_succ_of_lt j.2⟩).centre) := by
  rw [MStarParserTailSoundness.slotOne_timeOne_tape_eq_timeZero F]
  exact slotOne_timeZero_tape_eq_scannerBuffer F j

theorem slotOneTrimmedZipper_cells_eq_drop {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      (PakOuterParserReflection.windowCells n
        ((PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).config
          ⟨1, Nat.succ_lt_succ F.1.width_pos⟩)).drop 1 := by
  unfold PakSlotOneParserDecode.slotOneTrimmedZipper
    PakSlotOneParserDecode.slotOneTimeOneZipper
    PakOuterParserReflection.windowZipper
  rw [PakSlotOneParserDecode.slotOne_timeOne_headIndex_eq_one F]
  dsimp
  let c := (PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).config
    ⟨1, Nat.succ_lt_succ F.1.width_pos⟩
  let cells := PakOuterParserReflection.windowCells n c
  change c.tape 1 :: cells.drop 2 = cells.drop 1
  have hlen : 1 < cells.length := by
    simp [cells, PakOuterParserReflection.windowCells]
    have := (PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).width_ge_three
    omega
  calc
    c.tape 1 :: cells.drop 2 = cells[1] :: cells.drop 2 := by
      simp [cells, PakOuterParserReflection.windowCells]
    _ = cells.drop 1 := (List.drop_eq_getElem_cons hlen).symm

theorem slotOneTrimmedZipper_cells_eq_scannerBufferPrefix {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
      (scannerBufferPrefix
        (PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1)
        (n - 1) (Nat.sub_le n 1)).map scannerTapeLetter := by
  have hwidth :=
    (PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).width_ge_three
  rw [slotOneTrimmedZipper_cells_eq_drop F]
  rw [windowCells_drop_eq_ofFn n 1 _ (by omega)]
  rw [scannerBufferPrefix_eq_ofFn, List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext i
  simp only [Function.comp_apply]
  let j : Fin n := ⟨i.1 + 1, by
    have := i.2
    omega⟩
  have htape := slotOne_timeOne_tape_eq_scannerBuffer F j
  simpa [scannerTapeLetter, j] using htape

theorem slotOneTrimmedZipper_ordered_tape_shape {n : ℕ}
    (F : PakSlotOneFullFrameReflection.SlotOneFullFrame n) :
    ∃ core : List MStarULogAssembly.CoreTape, ∃ hasRightEnd : Bool,
      ∃ hashes : ℕ,
        (PakSlotOneParserDecode.slotOneTrimmedZipper F).focus ::
            (PakSlotOneParserDecode.slotOneTrimmedZipper F).right =
          core.map MStarOuterProgram.Tape.core ++
            (if hasRightEnd then
              [MStarOuterProgram.Tape.scratch ⟨2, by decide⟩]
            else []) ++
            List.replicate hashes MStarOuterProgram.Tape.hash := by
  let P := PakScannerBaselineAutomaton.FullFrame.toScannerPath F.1
  have hwidth :=
    (PakFullFrameTableauReadback.FullFrame.toUniformWindowedRun F.1).width_ge_three
  have hordered₀ := scannerBufferPrefix_ordered P (n - 2) (by omega)
  have hindex : n - 2 + 1 = n - 1 := by omega
  have hordered : OrderedScannerBuffers
      (scannerBufferPrefix P (n - 1) (Nat.sub_le n 1))
      (bufferStage (P.states ⟨n - 1, by omega⟩).centre) := by
    simpa [hindex] using hordered₀
  rcases hordered.decompose with
    ⟨buffers, hasRightEnd, hashes, hshape, hcore, hstage⟩
  refine ⟨buffers.map scannerCoreLetter, hasRightEnd, hashes, ?_⟩
  rw [slotOneTrimmedZipper_cells_eq_scannerBufferPrefix F, hshape]
  simp only [List.map_append, List.map_map]
  have hcoreMap : buffers.map scannerTapeLetter =
      buffers.map (fun b => MStarOuterProgram.Tape.core (scannerCoreLetter b)) := by
    apply List.map_congr_left
    intro b hb
    exact scannerTapeLetter_eq_core_of_stage_core b (hcore b hb)
  rw [hcoreMap]
  cases hasRightEnd <;>
    simp [scannerTapeLetter, PakCouplingGenerated.bufferCell,
      MStarULogAssembly.boundaryData, MStarOuterProgram.boundaryData,
      OneTapeTableau.cellLetter, Function.comp_def]

end PakFixedPolyomino.PakScannerRawShape
