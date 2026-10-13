import PakFixedPolyomino.PakSideScannerRow

/-!
# Parser/copier execution in the literal outer program

`MStarParserExecution` and `MStarCopierExecution` use finite zippers.  The
tableau, on the other hand, is driven by labelled arrows of the literal
`MStarULogAssembly.program` acting on integer-indexed configurations.  This
file records the exact type comparison and starts the operational bridge at
the smallest common interface: an occupied slot-zero rule of the combined
parser/copier table.

The bridge below does not replace a computation by an unlabelled reachability
witness.  It constructs the literal outer arrow, executes it with
`FiniteOneTapeSemantics.step`, packages it as a literal arrow list, and proves
that hash padding outside a supplied window is preserved.  A later zipper
lift only has to establish, for every successful zipper step, the corresponding
`MStarCopierMicrocode.step` equation and the usual finite-zipper/ambient-tape
agreement.
-/

namespace PakFixedPolyomino.PakParserOuterBridge

open OneTapeTableau FiniteOneTapeProgram FiniteOneTapeSemantics

abbrev OuterState := MStarULogAssembly.State
abbrev OuterTape := MStarULogAssembly.Tape
abbrev OuterConfig := PakMStarCouplingCorrectness.MStarConfig
abbrev OuterArrow := MStarULogAssembly.Arrow
abbrev ParserControl := MStarULogAssembly.ParserControl
abbrev OuterAction := Action OuterState OuterTape

/-- The concrete post-configuration described by an outer-machine action. -/
def afterAction (c : OuterConfig) (act : OuterAction) : OuterConfig :=
  { state := act.target
    head := moveHead act.move c.head
    tape := writtenTape c act.write }

/-- Actual reachability in the fixed outer program, retaining the complete
list of occupied labelled arrows. -/
def OuterReaches (c d : OuterConfig) : Prop :=
  ∃ arrows : List OuterArrow,
    FiniteOneTapeSemantics.run MStarULogAssembly.program
      MStarOuterProgram.movable arrows c = some d

theorem outerReaches_refl (c : OuterConfig) : OuterReaches c c := by
  exact ⟨[], rfl⟩

theorem outerRun_append (xs ys : List OuterArrow) (c : OuterConfig) :
    FiniteOneTapeSemantics.run MStarULogAssembly.program
        MStarOuterProgram.movable (xs ++ ys) c =
      (FiniteOneTapeSemantics.run MStarULogAssembly.program
        MStarOuterProgram.movable xs c).bind
          (FiniteOneTapeSemantics.run MStarULogAssembly.program
            MStarOuterProgram.movable ys) := by
  induction xs generalizing c with
  | nil => rfl
  | cons a as ih =>
      simp only [List.cons_append, run_cons]
      cases hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
          MStarOuterProgram.movable c a with
      | none => simp [hstep]
      | some c' => simp [hstep, ih]

theorem outerReaches_trans {c d e : OuterConfig}
    (hcd : OuterReaches c d) (hde : OuterReaches d e) :
    OuterReaches c e := by
  rcases hcd with ⟨xs, hxs⟩
  rcases hde with ⟨ys, hys⟩
  refine ⟨xs ++ ys, ?_⟩
  rw [outerRun_append, hxs]
  exact hys

/-- A stepwise realization of the finite parser zipper in the integer-indexed
outer tape.  The relation is deliberately supplied by the caller: the finite
zipper does not itself choose where its finite support is placed in the
ambient hash-padded tape. -/
def ParserOuterStepSimulation
    (zero one work : MStarULogAssembly.CoreTape)
    (realize : MStarParserExecution.Result MStarULogAssembly.CoreTape →
      OuterConfig → Prop) : Prop :=
  ∀ r s c, realize r c →
    MStarParserExecution.oneStep zero one work r = s →
      ∃ d, realize s d ∧ OuterReaches c d

/-- Lift a finite-parser reachability witness to a literal outer-program run.
Unlike the zipper witness, the result retains the concrete list of occupied
outer arrows.  The supplied simulation is exactly where a client proves the
finite zipper agrees with its chosen hash-padded ambient tape. -/
theorem parserReaches_outerArrowList
    (zero one work : MStarULogAssembly.CoreTape)
    (realize : MStarParserExecution.Result MStarULogAssembly.CoreTape →
      OuterConfig → Prop)
    (hsim : ParserOuterStepSimulation zero one work realize)
    {r s : MStarParserExecution.Result MStarULogAssembly.CoreTape}
    {c : OuterConfig}
    (hreaches : MStarParserExecution.Reaches zero one work r s)
    (hrealize : realize r c) :
    ∃ d arrows, realize s d ∧
      FiniteOneTapeSemantics.run MStarULogAssembly.program
        MStarOuterProgram.movable arrows c = some d := by
  rcases hreaches with ⟨fuel, hrun⟩
  induction fuel generalizing r c with
  | zero =>
      simp only [MStarParserExecution.run_zero] at hrun
      subst s
      exact ⟨c, [], hrealize, rfl⟩
  | succ fuel ih =>
      change MStarParserExecution.run zero one work fuel
        (MStarParserExecution.oneStep zero one work r) = s at hrun
      rcases hsim r (MStarParserExecution.oneStep zero one work r) c
          hrealize rfl with ⟨d, hd, hcd⟩
      rcases ih hd hrun with ⟨e, ys, he, hys⟩
      rcases hcd with ⟨xs, hxs⟩
      refine ⟨e, xs ++ ys, he, ?_⟩
      rw [outerRun_append, hxs]
      exact hys

/-- The scanner's certified parser trace can be fed directly into any
hash-padded ambient realization.  The conclusion is an actual outer run to
the parser's `copyReady` zipper, together with the unchanged exterior fact
for the realized endpoint. -/
theorem sideParser_reaches_outerCopyReady_arrowList_of_simulation
    (x : ConcretePakSide.Word)
    (realize : MStarParserExecution.Result MStarULogAssembly.CoreTape →
      OuterConfig → Prop)
    (hsim : ParserOuterStepSimulation MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work realize)
    (hinit : realize
      (MStarParserExecution.extendResultRight
        (MStarParserExecution.initial MStarConcreteAlphabet.zero
          MStarConcreteAlphabet.one MStarConcreteAlphabet.work
          (ConcretePakSide.encodedWord x))
        (MStarCopierExecution.parserCopierReserve x ++
          PakSideScanner.sideCopierHashTail x))
      (PakSideScannerRow.sideEncodedParserConfig x))
    (hhash : ∀ r c, realize r c → ∀ z : Int,
      z < 0 ∨ ((PakSideScanner.sideScannerBits x).length + 2 : Int) ≤ z →
        c.tape z = .hash) :
    ∃ d arrows,
      realize
        (.copyReady (MStarParserExecution.extendRight
          (MStarConcreteAlphabet.finalZipper x.reverse)
          (MStarCopierExecution.parserCopierReserve x ++
            PakSideScanner.sideCopierHashTail x))) d ∧
      FiniteOneTapeSemantics.run MStarULogAssembly.program
        MStarOuterProgram.movable arrows
          (PakSideScannerRow.sideEncodedParserConfig x) = some d ∧
      (∀ z : Int,
        z < 0 ∨ ((PakSideScanner.sideScannerBits x).length + 2 : Int) ≤ z →
          d.tape z = .hash) := by
  rcases parserReaches_outerArrowList MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work realize hsim
      (PakSideScanner.parser_reaches_sideCopierReserve x) hinit with
    ⟨d, arrows, hd, hrun⟩
  exact ⟨d, arrows, hd, hrun, hhash _ _ hd⟩

/-- Stepwise ambient realization for the copier zipper.  As for the parser,
the relation records the non-definitional placement of finite zipper cells in
the integer-indexed hash-padded tape. -/
def CopierOuterStepSimulation
    (realize : MStarCopierExecution.Result → OuterConfig → Prop) : Prop :=
  ∀ r s c, realize r c → MStarCopierExecution.oneStep r = s →
    ∃ d, realize s d ∧ OuterReaches c d

/-- Every finite copier reachability proof lifts to a concrete list of
occupied outer arrows once its ambient step realization has been supplied. -/
theorem copierReaches_outerArrowList
    (realize : MStarCopierExecution.Result → OuterConfig → Prop)
    (hsim : CopierOuterStepSimulation realize)
    {r s : MStarCopierExecution.Result} {c : OuterConfig}
    (hreaches : MStarCopierExecution.Reaches r s)
    (hrealize : realize r c) :
    ∃ d arrows, realize s d ∧
      FiniteOneTapeSemantics.run MStarULogAssembly.program
        MStarOuterProgram.movable arrows c = some d := by
  rcases hreaches with ⟨fuel, hrun⟩
  induction fuel generalizing r c with
  | zero =>
      simp only [MStarCopierExecution.run_zero] at hrun
      subst s
      exact ⟨c, [], hrealize, rfl⟩
  | succ fuel ih =>
      change MStarCopierExecution.run fuel
        (MStarCopierExecution.oneStep r) = s at hrun
      rcases hsim r (MStarCopierExecution.oneStep r) c hrealize rfl with
        ⟨d, hd, hcd⟩
      rcases ih hd hrun with ⟨e, ys, he, hys⟩
      rcases hcd with ⟨xs, hxs⟩
      refine ⟨e, xs ++ ys, he, ?_⟩
      rw [outerRun_append, hxs]
      exact hys

/-! ## Anchored finite parser tapes -/

/-- The finite occupied segment of a parser zipper, written in physical
left-to-right order.  Using its left endpoint as the ambient origin keeps
that origin fixed under both zipper moves. -/
def anchoredZipperCells (z : MStarParserExecution.Zipper OuterTape) :
    List OuterTape :=
  z.leftRev.reverse ++ z.focus :: z.right

/-- Place a finite parser zipper at a chosen left endpoint and fill every
other integer tape position with the physical hash sentinel. -/
def anchoredZipperTape (origin : Int)
    (z : MStarParserExecution.Zipper OuterTape) (i : Int) : OuterTape :=
  if origin ≤ i then
    (anchoredZipperCells z).getD (Int.toNat (i - origin)) .hash
  else .hash

/-- The actual outer configuration represented by a running parser zipper.
The finite support's left endpoint, rather than the moving head, is the
stable spatial origin. -/
def anchoredParserConfig (p : MStarParserMicrocode.ParserState) (origin : Int)
    (z : MStarParserExecution.Zipper OuterTape) : OuterConfig :=
  { state := .parser (.inl p)
    head := origin + z.leftRev.length
    tape := anchoredZipperTape origin z }

/-- The concrete side realization: running parser states use their literal
parser control, while `copyReady` denotes the same pre-entry `copyStart`
configuration.  Reject/stuck zipper outcomes intentionally have no live
outer realization. -/
def sideParserRealize (_x : ConcretePakSide.Word)
    (r : MStarParserExecution.Result MStarULogAssembly.CoreTape)
    (c : OuterConfig) : Prop :=
  match r with
  | .running p z => ∃ origin, c = anchoredParserConfig p origin z
  | .copyReady z => ∃ origin,
      c = anchoredParserConfig MStarParserMicrocode.copyStart origin z
  | .rejected => False
  | .stuck => False

theorem sideParserRealize_running (x : ConcretePakSide.Word)
    (p : MStarParserMicrocode.ParserState) (origin : Int)
    (z : MStarParserExecution.Zipper OuterTape) :
    sideParserRealize x (.running p z) (anchoredParserConfig p origin z) :=
  ⟨origin, rfl⟩

theorem sideParserRealize_copyReady (x : ConcretePakSide.Word)
    (origin : Int) (z : MStarParserExecution.Zipper OuterTape) :
    sideParserRealize x (.copyReady z)
      (anchoredParserConfig MStarParserMicrocode.copyStart origin z) :=
  ⟨origin, rfl⟩

theorem anchoredZipperTape_hash_left (origin : Int)
    (z : MStarParserExecution.Zipper OuterTape) {i : Int}
    (hi : i < origin) : anchoredZipperTape origin z i = .hash := by
  simp [anchoredZipperTape, not_le_of_gt hi]

theorem anchoredZipperTape_hash_right (origin : Int)
    (z : MStarParserExecution.Zipper OuterTape) {i : Int}
    (hi : origin + (anchoredZipperCells z).length ≤ i) :
    anchoredZipperTape origin z i = .hash := by
  rw [anchoredZipperTape, if_pos (by omega)]
  apply List.getD_eq_default
  have hnonneg : 0 ≤ i - origin := by omega
  exact Int.ofNat_le.mp (by rw [Int.toNat_of_nonneg hnonneg]; omega)

/-- When an anchored zipper contains exactly the scanner's parser/copier row,
its ambient integer tape is definitionally the scanner's side input tape. -/
theorem anchoredZipperTape_eq_sideInputTape_of_cells
    (x : ConcretePakSide.Word) (z : MStarParserExecution.Zipper OuterTape)
    (hcells : anchoredZipperCells z =
      PakSideScanner.parserCellsWithCopierReserve x) :
    anchoredZipperTape 1 z = PakSideScannerRow.sideInputTape x := by
  funext i
  unfold anchoredZipperTape PakSideScannerRow.sideInputTape
  by_cases hi : (1 : Int) ≤ i
  · rw [if_pos hi, if_pos hi, hcells]
  · rw [if_neg hi, if_neg hi]

/-- Every occupied finite zipper cell is read back at its literal offset from
the fixed left endpoint. -/
theorem anchoredZipperTape_at_offset (origin : Int)
    (z : MStarParserExecution.Zipper OuterTape) (k : ℕ) :
    anchoredZipperTape origin z (origin + k) =
      (anchoredZipperCells z).getD k .hash := by
  rw [anchoredZipperTape, if_pos (by omega)]
  have hnonneg : 0 ≤ origin + k - origin := by omega
  have hidx : (origin + (k : Int) - origin).toNat = k := by
    have hcalc : origin + (k : Int) - origin = (k : Int) := by ring
    rw [hcalc]
    simp
  exact congrArg (fun n : ℕ => (anchoredZipperCells z).getD n .hash) hidx

/-- In particular, the ambient head reads precisely the zipper focus. -/
theorem anchoredZipperTape_at_head (origin : Int)
    (z : MStarParserExecution.Zipper OuterTape) :
    anchoredZipperTape origin z (origin + z.leftRev.length) = z.focus := by
  rw [anchoredZipperTape_at_offset]
  unfold anchoredZipperCells
  rw [List.getD_append_right]
  · simp
  · simp

/-- A successful finite zipper action changes exactly the focused physical
cell of the anchored segment; moving merely changes which segment position is
called the focus. -/
theorem anchoredZipperCells_applyAction {State : Type*}
    (z z' : MStarParserExecution.Zipper OuterTape)
    (act : FiniteOneTapeProgram.Action State OuterTape)
    (happly : MStarParserExecution.applyAction z act = some z') :
    anchoredZipperCells z' =
      (anchoredZipperCells z).set z.leftRev.length act.write := by
  rcases z with ⟨left, focus, right⟩
  rcases act with ⟨write, target, move⟩
  cases move with
  | stay =>
      simp only [MStarParserExecution.applyAction] at happly
      have hz' := (Option.some.inj happly).symm
      subst z'
      simp [anchoredZipperCells]
  | right =>
      cases right with
      | nil => simp [MStarParserExecution.applyAction] at happly
      | cons next rest =>
          simp only [MStarParserExecution.applyAction] at happly
          have hz' := (Option.some.inj happly).symm
          subst z'
          simp [anchoredZipperCells, List.append_assoc]
  | left =>
      cases left with
      | nil => simp [MStarParserExecution.applyAction] at happly
      | cons prev rest =>
          simp only [MStarParserExecution.applyAction] at happly
          have hz' := (Option.some.inj happly).symm
          subst z'
          simp [anchoredZipperCells, List.append_assoc]

/-- The physical head coordinate follows the same move as a successful
zipper action when the left support endpoint is held fixed. -/
theorem anchoredZipperHead_applyAction {State : Type*}
    (origin : Int) (z z' : MStarParserExecution.Zipper OuterTape)
    (act : FiniteOneTapeProgram.Action State OuterTape)
    (happly : MStarParserExecution.applyAction z act = some z') :
    origin + z'.leftRev.length =
      moveHead act.move (origin + z.leftRev.length) := by
  rcases z with ⟨left, focus, right⟩
  rcases act with ⟨write, target, move⟩
  cases move with
  | stay =>
      simp only [MStarParserExecution.applyAction] at happly
      have hz' := (Option.some.inj happly).symm
      subst z'
      simp [FiniteOneTapeSemantics.moveHead]
  | right =>
      cases right with
      | nil => simp [MStarParserExecution.applyAction] at happly
      | cons next rest =>
          simp only [MStarParserExecution.applyAction] at happly
          have hz' := (Option.some.inj happly).symm
          subst z'
          simp [FiniteOneTapeSemantics.moveHead]
          ring
  | left =>
      cases left with
      | nil => simp [MStarParserExecution.applyAction] at happly
      | cons prev rest =>
          simp only [MStarParserExecution.applyAction] at happly
          have hz' := (Option.some.inj happly).symm
          subst z'
          simp [FiniteOneTapeSemantics.moveHead]
          ring

/-- Pointwise form of the physical write correspondence.  Together with the
fixed-origin exterior lemmas it is the local form needed to identify the
updated ambient tape with the post-action zipper. -/
theorem anchoredZipperTape_applyAction_at_offset {State : Type*}
    (origin : Int) (z z' : MStarParserExecution.Zipper OuterTape)
    (act : FiniteOneTapeProgram.Action State OuterTape)
    (happly : MStarParserExecution.applyAction z act = some z') (k : ℕ) :
    anchoredZipperTape origin z' (origin + k) =
      ((anchoredZipperCells z).set z.leftRev.length act.write).getD k .hash := by
  rw [anchoredZipperTape_at_offset,
    anchoredZipperCells_applyAction z z' act happly]

/-- At the old physical head, the pointwise post-action tape contains the
action's write letter. -/
theorem anchoredZipperTape_applyAction_at_oldHead {State : Type*}
    (origin : Int) (z z' : MStarParserExecution.Zipper OuterTape)
    (act : FiniteOneTapeProgram.Action State OuterTape)
    (happly : MStarParserExecution.applyAction z act = some z') :
    anchoredZipperTape origin z' (origin + z.leftRev.length) = act.write := by
  rw [anchoredZipperTape_applyAction_at_offset origin z z' act happly]
  rcases z with ⟨left, focus, right⟩
  simp [anchoredZipperCells]

/-- `getD` of an in-range finite-list update is exactly function update of
the corresponding total `getD` readout. -/
theorem list_getD_set_eq_function_update {A : Type*} (default : A)
    (xs : List A) (k : ℕ) (write : A) (hk : k < xs.length) (n : ℕ) :
    (xs.set k write).getD n default =
      Function.update (fun j : ℕ => xs.getD j default) k write n := by
  induction xs generalizing k n with
  | nil => simp at hk
  | cons x xs ih =>
      cases k with
      | zero =>
          cases n <;> simp [Function.update]
      | succ k =>
          have hk' : k < xs.length := by simpa using hk
          cases n with
          | zero => simp [Function.update]
          | succ n =>
              simpa [Function.update] using ih k hk' n

/-- A successful zipper action has exactly the same total ambient tape effect
as writing its action letter at the old physical head. -/
theorem anchoredZipperTape_applyAction {State : Type*}
    (origin : Int) (z z' : MStarParserExecution.Zipper OuterTape)
    (act : FiniteOneTapeProgram.Action State OuterTape)
    (happly : MStarParserExecution.applyAction z act = some z') :
    anchoredZipperTape origin z' =
      Function.update (anchoredZipperTape origin z)
        (origin + z.leftRev.length) act.write := by
  funext i
  by_cases hlow : i < origin
  · have hhead : origin + z.leftRev.length ≠ i := by omega
    have hhead' : i ≠ origin + z.leftRev.length := Ne.symm hhead
    simp [anchoredZipperTape, not_le_of_gt hlow, Function.update, hhead, hhead']
  · have hge : origin ≤ i := le_of_not_gt hlow
    let n : ℕ := (i - origin).toNat
    have hnonneg : 0 ≤ i - origin := by omega
    have hpos : origin + n = i := by
      dsimp [n]
      rw [Int.toNat_of_nonneg hnonneg]
      omega
    rw [← hpos,
      anchoredZipperTape_applyAction_at_offset origin z z' act happly]
    have hk : z.leftRev.length < (anchoredZipperCells z).length := by
      unfold anchoredZipperCells
      simp
    rw [list_getD_set_eq_function_update .hash
      (anchoredZipperCells z) z.leftRev.length act.write hk]
    by_cases hkn : n = z.leftRev.length
    · have hcoordEq : origin + z.leftRev.length = origin + n := by omega
      simp [Function.update, hkn.symm, hcoordEq]
    · have hcoord : origin + z.leftRev.length ≠ origin + n := by
        intro h
        apply hkn
        omega
      simpa [Function.update, hcoord, hkn] using
        (anchoredZipperTape_at_offset origin z n).symm

/-- The parser executor's abstract terminal is genuinely a zero-arrow outer
transition: both sides denote the same pre-entry `copyStart` configuration.
The following `sideCopyEntryArrow` supplies the separate physical copier
entry. -/
theorem sideParserRealize_copyStart_refl (x : ConcretePakSide.Word)
    (z : MStarParserExecution.Zipper OuterTape) (c : OuterConfig)
    (hrealize : sideParserRealize x
      (.running MStarParserMicrocode.copyStart z) c) :
    ∃ d, sideParserRealize x
      (MStarParserExecution.oneStep MStarConcreteAlphabet.zero
        MStarConcreteAlphabet.one MStarConcreteAlphabet.work
        (.running MStarParserMicrocode.copyStart z)) d ∧
      OuterReaches c d := by
  rcases hrealize with ⟨origin, rfl⟩
  refine ⟨anchoredParserConfig MStarParserMicrocode.copyStart origin z, ?_,
    outerReaches_refl _⟩
  simpa [MStarParserExecution.oneStep] using
    sideParserRealize_copyReady x origin z

/-- Results on the canonical side-parser path carry a genuine eventual
`copyReady` witness.  Phase-specific non-core/hash rejection lemmas can use
this invariant to rule out attempted moves into a hash sentinel. -/
def SideParserCanonical (x : ConcretePakSide.Word)
    (r : MStarParserExecution.Result MStarULogAssembly.CoreTape) : Prop :=
  MStarParserExecution.Reaches MStarConcreteAlphabet.zero
    MStarConcreteAlphabet.one MStarConcreteAlphabet.work
    (MStarParserExecution.extendResultRight
      (MStarParserExecution.initial MStarConcreteAlphabet.zero
        MStarConcreteAlphabet.one MStarConcreteAlphabet.work
        (ConcretePakSide.encodedWord x))
      (MStarCopierExecution.parserCopierReserve x ++
        PakSideScanner.sideCopierHashTail x)) r

def sideParserInitialResult (x : ConcretePakSide.Word) :
    MStarParserExecution.Result MStarULogAssembly.CoreTape :=
  MStarParserExecution.extendResultRight
    (MStarParserExecution.initial MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work
      (ConcretePakSide.encodedWord x))
    (MStarCopierExecution.parserCopierReserve x ++
      PakSideScanner.sideCopierHashTail x)

theorem sideParserInitialResult_shape (x : ConcretePakSide.Word) :
    ∃ z : MStarParserExecution.Zipper OuterTape,
      sideParserInitialResult x =
        .running (MStarParserMicrocode.fixed ⟨0, by decide⟩) z ∧
      z.leftRev = [] ∧
      anchoredZipperCells z = PakSideScanner.parserCellsWithCopierReserve x := by
  let tail := MStarCopierExecution.parserCopierReserve x ++
    PakSideScanner.sideCopierHashTail x
  cases hcells : MStarParserExecution.inputCells MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work
      (ConcretePakSide.encodedWord x) with
  | nil =>
      exact (MStarParserExecution.inputCells_ne_nil
        MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
        MStarConcreteAlphabet.work (ConcretePakSide.encodedWord x) hcells).elim
  | cons focus right =>
      let z : MStarParserExecution.Zipper OuterTape := ⟨[], focus, right ++ tail⟩
      refine ⟨z, ?_, by simp [z], ?_⟩
      · simp [sideParserInitialResult, MStarParserExecution.initial, hcells,
          MStarParserExecution.extendResultRight, MStarParserExecution.extendRight,
          z, tail]
      · unfold anchoredZipperCells z
        change (focus :: right) ++ tail =
          PakSideScanner.parserCellsWithCopierReserve x
        rw [← hcells]
        simp [PakSideScanner.parserCellsWithCopierReserve,
          PakEncodedStart.parserCells, tail, List.append_assoc]

theorem sideParserCanonical_canAccept (x : ConcretePakSide.Word)
    {r : MStarParserExecution.Result MStarULogAssembly.CoreTape}
    (hr : SideParserCanonical x r) :
    MStarParserSoundness.CanAcceptResult r := by
  apply MStarParserSoundness.canAcceptResult_reaches_forward hr
  apply MStarParserSoundness.canAcceptResult_of_reaches
    (PakSideScanner.parser_reaches_sideCopierReserve x)
  exact MStarParserSoundness.canAcceptResult_copyReady _

/-- The concrete domain for parser-to-outer simulation: an anchored physical
configuration together with evidence that this zipper result lies on the
canonical successful side-parser path. -/
def CanonicalSideParserRealize (x : ConcretePakSide.Word)
    (r : MStarParserExecution.Result MStarULogAssembly.CoreTape)
    (c : OuterConfig) : Prop :=
  SideParserCanonical x r ∧ sideParserRealize x r c

/-- The certified side start row is the anchored initial parser zipper at
origin one.  This lives after `CanonicalSideParserRealize` so the invariant
is available when elaborating the theorem. -/
theorem sideParserCanonicalRealize_initial (x : ConcretePakSide.Word) :
    CanonicalSideParserRealize x (sideParserInitialResult x)
      (PakSideScannerRow.sideEncodedParserConfig x) := by
  rcases sideParserInitialResult_shape x with ⟨z, hz, hzleft, hcells⟩
  constructor
  · unfold SideParserCanonical
    exact MStarParserExecution.reaches_refl MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work _
  · rw [hz]
    refine ⟨1, ?_⟩
    change
      { state := .parser MStarULogAssembly.data.parserStart
        head := 1
        tape := PakSideScannerRow.sideInputTape x } =
      anchoredParserConfig (MStarParserMicrocode.fixed ⟨0, by decide⟩) 1 z
    simp only [anchoredParserConfig]
    rw [hzleft]
    congr
    exact (anchoredZipperTape_eq_sideInputTape_of_cells x z hcells).symm

/-- Canonical parser-path membership is closed under one executable parser
step.  This prevents later phase proofs from silently reasoning about an
arbitrary, possibly hash-entering zipper state. -/
theorem sideParserCanonical_oneStep (x : ConcretePakSide.Word)
    (r : MStarParserExecution.Result MStarULogAssembly.CoreTape)
    (hr : SideParserCanonical x r) :
    SideParserCanonical x
      (MStarParserExecution.oneStep MStarConcreteAlphabet.zero
        MStarConcreteAlphabet.one MStarConcreteAlphabet.work r) :=
  MStarParserExecution.reaches_trans MStarConcreteAlphabet.zero
    MStarConcreteAlphabet.one MStarConcreteAlphabet.work hr
    (MStarParserExecution.reaches_of_oneStep MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work rfl)

/-- Canonical side-parser states cannot be a rejected outcome. -/
theorem sideParserCanonical_ne_rejected (x : ConcretePakSide.Word)
    {r : MStarParserExecution.Result MStarULogAssembly.CoreTape}
    (hr : SideParserCanonical x r) : r ≠ .rejected := by
  intro hreject
  subst r
  exact MStarParserSoundness.not_canAcceptResult_rejected
    (sideParserCanonical_canAccept x hr)

/-- Nor can a canonical side-parser state be stuck. -/
theorem sideParserCanonical_ne_stuck (x : ConcretePakSide.Word)
    {r : MStarParserExecution.Result MStarULogAssembly.CoreTape}
    (hr : SideParserCanonical x r) : r ≠ .stuck := by
  intro hstuck
  subst r
  exact MStarParserSoundness.not_canAcceptResult_stuck
    (sideParserCanonical_canAccept x hr)

/-- Canonical fixed-counter states are positioned on a zero with an actual
right successor, so their right-moving parser action cannot enter hash. -/
theorem sideParserCanonical_fixed_zero_and_right
    (x : ConcretePakSide.Word) (k : Fin 73) (hk : k.1 < 72)
    (z : MStarParserExecution.Zipper OuterTape)
    (hr : SideParserCanonical x (.running (MStarParserMicrocode.fixed k) z)) :
    z.focus = .core MStarConcreteAlphabet.zero ∧ z.right ≠ [] :=
  MStarParserSoundness.fixed_canAccept_forces_zero_and_right k hk z
    (sideParserCanonical_canAccept x hr)

/-- Canonical crossing-counter states are positioned on a zero with an
actual left successor, excluding a move into the left hash exterior. -/
theorem sideParserCanonical_cross_zero_and_left
    (x : ConcretePakSide.Word) (k : Fin 73) (hk : k.1 < 72)
    (z : MStarParserExecution.Zipper OuterTape)
    (hr : SideParserCanonical x (.running (MStarParserMicrocode.cross k) z)) :
    z.focus = .core MStarConcreteAlphabet.zero ∧ z.leftRev ≠ [] :=
  MStarParserSoundness.cross_canAccept_forces_zero_and_left k hk z
    (sideParserCanonical_canAccept x hr)

/-- The scanning-pad phase of a canonical side execution likewise always
reads a core letter (zero while scanning, or the unique one separator). -/
theorem sideParserCanonical_scanPad_core
    (x : ConcretePakSide.Word) (z : MStarParserExecution.Zipper OuterTape)
    (hr : SideParserCanonical x (.running MStarParserMicrocode.scanPad z)) :
    ∃ a : MStarULogAssembly.CoreTape, z.focus = .core a := by
  rcases MStarParserSoundness.scanPad_canAccept_split z.leftRev z.focus z.right
      (sideParserCanonical_canAccept x hr) with ⟨n, y, ys, hshape, _⟩
  cases n with
  | zero =>
      exact ⟨MStarConcreteAlphabet.one,
        by simpa using congrArg List.head? hshape⟩
  | succ n =>
      exact ⟨MStarConcreteAlphabet.zero, by
        simpa [List.replicate_succ] using congrArg List.head? hshape⟩

/-- The length-scanning phase also cannot read a non-core ambient letter on
the canonical accepting path: its next parser step would reject. -/
theorem sideParserCanonical_scanLen_core
    (x : ConcretePakSide.Word) (z : MStarParserExecution.Zipper OuterTape)
    (hr : SideParserCanonical x (.running MStarParserMicrocode.scanLen z)) :
    ∃ a : MStarULogAssembly.CoreTape, z.focus = .core a := by
  cases hfocus : z.focus with
  | core a => exact ⟨a, rfl⟩
  | hash | markL | markR | scratch =>
      have hnext := (MStarParserSoundness.canAcceptResult_oneStep_iff
        (.running MStarParserMicrocode.scanLen z)).2
          (sideParserCanonical_canAccept x hr)
      have hreject := MStarParserSoundness.oneStep_scanLen_noncore
        z.leftRev z.right z.focus (by simp [hfocus])
      rw [hreject] at hnext
      exact (MStarParserSoundness.not_canAcceptResult_rejected hnext).elim

/-- Hence an accepting canonical parser state other than the abstract
`copyStart` terminal can never have hash at its focus.  The terminal counter
states first enter their named scanning phase, so they are handled by the
next-phase rejection fact rather than by the incorrect blanket claim that
every nonterminal state rejects hash in one step. -/
private theorem parserStep_control_hash_rejected_all :
    ∀ q : Fin 18, q ≠ (⟨5, by decide⟩ : Fin 18) →
      q ≠ (⟨17, by decide⟩ : Fin 18) →
      MStarParserMicrocode.step (UState := Unit)
        MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
        MStarConcreteAlphabet.work (MStarParserMicrocode.control q) .hash =
          some (MStarParserMicrocode.reject .hash) := by
  native_decide

theorem sideParserCanonical_noncopy_focus_ne_hash
    (x : ConcretePakSide.Word) (p : MStarParserMicrocode.ParserState)
    (z : MStarParserExecution.Zipper OuterTape)
    (hp : p ≠ MStarParserMicrocode.copyStart)
    (hr : SideParserCanonical x (.running p z)) : z.focus ≠ .hash := by
  intro hhash
  cases p with
  | inl counters =>
      cases counters with
      | inl k =>
          by_cases hk : k.1 < 72
          · have hzero := sideParserCanonical_fixed_zero_and_right x k hk z hr
            exact (by simpa [hhash] using hzero.1)
          · have hkval : k.1 = 72 := by omega
            have hk72 : k = (⟨72, by decide⟩ : Fin 73) := Fin.ext hkval
            subst k
            have hnext := (MStarParserSoundness.canAcceptResult_oneStep_iff
              (.running (MStarParserMicrocode.fixed ⟨72, by decide⟩) z)).2
                (sideParserCanonical_canAccept x hr)
            rw [show z = ⟨z.leftRev, .hash, z.right⟩ by
              apply MStarParserExecution.Zipper.ext <;> simp [hhash],
              MStarConcreteAlphabet.oneStep_fixed_72] at hnext
            have hafter := (MStarParserSoundness.canAcceptResult_oneStep_iff
              (.running MStarParserMicrocode.scanPad
                ⟨z.leftRev, .hash, z.right⟩)).2 hnext
            rw [MStarParserSoundness.oneStep_scanPad_noncore _ _ .hash
              (by simp)] at hafter
            exact MStarParserSoundness.not_canAcceptResult_rejected hafter
      | inr k =>
          by_cases hk : k.1 < 72
          · have hzero := sideParserCanonical_cross_zero_and_left x k hk z hr
            exact (by simpa [hhash] using hzero.1)
          · have hkval : k.1 = 72 := by omega
            have hk72 : k = (⟨72, by decide⟩ : Fin 73) := Fin.ext hkval
            subst k
            have hnext := (MStarParserSoundness.canAcceptResult_oneStep_iff
              (.running (MStarParserMicrocode.cross ⟨72, by decide⟩) z)).2
                (sideParserCanonical_canAccept x hr)
            rw [show z = ⟨z.leftRev, .hash, z.right⟩ by
              apply MStarParserExecution.Zipper.ext <;> simp [hhash]] at hnext
            have hcross72 : MStarParserExecution.oneStep
                MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
                MStarConcreteAlphabet.work
                (.running (MStarParserMicrocode.cross ⟨72, by decide⟩)
                  ⟨z.leftRev, .hash, z.right⟩) =
                .running MStarParserMicrocode.returnSepPad
                  ⟨z.leftRev, .hash, z.right⟩ := by
              rfl
            rw [hcross72] at hnext
            have hreject : MStarParserExecution.oneStep
                MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
                MStarConcreteAlphabet.work
                (.running MStarParserMicrocode.returnSepPad
                  ⟨z.leftRev, .hash, z.right⟩) = .rejected := by
              rfl
            have hafter := (MStarParserSoundness.canAcceptResult_oneStep_iff
              (.running MStarParserMicrocode.returnSepPad
                ⟨z.leftRev, .hash, z.right⟩)).2 hnext
            rw [hreject] at hafter
            exact MStarParserSoundness.not_canAcceptResult_rejected hafter
  | inr phase =>
      have hnext := (MStarParserSoundness.canAcceptResult_oneStep_iff
        (.running (MStarParserMicrocode.control phase) z)).2
          (sideParserCanonical_canAccept x hr)
      rw [show z = ⟨z.leftRev, .hash, z.right⟩ by
        apply MStarParserExecution.Zipper.ext <;> simp [hhash]] at hnext
      have hphase : phase ≠ (⟨17, by decide⟩ : Fin 18) := by
        intro h17
        apply hp
        simpa [MStarParserMicrocode.copyStart,
          MStarParserMicrocode.control, h17]
      by_cases h5 : phase = (⟨5, by decide⟩ : Fin 18)
      · subst phase
        change MStarParserSoundness.CanAcceptResult
          (.running MStarParserMicrocode.scanLen
            ⟨z.leftRev, .hash, z.right⟩) at hnext
        have hafter := (MStarParserSoundness.canAcceptResult_oneStep_iff
          (.running MStarParserMicrocode.scanLen
            ⟨z.leftRev, .hash, z.right⟩)).2 hnext
        rw [MStarParserSoundness.oneStep_scanLen_noncore _ _ .hash
          (by simp)] at hafter
        exact MStarParserSoundness.not_canAcceptResult_rejected hafter
      · have hstep : MStarParserExecution.oneStep
            MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
            MStarConcreteAlphabet.work
            (.running (MStarParserMicrocode.control phase)
              ⟨z.leftRev, .hash, z.right⟩) = .rejected := by
            unfold MStarParserExecution.oneStep
            change (if MStarParserMicrocode.control phase =
                MStarParserMicrocode.copyStart then _ else _) = _
            rw [if_neg (by
              intro h
              apply hphase
              simpa [MStarParserMicrocode.control,
                MStarParserMicrocode.copyStart] using h)]
            rw [parserStep_control_hash_rejected_all phase h5 hphase]
            rfl
        rw [hstep] at hnext
        exact MStarParserSoundness.not_canAcceptResult_rejected hnext

/-- Reinterpret the finite parser executor's `Unit` continuation state in the
actual outer program.  Parser microcode never normally emits `.sim`, but the
map is total so action transport does not rely on that implementation detail. -/
def liftUnitParserState (uStart : MStarULogAssembly.UniversalState) :
    MStarOuterProgram.State MStarParserMicrocode.ParserState Unit →
      MStarCopierMicrocode.CopierOuterState MStarULogAssembly.UniversalState
  | .start => .start
  | .accept => .accept
  | .reject => .reject
  | .parser p => .parser (.inl p)
  | .sim () => .sim uStart

/-- Total action map from the `Unit` parser executor into the concrete ULog
parser/copier machine.  In particular, `.sim ()` is sent to the configured
universal start state rather than being coerced across incompatible types. -/
def liftUnitParserAction (uStart : MStarULogAssembly.UniversalState)
    (a : FiniteOneTapeProgram.Action
      (MStarOuterProgram.State MStarParserMicrocode.ParserState Unit) OuterTape) :
    OuterAction :=
  { write := a.write, target := liftUnitParserState uStart a.target, move := a.move }

/-- Zipper execution observes only a parser action's write and move fields;
the state-target reinterpretation is therefore operationally inert here. -/
theorem applyAction_liftUnitParserAction
    (uStart : MStarULogAssembly.UniversalState)
    (z : MStarParserExecution.Zipper OuterTape)
    (a : FiniteOneTapeProgram.Action
      (MStarOuterProgram.State MStarParserMicrocode.ParserState Unit) OuterTape) :
    MStarParserExecution.applyAction z (liftUnitParserAction uStart a) =
      MStarParserExecution.applyAction z a := by
  rcases a with ⟨write, target, move⟩
  cases move <;> rfl

def changeUnitParserAction
    (uStart : MStarULogAssembly.UniversalState)
    (a : FiniteOneTapeProgram.Action
      (MStarOuterProgram.State MStarParserMicrocode.ParserState Unit) OuterTape) :
    FiniteOneTapeProgram.Action
      (MStarOuterProgram.State MStarParserMicrocode.ParserState
        MStarULogAssembly.UniversalState) OuterTape :=
  { write := a.write
    target := match a.target with
      | .start => .start
      | .accept => .accept
      | .reject => .reject
      | .parser q => .parser q
      | .sim () => .sim uStart
    move := a.move }

theorem parserStep_changeUState_all :
    ∀ p : MStarParserMicrocode.ParserState, ∀ x : OuterTape,
    MStarParserMicrocode.step (UState := MStarULogAssembly.UniversalState)
      MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
      MStarConcreteAlphabet.work p x =
      (MStarParserMicrocode.step (UState := Unit)
        MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
        MStarConcreteAlphabet.work p x).map
          (changeUnitParserAction MStarULogAssembly.data.uStart) := by
  native_decide

theorem parserStep_changeUState
    (p : MStarParserMicrocode.ParserState) (x : OuterTape) :
    MStarParserMicrocode.step (UState := MStarULogAssembly.UniversalState)
      MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
      MStarConcreteAlphabet.work p x =
      (MStarParserMicrocode.step (UState := Unit)
        MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
        MStarConcreteAlphabet.work p x).map
          (changeUnitParserAction MStarULogAssembly.data.uStart) :=
  parserStep_changeUState_all p x

/- Transport a nonterminal parser-table action from the `Unit` zipper
executor into the actual ULog-instantiated combined parser/copier table. -/
theorem parserUnitAction_to_outerAction
    (p : MStarParserMicrocode.ParserState) (x : OuterTape)
    (a : FiniteOneTapeProgram.Action
      (MStarOuterProgram.State MStarParserMicrocode.ParserState Unit) OuterTape)
    (hp : p ≠ MStarParserMicrocode.copyStart)
    (hstep : MStarParserMicrocode.step (UState := Unit)
      MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
      MStarConcreteAlphabet.work p x = some a) :
    MStarCopierMicrocode.step MStarULogAssembly.data.uStart (.inl p) x =
      some (liftUnitParserAction MStarULogAssembly.data.uStart a) := by
  simp only [MStarCopierMicrocode.step, hp, ↓reduceIte]
  rw [parserStep_changeUState p x, hstep]
  cases htarget : a.target <;>
    simp [changeUnitParserAction, liftUnitParserAction, liftUnitParserState,
      MStarCopierMicrocode.liftAction, MStarCopierMicrocode.liftState, htarget]

/-- The parser table reaches its abstract `copyStart` terminal only by a
stay action which writes the literal work letter.  This finite-table fact
closes the one case not covered by the noncopy hash-focus invariant. -/
theorem parserUnitAction_target_copyStart_stays_work :
    ∀ (p : MStarParserMicrocode.ParserState) (x : OuterTape)
      (a : FiniteOneTapeProgram.Action
        (MStarOuterProgram.State MStarParserMicrocode.ParserState Unit) OuterTape),
      MStarParserMicrocode.step (UState := Unit)
        MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
        MStarConcreteAlphabet.work p x = some a →
      a.target = .parser MStarParserMicrocode.copyStart →
        a.move = .stay ∧ a.write = .core MStarConcreteAlphabet.work := by
  native_decide
/-- An occupied slot-zero rule is a literal labelled arrow of the fixed outer
program.  The source state and read letter are retained in the subtype value,
not recovered abstractly after the fact. -/
def slotZeroArrow (q : OuterState) (x : OuterTape) (act : OuterAction)
    (hrule : MStarULogAssembly.program.rule q x 0 = some act) : OuterArrow :=
  ⟨((q, x), (0 : Fin 2)), by simp [hrule]⟩

theorem actionOf_slotZeroArrow (q : OuterState) (x : OuterTape)
    (act : OuterAction)
    (hrule : MStarULogAssembly.program.rule q x 0 = some act) :
    actionOf MStarULogAssembly.program (slotZeroArrow q x act hrule) = act := by
  unfold actionOf
  split
  · rename_i found hfound
    exact Option.some.inj (hfound.symm.trans hrule)
  · rename_i hnone
    exact ((slotZeroArrow q x act hrule).2 hnone).elim

@[simp] theorem slotZeroArrow_source (q : OuterState) (x : OuterTape)
    (act : OuterAction)
    (hrule : MStarULogAssembly.program.rule q x 0 = some act) :
    (slotZeroArrow q x act hrule).1.1.1 = q := rfl

@[simp] theorem slotZeroArrow_read (q : OuterState) (x : OuterTape)
    (act : OuterAction)
    (hrule : MStarULogAssembly.program.rule q x 0 = some act) :
    (slotZeroArrow q x act hrule).1.1.2 = x := rfl

/-- Exact one-step lifting for a concrete occupied slot.  In particular the
result is an equality for `FiniteOneTapeSemantics.step`, not merely an
unlabelled or zipper-level `Reaches`. -/
theorem step_slotZeroArrow (c : OuterConfig) (q : OuterState) (x : OuterTape)
    (act : OuterAction)
    (hrule : MStarULogAssembly.program.rule q x 0 = some act)
    (hstate : c.state = q) (hread : c.tape c.head = x)
    (hmovable : MStarOuterProgram.movable
      ((writtenTape c act.write) (moveHead act.move c.head)) = true) :
    FiniteOneTapeSemantics.step MStarULogAssembly.program
        MStarOuterProgram.movable c (slotZeroArrow q x act hrule) =
      some (afterAction c act) := by
  simp [FiniteOneTapeSemantics.step, FiniteOneTapeProgram.transition,
    actionOf_slotZeroArrow, hstate, hread, hmovable, afterAction]

theorem outerReaches_slotZeroArrow (c : OuterConfig) (q : OuterState)
    (x : OuterTape) (act : OuterAction)
    (hrule : MStarULogAssembly.program.rule q x 0 = some act)
    (hstate : c.state = q) (hread : c.tape c.head = x)
    (hmovable : MStarOuterProgram.movable
      ((writtenTape c act.write) (moveHead act.move c.head)) = true) :
    OuterReaches c (afterAction c act) := by
  refine ⟨[slotZeroArrow q x act hrule], ?_⟩
  simp only [run_cons]
  rw [step_slotZeroArrow c q x act hrule hstate hread hmovable]
  rfl

/-- The slot-zero realization is literally a singleton arrow list.  This
raw quantitative witness stays upstream of the later front-bounds module. -/
theorem outer_slotZeroArrow_length_at_most_one (c : OuterConfig) (q : OuterState)
    (x : OuterTape) (act : OuterAction)
    (hrule : MStarULogAssembly.program.rule q x 0 = some act)
    (hstate : c.state = q) (hread : c.tape c.head = x)
    (hmovable : MStarOuterProgram.movable
      ((writtenTape c act.write) (moveHead act.move c.head)) = true) :
    ∃ arrows : List OuterArrow, arrows.length ≤ 1 ∧
      FiniteOneTapeSemantics.run MStarULogAssembly.program
        MStarOuterProgram.movable arrows c = some (afterAction c act) := by
  refine ⟨[slotZeroArrow q x act hrule], by simp, ?_⟩
  simp only [run_cons]
  rw [step_slotZeroArrow c q x act hrule hstate hread hmovable]
  rfl

/-- The literal outer rule table agrees definitionally with the concrete
combined parser/copier microcode at its unique occupied slot. -/
theorem parserCopier_slotZero_rule (p : ParserControl) (x : OuterTape)
    (act : OuterAction)
    (hstep : MStarCopierMicrocode.step MStarULogAssembly.data.uStart p x =
      some act) :
    MStarULogAssembly.program.rule (.parser p) x 0 = some act := by
  simpa [MStarULogAssembly.program, MStarULogAssembly.data,
    MStarOuterProgram.program, MStarCopierMicrocode.attach] using hstep

/-- First parser/copier bridge: one concrete combined-microcode step becomes
one actual slot-zero arrow and one actual outer-program step.  This theorem
applies both to `.inl` parser controls and `.inr` copier controls. -/
theorem parserCopier_oneStep_outer (c : OuterConfig) (p : ParserControl)
    (x : OuterTape) (act : OuterAction)
    (hstep : MStarCopierMicrocode.step MStarULogAssembly.data.uStart p x =
      some act)
    (hstate : c.state = .parser p) (hread : c.tape c.head = x)
    (hmovable : MStarOuterProgram.movable
      ((writtenTape c act.write) (moveHead act.move c.head)) = true) :
    ∃ a : OuterArrow,
      a.1.2 = 0 ∧
      FiniteOneTapeSemantics.step MStarULogAssembly.program
        MStarOuterProgram.movable c a = some (afterAction c act) ∧
      OuterReaches c (afterAction c act) := by
  let hrule := parserCopier_slotZero_rule p x act hstep
  let a := slotZeroArrow (.parser p) x act hrule
  refine ⟨a, rfl, ?_, ?_⟩
  · exact step_slotZeroArrow c (.parser p) x act hrule hstate hread hmovable
  · exact outerReaches_slotZeroArrow c (.parser p) x act hrule
      hstate hread hmovable

private theorem anchoredZipper_movable_of_focus_ne_hash
    (origin : Int) (z : MStarParserExecution.Zipper OuterTape)
    (hfocus : z.focus ≠ .hash) :
    MStarOuterProgram.movable
      (anchoredZipperTape origin z (origin + z.leftRev.length)) = true := by
  rw [anchoredZipperTape_at_head]
  cases hz : z.focus with
  | core a => rfl
  | hash => exact (hfocus hz).elim
  | markL => rfl
  | markR => rfl
  | scratch i => rfl

private theorem anchoredZipper_movable_of_focus_work
    (origin : Int) (z : MStarParserExecution.Zipper OuterTape)
    (hfocus : z.focus = .core MStarConcreteAlphabet.work) :
    MStarOuterProgram.movable
      (anchoredZipperTape origin z (origin + z.leftRev.length)) = true := by
  rw [anchoredZipperTape_at_head, hfocus]
  rfl

/-- A nonterminal parser/copy table action has a concrete anchored ambient
successor whenever its finite zipper action succeeds and its new focus is
non-hash.  This is the local running branch used by the canonical phase
invariant; it does not assert safety for arbitrary zipper `Reaches`. -/
theorem sideParserRealize_outerRunningStep (x : ConcretePakSide.Word)
    (p p' : MStarParserMicrocode.ParserState) (origin : Int)
    (z z' : MStarParserExecution.Zipper OuterTape) (act : OuterAction)
    (hstep : MStarCopierMicrocode.step MStarULogAssembly.data.uStart
      (.inl p) z.focus = some act)
    (happly : MStarParserExecution.applyAction z act = some z')
    (htarget : act.target = .parser (.inl p'))
    (hmovable : MStarOuterProgram.movable
      (anchoredZipperTape origin z'
        (origin + z'.leftRev.length)) = true) :
    ∃ d, sideParserRealize x (.running p' z') d ∧
      OuterReaches (anchoredParserConfig p origin z) d := by
  let c := anchoredParserConfig p origin z
  let d := anchoredParserConfig p' origin z'
  have hafter : afterAction c act = d := by
    simp only [c, d, afterAction, anchoredParserConfig,
      FiniteOneTapeSemantics.writtenTape]
    rw [htarget, anchoredZipperHead_applyAction origin z z' act happly,
      anchoredZipperTape_applyAction origin z z' act happly]
  have htape : writtenTape c act.write = anchoredZipperTape origin z' := by
    simpa only [c, anchoredParserConfig, writtenTape] using
      (anchoredZipperTape_applyAction origin z z' act happly).symm
  have hmove : MStarOuterProgram.movable
      ((writtenTape c act.write) (moveHead act.move c.head)) = true := by
    change MStarOuterProgram.movable
      ((writtenTape c act.write)
        (moveHead act.move (origin + z.leftRev.length))) = true
    rw [htape, ← anchoredZipperHead_applyAction origin z z' act happly]
    exact hmovable
  refine ⟨d, sideParserRealize_running x p' origin z', ?_⟩
  rw [← hafter]
  exact outerReaches_slotZeroArrow c (.parser (.inl p)) z.focus act
    (parserCopier_slotZero_rule _ _ _ hstep)
    (by simp [c, anchoredParserConfig])
    (by simpa [c, anchoredParserConfig] using anchoredZipperTape_at_head origin z)
    hmove

/-- Quantitative form of the running parser atom: the physical realization
is exactly one occupied slot-zero arrow. -/
theorem sideParserRealize_outerRunningStep_atMostOne
    (x : ConcretePakSide.Word)
    (p p' : MStarParserMicrocode.ParserState) (origin : Int)
    (z z' : MStarParserExecution.Zipper OuterTape) (act : OuterAction)
    (hstep : MStarCopierMicrocode.step MStarULogAssembly.data.uStart
      (.inl p) z.focus = some act)
    (happly : MStarParserExecution.applyAction z act = some z')
    (htarget : act.target = .parser (.inl p'))
    (hmovable : MStarOuterProgram.movable
      (anchoredZipperTape origin z'
        (origin + z'.leftRev.length)) = true) :
    ∃ d, sideParserRealize x (.running p' z') d ∧
      ∃ arrows : List OuterArrow, arrows.length ≤ 1 ∧
        FiniteOneTapeSemantics.run MStarULogAssembly.program
          MStarOuterProgram.movable arrows (anchoredParserConfig p origin z) =
            some d := by
  let c := anchoredParserConfig p origin z
  let d := anchoredParserConfig p' origin z'
  have hafter : afterAction c act = d := by
    simp only [c, d, afterAction, anchoredParserConfig,
      FiniteOneTapeSemantics.writtenTape]
    rw [htarget, anchoredZipperHead_applyAction origin z z' act happly,
      anchoredZipperTape_applyAction origin z z' act happly]
  have htape : writtenTape c act.write = anchoredZipperTape origin z' := by
    simpa only [c, anchoredParserConfig, writtenTape] using
      (anchoredZipperTape_applyAction origin z z' act happly).symm
  have hmove : MStarOuterProgram.movable
      ((writtenTape c act.write) (moveHead act.move c.head)) = true := by
    change MStarOuterProgram.movable
      ((writtenTape c act.write)
        (moveHead act.move (origin + z.leftRev.length))) = true
    rw [htape, ← anchoredZipperHead_applyAction origin z z' act happly]
    exact hmovable
  refine ⟨d, sideParserRealize_running x p' origin z', ?_⟩
  rw [← hafter]
  exact outer_slotZeroArrow_length_at_most_one c (.parser (.inl p))
    z.focus act (parserCopier_slotZero_rule _ _ _ hstep)
    (by simp [c, anchoredParserConfig])
    (by simpa [c, anchoredParserConfig] using
      anchoredZipperTape_at_head origin z)
    hmove

def ParserOuterStepSimulationAtMostOne
    (zero one work : MStarULogAssembly.CoreTape)
    (realize : MStarParserExecution.Result MStarULogAssembly.CoreTape →
      OuterConfig → Prop) : Prop :=
  ∀ r s c, realize r c →
    MStarParserExecution.oneStep zero one work r = s →
      ∃ d, realize s d ∧
        ∃ arrows : List OuterArrow, arrows.length ≤ 1 ∧
          FiniteOneTapeSemantics.run MStarULogAssembly.program
            MStarOuterProgram.movable arrows c = some d

/-- The canonical side-parser zipper has a total concrete outer-step
realization.  The terminal `copyStart` is deliberately a zero-arrow parser
step; every other successful parser zipper action is transported through the
actual ULog-instantiated combined table. -/
theorem canonicalSideParser_outerStepSimulation_atMostOne
    (x : ConcretePakSide.Word) :
    ParserOuterStepSimulationAtMostOne MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work
      (CanonicalSideParserRealize x) := by
  intro r s c hrealize hrun
  rcases hrealize with ⟨hr, hside⟩
  cases r with
  | rejected =>
      exact (sideParserCanonical_ne_rejected x hr rfl).elim
  | stuck =>
      exact (sideParserCanonical_ne_stuck x hr rfl).elim
  | copyReady z =>
      simp only [MStarParserExecution.oneStep] at hrun
      subst s
      exact ⟨c, ⟨sideParserCanonical_oneStep x (.copyReady z) hr, hside⟩,
        ⟨[], by simp, rfl⟩⟩
  | running p z =>
      by_cases hp : p = MStarParserMicrocode.copyStart
      · subst p
        simp only [MStarParserExecution.oneStep, ↓reduceIte] at hrun
        subst s
        rcases hside with ⟨origin, rfl⟩
        refine ⟨anchoredParserConfig MStarParserMicrocode.copyStart origin z,
          ⟨?_, sideParserRealize_copyReady x origin z⟩,
          ⟨[], by simp, rfl⟩⟩
        simpa [MStarParserExecution.oneStep] using
          (sideParserCanonical_oneStep x
            (.running MStarParserMicrocode.copyStart z) hr)
      · cases htable : MStarParserMicrocode.step (UState := Unit)
          MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
          MStarConcreteAlphabet.work p z.focus with
        | none =>
            have hbad : SideParserCanonical x .stuck := by
              simpa [MStarParserExecution.oneStep, hp, htable] using
                (sideParserCanonical_oneStep x (.running p z) hr)
            exact (sideParserCanonical_ne_stuck x hbad rfl).elim
        | some a =>
            cases happly : MStarParserExecution.applyAction z a with
            | none =>
                have hbad : SideParserCanonical x .stuck := by
                  simpa [MStarParserExecution.oneStep, hp, htable, happly] using
                    (sideParserCanonical_oneStep x (.running p z) hr)
                exact (sideParserCanonical_ne_stuck x hbad rfl).elim
            | some z' =>
                rcases a with ⟨write, target, move⟩
                cases target with
                | start | accept | sim _ =>
                    have hbad : SideParserCanonical x .stuck := by
                      simpa [MStarParserExecution.oneStep, hp, htable, happly] using
                        (sideParserCanonical_oneStep x (.running p z) hr)
                    exact (sideParserCanonical_ne_stuck x hbad rfl).elim
                | reject =>
                    have hbad : SideParserCanonical x .rejected := by
                      simpa [MStarParserExecution.oneStep, hp, htable, happly] using
                        (sideParserCanonical_oneStep x (.running p z) hr)
                    exact (sideParserCanonical_ne_rejected x hbad rfl).elim
                | parser p' =>
                    have hs : s = .running p' z' := by
                      simpa [MStarParserExecution.oneStep, hp, htable, happly] using
                        hrun.symm
                    have hnext : SideParserCanonical x (.running p' z') := by
                      simpa [MStarParserExecution.oneStep, hp, htable, happly] using
                        (sideParserCanonical_oneStep x (.running p z) hr)
                    have houter := parserUnitAction_to_outerAction p z.focus
                      { write := write, target := .parser p', move := move } hp
                      htable
                    have happlyOuter : MStarParserExecution.applyAction z
                        (liftUnitParserAction MStarULogAssembly.data.uStart
                          { write := write, target := .parser p', move := move }) =
                        some z' := by
                      rw [applyAction_liftUnitParserAction]
                      exact happly
                    have houterTarget :
                        (liftUnitParserAction MStarULogAssembly.data.uStart
                          { write := write, target := .parser p', move := move }).target =
                          .parser (.inl p') := by
                      simp [liftUnitParserAction, liftUnitParserState]
                    rcases hside with ⟨origin, rfl⟩
                    by_cases hp' : p' = MStarParserMicrocode.copyStart
                    · subst p'
                      rcases parserUnitAction_target_copyStart_stays_work p z.focus
                          { write := write, target := .parser MStarParserMicrocode.copyStart,
                            move := move }
                          htable rfl with ⟨hstay, hwrite⟩
                      have hfocus : z'.focus = .core MStarConcreteAlphabet.work := by
                        change move = .stay at hstay
                        change write = .core MStarConcreteAlphabet.work at hwrite
                        subst move
                        subst write
                        have hsome : some { z with
                            focus := (.core MStarConcreteAlphabet.work : OuterTape) } =
                            some z' := by
                          simpa [MStarParserExecution.applyAction] using happly
                        exact (congrArg MStarParserExecution.Zipper.focus
                          (Option.some.inj hsome)).symm
                      have hmovable := anchoredZipper_movable_of_focus_work
                        origin z' hfocus
                      rcases sideParserRealize_outerRunningStep_atMostOne x p
                          MStarParserMicrocode.copyStart origin z z'
                          (liftUnitParserAction MStarULogAssembly.data.uStart
                            { write := write, target := .parser MStarParserMicrocode.copyStart,
                              move := move })
                          houter happlyOuter houterTarget hmovable with ⟨d, hd, hout⟩
                      refine ⟨d, ?_, hout⟩
                      rw [hs]
                      exact ⟨hnext, hd⟩
                    · have hfocus := sideParserCanonical_noncopy_focus_ne_hash x
                          p' z' hp' hnext
                      have hmovable := anchoredZipper_movable_of_focus_ne_hash
                        origin z' hfocus
                      rcases sideParserRealize_outerRunningStep_atMostOne x p p' origin z z'
                          (liftUnitParserAction MStarULogAssembly.data.uStart
                            { write := write, target := .parser p', move := move })
                          houter happlyOuter houterTarget hmovable with ⟨d, hd, hout⟩
                      refine ⟨d, ?_, hout⟩
                      rw [hs]
                      exact ⟨hnext, hd⟩

/-- Forgetting the singleton bound recovers the original qualitative
canonical step simulation. -/
theorem canonicalSideParser_outerStepSimulation (x : ConcretePakSide.Word) :
    ParserOuterStepSimulation MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work
      (CanonicalSideParserRealize x) := by
  intro r s c hrealize hrun
  rcases canonicalSideParser_outerStepSimulation_atMostOne x r s c hrealize
      hrun with ⟨d, hd, arrows, _, harrows⟩
  exact ⟨d, hd, ⟨arrows, harrows⟩⟩

/-- The certified finite side-parser trace now produces a literal list of
outer arrows with no ambient-realization parameter left to supply. -/
theorem sideParser_reaches_outerCopyReady_arrowList
    (x : ConcretePakSide.Word) :
    ∃ d arrows,
      CanonicalSideParserRealize x
        (.copyReady (MStarParserExecution.extendRight
          (MStarConcreteAlphabet.finalZipper x.reverse)
          (MStarCopierExecution.parserCopierReserve x ++
            PakSideScanner.sideCopierHashTail x))) d ∧
      FiniteOneTapeSemantics.run MStarULogAssembly.program
        MStarOuterProgram.movable arrows
        (PakSideScannerRow.sideEncodedParserConfig x) = some d := by
  apply parserReaches_outerArrowList MStarConcreteAlphabet.zero
    MStarConcreteAlphabet.one MStarConcreteAlphabet.work
    (CanonicalSideParserRealize x)
    (canonicalSideParser_outerStepSimulation x)
    (r := sideParserInitialResult x)
    (c := PakSideScannerRow.sideEncodedParserConfig x)
  · simpa [sideParserInitialResult] using
      (PakSideScanner.parser_reaches_sideCopierReserve x)
  · exact sideParserCanonicalRealize_initial x

/-- Updating an interior head cell cannot disturb either hash exterior of the
finite tableau window. -/
theorem afterAction_hash_outside (c : OuterConfig) (act : OuterAction)
    (origin : Int) (width : ℕ)
    (hheadLow : origin ≤ c.head)
    (hheadHigh : c.head < origin + width)
    (hhash : ∀ z : Int, z < origin ∨ origin + width ≤ z →
      c.tape z = .hash) :
    ∀ z : Int, z < origin ∨ origin + width ≤ z →
      (afterAction c act).tape z = .hash := by
  intro z hz
  have hne : z ≠ c.head := by
    intro heq
    subst z
    rcases hz with hz | hz <;> omega
  have hne' : c.head ≠ z := Ne.symm hne
  simp [afterAction, writtenTape, hne, hne', hhash z hz]

/-- One concrete parser/copier step together with the exact hash-window fact
needed when it is inserted into a `WindowedMStarStep` or a uniform run. -/
theorem parserCopier_oneStep_outer_hashWindow (c : OuterConfig)
    (p : ParserControl) (x : OuterTape) (act : OuterAction)
    (origin : Int) (width : ℕ)
    (hstep : MStarCopierMicrocode.step MStarULogAssembly.data.uStart p x =
      some act)
    (hstate : c.state = .parser p) (hread : c.tape c.head = x)
    (hmovable : MStarOuterProgram.movable
      ((writtenTape c act.write) (moveHead act.move c.head)) = true)
    (hheadLow : origin ≤ c.head)
    (hheadHigh : c.head < origin + width)
    (hhash : ∀ z : Int, z < origin ∨ origin + width ≤ z →
      c.tape z = .hash) :
    ∃ a : OuterArrow,
      a.1.2 = 0 ∧
      FiniteOneTapeSemantics.step MStarULogAssembly.program
        MStarOuterProgram.movable c a = some (afterAction c act) ∧
      (∀ z : Int, z < origin ∨ origin + width ≤ z →
        (afterAction c act).tape z = .hash) := by
  rcases parserCopier_oneStep_outer c p x act hstep hstate hread hmovable with
    ⟨a, ha0, ha, _⟩
  exact ⟨a, ha0, ha,
    afterAction_hash_outside c act origin width hheadLow hheadHigh hhash⟩

/-! ## The first parser step after the certified side start row -/

/-- The first parser action, now in the actual ULog-instantiated outer state
type rather than the `Unit` state used by the finite zipper executor. -/
def sideFirstParserAction : OuterAction :=
  { write := MStarParserMicrocode.endpointMark
    target := .parser (.inl (MStarParserMicrocode.fixed ⟨1, by decide⟩))
    move := .right }

theorem sideFirstParser_microStep :
    MStarCopierMicrocode.step MStarULogAssembly.data.uStart
      MStarULogAssembly.data.parserStart
      (.core MStarConcreteAlphabet.zero) = some sideFirstParserAction := by
  native_decide

theorem sideFirstParser_rule :
    MStarULogAssembly.program.rule
      (.parser MStarULogAssembly.data.parserStart)
      (.core MStarConcreteAlphabet.zero) 0 = some sideFirstParserAction :=
  parserCopier_slotZero_rule _ _ _ sideFirstParser_microStep

/-- The literal arrow used by the first M3 transition. -/
def sideFirstParserArrow : OuterArrow :=
  slotZeroArrow (.parser MStarULogAssembly.data.parserStart)
    (.core MStarConcreteAlphabet.zero) sideFirstParserAction
    sideFirstParser_rule

theorem sideInputTape_two (x : ConcretePakSide.Word) :
    PakSideScannerRow.sideInputTape x 2 =
      .core MStarConcreteAlphabet.zero := by
  unfold PakSideScannerRow.sideInputTape
  rw [if_pos (by norm_num)]
  change (PakSideScanner.parserCellsWithCopierReserve x).getD 1 .hash =
    .core MStarConcreteAlphabet.zero
  rw [PakSideScannerRow.parserCellsWithCopierReserve_getD_prefix]
  · unfold PakEncodedStart.parserCells
    rw [MStarParserExecution.inputCells_encodedWord]
    let rest : List OuterTape :=
      [.core MStarConcreteAlphabet.one] ++
        List.replicate x.length (.core MStarConcreteAlphabet.zero) ++
        [.core MStarConcreteAlphabet.one] ++
        x.reverse.map (MStarParserExecution.bitCell
          MStarConcreteAlphabet.zero MStarConcreteAlphabet.one) ++
        [.core MStarConcreteAlphabet.one, .core MStarConcreteAlphabet.work]
    change (List.replicate (ConcretePakSide.paddingLength x.length)
        (MStarOuterProgram.Tape.core MStarConcreteAlphabet.zero : OuterTape) ++ rest).getD 1 .hash =
      .core MStarConcreteAlphabet.zero
    have hpad : 1 < ConcretePakSide.paddingLength x.length := by
      simp [ConcretePakSide.paddingLength]
    have hpadLen : 1 < (List.replicate
        (ConcretePakSide.paddingLength x.length)
        (MStarOuterProgram.Tape.core MStarConcreteAlphabet.zero : OuterTape)).length := by
      simpa using hpad
    rw [List.getD_append _ rest _ _ hpadLen]
    exact List.getD_replicate _ hpad
  · rw [PakSideScanner.parserCells_length]
    omega

/-- The first canonical parser move has a literal core successor, hence it
cannot be blocked by the outer machine's hash-sentinel mobility check. -/
theorem sideFirstParser_successor_nonhash (x : ConcretePakSide.Word) :
    MStarOuterProgram.movable
      ((writtenTape (PakSideScannerRow.sideEncodedParserConfig x)
        sideFirstParserAction.write)
        (moveHead sideFirstParserAction.move
          (PakSideScannerRow.sideEncodedParserConfig x).head)) = true := by
  simp [sideFirstParserAction, PakSideScannerRow.sideEncodedParserConfig,
    writtenTape, moveHead, sideInputTape_two, MStarOuterProgram.movable]

theorem sideFirstParser_outerStep (x : ConcretePakSide.Word) :
    FiniteOneTapeSemantics.step MStarULogAssembly.program
        MStarOuterProgram.movable
        (PakSideScannerRow.sideEncodedParserConfig x)
        sideFirstParserArrow =
      some (afterAction (PakSideScannerRow.sideEncodedParserConfig x)
        sideFirstParserAction) := by
  apply step_slotZeroArrow
  · rfl
  · exact PakSideScannerRow.sideInputTape_one x
  · exact sideFirstParser_successor_nonhash x

/-- The scanner's actual slot-one start transition is already an outer run,
not merely its tableau `WindowedMStarStep` presentation. -/
theorem sideStart_outerReaches (x : ConcretePakSide.Word) :
    OuterReaches (PakSideScannerRow.sideEncodedStartConfig x)
      (PakSideScannerRow.sideEncodedParserConfig x) := by
  refine ⟨[PakEncodedStart.startOneArrow], ?_⟩
  simp only [run_cons]
  rw [PakSideScannerRow.sideEncodedStart_slotOne_step]
  rfl

/-- The side row has two consecutive literal outer arrows: the scanner/start
slot-one arrow followed by the parser's occupied slot-zero arrow. -/
theorem sideStart_then_firstParser_outerReaches (x : ConcretePakSide.Word) :
    OuterReaches (PakSideScannerRow.sideEncodedStartConfig x)
      (afterAction (PakSideScannerRow.sideEncodedParserConfig x)
        sideFirstParserAction) := by
  apply outerReaches_trans (sideStart_outerReaches x)
  refine ⟨[sideFirstParserArrow], ?_⟩
  simp only [run_cons]
  rw [sideFirstParser_outerStep]
  rfl

/-! ## The concrete parser-terminal/copier-entry junction -/

/-- `copyReady` is represented at the outer level by the pre-entry parser
control.  Its next *real* outer transition is this copier-entry action. -/
def sideCopyEntryAction : OuterAction :=
  MStarCopierMicrocode.copyGo .markL .seedCell .right

theorem sideCopyEntry_microStep :
    MStarCopierMicrocode.step MStarULogAssembly.data.uStart
      (.inl MStarParserMicrocode.copyStart)
      (.core MStarConcreteAlphabet.work) = some sideCopyEntryAction := by
  native_decide

theorem sideCopyEntry_rule :
    MStarULogAssembly.program.rule
      (.parser (.inl MStarParserMicrocode.copyStart))
      (.core MStarConcreteAlphabet.work) 0 = some sideCopyEntryAction :=
  parserCopier_slotZero_rule _ _ _ sideCopyEntry_microStep

/-- The occupied slot-zero arrow which crosses from the parser's abstract
`copyReady` terminal into the literal copier seed control. -/
def sideCopyEntryArrow : OuterArrow :=
  slotZeroArrow (.parser (.inl MStarParserMicrocode.copyStart))
    (.core MStarConcreteAlphabet.work) sideCopyEntryAction sideCopyEntry_rule

theorem sideCopyEntry_outerStep (c : OuterConfig)
    (hstate : c.state = .parser (.inl MStarParserMicrocode.copyStart))
    (hread : c.tape c.head = .core MStarConcreteAlphabet.work)
    (hmovable : MStarOuterProgram.movable
      ((writtenTape c sideCopyEntryAction.write)
        (moveHead sideCopyEntryAction.move c.head)) = true) :
    FiniteOneTapeSemantics.step MStarULogAssembly.program
        MStarOuterProgram.movable c sideCopyEntryArrow =
      some (afterAction c sideCopyEntryAction) := by
  apply step_slotZeroArrow
  · exact hstate
  · exact hread
  · exact hmovable

theorem sideCopyEntry_outerReaches (c : OuterConfig)
    (hstate : c.state = .parser (.inl MStarParserMicrocode.copyStart))
    (hread : c.tape c.head = .core MStarConcreteAlphabet.work)
    (hmovable : MStarOuterProgram.movable
      ((writtenTape c sideCopyEntryAction.write)
        (moveHead sideCopyEntryAction.move c.head)) = true) :
    OuterReaches c (afterAction c sideCopyEntryAction) := by
  refine ⟨[sideCopyEntryArrow], ?_⟩
  simp only [run_cons]
  rw [sideCopyEntry_outerStep c hstate hread hmovable]
  rfl

theorem sideCopyEntry_outerStep_hashWindow (c : OuterConfig)
    (origin : Int) (width : ℕ)
    (hstate : c.state = .parser (.inl MStarParserMicrocode.copyStart))
    (hread : c.tape c.head = .core MStarConcreteAlphabet.work)
    (hmovable : MStarOuterProgram.movable
      ((writtenTape c sideCopyEntryAction.write)
        (moveHead sideCopyEntryAction.move c.head)) = true)
    (hheadLow : origin ≤ c.head) (hheadHigh : c.head < origin + width)
    (hhash : ∀ z : Int, z < origin ∨ origin + width ≤ z →
      c.tape z = .hash) :
    ∃ a : OuterArrow,
      a = sideCopyEntryArrow ∧
      FiniteOneTapeSemantics.step MStarULogAssembly.program
        MStarOuterProgram.movable c a = some (afterAction c sideCopyEntryAction) ∧
      (∀ z : Int, z < origin ∨ origin + width ≤ z →
        (afterAction c sideCopyEntryAction).tape z = .hash) := by
  exact ⟨sideCopyEntryArrow, rfl,
    sideCopyEntry_outerStep c hstate hread hmovable,
    afterAction_hash_outside c sideCopyEntryAction origin width
      hheadLow hheadHigh hhash⟩

/-- The already-green side start row extends by one genuine M3 arrow while
retaining exactly the same left and right hash exterior. -/
theorem sideFirstParser_outerStep_hashWindow (x : ConcretePakSide.Word) :
    (∀ z : Int,
      z < 0 ∨
          ((PakSideScanner.sideScannerBits x).length + 2 : Int) ≤ z →
        (afterAction (PakSideScannerRow.sideEncodedParserConfig x)
          sideFirstParserAction).tape z = .hash) := by
  have h := afterAction_hash_outside
    (PakSideScannerRow.sideEncodedParserConfig x) sideFirstParserAction 0
    ((PakSideScanner.sideScannerBits x).length + 2)
    (by simp [PakSideScannerRow.sideEncodedParserConfig])
    (by
      have hpos := PakSideScanner.sideScannerBits_pos x
      simp [PakSideScannerRow.sideEncodedParserConfig]
      omega)
    (by
      intro z hz
      apply PakSideScannerRow.sideInputTape_hash_outside x z
      simpa [PakSideScannerRow.sideEncodedParserConfig] using hz)
  simpa only [zero_add, Nat.cast_add, Nat.cast_ofNat] using h

end PakFixedPolyomino.PakParserOuterBridge
