import PakFixedPolyomino.PakParserOuterBridge
import PakFixedPolyomino.PakParserKernelTableFacts
import PakFixedPolyomino.PakOuterParserReflection

/-! # Kernel-only finite-window reflection of actual outer parser configurations

The window, labels and actions are literal unchanged definitions. Only the
inherited finite table transport proof is replaced by the clean kernel fact.
Original source preserved; full frame/source census remains separate. -/

namespace PakFixedPolyomino.PakOuterParserReflectionStandard

open PakMStarCouplingCorrectness
open PakParserOuterBridge

/-- The complete finite tape window, in physical left-to-right order. -/
def windowCells (n : ℕ) (c : OuterConfig) : List OuterTape :=
  List.ofFn (fun k : Fin n => c.tape k.1)

/-- Split a finite outer tape window at its literal head index.  The left
part is reversed because that is the parser zipper convention. -/
def windowZipper (n : ℕ) (c : OuterConfig) (h : Fin n) :
    MStarParserExecution.Zipper OuterTape where
  leftRev := (windowCells n c).take h.1 |>.reverse
  focus := c.tape h.1
  right := (windowCells n c).drop (h.1 + 1)

theorem windowCells_get (n : ℕ) (c : OuterConfig) (k : Fin n) :
    (windowCells n c).get ⟨k.1, by simp [windowCells]⟩ = c.tape k.1 := by
  simp [windowCells]

/-- Splitting and immediately reassembling the zipper gives the entire
finite physical window. -/
theorem anchoredZipperCells_windowZipper (n : ℕ) (c : OuterConfig)
    (h : Fin n) :
    anchoredZipperCells (windowZipper n c h) = windowCells n c := by
  let xs := windowCells n c
  have hhead : xs.get ⟨h.1, by simpa [xs, windowCells] using h.2⟩ = c.tape h.1 := by
    simpa [xs] using windowCells_get n c h
  have hsplit : xs.take h.1 ++ c.tape h.1 :: xs.drop (h.1 + 1) = xs := by
    rw [← hhead]
    simpa using (List.take_append_drop (h.1 + 1) xs)
  unfold anchoredZipperCells windowZipper
  dsimp
  rw [List.reverse_reverse]
  exact hsplit

/-- A configuration satisfying the ordinary finite-window hash condition is
exactly recovered by anchoring its split zipper at zero. -/
theorem anchoredZipperTape_windowZipper_eq
    (n : ℕ) (c : OuterConfig) (h : Fin n)
    (hhash : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → c.tape z = .hash) :
    anchoredZipperTape 0 (windowZipper n c h) = c.tape := by
  funext z
  by_cases hneg : z < 0
  · rw [anchoredZipperTape_hash_left]
    · exact (hhash z (Or.inl hneg)).symm
    · simpa using hneg
  by_cases hhigh : (n : Int) ≤ z
  · have hlen : (anchoredZipperCells (windowZipper n c h)).length = n := by
      rw [anchoredZipperCells_windowZipper]
      simp [windowCells]
    rw [anchoredZipperTape_hash_right]
    · exact (hhash z (Or.inr hhigh)).symm
    · rw [hlen]
      simpa using hhigh
  · have hz : 0 ≤ z ∧ z < (n : Int) := by omega
    let k : Fin n := ⟨z.toNat, by omega⟩
    have hk : (k.1 : Int) = z := by
      dsimp [k]
      exact Int.toNat_of_nonneg hz.1
    rw [← hk]
    have hoff := anchoredZipperTape_at_offset 0 (windowZipper n c h) k.1
    have hoff' : anchoredZipperTape 0 (windowZipper n c h) k.1 =
        (anchoredZipperCells (windowZipper n c h)).getD k.1 .hash := by
      simpa using hoff
    rw [hoff']
    rw [anchoredZipperCells_windowZipper]
    have hget : (windowCells n c).getD k.1 .hash = c.tape k.1 := by
      rw [List.getD_eq_get (windowCells n c) .hash
        ⟨k.1, by simpa [windowCells] using k.2⟩]
      exact windowCells_get n c k
    simpa [k] using hget

private theorem outerConfig_ext (c d : OuterConfig)
    (hstate : c.state = d.state) (hhead : c.head = d.head)
    (htape : c.tape = d.tape) : c = d := by
  cases c
  cases d
  simp only at hstate hhead htape
  subst_vars
  rfl

/-- A genuine finite-window parser configuration is recovered exactly by
splitting at its physical head and re-anchoring the resulting zipper at zero. -/
theorem anchoredParserConfig_windowZipper_eq
    (n : ℕ) (c : OuterConfig) (p : MStarParserMicrocode.ParserState)
    (h : Fin n)
    (hstate : c.state = .parser (.inl p))
    (hhead : c.head = h.1)
    (hhash : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → c.tape z = .hash) :
    anchoredParserConfig p 0 (windowZipper n c h) = c := by
  apply outerConfig_ext
  · simpa [anchoredParserConfig] using hstate.symm
  · unfold anchoredParserConfig windowZipper
    change 0 + ((windowCells n c).take h.1).reverse.length = c.head
    rw [List.length_reverse, List.length_take, hhead]
    simpa [windowCells] using Nat.le_of_lt h.2
  · exact anchoredZipperTape_windowZipper_eq n c h hhash

/-- Closed finite-table inverse for a nonterminal parser row.  This is kept
separate from the geometric zipper argument: it recovers the `Unit` parser
action whose lifted action is the occupied outer rule. -/
theorem parser_outer_rule_inverse
    (p : MStarParserMicrocode.ParserState) (x : OuterTape) (slot : Fin 2)
    (act : OuterAction)
    (hp : p ≠ MStarParserMicrocode.copyStart)
    (hrule : MStarULogAssembly.program.rule (.parser (.inl p)) x slot = some act) :
    ∃ ua : FiniteOneTapeProgram.Action
        (MStarOuterProgram.State MStarParserMicrocode.ParserState Unit) OuterTape,
      MStarParserMicrocode.step (UState := Unit)
          MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
          MStarConcreteAlphabet.work p x = some ua ∧
      act = liftUnitParserAction MStarULogAssembly.data.uStart ua := by
  have hslot : slot = 0 := by
    fin_cases slot
    · rfl
    · simp [MStarULogAssembly.program, MStarULogAssembly.data,
        MStarOuterProgram.program] at hrule
  subst slot
  have hcombined : MStarCopierMicrocode.step MStarULogAssembly.data.uStart
      (.inl p) x = some act := by
    simpa [MStarULogAssembly.program, MStarULogAssembly.data,
      MStarOuterProgram.program, MStarCopierMicrocode.attach] using hrule
  simp only [MStarCopierMicrocode.step, hp, if_false] at hcombined
  rw [PakParserKernelTableFacts.change_unit_table p x] at hcombined
  simp only [Option.map_map] at hcombined
  rcases Option.map_eq_some_iff.mp hcombined with ⟨ua, hua, hmap⟩
  refine ⟨ua, hua, ?_⟩
  rw [← hmap]
  rcases ua with ⟨write, target, move⟩
  cases target <;> rfl

/-! ## Decoding a literal parser arrow

The finite-table inverse above takes an explicit occupied rule.  The next
lemmas extract that rule from a *successful labelled outer transition*, so a
caller does not have to supply an abstract action-realisation premise. -/

private theorem outer_rule_eq_actionOf (a : OuterArrow) :
    MStarULogAssembly.program.rule a.1.1.1 a.1.1.2 a.1.2 =
      some (FiniteOneTapeProgram.actionOf MStarULogAssembly.program a) := by
  unfold FiniteOneTapeProgram.actionOf
  split
  · rename_i found hfound
    exact hfound
  · rename_i hnone
    exact (a.2 hnone).elim

/-- A successful labelled outer step has precisely the `afterAction`
successor displayed by that arrow. -/
theorem outerStep_eq_afterAction (c d : OuterConfig) (a : OuterArrow)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some d) :
    d = afterAction c (FiniteOneTapeProgram.actionOf MStarULogAssembly.program a) := by
  unfold FiniteOneTapeSemantics.step at hstep
  dsimp only at hstep
  split at hstep
  · simp at hstep
  · split at hstep
    · exact (Option.some.inj hstep).symm
    · simp at hstep

/-- Decode the unique `Unit` parser action from an occupied successful outer
step at a nonterminal parser source.  Both the source/read pair and slot zero
are consequences of the actual transition; they are not assumptions. -/
theorem parserUnitAction_of_outerStep
    (p : MStarParserMicrocode.ParserState) (c d : OuterConfig) (a : OuterArrow)
    (hstate : c.state = .parser (.inl p))
    (hp : p ≠ MStarParserMicrocode.copyStart)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some d) :
    ∃ uact : FiniteOneTapeProgram.Action
        (MStarOuterProgram.State MStarParserMicrocode.ParserState Unit) OuterTape,
      MStarParserMicrocode.step (UState := Unit)
          MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
          MStarConcreteAlphabet.work p (c.tape c.head) = some uact ∧
      a.1.2 = 0 ∧
      FiniteOneTapeProgram.actionOf MStarULogAssembly.program a =
        liftUnitParserAction MStarULogAssembly.data.uStart uact ∧
      d = afterAction c (liftUnitParserAction MStarULogAssembly.data.uStart uact) := by
  have hsource := FiniteOneTapeSemantics.step_some_forces_source
    MStarULogAssembly.program MStarOuterProgram.movable c d a hstep
  have hq : a.1.1.1 = (.parser (.inl p) : OuterState) :=
    hsource.1.symm.trans hstate
  have hx : a.1.1.2 = c.tape c.head := hsource.2.symm
  have hslot : a.1.2 = 0 := by
    by_contra hnotzero
    have hone : a.1.2 = 1 := by
      apply Fin.ext
      have hval : a.1.2.1 = 1 := by
        by_contra hval
        have hzero : a.1.2.1 = 0 := by omega
        exact hnotzero (Fin.ext hzero)
      exact hval
    have hnone : MStarULogAssembly.program.rule
        (.parser (.inl p)) a.1.1.2 a.1.2 = none := by
      simpa [MStarULogAssembly.program, MStarULogAssembly.data, hone] using
        (MStarCopierMicrocode.combined_slot_one_empty ULogProgram.program
          ULogControl.qAccept ULogControl.qReject ULogControl.qStart
          (.inl p) a.1.1.2)
    apply a.2
    simpa [hq] using hnone
  have hrule : MStarULogAssembly.program.rule (.parser (.inl p))
      (c.tape c.head) a.1.2 =
        some (FiniteOneTapeProgram.actionOf MStarULogAssembly.program a) := by
    simpa [hq, hx] using outer_rule_eq_actionOf a
  rcases parser_outer_rule_inverse p (c.tape c.head) a.1.2
      (FiniteOneTapeProgram.actionOf MStarULogAssembly.program a) hp hrule with
    ⟨uact, huact, haction⟩
  refine ⟨uact, huact, hslot, haction, ?_⟩
  have hafter := outerStep_eq_afterAction c d a hstep
  rw [haction] at hafter
  exact hafter

/-- Splitting a window at its certified physical head reads exactly the head
letter.  Thus the `uact` recovered by `parserUnitAction_of_outerStep` is an
action on the projected finite parser configuration. -/
theorem windowZipper_focus_eq_head
    (n : ℕ) (c : OuterConfig) (h : Fin n) (hhead : c.head = h.1) :
    (windowZipper n c h).focus = c.tape c.head := by
  simp [windowZipper, hhead]

/-- At a fixed finite support length, the anchored ambient configuration
determines the zipper.  The length side condition is essential: trailing
literal hash cells otherwise cannot be distinguished from the exterior. -/
private theorem anchoredParserConfig_injective_of_cells_length
    (p : MStarParserMicrocode.ParserState)
    (z w : MStarParserExecution.Zipper OuterTape) (n : ℕ)
    (hz : (anchoredZipperCells z).length = n)
    (hw : (anchoredZipperCells w).length = n)
    (hcfg : anchoredParserConfig p 0 z = anchoredParserConfig p 0 w) : z = w := by
  have hleftlen : z.leftRev.length = w.leftRev.length := by
    have hhead := congrArg (fun c : OuterConfig => c.head) hcfg
    simpa [anchoredParserConfig] using hhead
  have htape : anchoredZipperTape 0 z = anchoredZipperTape 0 w := by
    have := congrArg (fun c : OuterConfig => c.tape) hcfg
    simpa [anchoredParserConfig] using this
  have hcells : anchoredZipperCells z = anchoredZipperCells w := by
    apply List.ext_get (hz.trans hw.symm)
    intro i hiz hiw
    have hpoint := congrFun htape (i : Int)
    have hzoff := anchoredZipperTape_at_offset 0 z i
    have hwoff := anchoredZipperTape_at_offset 0 w i
    have hzoff' : anchoredZipperTape 0 z i =
        (anchoredZipperCells z).getD i .hash := by simpa using hzoff
    have hwoff' : anchoredZipperTape 0 w i =
        (anchoredZipperCells w).getD i .hash := by simpa using hwoff
    rw [hzoff', hwoff'] at hpoint
    rw [List.getD_eq_get (anchoredZipperCells z) .hash ⟨i, hiz⟩,
      List.getD_eq_get (anchoredZipperCells w) .hash ⟨i, hiw⟩] at hpoint
    simpa using hpoint
  have hleftrev : z.leftRev.reverse = w.leftRev.reverse := by
    have := congrArg (fun xs : List OuterTape => xs.take z.leftRev.length) hcells
    simpa [anchoredZipperCells, hleftlen] using this
  have htail : z.focus :: z.right = w.focus :: w.right := by
    have := congrArg (fun xs : List OuterTape => xs.drop z.leftRev.length) hcells
    simpa [anchoredZipperCells, hleftlen] using this
  apply MStarParserExecution.Zipper.ext
  · exact List.reverse_injective hleftrev
  · exact List.cons.inj htail |>.1
  · exact List.cons.inj htail |>.2

/-- A nonterminal parser action which is witnessed by a real outer step
acts successfully on the split finite window, provided both old and new heads
are in that window.  The conclusion identifies the resulting zipper with the
literal successor window, not merely with an ambient realisation. -/
theorem windowZipper_applyAction_of_outer_after
    (n : ℕ) (p p' : MStarParserMicrocode.ParserState)
    (c d : OuterConfig) (h h' : Fin n)
    (uact : FiniteOneTapeProgram.Action
      (MStarOuterProgram.State MStarParserMicrocode.ParserState Unit) OuterTape)
    (hstate : c.state = .parser (.inl p))
    (hstate' : d.state = .parser (.inl p'))
    (hhead : c.head = h.1) (hhead' : d.head = h'.1)
    (hhash : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → c.tape z = .hash)
    (hhash' : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → d.tape z = .hash)
    (htarget : uact.target = .parser p')
    (hafter : d = afterAction c
      (liftUnitParserAction MStarULogAssembly.data.uStart uact)) :
    MStarParserExecution.applyAction (windowZipper n c h) uact =
      some (windowZipper n d h') := by
  let z := windowZipper n c h
  have hmove : d.head = FiniteOneTapeSemantics.moveHead uact.move c.head := by
    have := congrArg (fun c : OuterConfig => c.head) hafter
    simpa [afterAction, liftUnitParserAction] using this
  have happly : ∃ z', MStarParserExecution.applyAction z uact = some z' := by
    cases hmoveact : uact.move with
    | stay => exact ⟨{ z with focus := uact.write }, by simp [z,
        MStarParserExecution.applyAction, hmoveact]⟩
    | right =>
        have hnext : h.1 + 1 < n := by
          have : (h'.1 : Int) = (h.1 : Int) + 1 := by
            rw [← hhead', hmove, hhead]
            simp [FiniteOneTapeSemantics.moveHead, hmoveact]
          omega
        have hright : z.right ≠ [] := by
          intro hnil
          have hdrop : (windowCells n c).drop (h.1 + 1) = [] := by
            simpa [z, windowZipper] using hnil
          have hle := List.drop_eq_nil_iff.mp hdrop
          have hlen : (windowCells n c).length = n := by simp [windowCells]
          omega
        cases hzright : z.right with
        | nil => exact (hright hzright).elim
        | cons x xs =>
            let z' : MStarParserExecution.Zipper OuterTape :=
              { leftRev := uact.write :: z.leftRev, focus := x, right := xs }
            exact ⟨z', by
              simp [z', MStarParserExecution.applyAction, hmoveact, hzright]⟩
    | left =>
        have hpositive : 0 < h.1 := by
          have : (h'.1 : Int) = (h.1 : Int) - 1 := by
            rw [← hhead', hmove, hhead]
            simp [FiniteOneTapeSemantics.moveHead, hmoveact]
          omega
        have hleft : z.leftRev ≠ [] := by
          intro hnil
          have hlen : z.leftRev.length = h.1 := by
            simp [z, windowZipper, windowCells, Nat.le_of_lt h.2]
          simp [hnil] at hlen
          omega
        cases hzleft : z.leftRev with
        | nil => exact (hleft hzleft).elim
        | cons x xs =>
            let z' : MStarParserExecution.Zipper OuterTape :=
              { leftRev := xs, focus := x, right := uact.write :: z.right }
            exact ⟨z', by
              simp [z', MStarParserExecution.applyAction, hmoveact, hzleft]⟩
  rcases happly with ⟨z', happly⟩
  have happlyLift : MStarParserExecution.applyAction z
      (liftUnitParserAction MStarULogAssembly.data.uStart uact) = some z' := by
    rw [applyAction_liftUnitParserAction]
    exact happly
  have htargetLift : (liftUnitParserAction MStarULogAssembly.data.uStart
      uact).target = (.parser (.inl p') : OuterState) := by
    simp [liftUnitParserAction, liftUnitParserState, htarget]
  have hforward : afterAction (anchoredParserConfig p 0 z)
      (liftUnitParserAction MStarULogAssembly.data.uStart uact) =
        anchoredParserConfig p' 0 z' := by
    simp only [afterAction, anchoredParserConfig,
      FiniteOneTapeSemantics.writtenTape]
    rw [htargetLift,
      anchoredZipperHead_applyAction 0 z z'
        (liftUnitParserAction MStarULogAssembly.data.uStart uact) happlyLift,
      anchoredZipperTape_applyAction 0 z z'
        (liftUnitParserAction MStarULogAssembly.data.uStart uact) happlyLift]
  have hc : anchoredParserConfig p 0 z = c := by
    simpa [z] using anchoredParserConfig_windowZipper_eq n c p h hstate hhead hhash
  have hd : anchoredParserConfig p' 0 (windowZipper n d h') = d :=
    anchoredParserConfig_windowZipper_eq n d p' h' hstate' hhead' hhash'
  have hcfg : anchoredParserConfig p' 0 z' =
      anchoredParserConfig p' 0 (windowZipper n d h') := by
    calc
      anchoredParserConfig p' 0 z' =
          afterAction (anchoredParserConfig p 0 z)
            (liftUnitParserAction MStarULogAssembly.data.uStart uact) := hforward.symm
      _ = afterAction c (liftUnitParserAction MStarULogAssembly.data.uStart uact) := by
        rw [hc]
      _ = d := hafter.symm
      _ = anchoredParserConfig p' 0 (windowZipper n d h') := hd.symm
  have hzlen : (anchoredZipperCells z').length = n := by
    rw [anchoredZipperCells_applyAction z z' uact happly]
    change ((anchoredZipperCells (windowZipper n c h)).set
      (windowZipper n c h).leftRev.length uact.write).length = n
    rw [List.length_set, anchoredZipperCells_windowZipper]
    simp [windowCells]
  have hwlen : (anchoredZipperCells (windowZipper n d h')).length = n := by
    rw [anchoredZipperCells_windowZipper]
    simp [windowCells]
  have hzw := anchoredParserConfig_injective_of_cells_length p' z'
    (windowZipper n d h') n hzlen hwlen hcfg
  simpa [z] using happly.trans (congrArg some hzw)

/-- Total parser-to-parser one-step reflection.  An actual successful outer
step and the two finite-window facts determine the `Unit` parser action,
prove its zipper move is in-bounds, and identify its result with the literal
successor window.  No finite-parser action witness is an input. -/
theorem noncopy_parser_oneStep_reflection
    (n : ℕ) (p p' : MStarParserMicrocode.ParserState)
    (c d : OuterConfig) (a : OuterArrow) (h h' : Fin n)
    (hstate : c.state = .parser (.inl p))
    (hstate' : d.state = .parser (.inl p'))
    (hp : p ≠ MStarParserMicrocode.copyStart)
    (hhead : c.head = h.1) (hhead' : d.head = h'.1)
    (hhash : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → c.tape z = .hash)
    (hhash' : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → d.tape z = .hash)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some d) :
    MStarParserExecution.oneStep MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work
      (.running p (windowZipper n c h)) =
        .running p' (windowZipper n d h') := by
  rcases parserUnitAction_of_outerStep p c d a hstate hp hstep with
    ⟨uact, huact, _hslot, haction, hafter⟩
  have houterTarget : (liftUnitParserAction MStarULogAssembly.data.uStart
      uact).target = (.parser (.inl p') : OuterState) := by
    have hstates := congrArg (fun c : OuterConfig => c.state) hafter
    simpa [afterAction] using hstates.symm.trans hstate'
  have htarget : uact.target = .parser p' := by
    cases huTarget : uact.target with
    | start => simp [liftUnitParserAction, liftUnitParserState, huTarget] at houterTarget
    | accept => simp [liftUnitParserAction, liftUnitParserState, huTarget] at houterTarget
    | reject => simp [liftUnitParserAction, liftUnitParserState, huTarget] at houterTarget
    | parser q =>
        simpa [liftUnitParserAction, liftUnitParserState, huTarget] using houterTarget
    | sim u => simp [liftUnitParserAction, liftUnitParserState, huTarget] at houterTarget
  have happly := windowZipper_applyAction_of_outer_after n p p' c d h h'
    uact hstate hstate' hhead hhead' hhash hhash' htarget hafter
  have hfocus := windowZipper_focus_eq_head n c h hhead
  have huact' : MStarParserMicrocode.step (UState := Unit)
      MStarConcreteAlphabet.zero MStarConcreteAlphabet.one
      MStarConcreteAlphabet.work p (windowZipper n c h).focus = some uact := by
    simpa [hfocus] using huact
  simp only [MStarParserExecution.oneStep, hp, if_false, huact', happly, htarget]

/-- The parser executor treats `copyStart` as its zero-arrow terminal:
the corresponding finite result is `copyReady` on the unchanged window.
The subsequent physical copier-entry arrow is intentionally outside this
parser reflection theorem. -/
theorem copyStart_oneStep_windowZipper
    (n : ℕ) (c : OuterConfig) (h : Fin n) :
    MStarParserExecution.oneStep MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work
      (.running MStarParserMicrocode.copyStart (windowZipper n c h)) =
        .copyReady (windowZipper n c h) := by
  simp [MStarParserExecution.oneStep]

theorem window_cells_eq_original (n : Nat) (c : OuterConfig) :
    windowCells n c = PakOuterParserReflection.windowCells n c := rfl

theorem window_zipper_eq_original (n : Nat) (c : OuterConfig) (h : Fin n) :
    windowZipper n c h = PakOuterParserReflection.windowZipper n c h := rfl

end PakFixedPolyomino.PakOuterParserReflectionStandard
