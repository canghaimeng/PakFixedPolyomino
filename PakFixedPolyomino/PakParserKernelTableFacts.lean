import PakFixedPolyomino.PakParserOuterBridge

/-! Kernel-reduced finite parser table facts replacing compiler-trust
leaves of the inherited outer-front proof. The machine tables and labels
are unchanged. These facts alone do not yet repair that proof's closure. -/
namespace PakFixedPolyomino.PakParserKernelTableFacts
open MStarParserMicrocode MStarConcreteAlphabet
open PakParserOuterBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem scanPad_ne_copyStart : scanPad ≠ copyStart := by decide
theorem scanLen_ne_copyStart : scanLen ≠ copyStart := by decide

theorem control_hash_rejected :
    ∀ q : Fin 18, q ≠ (⟨5, by decide⟩ : Fin 18) →
      q ≠ (⟨17, by decide⟩ : Fin 18) →
      MStarParserMicrocode.step (UState := Unit) zero one work
        (control q) .hash = some (MStarParserMicrocode.reject .hash) := by
  decide

theorem change_unit_table :
    ∀ p : ParserState, ∀ x : PakParserOuterBridge.OuterTape,
      MStarParserMicrocode.step (UState := MStarULogAssembly.UniversalState)
        zero one work p x =
      (MStarParserMicrocode.step (UState := Unit) zero one work p x).map
        (changeUnitParserAction MStarULogAssembly.data.uStart) := by
  decide

theorem copyStart_table_output :
    ∀ p : ParserState, ∀ x : PakParserOuterBridge.OuterTape,
      (MStarParserMicrocode.step (UState := Unit) zero one work p x).all
        (fun a => decide (a.target = .parser copyStart →
          a.move = .stay ∧ a.write = .core work)) = true := by
  decide

theorem target_copyStart_stays_work (p : ParserState) (x : PakParserOuterBridge.OuterTape)
    (a : FiniteOneTapeProgram.Action (MStarOuterProgram.State ParserState Unit)
      PakParserOuterBridge.OuterTape)
    (table : MStarParserMicrocode.step (UState := Unit) zero one work p x = some a)
    (target : a.target = .parser copyStart) :
    a.move = .stay ∧ a.write = .core work := by
  have output := copyStart_table_output p x
  rw [table] at output
  have condition : a.target = .parser copyStart →
      a.move = .stay ∧ a.write = .core work := of_decide_eq_true output
  exact condition target

theorem unit_action_to_outer_action (p : ParserState) (x : PakParserOuterBridge.OuterTape)
    (a : FiniteOneTapeProgram.Action (MStarOuterProgram.State ParserState Unit)
      PakParserOuterBridge.OuterTape)
    (nonterminal : p ≠ copyStart)
    (table : MStarParserMicrocode.step (UState := Unit) zero one work p x = some a) :
    MStarCopierMicrocode.step MStarULogAssembly.data.uStart (.inl p) x =
      some (liftUnitParserAction MStarULogAssembly.data.uStart a) := by
  simp only [MStarCopierMicrocode.step, nonterminal, ↓reduceIte]
  rw [change_unit_table p x, table]
  cases target : a.target <;>
    simp [changeUnitParserAction, liftUnitParserAction, liftUnitParserState,
      MStarCopierMicrocode.liftAction, MStarCopierMicrocode.liftState, target]

theorem copy_entry_microstep :
    MStarCopierMicrocode.step MStarULogAssembly.data.uStart (.inl copyStart)
      (.core work) = some sideCopyEntryAction := by
  rfl

end PakFixedPolyomino.PakParserKernelTableFacts
