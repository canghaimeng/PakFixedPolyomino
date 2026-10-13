import PakFixedPolyomino.PakParserKernelTableFacts

/-! Actual parser outcome kinds, proved by structural reduction of the literal
unchanged table. These replace finite compiler-trust leaves of the inherited
window inverse; they do not themselves prove the full inverse. -/
namespace PakFixedPolyomino.PakParserKernelOutcomeFacts
open MStarParserMicrocode MStarConcreteAlphabet PakParserOuterBridge
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def unitParserTargetGood (q : MStarOuterProgram.State ParserState Unit) : Bool :=
  match q with
  | .parser _ | .reject => true
  | _ => false

def unitParserOutcomeGood
    (o : Option (FiniteOneTapeProgram.Action
      (MStarOuterProgram.State ParserState Unit) PakParserOuterBridge.OuterTape)) : Bool :=
  match o with
  | none => true
  | some a => unitParserTargetGood a.target

theorem every_unit_outcome_good : ∀ (p : ParserState) (x : PakParserOuterBridge.OuterTape),
    unitParserOutcomeGood (MStarParserMicrocode.step (UState := Unit)
      zero one work p x) = true := by
  decide

theorem left_target_ne_copyStart (p : ParserState) (x : PakParserOuterBridge.OuterTape)
    (a : FiniteOneTapeProgram.Action
      (MStarOuterProgram.State ParserState Unit) PakParserOuterBridge.OuterTape)
    (h : MStarParserMicrocode.step (UState := Unit) zero one work p x = some a)
    (hl : a.move = .left) : a.target ≠ .parser copyStart := by
  intro ht
  have hs := (PakParserKernelTableFacts.target_copyStart_stays_work p x a h ht).1
  rw [hl] at hs
  cases hs

end PakFixedPolyomino.PakParserKernelOutcomeFacts
