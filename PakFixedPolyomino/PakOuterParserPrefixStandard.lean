import PakFixedPolyomino.PakOuterParserReflectionStandard
import PakFixedPolyomino.PakOuterParserPrefixReflection

/-! Standard closure on the unchanged literal parser-prefix datatype. -/
namespace PakFixedPolyomino.PakOuterParserPrefixStandard
open PakParserOuterBridge PakOuterParserReflection PakOuterParserPrefixReflection

theorem noncopy_canAccept_of_outer_step
    (n : Nat) (p p' : MStarParserMicrocode.ParserState)
    (c d : OuterConfig) (a : OuterArrow) (h h' : Fin n)
    (hstate : c.state = .parser (.inl p))
    (hstate' : d.state = .parser (.inl p'))
    (hp : p ≠ MStarParserMicrocode.copyStart)
    (hhead : c.head = h.1) (hhead' : d.head = h'.1)
    (hhash : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → c.tape z = .hash)
    (hhash' : ∀ z : Int, z < 0 ∨ (n : Int) ≤ z → d.tape z = .hash)
    (hstep : FiniteOneTapeSemantics.step MStarULogAssembly.program
      MStarOuterProgram.movable c a = some d)
    (ha : MStarParserSoundness.CanAcceptResult (.running p' (windowZipper n d h'))) :
    MStarParserSoundness.CanAcceptResult (.running p (windowZipper n c h)) := by
  have hr := PakOuterParserReflectionStandard.noncopy_parser_oneStep_reflection
    n p p' c d a h h' hstate hstate' hp hhead hhead' hhash hhash' hstep
  have hr' : MStarParserExecution.oneStep MStarConcreteAlphabet.zero
      MStarConcreteAlphabet.one MStarConcreteAlphabet.work
      (.running p (windowZipper n c h)) = .running p' (windowZipper n d h') := hr
  apply (MStarParserSoundness.canAcceptResult_oneStep_iff
    (.running p (windowZipper n c h))).mp
  rw [hr']
  exact ha

theorem outer_parser_prefix_canAccept {n : Nat} {c : OuterConfig} {h : Fin n}
    {p : MStarParserMicrocode.ParserState} (P : OuterParserPrefix n c h p) :
    MStarParserSoundness.CanAcceptResult (.running p (windowZipper n c h)) := by
  induction P with
  | copyStart c h => exact copyStart_window_canAccept n c h
  | @step c d h h' p p' a hstate hstate' hp hhead hhead'
      hhash hhash' hstep tail ih =>
      exact noncopy_canAccept_of_outer_step n p p' c d a h h'
        hstate hstate' hp hhead hhead' hhash hhash' hstep ih

end PakFixedPolyomino.PakOuterParserPrefixStandard
