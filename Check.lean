import PakFixedPolyomino
import Lean.Util.CollectAxioms

open PakFixedPolyomino in
example : ∃ T : Finset Polyomino,
    T.Nonempty ∧ (∀ P ∈ T, P.Nonempty ∧ FourConnected P) ∧
    StandardBitMetric.CompleteForSharpEXP
      (PakFixedShapeExactCountingModel.binaryTranslationSquareCount T) :=
  PakFixedShapeHeadline.pak_headline

#print axioms PakFixedPolyomino.PakFixedShapeHeadline.membership
#print axioms PakFixedPolyomino.PakFixedShapeHeadline.metric_hardness
#print axioms PakFixedPolyomino.PakFixedShapeHeadline.complete
#print axioms PakFixedPolyomino.PakFixedShapeHeadline.pak_headline

open Lean in
run_cmd do
  let targets : Array Name := #[
    ``PakFixedPolyomino.PakFixedShapeHeadline.membership,
    ``PakFixedPolyomino.PakFixedShapeHeadline.metric_hardness,
    ``PakFixedPolyomino.PakFixedShapeHeadline.complete,
    ``PakFixedPolyomino.PakFixedShapeHeadline.pak_headline]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for target in targets do
    unless (← getEnv).contains target do
      throwError "Missing theorem: {target}"
    let axioms ← Lean.collectAxioms target
    let unexpected := axioms.filter fun name => !allowed.contains name
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {target}: {unexpected.toList}"
