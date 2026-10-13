import PakFixedPolyomino.ULogFiniteTapeNondeterministicResourceBridge
import PakFixedPolyomino.ULogConcreteMicroExpansionInjectivity

/-! Count ALL actual accepting micro-label words of a literal cycle frame.
The raw subtype requires only local physical edges, with no expansion,
semantic/image membership or chosen word certificate. Generic all-prefix
growth/length bounds remain explicit and must be internally instantiated. -/

namespace PakFixedPolyomino.ULogFiniteTapeNondeterministicMicroCounts
open ULogCompiler ULogFiniteTapeZipperRun ULogFiniteTapeGrowthLedger
open ULogFiniteTapeBoundedGrowthReadiness ULogFiniteTapeNondeterministicMicroInverse
open ULogFiniteTapeNondeterministicResourceBridge
open ULogBootstrapExecution ULogAlphabet ULogProgram ULogConcreteSlotMicroExpansion
open MStarParserExecution (Zipper)

variable {ns : Nat}

def LogicalAcceptingWords (p : BoundedProgram ns 3) (head : Int)
    (z : BoundedConfig ns 3) : Type :=
  { w : List Bool // ∃ hf out,
    ULogFiniteTapeZipperRun.run p 2 w head z = some (hf, out) ∧ out.state.val = 0 }

def RawAcceptingMicroWords (start : Result) : Type :=
  { labels : List (Fin 2) // ∃ tape : Zipper Tape,
    ConcreteMicroPath start labels (.accepted tape) }

theorem accepting_trace_has_expansion {start : Result} {w : List Bool}
    (trace : ExactConcreteAcceptingSlotTrace start w) :
    ∃ labels tape, SlotMicroExpansion start w labels (.accepted tape) := by
  obtain ⟨finish, path, accepts⟩ := trace
  cases finish with
  | running q tape => simp [concreteAccepting] at accepts
  | rejected => simp [concreteAccepting] at accepts
  | stuck => simp [concreteAccepting] at accepts
  | accepted tape =>
    obtain ⟨labels, expansion⟩ := exists_expansion path
    exact ⟨labels, tape, expansion⟩

theorem all_micro_card_eq {input : List Bool} {suffix : List Tape}
    (p : BoundedProgram ns 3) (hp : compile p ≠ []) (B : Nat)
    (head : Int) (z : BoundedConfig ns 3) (L R C : Nat) (tail : List Tape)
    (bounds : AllGrowthBounded p head z L R) (lengths : AllRunLengthBound p head z B)
    (hc : R + (ns - 1) ≤ C) (halt : boundedHalted z = false)
    (frame : SemanticCycleFrame input suffix)
    (hconfig : frame.config = liftConfig p z) (hcapacity : frame.capacity = C)
    (houter : frame.outer = List.replicate L MStarConcreteAlphabet.work ++ tail)
    (runtime : PassivePath frame.runtime) (budget : Nat)
    (clock : decodeBinaryClock
      (List.replicate frame.clockZeros (ulogCore clockZero) ++
        ulogCore clockOne :: frame.runtime) = some budget) (slack : B < budget) :
    Nat.card (LogicalAcceptingWords p head z) = Nat.card (RawAcceptingMicroWords frame.encode) := by
  classical
  have physical := bounded_growth_nd_physical_spec p hp B head z L R C tail bounds lengths hc
    halt frame hconfig hcapacity houter runtime budget clock slack
  have witness : ∀ leaf : LogicalAcceptingWords p head z,
      ∃ labels tape, SlotMicroExpansion frame.encode leaf.val labels (.accepted tape) := by
    intro leaf
    obtain ⟨hf, out, path, accepts⟩ := leaf.property
    exact accepting_trace_has_expansion (physical.2 leaf.val hf out path accepts)
  let f : LogicalAcceptingWords p head z → RawAcceptingMicroWords frame.encode := fun leaf =>
    ⟨Classical.choose (witness leaf), by
      obtain ⟨tape, expansion⟩ := Classical.choose_spec (witness leaf)
      exact ⟨tape, to_micro_path expansion⟩⟩
  have expands : ∀ leaf : LogicalAcceptingWords p head z,
      ∃ tape, SlotMicroExpansion frame.encode leaf.val (f leaf).val (.accepted tape) := by
    intro leaf
    exact Classical.choose_spec (witness leaf)
  have injective : Function.Injective f := by
    intro first last same
    obtain ⟨tape₁, firstExpansion⟩ := expands first
    obtain ⟨tape₂, lastExpansion⟩ := expands last
    have slots := ULogConcreteMicroExpansionInjectivity.slots_and_finish_unique
      firstExpansion lastExpansion (congrArg Subtype.val same)
    exact Subtype.ext slots.1
  have surjective : Function.Surjective f := by
    intro raw
    obtain ⟨tape, path⟩ := raw.property
    obtain ⟨w, hf, out, word, accepts, expansion⟩ := physical.1 raw.val tape path
    let leaf : LogicalAcceptingWords p head z := ⟨w, hf, out, word, accepts⟩
    refine ⟨leaf, ?_⟩
    obtain ⟨actualTape, actualExpansion⟩ := expands leaf
    have labels := word_and_finish_unique actualExpansion expansion
    exact Subtype.ext labels.1
  exact Nat.card_congr (Equiv.ofBijective f ⟨injective, surjective⟩)

end PakFixedPolyomino.ULogFiniteTapeNondeterministicMicroCounts
