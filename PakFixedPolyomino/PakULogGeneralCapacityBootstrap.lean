import PakFixedPolyomino.PakCopierReserveLowerBound
import PakFixedPolyomino.PakULogCapacityThreshold

/-! # Bootstrap from a general physical copier capacity -/

namespace PakFixedPolyomino.PakULogGeneralCapacityBootstrap

open ULogAlphabet ULogProgram ULogBootstrapExecution

def bootstrapWorkspaceOverhead (input : List Bool) : ℕ :=
  match input with
  | [] => 7
  | _ :: _ => 6

def generalBootstrapTail (input : List Bool) (physicalCapacity : ℕ) :
    List ULogProgram.Tape :=
  List.replicate (physicalCapacity - bootstrapWorkspaceOverhead input)
    MStarConcreteAlphabet.work

def generalSemanticCapacity (input : List Bool) (physicalCapacity : ℕ) : ℕ :=
  (generalBootstrapTail input physicalCapacity).length + 2

def generalCapacityCoreZipper (x : ConcretePakSide.Word)
    (physicalCapacity : ℕ) :
    MStarParserExecution.Zipper ULogProgram.Tape :=
  ⟨[], MStarConcreteAlphabet.work,
    List.replicate (PakOuterULogBridge.copiedCoreRadius x)
        MStarConcreteAlphabet.work ++
      x.map ULogProgram.bitTape ++
        List.replicate physicalCapacity MStarConcreteAlphabet.work⟩

theorem physicalCapacity_eq_runtimeWorkspace
    (input : List Bool) (physicalCapacity : ℕ)
    (hcapacity : bootstrapWorkspaceOverhead input ≤ physicalCapacity) :
    List.replicate physicalCapacity MStarConcreteAlphabet.work =
      MStarConcreteAlphabet.work ::
        payloadRuntimeWorkspace input
          (generalBootstrapTail input physicalCapacity) := by
  cases input with
  | nil =>
      change 7 ≤ physicalCapacity at hcapacity
      rw [show physicalCapacity = 7 + (physicalCapacity - 7) by omega,
        List.replicate_add]
      simp [bootstrapWorkspaceOverhead, generalBootstrapTail,
        payloadRuntimeWorkspace, initializationWorkspace,
        List.replicate_succ]
  | cons b bs =>
      change 6 ≤ physicalCapacity at hcapacity
      rw [show physicalCapacity = 6 + (physicalCapacity - 6) by omega,
        List.replicate_add]
      simp [bootstrapWorkspaceOverhead, generalBootstrapTail,
        payloadRuntimeWorkspace, initializationWorkspace,
        List.replicate_succ]

theorem generalCapacityCoreZipper_eq_bootstrap
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (physicalCapacity : ℕ)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (hcapacity : bootstrapWorkspaceOverhead input ≤ physicalCapacity) :
    generalCapacityCoreZipper x physicalCapacity =
      ⟨[], MStarConcreteAlphabet.work,
        List.replicate (PakOuterULogBridge.copiedCoreRadius x)
            MStarConcreteAlphabet.work ++
          (ULogBytecode.encodeProgram rules ++
            ULogBytecode.encodePayload input padding).map ULogProgram.bitTape ++
          MStarConcreteAlphabet.work ::
            payloadRuntimeWorkspace input
              (generalBootstrapTail input physicalCapacity)⟩ := by
  subst x
  apply MStarParserExecution.Zipper.ext
  · rfl
  · rfl
  · simp only [generalCapacityCoreZipper]
    rw [physicalCapacity_eq_runtimeWorkspace input physicalCapacity hcapacity]

def generalCapacitySemanticFrame
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (physicalCapacity : ℕ) :
    SemanticCycleFrame input ([] : List ULogProgram.Tape) :=
  bootstrapSemanticFrame rules input padding
    (generalSemanticCapacity input physicalCapacity)
    (List.replicate (PakOuterULogBridge.copiedCoreRadius x - 1)
      MStarConcreteAlphabet.work)

theorem generalCapacitySemanticFrame_encode_eq
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (physicalCapacity : ℕ) :
    (generalCapacitySemanticFrame x rules input padding physicalCapacity).encode =
      semanticCycleEncoding input
        (clockCellsBefore
          ((ULogSemantics.startFrom rules input).right.map payloadNat)
          padding.length [ulogCore clockSep])
        2
        (List.replicate (PakOuterULogBridge.copiedCoreRadius x)
          MStarConcreteAlphabet.work)
        (generalBootstrapTail input physicalCapacity)
        (ULogSemantics.startFrom rules input) := by
  have hR := PakOuterULogBridge.copiedCoreRadius_ge_256 x
  let R := PakOuterULogBridge.copiedCoreRadius x
  have houter : MStarConcreteAlphabet.work ::
      List.replicate (R - 1) MStarConcreteAlphabet.work =
      List.replicate R MStarConcreteAlphabet.work := by
    have heq : R = (R - 1) + 1 := by omega
    rw [heq, List.replicate_succ]
    rfl
  have hcap : generalSemanticCapacity input physicalCapacity - 2 =
      (generalBootstrapTail input physicalCapacity).length := by
    unfold generalSemanticCapacity
    omega
  have hwork : List.replicate
        (generalSemanticCapacity input physicalCapacity - 2)
        MStarConcreteAlphabet.work =
      generalBootstrapTail input physicalCapacity := by
    rw [hcap]
    simp [generalBootstrapTail]
  simp [generalCapacitySemanticFrame, bootstrapSemanticFrame,
    SemanticCycleFrame.encode, semanticCycleEncoding, stateWorkspace,
    ULogSemantics.startFrom, ULogSemantics.startCode, houter, hwork, R,
    List.append_assoc]

theorem generalCapacity_reaches_semanticFrame
    (x : ConcretePakSide.Word) (rules : List ULogBytecode.RuleCode)
    (input padding : List Bool) (physicalCapacity : ℕ)
    (hword : x = ULogBytecode.encodeProgram rules ++
      ULogBytecode.encodePayload input padding)
    (hcapacity : bootstrapWorkspaceOverhead input ≤ physicalCapacity) :
    Reaches (.running ULogControl.qStart
        (generalCapacityCoreZipper x physicalCapacity))
      (generalCapacitySemanticFrame x rules input padding physicalCapacity).encode := by
  rw [generalCapacityCoreZipper_eq_bootstrap x rules input padding
    physicalCapacity hword hcapacity]
  rw [generalCapacitySemanticFrame_encode_eq]
  simpa [ULogControl.qStart] using
    (reaches_bootstrap_semanticStart
      (PakOuterULogBridge.copiedCoreRadius x) rules input padding []
        (generalBootstrapTail input physicalCapacity))

theorem rawGeneralCapacityGroupZipper_eq_framed
    (x : ConcretePakSide.Word) (physicalCapacity : ℕ)
    (junk external : List MStarCopierMicrocode.ConcreteTape) :
    PakCopierReserveLowerBound.rawGeneralCapacityGroupZipper x
        physicalCapacity junk external =
      PakOuterULogBridge.frameCoreZipper
        (PakCopierReserveLowerBound.rawGeneralCapacityGroupZipper x
          physicalCapacity junk external).leftRev
        (.markR :: external)
        (generalCapacityCoreZipper x physicalCapacity) := by
  have hR : MStarCopierExecution.iteratedGroupWidth x.length 256 =
      PakOuterULogBridge.copiedCoreRadius x := by
    rw [MStarCopierExecution.copier_width_eq_time_bound]
    rfl
  have hmap : x.map MStarCopierExecution.coreBit =
      x.map (MStarOuterProgram.Tape.core ∘ ULogProgram.bitTape) := by
    apply List.map_congr_left
    intro b hb
    cases b <;> rfl
  apply MStarParserExecution.Zipper.ext
  · rfl
  · rfl
  · simp [PakCopierReserveLowerBound.rawGeneralCapacityGroupZipper,
      generalCapacityCoreZipper, PakOuterULogBridge.frameCoreZipper,
      hR, hmap,
      List.map_append, List.map_replicate, List.append_assoc]

end PakFixedPolyomino.PakULogGeneralCapacityBootstrap
