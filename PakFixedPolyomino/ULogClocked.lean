import PakFixedPolyomino.ULogCompiler
import Mathlib.Tactic

/-!
# Clocked universal semantic machine

Padding after the framed payload supplies an exponential step budget.  The
clocked wrapper decrements that budget once per simulated bytecode transition
and forces a rejecting halt at zero.  Hence extra outer tableau time cannot
create late accepting paths.
-/

namespace PakFixedPolyomino.ULogClocked

open ULogBytecode ULogSemantics

structure Config where
  base : ULogSemantics.Config
  remaining : ℕ
  deriving DecidableEq, Repr

def halted (c : Config) : Bool :=
  ULogSemantics.halted c.base || decide (c.remaining = 0)

def accepting (c : Config) : Bool := ULogSemantics.accepting c.base

theorem accepting_halted {c : Config} (h : accepting c = true) :
    halted c = true := by
  have hb := ULogSemantics.accepting_halted h
  simp [halted, hb]

def next (c : Config) : List Config :=
  if ULogSemantics.halted c.base then []
  else match c.remaining with
    | 0 => []
    | n + 1 => (ULogSemantics.next c.base).map fun q => ⟨q, n⟩

def start (x : BitString) : Config :=
  match decodeProgramPrefix x with
  | none => ⟨⟨[], rejectCode, [], blankCode, []⟩, 0⟩
  | some (program, payload) =>
      match decodePayloadWithPadding payload with
      | none => ⟨⟨program, rejectCode, [], blankCode, []⟩, 0⟩
      | some (input, paddingLength) =>
          ⟨ULogSemantics.startFrom program input, 2 ^ paddingLength⟩

@[simp] theorem next_length_le_two (c : Config) : (next c).length ≤ 2 := by
  unfold next
  split
  · simp
  · cases c.remaining with
    | zero => simp
    | succ n =>
        simp only [List.length_map]
        exact ULogSemantics.next_length_le_two c.base

def machine : BinaryNondeterministicMachine where
  Config := Config
  start := start
  next := next
  halt := halted
  accept := accepting
  accept_halts := fun _ h => accepting_halted h
  binary_branching := next_length_le_two

@[simp] theorem halted_zero (c : ULogSemantics.Config) :
    halted ⟨c, 0⟩ = true := by
  simp [halted]

theorem acceptingPaths_exact (t : ℕ) (c : ULogSemantics.Config) :
    machine.acceptingPaths t ⟨c, t⟩ =
      ULogSemantics.machine.acceptingPaths t c := by
  induction t generalizing c with
  | zero =>
      simp only [BinaryNondeterministicMachine.acceptingPaths]
      simp only [machine, halted_zero, if_true, accepting,
        ULogSemantics.machine]
      by_cases ha : ULogSemantics.accepting c = true
      · have hh := ULogSemantics.accepting_halted ha
        simp [ha, hh]
      · have haf : ULogSemantics.accepting c = false := by
          cases hv : ULogSemantics.accepting c <;> simp_all
        by_cases hh : ULogSemantics.halted c = true <;> simp [ha, haf, hh]
  | succ t ih =>
      simp only [BinaryNondeterministicMachine.acceptingPaths]
      simp only [machine, accepting, ULogSemantics.machine]
      by_cases hh : ULogSemantics.halted c = true
      · simp [halted, hh]
        rfl
      · have hhf : ULogSemantics.halted c = false := by
          cases hv : ULogSemantics.halted c <;> simp_all
        simp only [halted, hhf, Bool.false_or, Nat.succ_ne_zero,
          decide_false, Bool.false_eq_true, if_false]
        simp only [next, hhf, Bool.false_eq_true, if_false,
          List.map_map, Function.comp_def]
        apply congrArg List.sum
        apply List.map_congr_left
        intro q hq
        simpa [machine, ULogSemantics.machine] using ih q

theorem acceptingPaths_extra (t extra : ℕ)
    (c : ULogSemantics.Config) :
    machine.acceptingPaths (t + extra) ⟨c, t⟩ =
      ULogSemantics.machine.acceptingPaths t c := by
  induction t generalizing c with
  | zero =>
      simp only [Nat.zero_add]
      have hz : machine.halt (⟨c, 0⟩ : Config) = true := by
        simp [machine, halted]
      by_cases ha : ULogSemantics.accepting c = true
      · have hbase := ULogSemantics.accepting_halted ha
        rw [BinaryNondeterministicMachine.acceptingPaths_halt_accept
          machine hz ha]
        rw [BinaryNondeterministicMachine.acceptingPaths_halt_accept
          ULogSemantics.machine hbase ha]
      · have haf : ULogSemantics.accepting c = false := by
          cases hv : ULogSemantics.accepting c <;> simp_all
        rw [BinaryNondeterministicMachine.acceptingPaths_halt_reject
          machine hz haf]
        simp [BinaryNondeterministicMachine.acceptingPaths,
          ULogSemantics.machine, haf]
  | succ t ih =>
      rw [Nat.succ_add]
      simp only [BinaryNondeterministicMachine.acceptingPaths]
      simp only [machine, accepting, ULogSemantics.machine]
      by_cases hh : ULogSemantics.halted c = true
      · simp [halted, hh]
        rfl
      · have hhf : ULogSemantics.halted c = false := by
          cases hv : ULogSemantics.halted c <;> simp_all
        simp only [halted, hhf, Bool.false_or, Nat.succ_ne_zero,
          decide_false, Bool.false_eq_true, if_false]
        simp only [next, hhf, Bool.false_eq_true, if_false,
          List.map_map, Function.comp_def]
        apply congrArg List.sum
        apply List.map_congr_left
        intro q hq
        simpa [machine, ULogSemantics.machine] using ih q

def encodePaddedInstance {ns nt : ℕ}
    (p : ULogCompiler.BoundedProgram ns nt)
    (input padding : BitString) : BitString :=
  encodeProgram (ULogCompiler.compile p) ++ encodePayload input padding

@[simp] theorem length_encodePaddedInstance {ns nt : ℕ}
    (p : ULogCompiler.BoundedProgram ns nt)
    (input padding : BitString) :
    (encodePaddedInstance p input padding).length =
      (encodeProgram (ULogCompiler.compile p)).length +
        2 * input.length + padding.length + 1 := by
  simp [encodePaddedInstance, List.length_append]
  omega

def decodeUniversalInput (bits : BitString) : Option BitString := do
  let (_, payload) ← decodeProgramPrefix bits
  decodePayload payload

@[simp] theorem decodeUniversalInput_encodePaddedInstance {ns nt : ℕ}
    (p : ULogCompiler.BoundedProgram ns nt)
    (input padding : BitString) :
    decodeUniversalInput (encodePaddedInstance p input padding) = some input := by
  unfold decodeUniversalInput encodePaddedInstance
  rw [decodeProgramPrefix_encode_prefix]
  exact decodePayload_encode input padding

theorem encodePaddedInstance_injective {ns nt : ℕ}
    (p : ULogCompiler.BoundedProgram ns nt)
    (padding : BitString → BitString) :
    Function.Injective (fun input => encodePaddedInstance p input (padding input)) := by
  intro x y h
  change encodePaddedInstance p x (padding x) =
    encodePaddedInstance p y (padding y) at h
  have hx := decodeUniversalInput_encodePaddedInstance p x (padding x)
  have hy := decodeUniversalInput_encodePaddedInstance p y (padding y)
  rw [h, hy] at hx
  exact Option.some.inj hx.symm

@[simp] theorem start_encodePaddedInstance {ns nt : ℕ}
    (p : ULogCompiler.BoundedProgram ns nt)
    (qStart : Fin ns) (zero one blank : Fin nt)
    (hq : qStart.1 = ULogSemantics.startCode)
    (hzero : zero.1 = 0) (hone : one.1 = 1)
    (hblank : blank.1 = ULogSemantics.blankCode)
    (input padding : BitString) :
    start (encodePaddedInstance p input padding) =
      ⟨ULogCompiler.liftConfig p
          (ULogCompiler.boundedInitial qStart zero one blank input),
        2 ^ padding.length⟩ := by
  unfold start encodePaddedInstance
  rw [decodeProgramPrefix_encode_prefix]
  change (match decodePayloadWithPadding (encodePayload input padding) with
    | none =>
        Config.mk
          (ULogSemantics.Config.mk (ULogCompiler.compile p) rejectCode
            [] blankCode []) 0
    | some (input, paddingLength) =>
        Config.mk (ULogSemantics.startFrom (ULogCompiler.compile p) input)
          (2 ^ paddingLength)) = _
  rw [decodePayloadWithPadding_encode]
  change Config.mk (ULogSemantics.startFrom (ULogCompiler.compile p) input)
      (2 ^ padding.length) =
    Config.mk (ULogCompiler.liftConfig p
      (ULogCompiler.boundedInitial qStart zero one blank input))
      (2 ^ padding.length)
  have hbase := ULogCompiler.liftConfig_boundedInitial p qStart zero one blank
    hq hzero hone hblank input
  have hstart : ULogSemantics.start (ULogCompiler.encodeInstance p input) =
      ULogSemantics.startFrom (ULogCompiler.compile p) input := by
    unfold ULogSemantics.start ULogCompiler.encodeInstance
    rw [decodeProgramPrefix_encode_prefix]
    change (match decodePayload (encodePayload input []) with
      | none => ULogSemantics.Config.mk (ULogCompiler.compile p)
          rejectCode [] blankCode []
      | some input => ULogSemantics.startFrom (ULogCompiler.compile p) input) = _
    rw [decodePayload_encode]
  exact congrArg (fun base => Config.mk base (2 ^ padding.length))
    (hbase.trans hstart).symm

/-- Padding fixes the exact simulated clock while arbitrary additional outer
tableau time is harmless because the wrapper is already halted. -/
theorem acceptingPaths_paddedInstance {ns nt : ℕ}
    (p : ULogCompiler.BoundedProgram ns nt)
    (qStart : Fin ns) (zero one blank : Fin nt)
    (hq : qStart.1 = ULogSemantics.startCode)
    (hzero : zero.1 = 0) (hone : one.1 = 1)
    (hblank : blank.1 = ULogSemantics.blankCode)
    (input padding : BitString) (extra : ℕ) :
    machine.acceptingPaths (2 ^ padding.length + extra)
        (start (encodePaddedInstance p input padding)) =
      (ULogCompiler.boundedMachine p blank
        (ULogCompiler.boundedInitial qStart zero one blank)).acceptingPaths
          (2 ^ padding.length)
          (ULogCompiler.boundedInitial qStart zero one blank input) := by
  rw [start_encodePaddedInstance p qStart zero one blank hq hzero hone
    hblank input padding]
  rw [acceptingPaths_extra]
  exact ULogCompiler.acceptingPaths_liftConfig p blank hblank
    (ULogCompiler.boundedInitial qStart zero one blank)
    (2 ^ padding.length) _

def universalClock (n : ℕ) : ℕ := 2 ^ n

def universalCount (x : BitString) : ℕ :=
  machine.countOn universalClock x

theorem universalClock_exponential : ExponentialClock universalClock := by
  refine ⟨Polynomial.X, ?_⟩
  intro n
  simp [universalClock]

theorem universalCount_paddedInstance {ns nt : ℕ}
    (p : ULogCompiler.BoundedProgram ns nt)
    (qStart : Fin ns) (zero one blank : Fin nt)
    (hq : qStart.1 = ULogSemantics.startCode)
    (hzero : zero.1 = 0) (hone : one.1 = 1)
    (hblank : blank.1 = ULogSemantics.blankCode)
    (input padding : BitString) :
    universalCount (encodePaddedInstance p input padding) =
      (ULogCompiler.boundedMachine p blank
        (ULogCompiler.boundedInitial qStart zero one blank)).acceptingPaths
          (2 ^ padding.length)
          (ULogCompiler.boundedInitial qStart zero one blank input) := by
  let encoded := encodePaddedInstance p input padding
  have hlen : padding.length ≤ encoded.length := by
    simp [encoded, encodePaddedInstance, encodePayload, encodeNatField]
    omega
  have hpow : 2 ^ padding.length ≤ 2 ^ encoded.length := by
    exact Nat.pow_le_pow_right (by omega) hlen
  have hshape : 2 ^ encoded.length =
      2 ^ padding.length + (2 ^ encoded.length - 2 ^ padding.length) := by
    omega
  unfold universalCount BinaryNondeterministicMachine.countOn universalClock
  change machine.acceptingPaths (2 ^ encoded.length) (start encoded) = _
  rw [hshape]
  exact acceptingPaths_paddedInstance p qStart zero one blank hq hzero hone
    hblank input padding (2 ^ encoded.length - 2 ^ padding.length)

end PakFixedPolyomino.ULogClocked
