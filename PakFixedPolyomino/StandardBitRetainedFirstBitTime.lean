import PakFixedPolyomino.StandardBitRetainedFirstJoin
import PakFixedPolyomino.StandardBitPairSanitize

/-! Total initialized physical pairing with a computed word and retained
FIRST field. Valid input is unchanged by sanitization. Every literal first
field bit, including highzeros, is copied; malformed input has an empty field.
This is an ALLraw standard bit-time compiler with only a source Poly premise. -/
namespace PakFixedPolyomino.StandardBitRetainedFirstBitTime
open StandardNondeterministicMachine StandardBitTime StandardBitMetric
open StandardBitRetainedFirstJoin
open StandardBitRetainedFirstCleanup (stageFuel stageFuel_le)
open StandardBitPairSanitize (sanitize sanitize_pair sanitize_none sanitize_valid sanitize_length)
open StandardBitMachineComposition (compose compose_exact encodeConfigB)
open StandardBitTimeComposition (eval_mono)

def paired (f : List Bool → List Bool) (r : List Bool) : List Bool :=
  match unpairBits r with
  | none => []
  | some z => pairBits (f r) z.1
def lifting (f : List Bool → List Bool) : List Bool → List Bool := paired f ∘ sanitize

theorem lifting_pair (f : List Bool → List Bool) (x y : List Bool) :
    lifting f (pairBits x y)=pairBits (f (pairBits x y)) x := by
  simp [lifting,paired,sanitize_pair]

theorem lifting_none (f : List Bool → List Bool) (r : List Bool) (hr : unpairBits r=none) :
    lifting f r=pairBits (f [false]) [] := by
  simp [lifting,paired,sanitize_none r hr,unpairBits,pairBits]

noncomputable def pairBound (q : Polynomial Nat) : Polynomial Nat :=
  q+Polynomial.C 2*Polynomial.X+Polynomial.C 5+
    Polynomial.C 64*(Polynomial.C 2*Polynomial.X+q+Polynomial.C 2)*
      (Polynomial.C 2*Polynomial.X+q+Polynomial.C 2)

theorem pairBound_eval (q : Polynomial Nat) (n : Nat) :
    (pairBound q).eval n=2*n+q.eval n+5+64*(2*n+q.eval n+2)*(2*n+q.eval n+2) := by
  simp only [pairBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  ring

noncomputable def totalBound (p q : Polynomial Nat) : Polynomial Nat :=
  p+Polynomial.C 1+(pairBound q).comp (Polynomial.X+Polynomial.C 1)

theorem totalBound_eval (p q : Polynomial Nat) (n : Nat) :
    (totalBound p q).eval n=p.eval n+1+(pairBound q).eval (n+1) := by
  simp [totalBound,Polynomial.eval_comp]

theorem lifting_polyBitTime (f : List Bool → List Bool) (hf : PolyBitTime f) :
    PolyBitTime (lifting f) := by
  obtain ⟨ns,nt,M,q,hM⟩ := hf
  obtain ⟨ss,st,S,p,hS⟩ := StandardBitPairSanitize.sanitize_polyBitTime
  refine ⟨ss+((ns+4)+30+2)+2,st+4*(2*(4*nt))+3,compose S (pairMachine M),totalBound p q,?_⟩
  intro raw
  obtain ⟨s,outS,hs,hrS,hoS⟩ := hS raw
  change s≤p.eval raw.length at hs
  let r := sanitize raw
  obtain ⟨x,y,he⟩ := sanitize_valid raw
  change r=pairBits x y at he
  obtain ⟨n,outM,hn,hrM,hoM⟩ := hM r
  change n≤q.eval r.length at hn
  have hlen := ComputesWithin.output_length M f (fun k => q.eval k) hM r
  have hxy : x.length+y.length≤r.length := by
    have h := congrArg List.length he
    rw [pairBits_length] at h
    omega
  have hl : x.length+y.length+(f r).length+1≤2*r.length+q.eval r.length+2 := by omega
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul_left 64 hl) hl
  have hstage := stageFuel_le x y (f r)
  let nPair := (2*r.length+4+n)+1+stageFuel x y (f r)
  have htime : nPair≤(pairBound q).eval r.length := by
    rw [pairBound_eval]
    dsimp [nPair]
    omega
  have hsource : run M (ticks n) (initial M (pairBits x y))=some outM := by
    simpa only [← he] using hrM
  have hpair : run (pairMachine M) (ticks nPair) (initial (pairMachine M) r)=
      some (pairFinal M (pairBits (f r) x)) := by
    simpa only [← he] using initialized_pair_run M x y (f r) n outM hsource hoM
  have hvalue : paired f r=pairBits (f r) x := by simp only [paired,he,unpair_pairBits]
  have hout : Output (pairMachine M) (paired f r) (pairFinal M (pairBits (f r) x)) := by
    rw [hvalue]
    exact pair_output M _
  have hcompiled := compose_exact S (pairMachine M) sanitize (paired f) raw s nPair outS
    (pairFinal M (pairBits (f r) x)) hrS hoS hpair hout
  refine ⟨s+1+nPair,encodeConfigB (nsA:=ss) (ntA:=st) (pairMachine M)
    (pairFinal M (pairBits (f r) x)),?_,hcompiled.1,hcompiled.2⟩
  change s+1+nPair≤(totalBound p q).eval raw.length
  rw [totalBound_eval]
  have hmono : (pairBound q).eval r.length≤(pairBound q).eval (raw.length+1) :=
    eval_mono _ (sanitize_length raw)
  omega

theorem lifting_spec (f : List Bool → List Bool) (hf : PolyBitTime f) :
    PolyBitTime (lifting f) ∧
    (∀ x y, lifting f (pairBits x y)=pairBits (f (pairBits x y)) x) ∧
    (∀ r, unpairBits r=none → lifting f r=pairBits (f [false]) []) :=
  ⟨lifting_polyBitTime f hf,lifting_pair f,lifting_none f⟩

end PakFixedPolyomino.StandardBitRetainedFirstBitTime
