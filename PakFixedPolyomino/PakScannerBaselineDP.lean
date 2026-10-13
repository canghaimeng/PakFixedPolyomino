import PakFixedPolyomino.PakScannerBaselineAutomaton

/-! # Head-budget dynamic programming for scanner baselines -/

namespace PakFixedPolyomino.PakScannerBaselineDP

open PakScannerBaselineAutomaton

inductive HeadBudget where
  | zero | one | many
  deriving DecidableEq, Repr

instance : Fintype HeadBudget :=
  Fintype.ofList [.zero, .one, .many] (by
    intro b
    cases b <;> simp)

def addHead (h : Bool) : HeadBudget → HeadBudget
  | .zero => if h then .one else .zero
  | .one => if h then .many else .one
  | .many => .many

def stateHead (s : ConcretePakScanner.State) : Bool :=
  isHeadBuffer s.centre

def compressHeadCount : ℕ → HeadBudget
  | 0 => .zero
  | 1 => .one
  | _ + 2 => .many

abbrev BudgetState := ConcretePakScanner.State × HeadBudget

def budgetStep (bit : Bool) (source target : ConcretePakScanner.State)
    (budget : HeadBudget) : Prop :=
  ConcretePakScanner.LegalScan source target bit ∧
    addHead (stateHead source) budget = budget

/-- A literal scanner prefix, with the head count compressed to three values.
The head of the top state is intentionally not charged: scanner rows charge
their source/old window, exactly as `ScannerPath.headCount`. -/
@[ext] structure PrefixPath (n k : ℕ) where
  hk : k ≤ n
  states : Fin (k + 1) → ConcretePakScanner.State
  bottom : states ⟨0, Nat.zero_lt_succ _⟩ = PakCouplingGenerated.scannerBottom
  legal : ∀ j : Fin k,
    ConcretePakScanner.LegalScan (states ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
      (states ⟨j.1 + 1, by omega⟩) (n.testBit j.1)
  budget : HeadBudget
  budget_eq : budget = compressHeadCount (∑ j : Fin k,
    if stateHead (states ⟨j.1, Nat.lt_succ_of_lt j.2⟩) then 1 else 0)

/-! The finite-cardinality development is deliberately stated through the
actual prefix object, rather than an unconstrained transfer matrix.  The
following DP is the executable recurrence corresponding to extension by one
legal scanner edge. -/

def baselineDP (n : ℕ) : Fin (n + 1) → BudgetState → ℕ :=
  fun k => Nat.rec
    (fun sb => if sb.1 = PakCouplingGenerated.scannerBottom ∧ sb.2 = .zero then 1 else 0)
    (fun i v sb => ∑ source : ConcretePakScanner.State, ∑ b : HeadBudget,
      if ConcretePakScanner.LegalScan source sb.1 (n.testBit i) ∧
          addHead (stateHead source) b = sb.2 then v (source, b) else 0)
    k.1

def baselineDPAccept (n : ℕ) : ℕ :=
  baselineDP n ⟨n, Nat.lt_succ_self _⟩ (ConcretePakScanner.topNorth, .one)

theorem baselineDP_zero (n : ℕ) (s : ConcretePakScanner.State) (b : HeadBudget) :
    baselineDP n ⟨0, Nat.zero_lt_succ _⟩ (s, b) =
      if s = PakCouplingGenerated.scannerBottom ∧ b = .zero then 1 else 0 := rfl

theorem baselineDP_succ (n i : ℕ) (hi : i + 1 ≤ n)
    (target : ConcretePakScanner.State) (b : HeadBudget) :
    baselineDP n ⟨i + 1, by omega⟩ (target, b) =
      ∑ source : ConcretePakScanner.State, ∑ old : HeadBudget,
        if ConcretePakScanner.LegalScan source target (n.testBit i) ∧
            addHead (stateHead source) old = b then
          baselineDP n ⟨i, by omega⟩ (source, old) else 0 := rfl

abbrev PrefixFibre (n k : ℕ) (target : ConcretePakScanner.State)
    (budget : HeadBudget) :=
  {P : PrefixPath n k // P.states ⟨k, Nat.lt_succ_self _⟩ = target ∧ P.budget = budget}

instance prefixPathFinite (n k : ℕ) : Finite (PrefixPath n k) := by
  classical
  apply Finite.of_injective (fun P => (P.states, P.budget))
  intro P Q h
  cases P
  cases Q
  cases h
  rfl

noncomputable instance prefixFibreFintype (n k : ℕ)
    (target : ConcretePakScanner.State) (budget : HeadBudget) :
    Fintype (PrefixFibre n k target budget) := Fintype.ofFinite _

theorem prefixFibre_zero_card (n : ℕ) (target : ConcretePakScanner.State)
    (budget : HeadBudget) :
    Fintype.card (PrefixFibre n 0 target budget) =
      if target = PakCouplingGenerated.scannerBottom ∧ budget = .zero then 1 else 0 := by
  classical
  by_cases h : target = PakCouplingGenerated.scannerBottom ∧ budget = .zero
  · rcases h with ⟨rfl, rfl⟩
    let P : PrefixPath n 0 :=
      { hk := Nat.zero_le _
        states := fun _ => PakCouplingGenerated.scannerBottom
        bottom := rfl
        legal := fun j => Fin.elim0 j
        budget := .zero
        budget_eq := by simp [compressHeadCount] }
    let Q : PrefixFibre n 0 PakCouplingGenerated.scannerBottom .zero :=
      ⟨P, rfl, rfl⟩
    have hunique : ∀ R : PrefixFibre n 0 PakCouplingGenerated.scannerBottom .zero,
        R = Q := by
      intro R
      apply Subtype.ext
      apply PrefixPath.ext
      · funext i
        have hi : i = ⟨0, Nat.zero_lt_succ _⟩ := Fin.ext (by omega)
        subst i
        exact R.1.bottom.trans Q.1.bottom.symm
      · exact R.2.2.trans Q.2.2.symm
    let e : PrefixFibre n 0 PakCouplingGenerated.scannerBottom .zero ≃ Unit :=
      { toFun := fun _ => Unit.unit
        invFun := fun _ => Q
        left_inv := fun R => (hunique R).symm
        right_inv := by intro u; cases u; rfl }
    simpa using Fintype.card_congr e
  · have hempty : IsEmpty (PrefixFibre n 0 target budget) := ⟨by
      intro R
      apply h
      refine ⟨R.2.1.symm.trans R.1.bottom, ?_⟩
      calc
        budget = R.1.budget := R.2.2.symm
        _ = compressHeadCount (∑ j : Fin 0,
            if stateHead (R.1.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩) then 1 else 0) :=
          R.1.budget_eq
        _ = .zero := by simp [compressHeadCount]⟩
    letI := hempty
    rw [if_neg h]
    exact Fintype.card_eq_zero

theorem compressHeadCount_add_head (m : ℕ) (h : Bool) :
    compressHeadCount (m + if h then 1 else 0) =
      addHead h (compressHeadCount m) := by
  cases h with
  | false =>
      cases m with
      | zero => rfl
      | succ m => cases m <;> rfl
  | true =>
      cases m with
      | zero => rfl
      | succ m => cases m <;> rfl

abbrev ExtendedPrefix (n k : ℕ) (target : ConcretePakScanner.State)
    (budget : HeadBudget) :=
  Σ source : ConcretePakScanner.State, Σ old : HeadBudget,
    {P : PrefixFibre n k source old //
      ConcretePakScanner.LegalScan source target (n.testBit k) ∧
        addHead (stateHead source) old = budget}

noncomputable instance extendedPrefixFintype (n k : ℕ)
    (target : ConcretePakScanner.State) (budget : HeadBudget) :
    Fintype (ExtendedPrefix n k target budget) := Fintype.ofFinite _

/-- Structural DP witnesses.  Unlike `PrefixPath`, the budget transition is
part of the constructor index, so no dependent finite-sum reindexing is
needed to obtain the cardinal recurrence. -/
def DPPath (n : ℕ) : ℕ → ConcretePakScanner.State → HeadBudget → Type
  | 0, target, budget =>
      {u : Unit // target = PakCouplingGenerated.scannerBottom ∧ budget = .zero }
  | k + 1, target, budget =>
      Σ source : ConcretePakScanner.State, Σ old : HeadBudget,
        {p : DPPath n k source old //
          ConcretePakScanner.LegalScan source target (n.testBit k) ∧
            addHead (stateHead source) old = budget}

noncomputable instance dpPathFintype (n k : ℕ)
    (target : ConcretePakScanner.State) (budget : HeadBudget) :
    Fintype (DPPath n k target budget) := by
  induction k generalizing target budget with
  | zero =>
      unfold DPPath
      infer_instance
  | succ k ih =>
      unfold DPPath
      infer_instance

theorem dpPath_zero_card (n : ℕ) (target : ConcretePakScanner.State)
    (budget : HeadBudget) :
    Fintype.card (DPPath n 0 target budget) =
      baselineDP n ⟨0, Nat.zero_lt_succ _⟩ (target, budget) := by
  by_cases h : target = PakCouplingGenerated.scannerBottom ∧ budget = .zero
  · change Fintype.card {u : Unit //
        target = PakCouplingGenerated.scannerBottom ∧ budget = .zero} = _
    rw [Fintype.card_subtype]
    simp [baselineDP, h]
  · change Fintype.card {u : Unit //
        target = PakCouplingGenerated.scannerBottom ∧ budget = .zero} = _
    rw [Fintype.card_subtype]
    simp [baselineDP, h]

theorem dpPath_card (n k : ℕ) (hk : k ≤ n)
    (target : ConcretePakScanner.State) (budget : HeadBudget) :
    Fintype.card (DPPath n k target budget) =
      baselineDP n ⟨k, by omega⟩ (target, budget) := by
  induction k generalizing target budget with
  | zero => exact dpPath_zero_card n target budget
  | succ k ih =>
      classical
      unfold DPPath baselineDP
      simp only [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro source _
      apply Finset.sum_congr rfl
      intro old _
      by_cases hcond : ConcretePakScanner.LegalScan source target (n.testBit k) ∧
          addHead (stateHead source) old = budget
      · simp [hcond, ih (by omega) source old]
        rfl
      · simp [hcond]

theorem dpPath_succ_card (n k : ℕ) (hk : k + 1 ≤ n)
    (target : ConcretePakScanner.State) (budget : HeadBudget) :
    Fintype.card (DPPath n (k + 1) target budget) =
      baselineDP n ⟨k + 1, by omega⟩ (target, budget) :=
  dpPath_card n (k + 1) hk target budget

/-- Read the scanner-state word encoded by a structural DP witness. -/
def DPPath.states {n : ℕ} : ∀ {k : ℕ} {target : ConcretePakScanner.State}
    {budget : HeadBudget}, DPPath n k target budget → Fin (k + 1) → ConcretePakScanner.State
  | 0, target, _, _ => fun _ => target
  | k + 1, target, _, p =>
      Fin.lastCases target (fun j => DPPath.states p.2.2.1 j)

@[simp] theorem DPPath.states_zero {n : ℕ} {target : ConcretePakScanner.State}
    {budget : HeadBudget} (p : DPPath n 0 target budget) (i : Fin 1) :
    p.states i = target := by
  cases i using Fin.cases with
  | zero => rfl
  | succ i => exact Fin.elim0 i

@[simp] theorem DPPath.states_last {n k : ℕ} {target : ConcretePakScanner.State}
    {budget : HeadBudget} (p : DPPath n (k + 1) target budget) :
    p.states (Fin.last (k + 1)) = target := by
  simp [DPPath.states]

@[simp] theorem DPPath.states_final {n k : ℕ}
    {target : ConcretePakScanner.State} {budget : HeadBudget}
    (p : DPPath n k target budget) : p.states (Fin.last k) = target := by
  cases k with
  | zero => exact p.states_zero (Fin.last 0)
  | succ k => exact p.states_last

theorem DPPath.states_bottom {n k : ℕ} {target : ConcretePakScanner.State}
    {budget : HeadBudget} (p : DPPath n k target budget) :
    p.states ⟨0, Nat.zero_lt_succ _⟩ = PakCouplingGenerated.scannerBottom := by
  induction k generalizing target budget with
  | zero =>
      exact (p.states_zero ⟨0, Nat.zero_lt_succ _⟩).trans p.2.1
  | succ k ih =>
      let zero : Fin (k + 1) := ⟨0, by omega⟩
      have hidx : (⟨0, Nat.zero_lt_succ (k + 1)⟩ : Fin (k + 2)) =
          Fin.castSucc zero := Fin.ext (by rfl)
      rw [hidx]
      simpa only [DPPath.states, Fin.lastCases_castSucc] using ih p.2.2.1

theorem DPPath.states_legal {n k : ℕ} {target : ConcretePakScanner.State}
    {budget : HeadBudget} (p : DPPath n (k + 1) target budget) :
    ConcretePakScanner.LegalScan
      (p.states ⟨k, by omega⟩) target (n.testBit k) := by
  let last : Fin (k + 1) := Fin.last k
  have hidx : (⟨k, by omega⟩ : Fin (k + 2)) = Fin.castSucc last :=
    Fin.ext (by simp [last])
  rw [hidx]
  change ConcretePakScanner.LegalScan
    (Fin.lastCases target (fun j => (p.2.2.1).states j) (Fin.castSucc last))
    target (n.testBit k)
  rw [Fin.lastCases_castSucc]
  rw [DPPath.states_final]
  exact p.2.2.2.1

@[simp] theorem DPPath.states_penultimate {n k : ℕ}
    {target : ConcretePakScanner.State} {budget : HeadBudget}
    (p : DPPath n (k + 1) target budget) :
    p.states ⟨k, by omega⟩ = p.1 := by
  let last : Fin (k + 1) := Fin.last k
  rw [show (⟨k, by omega⟩ : Fin (k + 2)) = Fin.castSucc last by
    ext
    simp [last]]
  simp only [DPPath.states, Fin.lastCases_castSucc]
  change (p.2.2.1).states (Fin.last k) = p.1
  exact (p.2.2.1).states_final

theorem DPPath.legal_at {n k : ℕ} {target : ConcretePakScanner.State}
    {budget : HeadBudget} (p : DPPath n k target budget) (j : Fin k) :
    ConcretePakScanner.LegalScan
      (p.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
      (p.states ⟨j.1 + 1, by omega⟩) (n.testBit j.1) := by
  induction k generalizing target budget with
  | zero => exact Fin.elim0 j
  | succ k ih =>
      refine Fin.lastCases ?_ (fun i => ?_) j
      · have hsource : p.states (Fin.castSucc (Fin.last k)) = p.1 := by
          simp only [DPPath.states, Fin.lastCases_castSucc, DPPath.states_final]
        have htarget : p.states (Fin.last (k + 1)) = target := p.states_final
        rw [show (⟨(Fin.last k).1, by omega⟩ : Fin (k + 2)) =
          Fin.castSucc (Fin.last k) by ext; rfl]
        rw [hsource]
        rw [show (⟨(Fin.last k).1 + 1, by omega⟩ : Fin (k + 2)) =
          Fin.last (k + 1) by ext; simp]
        rw [htarget]
        simpa using p.2.2.2.1
      · let i₁ : Fin (k + 1) := ⟨i.1 + 1, by omega⟩
        have hsource : p.states (Fin.castSucc (Fin.castSucc i)) =
            (p.2.2.1).states (Fin.castSucc i) := by
          simp only [DPPath.states, Fin.lastCases_castSucc]
        have htarget : p.states (Fin.castSucc i₁) =
            (p.2.2.1).states i₁ := by
          simp only [DPPath.states, Fin.lastCases_castSucc]
        rw [show (⟨(Fin.castSucc i).1, by omega⟩ : Fin (k + 2)) =
          Fin.castSucc (Fin.castSucc i) by ext; rfl]
        rw [hsource]
        rw [show (⟨(Fin.castSucc i).1 + 1, by omega⟩ : Fin (k + 2)) =
          Fin.castSucc i₁ by ext; rfl]
        rw [htarget]
        convert ih p.2.2.1 i using 1 <;> try rfl
        all_goals
          apply congrArg (p.2.2.1).states
          apply Fin.ext
          rfl

def headBudgetFold {n k : ℕ} {target : ConcretePakScanner.State}
    {budget : HeadBudget} (p : DPPath n k target budget) : HeadBudget :=
  match k with
  | 0 => .zero
  | k + 1 => addHead (stateHead (p.states ⟨k, by omega⟩))
      (headBudgetFold p.2.2.1)

theorem DPPath.budget_eq_fold {n k : ℕ} {target : ConcretePakScanner.State}
    {budget : HeadBudget} (p : DPPath n k target budget) :
    headBudgetFold p = budget := by
  induction k generalizing target budget with
  | zero =>
      change .zero = budget
      exact p.2.2.symm
  | succ k ih =>
      change addHead (stateHead (p.states ⟨k, by omega⟩))
          (headBudgetFold p.2.2.1) = budget
      rw [ih p.2.2.1]
      let last : Fin (k + 1) := Fin.last k
      have hidx : (⟨k, by omega⟩ : Fin (k + 2)) = Fin.castSucc last :=
        Fin.ext (by simp [last])
      rw [hidx]
      change addHead
        (stateHead (Fin.lastCases target (fun j => (p.2.2.1).states j)
          (Fin.castSucc last))) p.2.1 = budget
      rw [Fin.lastCases_castSucc]
      rw [DPPath.states_final]
      exact p.2.2.2.2

def headNatFold {n k : ℕ} {target : ConcretePakScanner.State}
    {budget : HeadBudget} (p : DPPath n k target budget) : ℕ :=
  match k with
  | 0 => 0
  | k + 1 => headNatFold p.2.2.1 +
      if stateHead p.1 then 1 else 0

theorem DPPath.headBudgetFold_eq_compress {n k : ℕ}
    {target : ConcretePakScanner.State} {budget : HeadBudget}
    (p : DPPath n k target budget) :
    headBudgetFold p = compressHeadCount (headNatFold p) := by
  induction k generalizing target budget with
  | zero => rfl
  | succ k ih =>
      rw [show headBudgetFold p = addHead (stateHead p.1)
          (headBudgetFold p.2.2.1) by
        simp [headBudgetFold, DPPath.states_penultimate]]
      rw [ih p.2.2.1]
      exact (compressHeadCount_add_head (headNatFold p.2.2.1)
        (stateHead p.1)).symm

theorem DPPath.headNatFold_eq_sum {n k : ℕ}
    {target : ConcretePakScanner.State} {budget : HeadBudget}
    (p : DPPath n k target budget) :
    headNatFold p = ∑ j : Fin k,
      if stateHead (p.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩) then 1 else 0 := by
  induction k generalizing target budget with
  | zero => simp [headNatFold]
  | succ k ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [headNatFold]
      rw [ih p.2.2.1]
      congr 1
      · apply Finset.sum_congr rfl
        intro j _
        congr 2
        apply congrArg stateHead
        let q : Fin (k + 1) := ⟨j.1, Nat.lt_succ_of_lt j.2⟩
        rw [show (⟨j.castSucc.1, Nat.lt_succ_of_lt j.castSucc.2⟩ : Fin (k + 2)) =
          Fin.castSucc q by ext; rfl]
        simp only [DPPath.states, Fin.lastCases_castSucc]
        congr
      · congr 2
        apply congrArg stateHead
        symm
        exact p.states_penultimate

theorem compressHeadCount_eq_one_iff (m : ℕ) :
    compressHeadCount m = .one ↔ m = 1 := by
  cases m with
  | zero => simp [compressHeadCount]
  | succ m =>
      cases m with
      | zero => simp [compressHeadCount]
      | succ m => simp [compressHeadCount]

def DPPath.toScannerPath {n : ℕ} (hn : 0 < n)
    (p : DPPath n n ConcretePakScanner.topNorth .one) : ScannerPath n where
  pos := hn
  states := p.states
  bottom := p.states_bottom
  top := p.states_final
  legal := p.legal_at

theorem DPPath.toScannerPath_headCount {n : ℕ} (hn : 0 < n)
    (p : DPPath n n ConcretePakScanner.topNorth .one) :
    (p.toScannerPath hn).headCount = 1 := by
  have hbudget : headBudgetFold p = .one := p.budget_eq_fold
  rw [p.headBudgetFold_eq_compress] at hbudget
  have hnat : headNatFold p = 1 :=
    (compressHeadCount_eq_one_iff (headNatFold p)).mp hbudget
  unfold ScannerPath.headCount
  change (∑ j : Fin n,
    if stateHead (p.states ⟨j.1, Nat.lt_succ_of_lt j.2⟩) then 1 else 0) = 1
  rw [← p.headNatFold_eq_sum]
  exact hnat

def DPPath.toHeadedScannerPath {n : ℕ} (hn : 0 < n)
    (p : DPPath n n ConcretePakScanner.topNorth .one) : HeadedScannerPath n :=
  ⟨p.toScannerPath hn, p.toScannerPath_headCount hn⟩

def scannerPrefixBudget {n : ℕ} (P : ScannerPath n) :
    ∀ k : ℕ, k ≤ n → HeadBudget
  | 0, _ => .zero
  | k + 1, hk =>
      addHead (stateHead (P.states ⟨k, by omega⟩))
        (scannerPrefixBudget P k (by omega))

def scannerPathToDPPathPrefix {n : ℕ} (P : ScannerPath n) :
    ∀ (k : ℕ) (hk : k ≤ n),
      DPPath n k (P.states ⟨k, Nat.lt_succ_of_le hk⟩) (scannerPrefixBudget P k hk)
  | 0, _ => ⟨Unit.unit, P.bottom, rfl⟩
  | k + 1, hk =>
      ⟨P.states ⟨k, by omega⟩, scannerPrefixBudget P k (by omega),
        ⟨scannerPathToDPPathPrefix P k (by omega), P.legal ⟨k, by omega⟩, rfl⟩⟩

theorem scannerPrefixBudget_eq_compress {n : ℕ} (P : ScannerPath n)
    (k : ℕ) (hk : k ≤ n) :
    scannerPrefixBudget P k hk = compressHeadCount (∑ j : Fin k,
      if stateHead (P.states ⟨j.1, by omega⟩) then 1 else 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Fin.sum_univ_castSucc]
      change addHead (stateHead (P.states ⟨k, by omega⟩))
          (scannerPrefixBudget P k (by omega)) = _
      rw [ih (by omega)]
      rw [compressHeadCount_add_head]
      congr 1

theorem headedScannerPath_prefixBudget_final {n : ℕ}
    (P : HeadedScannerPath n) : scannerPrefixBudget P.1 n le_rfl = .one := by
  rw [scannerPrefixBudget_eq_compress]
  apply (compressHeadCount_eq_one_iff _).mpr
  exact P.2

def DPPath.cast {n k : ℕ} {source target : ConcretePakScanner.State}
    {old budget : HeadBudget} (hs : source = target) (hb : old = budget)
    (p : DPPath n k source old) : DPPath n k target budget := by
  subst target
  subst budget
  exact p

@[simp] theorem DPPath.cast_states {n k : ℕ}
    {source target : ConcretePakScanner.State} {old budget : HeadBudget}
    (hs : source = target) (hb : old = budget) (p : DPPath n k source old)
    (i : Fin (k + 1)) : (p.cast hs hb).states i = p.states i := by
  subst target
  subst budget
  rfl

noncomputable def headedScannerPathToDPPath {n : ℕ}
    (P : HeadedScannerPath n) :
    DPPath n n ConcretePakScanner.topNorth .one := by
  let p := scannerPathToDPPathPrefix P.1 n le_rfl
  exact p.cast P.1.top (headedScannerPath_prefixBudget_final P)

theorem scannerPathToDPPathPrefix_states {n : ℕ} (P : ScannerPath n) :
    ∀ (k : ℕ) (hk : k ≤ n) (i : Fin (k + 1)),
      (scannerPathToDPPathPrefix P k hk).states i =
        P.states ⟨i.1, by omega⟩ := by
  intro k
  induction k with
  | zero =>
      intro hk i
      have hi : i = ⟨0, Nat.zero_lt_succ _⟩ := Fin.ext (by omega)
      subst i
      simp [scannerPathToDPPathPrefix, DPPath.states, P.bottom]
  | succ k ih =>
      intro hk i
      refine Fin.lastCases ?_ ?_ i
      · simp [scannerPathToDPPathPrefix, DPPath.states]
      · intro j
        simp only [scannerPathToDPPathPrefix, DPPath.states,
          Fin.lastCases_castSucc]
        exact ih (by omega) j

theorem dpPath_toHeaded_right_inverse {n : ℕ} (P : HeadedScannerPath n) :
    (headedScannerPathToDPPath P).toHeadedScannerPath P.1.pos = P := by
  rcases P with ⟨P, hP⟩
  apply Subtype.ext
  let A := (headedScannerPathToDPPath (⟨P, hP⟩ : HeadedScannerPath n)).toScannerPath P.pos
  change A = P
  have hs : A.states = P.states := by
    funext i
    simpa [A, DPPath.toScannerPath, headedScannerPathToDPPath] using
      scannerPathToDPPathPrefix_states P n le_rfl i
  have hinj : Function.Injective (fun Q : ScannerPath n => Q.states) := by
    intro Q R h
    cases Q
    cases R
    cases h
    rfl
  exact hinj hs

theorem DPPath.eq_of_states_eq {n k : ℕ}
    {target : ConcretePakScanner.State} {budget : HeadBudget}
    (p q : DPPath n k target budget) (hstates : p.states = q.states) : p = q := by
  induction k generalizing target budget with
  | zero =>
      apply Subtype.ext
      cases p.1
      cases q.1
      rfl
  | succ k ih =>
      rcases p with ⟨ps, po, ⟨pp, hpcond⟩⟩
      rcases q with ⟨qs, qo, ⟨qp, hqcond⟩⟩
      have hsource : ps = qs := by
        have h := congrFun hstates ⟨k, by omega⟩
        let last : Fin (k + 1) := Fin.last k
        have hidx : (⟨k, by omega⟩ : Fin (k + 2)) = Fin.castSucc last := by
          apply Fin.ext
          simp [last]
        rw [hidx] at h
        simp only [DPPath.states, Fin.lastCases_castSucc] at h
        exact pp.states_final.symm.trans (h.trans qp.states_final)
      cases hsource
      have hpredStates : pp.states = qp.states := by
        funext i
        have h := congrFun hstates (Fin.castSucc i)
        simpa only [DPPath.states, Fin.lastCases_castSucc] using h
      have hold : po = qo := by
        calc
          po = headBudgetFold pp := pp.budget_eq_fold.symm
          _ = compressHeadCount (headNatFold pp) :=
            pp.headBudgetFold_eq_compress
          _ = compressHeadCount (headNatFold qp) := by
            congr 1
            rw [pp.headNatFold_eq_sum, qp.headNatFold_eq_sum, hpredStates]
          _ = headBudgetFold qp := qp.headBudgetFold_eq_compress.symm
          _ = qo := qp.budget_eq_fold
      cases hold
      have hpred : pp = qp := ih pp qp hpredStates
      subst qp
      rfl

theorem dpPath_toHeaded_left_inverse {n : ℕ} (hn : 0 < n)
    (p : DPPath n n ConcretePakScanner.topNorth .one) :
    headedScannerPathToDPPath (p.toHeadedScannerPath hn) = p := by
  apply DPPath.eq_of_states_eq
  funext i
  unfold headedScannerPathToDPPath
  rw [DPPath.cast_states]
  simpa [DPPath.toHeadedScannerPath, DPPath.toScannerPath] using
    scannerPathToDPPathPrefix_states (p.toScannerPath hn) n le_rfl i

noncomputable def dpPathEquivHeadedScannerPath (n : ℕ) (hn : 0 < n) :
    DPPath n n ConcretePakScanner.topNorth .one ≃ HeadedScannerPath n where
  toFun := DPPath.toHeadedScannerPath hn
  invFun := headedScannerPathToDPPath
  left_inv := dpPath_toHeaded_left_inverse hn
  right_inv := dpPath_toHeaded_right_inverse

theorem baselineDPAccept_eq_baselineCount (n : ℕ) (hn : 0 < n) :
    baselineDPAccept n = baselineCount n := by
  unfold baselineDPAccept baselineCount SlotZeroScannerPaths
  rw [← dpPath_card n n le_rfl ConcretePakScanner.topNorth .one]
  exact Fintype.card_congr (dpPathEquivHeadedScannerPath n hn)

/-! ## Compression of the long all-zero bit suffix -/

abbrev DPVector := BudgetState → ℕ

def initialDPVector : DPVector := fun sb =>
  if sb.1 = PakCouplingGenerated.scannerBottom ∧ sb.2 = .zero then 1 else 0

def transferVector (bit : Bool) (v : DPVector) : DPVector := fun sb =>
  ∑ source : ConcretePakScanner.State, ∑ old : HeadBudget,
    if ConcretePakScanner.LegalScan source sb.1 bit ∧
        addHead (stateHead source) old = sb.2 then v (source, old) else 0

def baselineBitFold (n : ℕ) : ℕ → DPVector
  | 0 => initialDPVector
  | k + 1 => transferVector (n.testBit k) (baselineBitFold n k)

theorem baselineBitFold_eq_baselineDP (n k : ℕ) (hk : k ≤ n) :
    baselineBitFold n k = baselineDP n ⟨k, by omega⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change transferVector (n.testBit k) (baselineBitFold n k) = _
      rw [ih (by omega)]
      rfl

def falseTransferIter : ℕ → DPVector → DPVector
  | 0, v => v
  | r + 1, v => falseTransferIter r (transferVector false v)

theorem testBit_false_of_size_le (n i : ℕ) (h : n.size ≤ i) :
    n.testBit i = false := by
  apply Nat.testBit_eq_false_of_lt
  exact Nat.lt_of_lt_of_le (Nat.lt_size_self n)
    (Nat.pow_le_pow_right (by decide) h)

theorem baselineBitFold_zero_tail (n k r : ℕ) (hk : n.size ≤ k) :
    baselineBitFold n (k + r) = falseTransferIter r (baselineBitFold n k) := by
  induction r generalizing k with
  | zero => rfl
  | succ r ih =>
      rw [show k + (r + 1) = (k + 1) + r by omega]
      rw [ih (k + 1) (by omega)]
      rw [show baselineBitFold n (k + 1) =
          transferVector (n.testBit k) (baselineBitFold n k) by rfl]
      rw [testBit_false_of_size_le n k hk]
      rfl

def baselineCompressed (n : ℕ) : ℕ :=
  (falseTransferIter (n - n.size) (baselineBitFold n n.size))
    (ConcretePakScanner.topNorth, .one)

theorem baselineCompressed_eq_baselineDPAccept (n : ℕ) :
    baselineCompressed n = baselineDPAccept n := by
  have hsize : n.size ≤ n := Nat.size_le.mpr n.lt_two_pow_self
  have hsum : n.size + (n - n.size) = n := Nat.add_sub_of_le hsize
  unfold baselineCompressed baselineDPAccept
  rw [← baselineBitFold_zero_tail n n.size (n - n.size) le_rfl]
  rw [hsum]
  exact congrFun (baselineBitFold_eq_baselineDP n n le_rfl)
    (ConcretePakScanner.topNorth, .one)

theorem baselineCompressed_eq_baselineCount (n : ℕ) (hn : 0 < n) :
    baselineCompressed n = baselineCount n :=
  (baselineCompressed_eq_baselineDPAccept n).trans
    (baselineDPAccept_eq_baselineCount n hn)

end PakFixedPolyomino.PakScannerBaselineDP
