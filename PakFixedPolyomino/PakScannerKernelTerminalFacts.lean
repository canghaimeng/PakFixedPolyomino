import PakFixedPolyomino.PakScannerBaselineAutomaton
import Mathlib.Tactic

/-! Kernel-only terminal facts for the literal six-clause scanner table.
Structural clause cases; not BIT-time and not the slot-zero bijection. -/

namespace PakFixedPolyomino.PakScannerKernelTerminalFacts

open ConcretePakScanner
open PakScannerBaselineAutomaton

lemma legalClause_source_phase {c : Clause} {s t : State} {b : Bool}
    (h : LegalClause c s t b) :
    s.phase = .bot ∨ s.phase = .mid ∨ s.phase = .top := by
  cases c
  · exact Or.inl h.2.1
  · exact Or.inr (Or.inl h.2.1)
  · exact Or.inr (Or.inl h.2.1)
  · exact Or.inr (Or.inl h.2.1)
  · exact Or.inr (Or.inl h.2.1)
  · exact Or.inr (Or.inr h.2.1)

lemma legalClause_target_phase {c : Clause} {s t : State} {b : Bool}
    (h : LegalClause c s t b) :
    t.phase = .mid ∨ t.phase = .top ∨ t.phase = .cap := by
  cases c
  · exact Or.inl h.2.2.2.2.2.1
  · exact Or.inl h.2.2.1
  · exact Or.inl h.2.2.1
  · exact Or.inl h.2.2.1
  · exact Or.inr (Or.inl h.2.2.1)
  · exact Or.inr (Or.inr h.2.2.1)

theorem no_clause_from_cap :
    ∀ (s t : State) (b : Bool), s.phase = .cap → ¬ LegalScan s t b := by
  intro s t b hs ⟨c, hc⟩
  rcases legalClause_source_phase hc with h | h | h
  · rw [hs] at h; cases h
  · rw [hs] at h; cases h
  · rw [hs] at h; cases h

theorem no_clause_to_bot :
    ∀ (s t : State) (b : Bool), t.phase = .bot → ¬ LegalScan s t b := by
  intro s t b ht ⟨c, hc⟩
  rcases legalClause_target_phase hc with h | h | h
  · rw [ht] at h; cases h
  · rw [ht] at h; cases h
  · rw [ht] at h; cases h

lemma legal_to_cap_is_top {s t : State} {b : Bool}
    (h : LegalScan s t b) (ht : t.phase = .cap) :
    LegalClause .top s t b := by
  rcases h with ⟨c, hc⟩
  cases c
  · have hmid : t.phase = .mid := hc.2.2.2.2.2.1
    rw [ht] at hmid; cases hmid
  · have hmid : t.phase = .mid := hc.2.2.1
    rw [ht] at hmid; cases hmid
  · have hmid : t.phase = .mid := hc.2.2.1
    rw [ht] at hmid; cases hmid
  · have hmid : t.phase = .mid := hc.2.2.1
    rw [ht] at hmid; cases hmid
  · have htop : t.phase = .top := hc.2.2.1
    rw [ht] at htop; cases htop
  · exact hc

theorem legal_to_top_source_hash :
    ∀ (s : State) (b : Bool),
      LegalScan s topNorth b → s.centre = .hash := by
  intro s b h
  have htop := legal_to_cap_is_top h (by rfl)
  exact htop.2.2.2.2.2.2.2.1

theorem no_head_source_to_top :
    ∀ (s : State) (b : Bool),
      (s.centre = .headZero ∨ s.centre = .headOne) →
      ¬ LegalScan s topNorth b := by
  intro s b hcentre hlegal
  have hh := legal_to_top_source_hash s b hlegal
  rcases hcentre with h | h
  · rw [hh] at h; cases h
  · rw [hh] at h; cases h

lemma legal_from_bot_is_bot {s t : State} {b : Bool}
    (h : LegalScan s t b) (hs : s.phase = .bot) :
    LegalClause .bot s t b := by
  rcases h with ⟨c, hc⟩
  cases c
  · exact hc
  · simp only [LegalClause] at hc
    have hsp := hc.2.1
    rw [hs] at hsp; cases hsp
  · simp only [LegalClause] at hc
    have hsp := hc.2.1
    rw [hs] at hsp; cases hsp
  · simp only [LegalClause] at hc
    have hsp := hc.2.1
    rw [hs] at hsp; cases hsp
  · simp only [LegalClause] at hc
    have hsp := hc.2.1
    rw [hs] at hsp; cases hsp
  · simp only [LegalClause] at hc
    have hsp := hc.2.1
    rw [hs] at hsp; cases hsp

theorem no_legal_bottom_to_top :
    ∀ b : Bool,
      ¬ LegalScan PakCouplingGenerated.scannerBottom topNorth b := by
  intro b h
  have hbot :=
    legal_from_bot_is_bot h (by rfl : PakCouplingGenerated.scannerBottom.phase = .bot)
  have hmid : topNorth.phase = .mid := hbot.2.2.2.2.2.1
  cases hmid

theorem no_two_edge_bottom_to_top :
    ∀ s : State,
      ¬ (LegalScan PakCouplingGenerated.scannerBottom s false ∧
          LegalScan s topNorth true) := by
  intro s ⟨h0, h1⟩
  have hbot :=
    legal_from_bot_is_bot h0
      (by rfl : PakCouplingGenerated.scannerBottom.phase = .bot)
  have hmid : s.phase = .mid := hbot.2.2.2.2.2.1
  have htop := legal_to_cap_is_top h1 (by rfl)
  have hsphase : s.phase = .top := htop.2.1
  rw [hmid] at hsphase
  cases hsphase

lemma two_testBit_zero : Nat.testBit 2 0 = false :=
  rfl

lemma two_testBit_one : Nat.testBit 2 1 = true :=
  rfl

theorem ScannerPath.size_ge_three {n : ℕ} (P : ScannerPath n) : 3 ≤ n := by
  by_contra hn
  have h12 : n = 1 ∨ n = 2 := by
    have := P.pos
    omega
  rcases h12 with rfl | rfl
  · have h := P.legal ⟨0, Nat.succ_pos 0⟩
    rw [P.bottom, P.top] at h
    exact no_legal_bottom_to_top _ h
  · have h0 := P.legal ⟨0, Nat.succ_pos 1⟩
    have h1 := P.legal ⟨1, Nat.lt_succ_self 1⟩
    rw [P.bottom] at h0
    rw [P.top] at h1
    rw [two_testBit_zero] at h0
    rw [two_testBit_one] at h1
    exact no_two_edge_bottom_to_top _ ⟨h0, h1⟩

def scanner_kernel_terminal_spec : Prop :=
  (∀ s t : State, ∀ b : Bool, s.phase = .cap → ¬ LegalScan s t b) ∧
  (∀ s t : State, ∀ b : Bool, t.phase = .bot → ¬ LegalScan s t b) ∧
  (∀ s : State, ∀ b : Bool, LegalScan s topNorth b → s.centre = .hash) ∧
  (∀ s : State, ∀ b : Bool,
    (s.centre = .headZero ∨ s.centre = .headOne) → ¬ LegalScan s topNorth b) ∧
  (∀ b : Bool, ¬ LegalScan PakCouplingGenerated.scannerBottom topNorth b) ∧
  (∀ s : State,
    ¬ (LegalScan PakCouplingGenerated.scannerBottom s false ∧
        LegalScan s topNorth true)) ∧
  (∀ n : ℕ, ∀ _P : ScannerPath n, 3 ≤ n)

theorem scanner_kernel_terminal_spec_holds :
    scanner_kernel_terminal_spec :=
  ⟨no_clause_from_cap, no_clause_to_bot, legal_to_top_source_hash,
    no_head_source_to_top, no_legal_bottom_to_top, no_two_edge_bottom_to_top,
    fun _ => ScannerPath.size_ge_three⟩

end PakFixedPolyomino.PakScannerKernelTerminalFacts
