import PakFixedPolyomino.PakFullFrameReverse
import PakFixedPolyomino.PakRippleCanonical
import Mathlib.Tactic

/-!
# Full-frame ripple readback and the scanner-classification boundary

The four activity sides determine the binary ripple track.  In contrast, the
scanner relation is locally nondeterministic: a bottom-to-top legal column can
use only `mid` and `preTop` clauses, so legality and vertical matching alone do
not select a terminal/copy boundary.
-/

namespace PakFixedPolyomino.PakFullFrameRippleClassify

open PakMStarCouplingCorrectness

/-- The literal west and south full-frame boundary conditions are a complete
code for the ripple tiling.  This derives the canonical counter from the
boundary and Wang matching; it does not take the canonical tiling as an
additional full-frame hypothesis. -/
theorem FullFrame.rippleProjection_eq_canonical {n : ℕ} (F : FullFrame n n) :
    rippleProjection F.tiling = PakRippleCanonical.canonicalTiling n n := by
  apply Subtype.ext
  funext i j
  have hcell : ∀ k : ℕ, ∀ i : Fin n, ∀ j : Fin n, i.1 + j.1 = k →
      rippleAt F.tiling i j =
        (PakRippleCanonical.canonicalTiling n n).1 i j := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro i j hsum
        apply Prod.ext
        · change (rippleAt F.tiling i j).1 =
            ((PakRippleCanonical.canonicalTiling n n).1 i j).1
          by_cases hi0 : i.1 = 0
          · have hi : i = (⟨0, F.width_pos⟩ : Fin n) := by
              apply Fin.ext
              exact hi0
            subst i
            exact (F.west_accepts j).1.trans
              (PakRippleCanonical.canonicalTiling_west n n j F.width_pos).symm
          · let ip : Fin n := ⟨i.1 - 1, by omega⟩
            have his : (⟨ip.1 + 1, by dsimp [ip]; omega⟩ : Fin n) = i := by
              apply Fin.ext
              dsimp [ip]
              omega
            have hprev : rippleAt F.tiling ip j =
                (PakRippleCanonical.canonicalTiling n n).1 ip j :=
              ih (ip.1 + j.1) (by dsimp [ip]; omega) ip j rfl
            have hf := (rippleProjection F.tiling).2.1 ip j
              (by dsimp [ip]; omega)
            have hc := (PakRippleCanonical.canonicalTiling n n).2.1 ip j
              (by dsimp [ip]; omega)
            rw [rippleProjection_cell, his] at hf
            rw [his] at hc
            change xor (rippleAt F.tiling ip j).1 (rippleAt F.tiling ip j).2 =
              (rippleAt F.tiling i j).1 at hf
            change xor ((PakRippleCanonical.canonicalTiling n n).1 ip j).1
                ((PakRippleCanonical.canonicalTiling n n).1 ip j).2 =
              ((PakRippleCanonical.canonicalTiling n n).1 i j).1 at hc
            rw [hprev] at hf
            exact hf.symm.trans hc
        · change (rippleAt F.tiling i j).2 =
            ((PakRippleCanonical.canonicalTiling n n).1 i j).2
          by_cases hj0 : j.1 = 0
          · have hj : j = (⟨0, F.height_pos⟩ : Fin n) := by
              apply Fin.ext
              exact hj0
            subst j
            exact (F.south_has_sentinel i).1.trans
              (PakRippleCanonical.canonicalTiling_south n n i F.height_pos).symm
          · let jb : Fin n := ⟨j.1 - 1, by omega⟩
            have hjs : (⟨jb.1 + 1, by dsimp [jb]; omega⟩ : Fin n) = j := by
              apply Fin.ext
              dsimp [jb]
              omega
            have hprev : rippleAt F.tiling i jb =
                (PakRippleCanonical.canonicalTiling n n).1 i jb :=
              ih (i.1 + jb.1) (by dsimp [jb]; omega) i jb rfl
            have hf := (rippleProjection F.tiling).2.2 i jb
              (by dsimp [jb]; omega)
            have hc := (PakRippleCanonical.canonicalTiling n n).2.2 i jb
              (by dsimp [jb]; omega)
            rw [hjs] at hf
            rw [hjs] at hc
            simp only [rippleProjection_cell, rippleTile] at hf
            simp only [rippleTile] at hc
            rw [hprev] at hf
            exact hf.symm.trans hc
  exact hcell (i.1 + j.1) i j rfl

/-! ## Why a terminal classifier needs an extra global invariant -/

/-- The ordinary scanner path is a completely legal east-column candidate
without a `terminal` clause.  Thus `LegalScan` plus vertical Wang matching
cannot imply that an east column is a `terminalScannerColumn`. -/
theorem scannerColumn_legal_without_terminal
    (bits : List Bool) (hbits : 0 < bits.length) (topBit : Bool)
    (j : Fin (bits.length + 2)) :
    ∃ s t : ConcretePakScanner.State,
      PakScannerPath.scannerColumn bits hbits j = some (s, t) ∧
        ConcretePakScanner.LegalScan s t
          (PakScannerPath.scannerBit bits false topBit j) :=
  PakScannerPath.scannerColumn_legal bits hbits topBit j

/-- A concrete two-bit witness separates the fully legal nonterminal column
from every admissible terminal column.  The only admissible terminal is `1`,
and its `tail` state already differs at row `1`. -/
theorem legal_scanner_column_not_terminal_column :
    ∀ terminal : ℕ, 0 < terminal → terminal < ([false, false] : List Bool).length →
      PakScannerPath.scannerColumn [false, false] (by decide) ≠
        PakScannerTerminal.terminalScannerColumn [false, false] (by decide) terminal := by
  intro terminal hterminal hbound heq
  have hterminal_eq : terminal = 1 := by
    norm_num at hbound
    omega
  subst terminal
  let row1 : Fin (([false, false] : List Bool).length + 2) := ⟨1, by decide⟩
  have hrow := congrFun heq row1
  have hne :
      PakScannerPath.scannerColumn [false, false] (by decide) row1 ≠
        PakScannerTerminal.terminalScannerColumn [false, false] (by decide) 1 row1 := by
    native_decide
  exact hne hrow

end PakFixedPolyomino.PakFullFrameRippleClassify
