import PakFixedPolyomino.Lattice
import Mathlib.Tactic

namespace PakFixedPolyomino

/-- A unit lattice edge is represented by an unordered pair of distinct cells. -/
abbrev CellEdge := Sym2 Cell

def edgeOf (a b : Cell) : CellEdge := s(a, b)

/-- Boundary edges of a finite cell region.  Each edge is emitted from its
inside endpoint and therefore occurs only once. -/
def boundaryEdges (P : Polyomino) : Finset CellEdge :=
  P.biUnion fun p =>
    ({(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)} : Finset Cell).filter
      (fun q => q ∉ P) |>.image (edgeOf p)

/-- The four sides of a positive rectangle have the expected total length. -/
theorem rectangle_perimeter_arithmetic (w h : ℕ) :
    2 * w + 2 * h = 2 * (w + h) := by omega

/-- Abstract incidence account of a rectangular dissection.  The hypothesis is
the genuine double count: outer unit sides occur once and seam unit sides
twice.  The theorem performs the cancellation needed in Fact
`de84a98c2f64a47e`, Claim 8.1. -/
theorem perimeter_identity_of_double_count
    {n seam sumWH : ℕ}
    (hcount : 2 * sumWH = 4 * n + 2 * seam) :
    sumWH = 2 * n + seam := by omega

/-- Conversely, the compact identity reproduces the perimeter double count. -/
theorem double_count_of_perimeter_identity
    {n seam sumWH : ℕ}
    (h : sumWH = 2 * n + seam) :
    2 * sumWH = 4 * n + 2 * seam := by omega

/-- The `n × n` index grid has exactly `2 n (n-1)` internal unit edges. -/
def gridEdgeCount (n : ℕ) : ℕ := 2 * n * (n - 1)

@[simp] theorem gridEdgeCount_zero : gridEdgeCount 0 = 0 := rfl
@[simp] theorem gridEdgeCount_one : gridEdgeCount 1 = 0 := rfl

theorem gridEdgeCount_succ (n : ℕ) :
    gridEdgeCount (n + 1) = 2 * n * (n + 1) := by
  simp [gridEdgeCount]
  ring

/-- The horizontal and vertical edge families have equal size. -/
theorem gridEdgeCount_split (n : ℕ) :
    gridEdgeCount n = n * (n - 1) + n * (n - 1) := by
  simp [gridEdgeCount]
  ring

end PakFixedPolyomino
