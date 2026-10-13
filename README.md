# Pak's Fixed-Polyomino Square-Counting Theorem

[![Lean](https://github.com/canghaimeng/PakFixedPolyomino/actions/workflows/lean.yml/badge.svg)](https://github.com/canghaimeng/PakFixedPolyomino/actions/workflows/lean.yml)

A Lean 4 formalization of **#EXP-completeness of square-tiling counting for one fixed finite family of connected polyominoes**, under polynomial-time metric reductions.

## The theorem

There exists a nonempty finite set `T` of nonempty, edge-connected polyominoes in the integer lattice such that the following counting problem is #EXP-complete:

> Given the side length `n` in binary, count all exact tilings of the ordinary `n × n` square by translations of shapes in `T`.

The family is fixed independently of the input. Placements use translations, with pairwise-disjoint supports covering the square exactly. The input convention is little-endian binary; the counting function is defined on every finite bit string, including empty strings and representations with extra high zero bits.

The development proves both membership in standard nondeterministic-machine #EXP and hardness for that full class. The metric reduction includes deterministic polynomial bit-time witnesses for the instance map and answer postprocessor.

## Main declaration

[`PakFixedShapeHeadline.pak_headline`](PakFixedPolyomino/PakFixedShapeHeadline.lean):

```lean
∃ T : Finset Polyomino,
  T.Nonempty ∧ (∀ P ∈ T, P.Nonempty ∧ FourConnected P) ∧
  StandardBitMetric.CompleteForSharpEXP
    (PakFixedShapeExactCountingModel.binaryTranslationSquareCount T)
```

The witness is `PakFixedShapeHeadline.targetFamily`. The declarations `membership`, `metric_hardness`, and `complete` expose the two complexity directions and their combination. The final theorem has no additional hypotheses.

## Build

Install [Lean through elan](https://github.com/leanprover/elan), then run:

```bash
git clone https://github.com/canghaimeng/PakFixedPolyomino.git
cd PakFixedPolyomino
lake exe cache get
lake build
lake env lean Check.lean
```

The toolchain is pinned to **Lean 4.33.0**. The manifest pins mathlib to `db584cd6d46c92f209a44c0f1c829460d327499d` and records its transitive dependencies. The first build compiles 767 local proof modules after downloading the mathlib cache.

## Reading the proof

| Entry point | Content |
| --- | --- |
| [Lattice](PakFixedPolyomino/Lattice.lean) and [Tiling](PakFixedPolyomino/Tiling.lean) | Integer cells, connected shapes, translation placements, disjointness, and exact coverage |
| [Exact counting model](PakFixedPolyomino/PakFixedShapeExactCountingModel.lean) | Counting all tilings using a finite set of shapes and its binary-side interpretation |
| [Standard nondeterministic machines](PakFixedPolyomino/StandardNondeterministicMachine.lean) | One-tape transitions, accepting-path counts, runtime bounds, and #EXP |
| [Bit-time model](PakFixedPolyomino/StandardBitTime.lean) and [metric reductions](PakFixedPolyomino/StandardBitMetric.lean) | Concrete time bounds and the completeness notion |
| [Standard membership](PakFixedPolyomino/PakFixedShapeStandardMembership.lean) | The initializer and counting machine witnessing membership |
| [Closed metric hardness](PakFixedPolyomino/PakFixedWeightedMetricHardnessClosed.lean) | Source-machine normalization, fixed scanner construction, counting identities, and bit-time reduction maps |
| [Exact-count hardness](PakFixedPolyomino/PakFixedShapeExactMetricHardness.lean) | Transfer to the literal translation-only square-counting function |
| [Main theorem](PakFixedPolyomino/PakFixedShapeHeadline.lean) | The fixed family and the complete theorem |

`PakFixedPolyomino.lean` imports the main theorem. The `PakFixedPolyomino/` directory contains its transitive local module dependencies.

## Verification

GitHub Actions builds the library and runs [`Check.lean`](Check.lean). This file checks the displayed theorem type and rejects any transitive axiom outside:

- `propext`
- `Classical.choice`
- `Quot.sound`

The check applies separately to membership, hardness, completeness, and the final existential theorem. Some auxiliary declarations in imported modules use `native_decide`; the audited main results do not depend on those declarations.

## License

This repository uses the [PolyForm Noncommercial License 1.0.0](LICENSE).

## Acknowledgments

We thank the [Euler system](https://github.com/canghaimeng/Euler) for supporting the development, organization, and verification of this formalization.
