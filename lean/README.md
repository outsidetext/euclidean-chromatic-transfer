# Lean verification: χ(ℝ³) ≥ 7 via measurable transfer

This package formally verifies:

* `three_space_transfer` (in `Check3.lean`): any proper `k`-coloring of ℝ³ = ℂ × ℝ, with arbitrary color classes,
  yields `k` measurable, pairwise disjoint sets that contain no two points at Euclidean distance 1 and whose
  union has null complement.
* `OAI.HN3.no_six_coloring_of_density`: `DensityBound 0.1532996 → ¬ ∃` a proper 6-coloring of ℝ³.
  `DensityBound δ` says that every measurable unit-distance-free set has upper cube density ≤ δ. The value
  0.1532996 is the published bound of DeCorte–Oliveira–Vallentin (Math. Program. 2022, Table 2).

`#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`.

## Contents
* `OAI/HN3/*.lean`: the new development, about 1,800 lines.
* `OAI/Geometry/PlaneColoring`, `OAI/Analysis/PlaneSpectrum`, `OAI/MeasureTheory/...`: the 70 modules of the
  Lean library accompanying OpenAI, "The Euclidean plane is not five-colorable" (github.com/openai/math, family 158),
  copied unmodified under the Apache License 2.0 (see `LICENSE-openai-math`). They supply the planar Haar-rigidity
  theorem (`residual_fourier`), the invariant mean, and the stationary-measure constructions.

## Build
```
lake exe cache get        # Mathlib oleans (pinned commit d13f23b)
lake build OAI.HN3.Corollary
lake env lean Check3.lean # prints the axioms
```
