# Lean development

Lean 4 + Mathlib (commit `d13f23b`). Every statement below is checked by the kernel; `#print axioms` reports only
`propext`, `Classical.choice` and `Quot.sound`. Numerical density bounds from the literature enter only as explicit
hypotheses (`DensityBound δ`, `DensityBoundE n δ`: every measurable unit-distance-free set has upper cube density ≤ δ).

| Declaration | Statement | Check file |
|---|---|---|
| `OAI.HN3.three_space_transfer` | a proper k-colouring of ℝ³ (arbitrary classes) yields k measurable, disjoint, conull, unit-distance-free sets | `Check3.lean` |
| `OAI.HN3.no_six_coloring_of_density` | `DensityBound 0.1532996 → ` ℝ³ has no proper 6-colouring | `Check3.lean` |
| `OAI.HN3.exists_finite_not_six_colorable` | … and some finite point set in ℝ³ is not 6-colourable | `Check3.lean` |
| `OAI.HNN.euclidean_transfer_set` | transfer in every dimension n ≥ 2, for every countable set of positive algebraic distances | `CheckN.lean` |
| `OAI.HNN.chromatic_eq_measurable_chromatic(_set)` | χ(ℝⁿ, D) = χ_m(ℝⁿ, D): a proper k-colouring exists iff one with Lebesgue-measurable classes does (n ≥ 2) | `CheckRepair.lean` |
| `OAI.HNN.no_6_coloring_R3` … `no_52_coloring_R8` | χ(ℝⁿ) bounds for 3 ≤ n ≤ 8 from published density bounds; finite forms `exists_finite_R3` … | `CheckN.lean` |
| `OAI.HN3.Indep.alpha1_eq_m1` | finite unit-distance graphs in ℝ³ attain the measurable density: α₁(ℝ³) = m₁(ℝ³) | `CheckIndep.lean` |
| `OAI.HN3.erdos188_R3`, `erdos214_R3` | Erdős #188 / #214 in ℝ³ for 6-point sets (from the density bound) | `CheckTranslates.lean` |
| `OAI.Soifer.soifer`, `kahle` | every finite colouring of ℝ² has monochromatic pairs at distance 2ⁿ and n! for all large n | `CheckSoifer.lean` |
| `OAI.Soifer.erdos706_not_polynomial`, `erdos706_finite` | Erdős #706: the number of colours needed to avoid r distances is not polynomial in r (explicit distances (10⁶)ʲ) | `CheckSoifer.lean` |
| `OAI.Soifer.soifer_quantitative` | a monochromatic 2ⁱ with i ≤ 20(2⌊log₂ 9k⌋ + 2) in every k-colouring | `CheckSoifer.lean` |

## Layout
* `OAI/HN3/` (ℝ³ = ℂ × ℝ), `OAI/HNN/` (all dimensions, `Repair.lean` = measurable repair), `OAI/Soifer/` (many distances):
  the new development, about 7,500 lines.
* `OAI/Geometry/PlaneColoring`, `OAI/Analysis/PlaneSpectrum`, `OAI/MeasureTheory/…`: the Lean library accompanying
  OpenAI, *The Euclidean plane is not five-colorable* (github.com/openai/math, family 158), copied unmodified under the
  Apache License 2.0 (`LICENSE-openai-math`). It supplies the planar rigidity theorem (`residual_fourier`), the invariant
  mean and the stationary-measure constructions.

## Build
```
lake exe cache get
lake build OAI.HNN.Corollary OAI.HNN.Repair OAI.HN3.Finite OAI.HN3.IndepEq OAI.HN3.Translates OAI.Soifer.Main
for f in Check3 CheckN CheckRepair CheckIndep CheckTranslates CheckSoifer; do lake env lean $f.lean; done
```
