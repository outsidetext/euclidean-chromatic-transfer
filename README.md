# Arbitrary colorings of Euclidean space are no easier than measurable ones

Paper: [`paper/transfer.pdf`](paper/transfer.pdf) (source in `paper/transfer.tex`).

**Main results**
- **Transfer in every dimension.** If ℝⁿ (n ≥ 2) has a proper k-coloring with arbitrary color classes, it has a
  measurable k-coloring whose monochromatic unit pairs form a null set. This extends the planar transfer theorem
  of OpenAI, "The Euclidean plane is not five-colorable" (2026). It uses the planar Haar-rigidity theorem block by
  block over a maximal torus of rotations, and an invariant-mean line average on the remaining axis.
- **Consequently χ(ℝⁿ) ≥ ⌈1/m₁(ℝⁿ)⌉.** This gives χ(ℝ³) ≥ 7 (previously 6), χ(ℝ⁴) ≥ 11, χ(ℝ⁸) ≥ 53, and
  χ(ℝⁿ) ≥ (1.268+o(1))ⁿ (previously (1.239+o(1))ⁿ).
- **Finite graphs attain the measurable density.** inf over finite unit-distance graphs of α(G)/|G| equals m₁(ℝⁿ).
  In the plane this proves the first part of the Dúcz–Varga conjecture: f(N) = (m₁(ℝ²)+o(1))N.

**Formal verification** ([`lean/`](lean/)). The ℝ³ transfer (`three_space_transfer`) and the implication
`DensityBound 0.1532996 → no proper 6-coloring of ℝ³` are verified in Lean 4 / Mathlib, using only the standard
axioms. The density bound itself is DeCorte–Oliveira–Vallentin's certificate, re-verified with their exact program
in [`numerics/dov-verifier/`](numerics/dov-verifier/).

The `lean/OAI/{Analysis,Geometry,MeasureTheory}` modules are from github.com/openai/math, used under the
Apache License 2.0.
