# Euclidean chromatic numbers and Euclidean Ramsey theory, after the transfer theorem

*Henry Bass, October 2026*

In October 2026 OpenAI proved that the plane is not 5-colourable ([openai/math](https://github.com/openai/math), family 158).
A central step is a **transfer theorem**: averaging an arbitrary colouring over algebraic translations and rotations, plus a
spectral rigidity theorem, makes pair correlations behave as if the colouring were measurable. This repository develops that
idea in several directions: higher dimensions, many forbidden distances, Erdős problems in Euclidean Ramsey theory, and a
Lean formalization. It contains four manuscripts, a Lean 4 development, and machine-checkable certificates for every
numerical claim.

## Results

| | Result | Previously | Verification |
|---|---|---|---|
| 1 | **χ(ℝ³) ≥ 7**: three-space is not six-colourable, for arbitrary colourings | χ(ℝ³) ≥ 6 | Lean, from the published bound m₁(ℝ³) ≤ 0.1533 |
| 2 | **χ(ℝⁿ) = χ_m(ℝⁿ) for every n ≥ 2**: the chromatic number equals the Lebesgue-measurable chromatic number (also for countable sets of algebraic distances) | n ≥ 4 (Davies) | Lean |
| 3 | **Erdős Problem #188: 8 ≤ k ≤ 49.** Every red/blue colouring of the plane with no red unit pair has a blue unit-step 7-term progression; an explicit periodic colouring has none of length 49 | 6 ≤ k ≤ 6330 | exact certificates, two independent verifiers each |
| 4 | **Monochromatic triangles in every 2-colouring of the plane** (Erdős #173): every collinear triple {0, a, a+b} with a/b algebraic, every triangle with algebraic side ratios and shortest side ≤ 0.654 × longest, and the near-equilateral triangles (4,5,6), (5,6,7), (7,8,9) and (3,3,4) | 3-term progressions only | proof + certified Bessel bound |
| 5 | **E³ → (ℓ₂, ℓ₁₁)**: red unit-distance-free colourings of ℝ³ contain blue unit-step 11-term progressions | ℓ₆ | exact certificate, two verifiers |
| 6 | **χ(ℝ⁴) ≥ 12, χ(ℝ⁶) ≥ 55, χ(ℝ⁷) ≥ 110, χ(ℝ⁸) ≥ 198, χ(ℝ¹⁰) ≥ 760** | 11, 52, 98, 174, 729 | ball-arithmetic certificates, independently re-checked |
| 7 | **m₁(ℝ³) ≤ 0.1485113** (density of unit-distance-free sets in ℝ³) | 0.1532996 | ball-arithmetic certificate, two verifiers |
| 8 | **Erdős Problem #706, negative answer**: the number of colours needed to avoid r distances in the plane is not polynomial in r; explicit bound > (22/15)(2.5ʳ − 1) | — | Lean (qualitative), certificate (explicit) |
| 9 | **Soifer's and Kahle's questions**: every finite colouring of the plane has monochromatic pairs at distance 2ⁿ and n! for all large n; quantitatively a monochromatic 2ⁱ < k^6.2 | open | Lean (qualitative), certificate (quantitative) |
| 10 | **Polychromatic colourings** whose avoided distances have algebraic ratios need ≥ 5 colours in ℝ² and ≥ 7 in ℝ³ | ≥ 4 in ℝ² (Raiskii) | proof |
| 11 | **Erdős Problem #214 (partial)**: 5-point sets with algebraic distances that are small or spread out have red copies | 4 ≤ k ≤ 7 | certificates |
| 12 | Finite unit-distance graphs attain the measurable density in ℝ³ (α₁ = m₁), hence finite graphs in ℝ³ with independence ratio < 0.1486 | — | Lean (α₁ = m₁) |
| 13 | Quantitative bounds for odd distances, lacunary and two-distance sets; e.g. χ(ℝ², {1, d}) ≥ 7 for algebraic d ≥ 7 | — | certificates |
| 14 | Records for two-distance graphs: χ(ℝ², {1, (√2+√6)/2}) ≥ 7 by finite certificates; 6-chromatic two-distance graphs on 26 and 30 vertices; e₅ ≤ 2278 | 117 and 33 vertices; e₅ ≤ 2406 | DRAT + exact arithmetic |

The transfer in all dimensions and results 1, 12 and the qualitative parts of 8 and 9 were also stated, conditionally on
OpenAI's rigidity theorem and without formalization or explicit bounds, by C. Crocker
([Zenodo, 10 October 2026](https://doi.org/10.5281/zenodo.23273952)), who also noted result 2 as expected.
J. Davies ([arXiv:2610.12301](https://arxiv.org/abs/2610.12301)) proved χ = χ_m and α₁ = m₁ in dimensions n ≥ 4 by a
different method; S. Li and Y. Su ([arXiv:2610.15424](https://arxiv.org/abs/2610.15424)) proved α₁ = m₁ in the plane.
See [history.md](history.md).

## Manuscripts

| Manuscript | Contents |
|---|---|
| [A machine-checked proof that three-space is not six-colorable](preprints/A-machine-checked-proof-that-three-space-is-not-six-colorable-October-14-2026/paper.pdf) | results 1, 2, 6, 7, 12 |
| [Monochromatic distances in finite colorings of the plane](preprints/Monochromatic-distances-in-finite-colorings-of-the-plane-October-14-2026/paper.pdf) | results 8, 9, 13 |
| [Euclidean Ramsey theorems for arbitrary colourings via spectral rigidity](preprints/Euclidean-Ramsey-theorems-for-arbitrary-colourings-October-14-2026/paper.pdf) | results 3, 4, 5, 10, 11; which constraints the transfer can and cannot carry |
| [Chromatic numbers of the plane with two forbidden distances](preprints/Chromatic-numbers-of-the-plane-with-two-forbidden-distances-October-14-2026/paper.pdf) | result 14 |

Each manuscript folder contains `paper.pdf`, `paper.tex` and the certificates and verification scripts for its claims.
[CONTENTS.md](CONTENTS.md) lists the results with abstracts.

## Checking

**Lean.** Requires [elan](https://github.com/leanprover/elan).
```
cd lean
lake exe cache get
lake build OAI.HNN.Corollary OAI.HNN.Repair OAI.HN3.Finite OAI.HN3.IndepEq OAI.HN3.Translates OAI.Soifer.Main
lake env lean CheckRepair.lean   # prints the theorem and its axioms; likewise Check3, CheckN, CheckIndep, CheckSoifer, CheckTranslates
```
See [lean/README.md](lean/README.md) for the list of formal statements.

**Certificates.** Python 3 with `numpy`, `scipy` and `python-flint` (ball arithmetic); SAT certificates need
[`drat-trim`](https://github.com/marijnheule/drat-trim). Each certificate folder documents its verifier command.

## Caveats

Nothing here has been refereed. The transfer applies to colourings restricted to algebraic points, so statements about
configurations require algebraic distances or ratios; the case of transcendental distances is open. In Lean, numerical density
bounds from the literature appear as explicit hypotheses. The chromatic number of the plane, 6 or 7, remains open.

## Acknowledgements

The results, proofs, Lean formalization, certificates and verification programs were developed with the assistance of Claude
(Anthropic). The planar transfer and rigidity theorem and its formalization are due to OpenAI.

## License

Apache License 2.0 ([LICENSE](LICENSE)). The modules under `lean/OAI/{Analysis,Geometry,MeasureTheory}` are from
[openai/math](https://github.com/openai/math), used unmodified under the Apache License 2.0 (`lean/LICENSE-openai-math`).
