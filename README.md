# Euclidean chromatic numbers: transfer theorems and records

A small manuscript collection on the chromatic number of Euclidean spaces, with Lean
formalizations and machine-checkable certificates. The layout follows
[openai/math](https://github.com/openai/math).

- [**CONTENTS.md**](CONTENTS.md): the result families and their manuscripts.
- [`preprints/`](preprints/): one folder per manuscript (`paper.pdf`, `paper.tex`, and any certificates).
- [`lean/`](lean/): the Lean 4 / Mathlib development and its catalog [`formalization.yaml`](lean/formalization.yaml).
- [**history.md**](history.md): dated record of the results and of related work.

**Status.** Nothing here has been refereed. The Lean statements are machine-checked
with only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Numerical
density bounds from the literature appear as explicit hypotheses.

## Results at a glance

**Verification key:** **Lean** = kernel-checked, standard axioms only · **Cert** = exact/rational certificate with ball-arithmetic (Arb) checks · **2×** = re-verified by an independent program · **DRAT** = SAT proof certificate · **Proof** = written proof, agent-refereed.

### New results

| # | Result | Previous | Verification | Priority / credit |
|---|---|---|---|---|
| 1 | **Erdős #188 (plane):** every red/blue coloring of ℝ² with no red unit pair has a blue unit-step 7-term progression; and an explicit periodic coloring (27 open discs of radius 1/2 per period) has no red unit pair and no blue unit-step 68-term progression. So **8 ≤ k ≤ 68** | 6 ≤ k ≤ 6330 (Tsaturian; Currier–Mody–Xie–Zhang, Sept 2026) | Cert, 2× (both bounds) | new |
| 1b | **New chromatic lower bounds in dimensions 4–10:** χ(ℝ⁴) ≥ 12, χ(ℝ⁶) ≥ 55, χ(ℝ⁷) ≥ 110, χ(ℝ⁸) ≥ 198, χ(ℝ¹⁰) ≥ 760, from m₁(ℝ⁴) ≤ 0.0901868, m₁(ℝ⁶) ≤ 0.0182084, m₁(ℝ⁷) ≤ 0.0091408, m₁(ℝ⁸) ≤ 0.0050689, m₁(ℝ¹⁰) ≤ 0.0013170 (Davies's derivative LP + triangle and hypermetric cuts) | 11, 52, 98, 174, 729 (DOV + Davies; Davies, Oct 8 2026) | Cert (Arb), 2× (float) | new |
| 1e | **E³ → (ℓ₂, ℓ₁₁):** every red/blue colouring of ℝ³ with no red unit pair contains a blue unit-step 11-term progression | ℓ₆ (Arman–Tsaturian) | Cert, 2× | new |
| 1c | **Monochromatic triangles in arbitrary 2-colourings (Erdős #173 / EGMRSS conjecture):** every red/blue colouring of ℝ² contains a monochromatic congruent copy of every collinear triple {0, a, a+b} with a/b algebraic, and of every triangle with algebraic side ratios whose shortest side is ≤ 0.654 × its longest (criterion: J₀(at)+J₀(bt)+J₀(ct) > −1 for all t) | 3-term APs {0,a,2a} only (Currier–Moore–Yip 2024); general criterion known only for measurable colourings (Shkredov 2015) | Proof + certified Bessel grid | new (priority checked 14 Oct 2026) |
| 1d | **Polychromatic colourings:** if each class of a k-colouring of ℝⁿ avoids some distance and these distances have algebraic ratios, then k ≥ ⌈1/m₁(ℝⁿ)⌉: k ≥ 5 in ℝ² (Raiskii: ≥ 4), k ≥ 7 in ℝ³ | χ_p(ℝ²) ≥ 4 (Raiskii 1970) | Proof | new (priority checked 14 Oct 2026) |
| 2 | **m₁(ℝ³) ≤ 0.1485113** (density of unit-distance-free sets in ℝ³) | 0.1532996 (DeCorte–Oliveira–Vallentin) | Cert, 2× | new |
| 3 | One-cut certificate m₁(ℝ³) ≤ 0.158035 < 1/6 (5 points, 10 distances) | — | Cert | new |
| 4 | Finite unit-distance graphs in ℝ³ with independence ratio < 0.1486 | — | Proof (from 2 + α₁ = m₁) | new |
| 5 | Quantitative Soifer: monochromatic 2ⁱ < k^6.2 in every k-coloring of ℝ² (k^2.58 in ℝ³); Kahle: n! with n ≤ 31 + log₁.₇₅ k | qualitative only | Cert (weaker exponent in Lean) | new |
| 6 | Dense sets meeting every [X, 2X], X ≥ X₀: monochromatic s ≤ 2X₀k^7.44 (squares: 9k^7.44) | — | Proof + Cert | new |
| 7 | Odd distances: monochromatic odd distance < 18k² in ℝ²; ≤ k in ℝ³ | existence only (Davies) | Proof | new |
| 8 | χ(ℝ², {1, q, …, q^(K−1)}) ≥ 1 + (22/15)(2.5^K − 1) for q ≥ 4096; ℝ³: ≥ 1 + (4/3)(4^K − 1) for q ≥ 256 | c·r√(log r) | Cert | new |
| 9 | Two distances: χ(ℝ², {1, d}) ≥ 7 for algebraic d ∈ [1.77, 1.92] ∪ [7, ∞); ≥ 8, 9, 10, 12, 13 for d ≥ 16, 40, 150, 10⁴, 10¹⁰; ℝ³: ≥ 31 for d ≥ 10⁴ | — | Cert, 2× | new |
| 10 | Small explicit sets: every 6-coloring of ℝ² has a monochromatic distance in {1,3,5,7}; 8-colorings: odd ≤ 15; 10: {2,3,5,7}; 16: {1,2,…,32}; 18: squares ≤ 64 | — | Cert | new |
| 11 | Erdős #188 / #214 in ℝ³: every 6-point set has a blue translate | — | Lean (from DOV bound) | new |

### Machine-checked versions of results also stated by others

| # | Result | Verification | Priority / credit |
|---|---|---|---|
| 12 | **χ(ℝ³) ≥ 7** (three-space is not six-colorable), and a finite non-6-colorable point set in ℝ³ | Lean (input: m₁(ℝ³) ≤ 0.1532996) | Crocker, conditional on OpenAI Thm 2.3; formal proof ours |
| 13 | Transfer in every dimension n ≥ 2 and for every countable set of algebraic distances; χ_D(ℝⁿ) ≥ 1/m_D(ℝⁿ); bounds for n = 4…8 and finite forms | Lean | Crocker (conditional); n ≥ 4 rational squares: Davies |
| 14 | **χ(ℝⁿ) = χ_m(ℝⁿ)** for every n ≥ 2 (ordinary = Lebesgue-measurable chromatic number; Székely's question) | Lean | Davies Lemma B.1 + transfer; plane flagged by Crocker; formal proof ours |
| 15 | α₁(ℝ³) = m₁(ℝ³): finite unit-distance graphs attain the measurable density | Lean | Crocker (conditional); plane Li–Su; n ≥ 4 Davies |
| 16 | Soifer (2ⁿ) and Kahle (n!): monochromatic for all large n in every finite coloring of ℝ² | Lean | Crocker (conditional, qualitative) |
| 17 | **Erdős #706 answered negatively:** colors needed to avoid r distances is not polynomial in r; explicit distances (10⁶)ʲ give ≥ (4/9)(3/2)^K | Lean | Crocker (conditional, non-explicit) |

### Earlier records (August–October 2026)

| # | Result | Previous | Verification |
|---|---|---|---|
| 18 | χ(ℝ², {1, (√2+√6)/2}) ≥ 7 by finite certificates | — | Exact arithmetic + DRAT |
| 19 | Smallest 6-chromatic two-distance graphs: 26 vertices; 30 for {1, √3} | 117; 33 | Exact arithmetic + DRAT |
| 20 | e₅ ≤ 2278 | 2406 | DRAT |
| 21 | Six-coloring continuum extended to [0.354, 0.667504532081] | 0.657 | 59 exact rational tilings |
| 22 | Forced densities 1/67, 1/28, 1/37 | — | DRAT |

### Open

χ(ℝ²) ∈ {6, 7} remains open. Density methods cannot decide it: Pritikin's six-coloring covers all but 0.015% of the plane. In ℝ³, m₁(ℝ³) < 1/7 would give χ(ℝ³) ≥ 8; work in progress.

## Build and check
```
cd lean
lake exe cache get              # Mathlib oleans (pinned commit d13f23b)
lake build OAI.HNN.Corollary OAI.HNN.Repair OAI.HN3.Finite OAI.HN3.IndepFolner OAI.HN3.Translates OAI.Soifer.Main
lake env lean CheckN.lean       # n-dimensional transfer and corollaries: prints axioms
lake env lean CheckRepair.lean  # chi(R^n) = measurable chi(R^n), n >= 2: prints axioms
lake env lean Check3.lean       # three-dimensional development
lake env lean CheckIndep.lean   # finite graphs attain the density in R^3
lake env lean CheckSoifer.lean  # monochromatic 2^n and n! distances (Soifer, Kahle)
lake env lean CheckTranslates.lean # Erdos #188/#214 in R^3: prints axioms
```
Certificates for the record graphs are checked by the scripts beside them; see
[`preprints/Chromatic-numbers-of-the-plane-with-two-forbidden-distances-October-14-2026/certificates/README.md`](preprints/Chromatic-numbers-of-the-plane-with-two-forbidden-distances-October-14-2026/certificates/README.md).

## License
Lean sources and scripts: Apache License 2.0 (see [LICENSE](LICENSE)). The modules under
`lean/OAI/{Analysis,Geometry,MeasureTheory}` are from github.com/openai/math, used
unmodified under the Apache License 2.0 (see `lean/LICENSE-openai-math`).
