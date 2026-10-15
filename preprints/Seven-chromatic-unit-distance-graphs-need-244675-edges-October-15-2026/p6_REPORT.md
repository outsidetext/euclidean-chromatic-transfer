# Independent check of chi6_devil's p₆ ≤ 4.1084344e-6 (2026-10-15)

## Verdict

**CONFIRMED, and the claim is conservative.** The colouring the agent certified is
`research/chi6_devil/maps/PRbest_exact.json` (commit 61c2bf6; sha256 24f57548…7b57). It has
42 exact-rational convex pieces, 6 colours and covolume 554179047/200000000. My from-scratch
checker, which uses a different method, gives a rigorous enclosure for its monochromatic unit-pair
density:

    p(PRbest_exact) ∈ [4.1024135074907462580e-6 ± 4.4e-26]

The agent's arb enclosure was [4.0999e-6 ± 8.44e-9], with upper end 4.1084344e-6. That interval
contains my value, so their bound is valid. It is loose by 6.0e-9, because their breakpoint
clusters are wide. Their float `indep_check.py` value, 4.102413413e-6, agrees with mine to 9e-14.

**Corollaries, by the de Grey–Parts argument, using my bound:**

| | p₆ upper bound | e₇ ≥ ⌈1/p⌉ | v₇ (Ágoston–Pálvölgyi) |
|---|---|---|---|
| de Grey–Parts 2023 (arXiv 2303.14714) | 1/232646 ≈ 4.29838e-6 (implied) | 232,646 | 6,456 |
| chi6_devil claim (PRbest) | 4.1084344e-6 | 243,402 ✔ | 6,679 ✔ |
| **this check, same map (PRbest)** | **4.10241350750e-6** | **243,759** | **6,686** |
| this check, `PRfine_exact.json` (90 pieces; the agent's own certification of it was unfinished) | 4.08706262041e-6 | 244,675 | 6,705 |

- **Both claimed numbers follow from the claimed p.** 1/4.1084344e-6 = 243,401.72 gives e₇ ≥ 243,402.
  The smallest v with 29v⁴ ≥ 4e³ is then 6,679.
- **Literature caveat on the vertex count.** The vertex corollary beats de Grey–Parts' *edge-route*
  6,456, but it is **not** a record. Parts 2020 ("What percent of the plane…", Geombinatorics 30,
  Table 2; `literature/parts2020_percent_plane.txt`) already has v₇ ≥ 6,993 from the void-density
  route. The agent's NOTES say so as well. The **edge** bound e₇ ≥ 243,402 (243,759 from this map,
  244,675 from PRfine) does improve on de Grey–Parts' e₇ ≥ 232,646. I found no better published
  e₇ in the repo's literature, but I did not do a fresh literature search.

## What is being computed

- **Definition.** p = P[c(x) = c(x+u)], with x uniform on ℝ²/Λ and u uniform on S¹. Summing over
  ordered same-colour piece pairs:

      p = (1/(2π·covol)) Σ_{(i,j,λ)} I(P_i, P_j+λ),   I(P,Q) = ∬_{P×Q} δ(|x−y|−1) dx dy.

- **The de Grey–Parts argument.** Drop a unit-distance graph with e edges at a uniformly random
  rotation and translation. The expected number of monochromatic edges is e·p. If e·p < 1, some
  placement avoiding all boundaries (a null set) has none, so the graph is 6-colourable.
  Therefore e₇·p₆ ≥ 1, and e₇ ≥ ⌈1/p_hi⌉.
- **From e₇ to v₇.** The paper uses e ≤ ∛(29/4)·v^{4/3} (Ágoston–Pálvölgyi, arXiv 2006.06285),
  i.e. v₇ ≥ min{v : 29v⁴ ≥ 4e³}. I evaluate this in exact integers. It reproduces de Grey–Parts'
  own pair, 232,646 → 6,456. I take the Ágoston–Pálvölgyi bound from the literature without
  re-checking it.

## My checker: `verify_mine/check_p6.py`

The checker is written from scratch and imports nothing from the repo (only python-flint and
numpy). It uses a different formula from the agent's. Their `certify.py` and `indep_check.py` both
integrate area(P ∩ (Q − u_θ)) over θ. Mine is a **double-Green, boundary-pair formula:**

- **The identity.** If Δψ = δ(r−1) with ψ radial, then
  ∬_{P×Q} Δψ(y−x) = −Σ_{e∈∂P, e′∈∂Q} (n_e·n_e′) ∫_e∫_e′ ψ(|x−y|) ds ds′.
  - ψ = log⁺r gives I = −Σ(n·n′)∬ log⁺|x−y|.
  - ψ = log⁻r, where Δlog⁻ = 2πδ₀ − δ(r−1), gives I = Σ(n·n′)∬ log⁻|x−y|. I use this form only
    when dist(P,Q) > ½.
- **Inner integral, in closed form.** For each edge pair, the integral of log√(τ²+h²) over e′,
  restricted to |x−y| ≥ 1 or ≤ 1, has a closed form. The atan terms are written so that they
  stay holomorphic through h = 0.
- **Outer integral, rigorous.** The integral over e uses arb's rigorous integrator, `acb.integral`,
  with holomorphy checked through `analytic=True` and atan written in terms of log.
  - [0,1] is first split at every point where the case changes: h = 0, ±1; τ₀ = 0, τ₁ = 0;
    |x − endpoint| = 1.
  - Each case is decided by **exact rational** comparisons at a rational interior point.
  - Breakpoints sit inside 2⁻²²⁰-dyadic intervals, each bounded by width·L′·max|ψ|.
- **Input validation, all exact over fmpq.**
  - Coordinates must be ints or "a/b" strings; floats are rejected.
  - At most 6 colours.
  - Every piece is strictly convex.
  - All lattice translates within reach have pairwise disjoint interiors (exact separating-axis
    test over a provably complete box of lattice vectors).
  - The piece areas sum exactly to the covolume.
- **Pair enumeration.** Same-colour pairs are found over a provably complete lattice box. A pair
  is skipped only if, exactly, max dist ≤ 1 or min dist ≥ 1.

## Results and tests (venv/bin/python3, nice, ≤ 4 workers; every run took seconds)

**The claimed map, PRbest.** 200 ordered pair classes, 1126 edge pairs, 1545 rigorous
sub-integrals, about 5 s. Two cross-checks:

- `--split plus` (every pair through log⁺) gives an identical enclosure.
- `--split both` evaluates log⁺ and log⁻ on every pair where both apply. These are two exact
  formulas with different integrands. They agree on every pair, with mid differences ≤ 3e-27.

**Reproduction of the agent's de Grey–Parts map.** For `prit_best_exact.json` I get
p = 4.2983742354e-6, which gives e₇ ≥ 232,647 and v₇ ≥ 6,456. This matches the agent's certified
4.298375e-6 and the published 232,646.

**Self-tests with closed-form answers (`--selftest`, all PASS):**

- constant colouring of ℤ² gives p = 1 exactly, both for the square and for 2 triangles on a
  skew basis;
- a 9-colour square pattern with side 3/4 matches the closed form 1.73892471551406e-4;
- a proper 9-colouring (side 3/5) gives 0;
- a 2-colour stripe pattern of width 2/3 matches the closed form 0.397713537078062. This test
  exercises the log⁻ branch.

**Negative tests on PRbest (`--negtest`, 12/12 PASS):**

- **Rejected:**
  - a float coordinate;
  - one vertex moved by ±1e-6;
  - two vertices swapped (non-convex piece);
  - a seventh colour;
  - a deleted piece;
  - a duplicated piece;
  - the lattice stretched by 1e-6.
- **Valid perturbations, with the expected behaviour:**
  - Permuting the colours leaves p identical.
  - Recolouring one 11-gon gives p = 0.0566107449, against Monte Carlo 0.056616 ± 1.2e-4.
  - Merging colours 0 and 1 gives p = 0.0566358193, against Monte Carlo 0.056584 ± 1.2e-4.
  - **All 42 pieces in one colour gives p = 1 ± 1e-22.** This is a global test of lattice-sum
    completeness and of every pair integral.
- **Uniform rescaling (unit distance 1/r).**
  - r = 1.001 gives p = 4.662e-6.
  - r = 0.999 gives p = 4.002e-5, 9.8× the baseline.
  - So the colouring sits on a knife-edge: the rows have height exactly ½ (2y = 1). Its p is
    exact for the exact rational data, but it is very sensitive to the geometry.

**Definition-level Monte Carlo on PRbest** (float, not rigorous; 4e8 random point/direction
samples): 1643 monochromatic, p ≈ 4.1075e-6 ± 1.0e-7, which is 0.05σ from the rigorous value. This confirms the normalisation and the semantics (random point, random direction) independently of every integral formula.

## Reproduce

    cd ~/hadwiger-nelson
    venv/bin/python3 verify_mine/check_p6.py --selftest
    venv/bin/python3 verify_mine/check_p6.py research/chi6_devil/maps/PRbest_exact.json --workers 4 [--split both] [--mc N]
    venv/bin/python3 verify_mine/check_p6.py research/chi6_devil/maps/PRbest_exact.json --negtest --workers 4
