# Certificate: a periodic 6-colouring of the plane with p₆ ≤ 4.1084344 × 10⁻⁶

2026-10-15. Workspace `research/chi6_devil/`.

## Statement

There is an explicit periodic polygonal 6-colouring c of ℝ² with
p₆(c) := P(c(x) = c(x+e)) ≤ **4.1084344 × 10⁻⁶**. Here x is uniform on a period cell and e is uniform on the unit
circle. Consequently every finite unit-distance graph that is not 6-colourable has

- **≥ 243,402 edges**, and
- **≥ 6,679 vertices**.

For comparison, de Grey–Parts (arXiv 2303.14714, §2) give e₇ ≥ 232,646 and v₇ ≥ 6,456, from Pritikin's
pentagonal tiling with p₆ = 4.29838 × 10⁻⁶. Parts (arXiv 2010.12668) gives v₇ > 6,992 by a different
(void-density) argument. **That remains the best vertex bound; our edge-route vertex bound 6,679 does not
beat it.** The edge bound 243,402 improves e₇ ≥ 232,646 by 4.6%.

## The colouring (exact data)

**File.** `maps/PRbest_exact.json`, sha256 `24f57548c8361ffe6bdfc8d470108e9f49deb89dc132198b9b52da47c05a7b57`.

**Format.** The certify.py format: `B` holds two rational lattice vectors, `polys` holds rational convex
polygons, `cols` holds a colour 0..5 for each polygon.

**Lattice.** b₁ = (184726349/10⁸, −3/4), b₂ = (0, 3/2). Covolume 554179047/(2·10⁸) ≈ 2.7708952.

**Pieces.** 42 strictly convex pieces, 7 per colour. They come from 6 non-convex cells (one per colour) by
exact ear clipping and greedy convex merging in `lowerbounds_v5/planar.py export`. Vertices are rationals:
optimised floats rounded to 10⁻⁸, plus exact intersection points.

**Topology.** This is Pritikin's pentagonal "rod" tiling (Parts 2010.12668 Fig. 3, voids absorbed):

- the tile is a pentagon A(0,0) B(x−z,0) C(x+z,y/2) D(x−z,y) E(0,y);
- columns meet alternately along straight lines (degree-4 vertices) and zigzags (degree-3 vertices);
- each column cycles 3 colours;
- one tile of each colour per period.

**Provenance** (how it was found, not needed for checking):

1. Optimise Pritikin's (x, y, z) on certified p₆: `prit_opt.py` → (0.9236317, 0.5, 0.0496654), giving
   p₆ = 4.298375e-6. This reproduces de Grey–Parts.
2. Subdivide every edge 3× and run continuous vertex optimisation with analytic gradient
   (`lowerbounds_v5/planar.py opt` via `plloop6.sh`, 8 rounds of collapse / needle-fix / subdivide / L-BFGS).
3. Remove near-collinear vertices (`planar.py simplify`, tolerance 10⁻⁵), then export.

The gain comes from **wavy zigzag edges**: the edges at degree-3 junctions become S-shaped, with teeth of
about 1.7·10⁻³ next to the junctions. The horizontal and vertical "contact" edges, where same-colour copies
sit at distance exactly 1, stay straight.

## How p₆ is computed (rigorous)

The quantity is

  p₆ = 1/(2π |F|) · Σ over same-colour piece pairs (i, j, λ ∈ Λ) of  ∫₀^{2π} area(Pᵢ ∩ (Pⱼ + λ − u_θ)) dθ,

with u_θ = (cos θ, sin θ) and |F| the covolume.

**Tiling check** (exact rationals): every piece is strictly convex; every pair of nearby lattice translates
is disjoint (exact separating axis); the areas sum to the covolume. So the pieces tile ℝ² up to a null set.
Boundary points can be coloured arbitrarily without changing p₆.

**Enclosure** (`lowerbounds_v5/certify.py`, engine `arb`, python-flint ball arithmetic at 128 bits):

- for each of the 103 contributing pair classes, the θ-breakpoints are where a vertex of one polygon meets an
  edge line of the other. This is a complete superset of the non-smooth points;
- on each arc the area is an exact degree-2 trigonometric polynomial, fitted from 5 rigorous evaluations
  with one consistency check, and integrated in closed form;
- tiny arcs are bounded by midpoint ± Lipschitz bound;
- breakpoint balls are bounded by [0, min area] · width.

**Result** (`results/cert_PRbest_arb.txt`, 284 s with 2 workers):

  p₆ ∈ [4.10 × 10⁻⁶ ± 8.44 × 10⁻⁹],  **p_hi = 4.1084343962438651943 × 10⁻⁶**.

The faster C interval engine (`certc.c`) also handles this format. On this map it stalls in its known
near-collinear midpoint-ambiguity path (v5 NOTES), so the arb engine is the certificate of record.

## Independent check

`indep_check.py` shares no code with planar.c, certc.c or certify.py. It uses its own pair enumeration; overlap
areas come from Green's theorem (the part of ∂P inside Q plus the part of ∂Q inside P, by vectorised
half-plane clipping), integrated over θ by the periodic midpoint rule at M and 2M samples.

| colouring | indep_check (M = 131072 / 262144) | certified |
|---|---|---|
| hex 4-colouring `lowerbounds_v5/hex4_11335.json` | 1/p = 98.496 / 98.496 | 98.495616664 (certc), 98.4956 (arb) |
| Pritikin optimum `maps/prit_best_exact.json` | 4.298373035e-6 / 4.298373934e-6 | [4.298375e-6 ± 8e-13] (certc) |
| **this colouring** `maps/PRbest_exact.json` | **4.102413146e-6 / 4.102413413e-6** | ⊂ [4.0916, 4.1084] × 10⁻⁶ (arb) ✓ |

The float value from planar.c at M = 8192 is 4.10259e-6, consistent.

## From p₆ to e₇ and v₇ (as in de Grey–Parts)

Let G be a finite unit-distance graph with e edges that is not 6-colourable. Place G by a uniformly random
rigid motion: a translation uniform over the period cell, and an independent uniform rotation.

- Each edge is then a unit segment with uniform position and direction, so it is monochromatic with
  probability exactly p₆.
- The expected number of monochromatic edges is e·p₆.
- But every placement induces a 6-colouring of V(G), which is improper, so it has ≥ 1 monochromatic edge.

Hence e·p₆ ≥ 1, i.e. e ≥ 1/p₆ ≥ 1/p_hi = 243,401.72, so **e ≥ 243,402**.

Vertices follow from Agoston–Pálvölgyi (arXiv 2006.06285), exactly as de Grey–Parts use it:

- maxE(v), the maximum number of unit distances among v points in the plane, satisfies
  maxE(v) ≤ (29/4)^{1/3} v^{4/3} for v ≥ 521 (and their finite table below that);
- `lowerbounds_v5/bounds.py v_from_e` gives the least v with maxE(v) ≥ 243,402, namely **v ≥ 6,679**;
- the same code reproduces de Grey–Parts' pairs (e₇, v₇) = (232,646 → 6,456) and (69,451 → 2,608).

## Verify

    cd research/lowerbounds_v5
    CERT_ENGINE=arb CERT_WORKERS=2 ../../venv/bin/python3 certify.py ../chi6_devil/maps/PRbest_exact.json   # ~5 min
    cd ../chi6_devil
    ../../venv/bin/python3 indep_check.py maps/PRbest_exact.json 131072                                      # ~2 min
