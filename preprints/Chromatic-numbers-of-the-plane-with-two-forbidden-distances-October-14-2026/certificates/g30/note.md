# A smaller 6-chromatic two-distance graph in the plane

*Draft note — Henry Bass & Claude (Anthropic Fable 5), August 2026*

## 1. Statement

Let χ(ℝ²; D) denote the minimum number of colors needed to color the plane so
that no two points whose distance lies in D receive the same color. De Grey's
breakthrough [dG18] gives χ(ℝ²; {1}) ≥ 5; for two forbidden distances,
6-chromatic finite witnesses are known for exactly four ratios: d = (1+√5)/2
(Huddleston 2008, non-explicit; explicit G₁₂₆ and record 31-vertex G₃₁ by Parts
[P20]), d = 2 (Exoo–Ismailescu [EI20], reduced to 397 vertices by Parts), and
d = √3, (√2+√6)/2 (De Neve, Vanden Kerchove, Colle, Tavernier, Pickavet
[DN25], with 33 and 117 vertices respectively).

**Theorem.** There is a 30-vertex graph, realized by 30 points in the plane
with 100 pairs at Euclidean distance exactly 1 or exactly √3, whose chromatic
number is 6. Consequently χ(ℝ²; {1, √3}) ≥ 6 via a 30-vertex witness, and 30
improves the smallest known 6-chromatic two-distance graph for any ratio
(previously 31 [P20]).

## 2. The graph

Each vertex is an integer 4-vector [a₀ a₁ a₂ a₃] denoting the point
((a₀ + a₁√5)/8, (a₂√3 + a₃√15)/8) ∈ ℚ(√3, √5)-space:

```
[-6,0,-2,0]  [-5,-3,-1,1] [-5,3,-3,1]  [-4,0,-2,2] [-4,0,0,0]  [-4,0,0,4]
[-3,-3,-1,3] [-3,-3,1,1]  [-3,3,-1,1]  [-2,0,-2,4] [-2,0,0,2]  [-1,-3,-3,3]
[-1,-3,-1,1] [-1,-3,1,3]  [-1,3,-1,3]  [-1,3,1,1]  [-1,3,3,3]  [0,0,-2,2]
[0,0,0,0]    [0,0,2,2]    [1,-3,-3,1]  [1,-3,1,1]  [1,3,-1,1]  [1,3,3,1]
[2,0,-2,0]   [2,0,0,2]    [2,0,2,0]    [3,-3,1,3]  [3,3,-1,3]  [4,0,0,4]
```

Edges are exactly the pairs at distance 1 (72 edges) or √3 (28 edges).
Distance verification is exact integer arithmetic: for difference vector
(p,q,r,s), 64·dist² = p²+5q²+3r²+15s² + (2pq+6rs)√5, so dist = 1 ⟺ (64, 0)
and dist = √3 ⟺ (192, 0).

## 3. Verification

- **Not 5-colorable:** UNSAT certified independently by CaDiCaL 1.9.5 and
  Glucose 4.2 on the direct 150-variable encoding, with no symmetry-breaking
  assumptions.
- **6-colorable:** explicit coloring found by SAT.
- **Vertex-critical:** all thirty 29-vertex induced subgraphs are 5-colorable.

A self-contained verifier (`verify30.py`, ~60 lines, python-sat) recomputes
everything from the integer vectors in seconds.

## 4. Method

The graph was found by SAT-guided iterated local search over a
bounded-coefficient slice of the module
{((a₀+a₁√5)/8, (a₂√3+a₃√15)/8) : aᵢ ∈ ℤ, a₀≡a₁, a₂≡a₃ (mod 2)}
(≈10⁴ points within radius 3.4), seeded from the 33-vertex graph of [DN25]
(coordinates from their Appendix Table 1). Moves: randomized greedy vertex
deletion under an incremental CaDiCaL oracle with selector-variable
assumptions, perturbation by adjacency-weighted candidate insertion, and
remove-k re-descend kicks. The 30-vertex minimum was reached within ~10⁴
oracle calls (≈1 minute on an Apple M4 Pro); it shares 23 vertices with the
[DN25] graph, omits 10, and adds 7 new vertices. The same run certifies
vertex-criticality; whether a 29-vertex 6-chromatic two-distance graph exists
(for any ratio) remains open — note v₆ ≥ 42 for unit-distance graphs [dGP22]
does not apply to two-distance graphs, where the true lower bound is far
smaller (K₅-free arguments give only trivial bounds for {1,√3}).

## References

- [dG18] A. de Grey, The chromatic number of the plane is at least 5,
  Geombinatorics 28 (2018).
- [P20] J. Parts, A small 6-chromatic two-distance graph in the plane,
  Geombinatorics 29(3) (2020), arXiv:2010.12656.
- [EI20] G. Exoo, D. Ismailescu, A 6-chromatic two-distance graph in the
  plane, Geombinatorics 29(3) (2020), arXiv:1909.13177.
- [DN25] J. De Neve, F. Vanden Kerchove, D. Colle, W. Tavernier, M. Pickavet,
  On the chromatic number of the plane with two forbidden distances,
  Amer. Math. Monthly 132(10):1007–1022 (2025).
- [dGP22] A. de Grey, J. Parts, On lower bounds of the order of k-chromatic
  unit distance graphs, Geombinatorics 32(2) (2022), arXiv:2303.14714.
